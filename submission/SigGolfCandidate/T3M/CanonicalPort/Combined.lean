import Mathlib
import Mathlib.Data.Nat.Bitwise
import SigGolfCandidate.Rv
import SigGolfCandidate.T3.Core
import SigGolfCandidate.T3.Nonbinary.AcceptedCost
import SigGolfCandidate.T3.Nonbinary.SourceDigits
import SigGolfCandidate.T3.Proofs
import SigGolfCandidate.T3.Rev
import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.T3M.Search.CsBlocks
import SigGolfCandidate.T3M.Search.TopTables
import SigGolfCandidate.T3M.Search.TopTail
import SigGolfCandidate.T3M.Search.TopWindow
import SigGolfCandidate.T3M.Sim
import SigGolfCandidate.T3M.Verify.CanonicalNative
import SigGolfCandidate.T3M.Witness.VerifyP


set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart0

namespace SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option linter.unusedSimpArgs false

def pairWeight (a b : Nat) : Nat := if a < 125 ∧ b < 125 then rankWeight a + rankWeight b else 255

def pairLookup (r : Nat) : Nat := pairWeight (r % 128) (r / 128)

theorem pairLookup_components (a b : Nat) (ha : a < 128) :
    pairLookup (a + 128 * b) = pairWeight a b := by
  unfold pairLookup
  congr 1 <;> omega

theorem pairWeight_le (a b : Nat) : pairWeight a b ≤ 255 := by
  unfold pairWeight
  split_ifs
  · have := rankWeight_le a; have := rankWeight_le b; omega
  · omega

theorem pairWeight_eq (a b : Nat) (ha : a < 125) (hb : b < 125) :
    pairWeight a b = rankLookup a + rankLookup b := by simp [pairWeight,rankLookup,ha,hb]

theorem pairWeight_bad_left (a b : Nat) (ha : 125 ≤ a) : pairWeight a b = 255 := by
  simp [pairWeight,show ¬ a < 125 by omega]

theorem pairWeight_bad_right (a b : Nat) (hb : 125 ≤ b) : pairWeight a b = 255 := by
  simp [pairWeight,show ¬ b < 125 by omega]

def compressedSum (f : Nat → Nat) : Nat :=
  pairWeight (f 0) (f 1) + pairWeight (f 2) (f 3) +
  pairWeight (f 4) (f 5) + pairWeight (f 6) (f 7) + rankLookup (f 8) +
  pairWeight (f 9) (f 10) + pairWeight (f 11) (f 12) +
  pairWeight (f 13) (f 14) + pairWeight (f 15) (f 16)

def fullSum (f : Nat → Nat) : Nat := ((List.range 17).map fun i => rankLookup (f i)).sum

theorem compressedSum_good (f : Nat → Nat) (h : ∀ i, i < 17 → f i < 125) :
    compressedSum f = fullSum f := by
  unfold compressedSum
  rw [pairWeight_eq _ _ (h 0 (by decide)) (h 1 (by decide)),
      pairWeight_eq _ _ (h 2 (by decide)) (h 3 (by decide)),
      pairWeight_eq _ _ (h 4 (by decide)) (h 5 (by decide)),
      pairWeight_eq _ _ (h 6 (by decide)) (h 7 (by decide)),
      pairWeight_eq _ _ (h 9 (by decide)) (h 10 (by decide)),
      pairWeight_eq _ _ (h 11 (by decide)) (h 12 (by decide)),
      pairWeight_eq _ _ (h 13 (by decide)) (h 14 (by decide)),
      pairWeight_eq _ _ (h 15 (by decide)) (h 16 (by decide))]
  simp only [fullSum,List.range_succ,List.range_zero,List.nil_append,List.map_append,
    List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil]
  omega

theorem compressedSum_bad (f : Nat → Nat) (i : Nat) (hi : i < 17) (hb : 125 ≤ f i) :
    255 ≤ compressedSum f := by
  unfold compressedSum
  interval_cases i
  all_goals first
    | rw [pairWeight_bad_left _ _ hb]; omega
    | rw [pairWeight_bad_right _ _ hb]; omega
    | rw [rankLookup_bad _ (by omega)]; omega

theorem fullSum_bad (f : Nat → Nat) (i : Nat) (hi : i < 17) (hb : 125 ≤ f i) :
    255 ≤ fullSum f := by
  have hx : rankLookup (f i) ≤ fullSum f := by
    unfold fullSum
    exact List.single_le_sum (by intro x hx; omega) _ (List.mem_map.mpr ⟨i, by simp [hi], rfl⟩)
  rw [rankLookup_bad _ (by omega)] at hx
  exact hx

/-- Poisoning an invalid pair once preserves every sum target below255. -/
theorem compressedSum_target (f : Nat → Nat) (tail target : Nat) (ht : target < 255) :
    compressedSum f + tail = target ↔ fullSum f + tail = target := by
  by_cases h : ∀ i, i < 17 → f i < 125
  · rw [compressedSum_good f h]
  · push_neg at h
    obtain ⟨i,hi,hb⟩ := h
    have h1 := compressedSum_bad f i hi hb
    have h2 := fullSum_bad f i hi hb
    omega

def pairedLookupSum (v : Digest) : Nat := compressedSum (topRank v) + tailWeight v

theorem pairedLookupSum_eq_iff (v : Digest) : pairedLookupSum v = 126 ↔ topLookupSum v = 126 := by
  change compressedSum (topRank v) + tailWeight v = 126 ↔ _
  rw [compressedSum_target _ _ _ (by decide)]
  rfl

/-- The optimized LUT uses the exact same strong source decoder. -/
theorem decode_top_paired (v : Digest) :
    SigGolfCandidate.T3.decode 0 v =
      if v.toNat < 2 ^ 125 ∧ pairedLookupSum v = 126 then some (topDigits v) else none := by
  simp only [decode_top_lookup,pairedLookupSum_eq_iff]

end SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary

end CanonicalPortPart0

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart1

namespace SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

abbrev PAIR_DATA : Nat := 0xFF8000
abbrev TAIL_DATA : Nat := 0xFFC000

def tailSum (r : Nat) : Nat := r % 4 + (r / 4) % 4 + r / 16

theorem tailSum_le (r : Nat) (hr : r < 64) : tailSum r ≤ 9 := by unfold tailSum; omega

theorem tailSum_eq (v : Digest) (hv : v.toNat < 2 ^ 125) :
    tailSum (v.toNat / 2 ^ 119) = tailWeight v := by
  unfold tailSum tailWeight
  simp only [Nat.div_div_eq_div_mul]
  norm_num
  omega

def PairTableOK (s : MachineState) : Prop :=
  ∀ r : Nat, r < 16384 → s.getByte (BitVec.ofNat 64 (PAIR_DATA + r)) = BitVec.ofNat 8 (pairLookup r)

def TailTableOK (s : MachineState) : Prop :=
  ∀ r : Nat, r < 64 → s.getByte (BitVec.ofNat 64 (TAIL_DATA + r)) = BitVec.ofNat 8 (126 - tailSum r)

structure PackedTables (s : MachineState) : Prop where
  pair : PairTableOK s
  tail : TailTableOK s

theorem PackedTables.frame {s t : MachineState} (ht : PackedTables s)
    (hf : Frame s t (fun _ => False)) : PackedTables t := by
  constructor
  · intro r hr
    exact (hf.getByte (by unfold PAIR_DATA; omega) (by simp)).trans (ht.pair r hr)
  · intro r hr
    exact (hf.getByte (by unfold TAIL_DATA; omega) (by simp)).trans (ht.tail r hr)

theorem PackedTables.congr {s t : MachineState} (ht : PackedTables s)
    (hm : ∀ A, PAIR_DATA ≤ A → A + 8 ≤ 2 ^ 24 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : PackedTables t := by
  constructor
  · intro r hr
    rw [getByte_eq_word _ _ (by unfold PAIR_DATA; omega),
      hm _ (by unfold PAIR_DATA; omega) (by unfold PAIR_DATA; omega),
      ← getByte_eq_word _ _ (by unfold PAIR_DATA; omega)]
    exact ht.pair r hr
  · intro r hr
    rw [getByte_eq_word _ _ (by unfold TAIL_DATA; omega),
      hm _ (by unfold PAIR_DATA TAIL_DATA; omega) (by unfold TAIL_DATA; omega),
      ← getByte_eq_word _ _ (by unfold TAIL_DATA; omega)]
    exact ht.tail r hr

theorem PairTableOK.rank (s : MachineState) (ht : PairTableOK s) (r : Nat) (hr : r < 16384) :
    (s.getByte (BitVec.ofNat 64 (PAIR_DATA + r))).zeroExtend 64 = BitVec.ofNat 64 (pairLookup r) := by
  rw [ht r hr]
  have h := pairWeight_le (r % 128) (r / 128)
  change pairLookup r ≤ 255 at h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem TailTableOK.rank (s : MachineState) (ht : TailTableOK s) (r : Nat) (hr : r < 64) :
    (s.getByte (BitVec.ofNat 64 (TAIL_DATA + r))).zeroExtend 64 = BitVec.ofNat 64 (126 - tailSum r) := by
  rw [ht r hr]
  have h := tailSum_le r hr
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega
end SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary

end CanonicalPortPart1

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart2

/-!
# Path-guided symbolic execution for the T3 verify image

(Adapted from the five-layer `Verify/Exec.lean`, which it replaces: generic in the instruction lookup
`look`, so it serves every T3M verify stream; no image is imported here.)

`pathAux cfg look stops fuel pc dirs σ brs` symbolically executes code fetched through `look`
(instruction index ↦ word), starting at `pc` from the symbolic state `σ`. Unlike `symRun` it does
not stop at jumps and branches: a jump with a constant target is followed, and a branch whose
condition is symbolic takes the direction given by the next element of `dirs`, recording the
assumed outcome as a *branch obligation* (`Br`). It stops before an `ECALL` (`ecall = true`) or
after reaching a pc in `stops` (`ecall = false`).

The initial symbolic state `σK known` has the registers in `known` replaced by constants.
-/

namespace SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-- An assumed branch outcome: `op.eval x y = d`. -/
structure Br where
  op : CmpOp
  x : E
  y : E
  d : Bool
  deriving Repr

def Br.holds (s : MachineState) (b : Br) : Prop := b.op.eval (b.x.eval s) (b.y.eval s) = b.d

structure PRes where
  st : SymState
  pc : Word
  ecall : Bool
  steps : Nat
  cycles : Nat
  brs : List Br
  /-- stopped after a jump with a symbolic target (the final pc is this expression) -/
  spc : Option E := none
  deriving Repr

def PRes.finalPc (r : PRes) (s : MachineState) : Word :=
  match r.spc with
  | some e => e.eval s
  | none => r.pc

def PRes.toState (r : PRes) (s : MachineState) : MachineState := r.st.toState s (r.finalPc s)

/-- Guidance for data-dependent control flow: a branch direction, or "stop at a symbolic jump". -/
inductive Dir where
  | br (d : Bool)
  | jmp
  deriving Repr

/-- Next pc of a micro-op, resolving a symbolic branch with `dirs`. `inr e` = stop at the
symbolic target `e`. -/
def nextSym (pc : Word) (ctl : Option E) (dirs : List Dir) :
    Option ((Word × List Dir × List Br) ⊕ E) :=
  match ctl with
  | none => some (.inl (pc + 4, dirs, []))
  | some (.c t) => some (.inl (t, dirs, []))
  | some (.ite op x y (.c a) (.c b)) =>
    match dirs with
    | .br d :: ds => some (.inl (if d then a else b, ds, [⟨op, x, y, d⟩]))
    | _ => none
  | some e =>
    match dirs with
    | .jmp :: _ => some (.inr e)
    | _ => none

def pathAux (cfg : Config) (look : Nat → Option (BitVec 32)) (stops : List Word) :
    Nat → Word → List Dir → SymState → List Br → Option PRes
  | 0, _, _, _, _ => none
  | f + 1, pc, dirs, σ, brs =>
    if pc.toNat < 0x1000 || pc.toNat % 4 != 0 then none else
    match look ((pc.toNat - 0x1000) / 4) with
    | none => none
    | some w =>
      match decodeInstruction w with
      | none => none
      | some i =>
        if isEcall i then some ⟨σ, pc, true, 0, 0, brs, none⟩ else
        match classify i with
        | none => none
        | some m =>
          match symMicro cfg pc σ m with
          | none => none
          | some (σ', ctl) =>
            match nextSym pc ctl dirs with
            | none => none
            | some (.inr e) => some ⟨σ', 0, false, 1, instructionCycles i, brs, some e⟩
            | some (.inl (pc', dirs', nb)) =>
              if stops.contains pc' then some ⟨σ', pc', false, 1, instructionCycles i, nb ++ brs, none⟩
              else
                match pathAux cfg look stops f pc' dirs' σ' (nb ++ brs) with
                | none => none
                | some r => some { r with steps := r.steps + 1, cycles := instructionCycles i + r.cycles }

/-! ## Soundness -/

/-- `look` agrees with the image code. -/
def LookOK (image : Image) (look : Nat → Option (BitVec 32)) : Prop :=
  ∀ n w, look n = some w → image.code[n]? = some w

theorem nextSym_sound {pc pc' : Word} {ctl : Option E} {dirs ds : List Dir} {nb : List Br}
    (h : nextSym pc ctl dirs = some (.inl (pc', ds, nb))) (s : MachineState) (hb : ∀ b ∈ nb, b.holds s) :
    nextPc s pc ctl = pc' := by
  unfold nextSym at h
  split at h
  · simp only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, -⟩ := h; rfl
  · simp only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, -⟩ := h; rfl
  · rename_i op x y a b
    split at h
    · rename_i d ds'
      simp only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      have := hb _ (List.mem_singleton_self _)
      simp only [Br.holds] at this
      simp only [nextPc, E.eval, this]
    · cases h
  · split at h
    · cases h
    · cases h

theorem nextSym_sound_jmp {pc : Word} {ctl : Option E} {dirs : List Dir} {e : E}
    (h : nextSym pc ctl dirs = some (.inr e)) (s : MachineState) :
    nextPc s pc ctl = e.eval s := by
  unfold nextSym at h
  split at h
  · cases h
  · cases h
  · split at h <;> cases h
  · split at h
    · rename_i e' _ _ _ _ _
      simp only [Option.some.injEq, Sum.inr.injEq] at h
      subst h; rfl
    · cases h

theorem fetch_of_look {image : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK image look)
    {pc : Word} {w : BitVec 32} (hpc : (pc.toNat < 0x1000 || pc.toNat % 4 != 0) = false)
    (hw : look ((pc.toNat - 0x1000) / 4) = some w) (t : MachineState) (ht : t.pc = pc) :
    fetch image t = decodeInstruction w := by
  unfold Riscv.fetch
  rw [ht, hpc]
  simp only [Bool.false_eq_true, if_false, hl _ _ hw]
  rfl

theorem pathAux_sound (cfg : Config) (image : Image) (look : Nat → Option (BitVec 32))
    (stops : List Word) (hl : LookOK image look) (s : MachineState) :
    ∀ (fuel : Nat) (pc : Word) (dirs : List Dir) (σ : SymState) (brs : List Br) (r : PRes),
      pathAux cfg look stops fuel pc dirs σ brs = some r →
      (∀ o ∈ r.st.obl, o.holds s) → (∀ b ∈ r.brs, b.holds s) →
      Steps image (σ.toState s pc) r.steps r.cycles (r.toState s) ∧ σ.obl ⊆ r.st.obl ∧
        brs ⊆ r.brs ∧ (r.ecall = true → fetch image (r.toState s) = some (.base .ECALL)) := by
  intro fuel
  induction fuel with
  | zero => intro pc dirs σ brs r h; simp [pathAux] at h
  | succ f ih =>
    intro pc dirs σ brs r h hobl hbr
    simp only [pathAux] at h
    split at h
    · cases h
    · rename_i hpc
      have hpc' : (pc.toNat < 0x1000 || pc.toNat % 4 != 0) = false := by simpa using hpc
      split at h
      · cases h
      · rename_i w hw
        split at h
        · cases h
        · rename_i i hdec
          have hfetch : ∀ t : MachineState, t.pc = pc → fetch image t = some i := fun t ht =>
            (fetch_of_look hl hpc' hw t ht).trans hdec
          split at h
          · rename_i he
            simp only [Option.some.injEq] at h; subst h
            refine ⟨Steps.refl _, List.Subset.refl _, List.Subset.refl _, fun _ => ?_⟩
            rw [hfetch _ rfl, isEcall_eq he]
          · split at h
            · cases h
            · rename_i m hcl
              split at h
              · cases h
              · rename_i σ' ctl hm
                split at h
                · cases h
                · rename_i e hns
                  simp only [Option.some.injEq] at h; subst h
                  obtain ⟨hsub', hexec⟩ := symMicro_sound hm s hobl
                  refine ⟨?_, hsub', List.Subset.refl _, fun h => by cases h⟩
                  refine Steps.step (i := i) (hfetch _ rfl) ?_ (Steps.refl _)
                  rw [classify_sound hcl, hexec, nextSym_sound_jmp hns s]; rfl
                · rename_i pc' dirs' nb hns
                  split at h
                  · simp only [Option.some.injEq] at h; subst h
                    have hnb : ∀ b ∈ nb, b.holds s := fun b hb => hbr b (List.mem_append_left _ hb)
                    obtain ⟨hsub', hexec⟩ := symMicro_sound hm s hobl
                    refine ⟨?_, hsub', List.subset_append_right _ _, fun h => by cases h⟩
                    refine Steps.step (i := i) (hfetch _ rfl) ?_ (Steps.refl _)
                    rw [classify_sound hcl, hexec, nextSym_sound hns s hnb]; try rfl
                  · split at h
                    · cases h
                    · rename_i r' hr'
                      simp only [Option.some.injEq] at h; subst h
                      obtain ⟨hsteps, hsub, hbsub, hec⟩ := ih pc' dirs' σ' (nb ++ brs) r' hr' hobl hbr
                      have hnb : ∀ b ∈ nb, b.holds s := fun b hb =>
                        hbr b (hbsub (List.mem_append_left _ hb))
                      obtain ⟨hsub', hexec⟩ := symMicro_sound hm s (fun o ho => hobl o (hsub ho))
                      refine ⟨?_, List.Subset.trans hsub' hsub,
                        List.Subset.trans (List.subset_append_right _ _) hbsub, hec⟩
                      refine Steps.step (hfetch _ rfl) ?_ hsteps
                      rw [classify_sound hcl, hexec, nextSym_sound hns s hnb]; try rfl

/-! ## Initial state with known registers -/

def RegFile.withKnown (known : List (Reg × Word)) : RegFile :=
  known.foldl (fun rf p => rf.set p.1 (.c p.2)) RegFile.init

def σK (known : List (Reg × Word)) : SymState := ⟨RegFile.withKnown known, [], []⟩

theorem RegFile.withKnown_eval (s : MachineState) (known : List (Reg × Word))
    (hk : ∀ p ∈ known, s.getReg p.1 = p.2) (r : Reg) :
    ((RegFile.withKnown known).get r).eval s = s.getReg r := by
  unfold RegFile.withKnown
  suffices ∀ (l : List (Reg × Word)) (rf : RegFile), (∀ p ∈ l, s.getReg p.1 = p.2) →
      (∀ r, (rf.get r).eval s = s.getReg r) →
      ∀ r, ((l.foldl (fun rf p => rf.set p.1 (.c p.2)) rf).get r).eval s = s.getReg r from
    this known _ hk (RegFile.init_get_eval s) r
  intro l
  induction l with
  | nil => intro rf _ h; exact h
  | cons p l ih =>
    intro rf hl hrf
    obtain ⟨q, v⟩ := p
    simp only [List.foldl_cons]
    apply ih _ (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    intro r
    by_cases hr : r = q
    · subst hr
      by_cases h0 : r = .x0
      · subst h0; rfl
      · rw [RegFile.get_set_self _ _ h0]; simp only [E.eval]
        exact (hl (r, v) (List.mem_cons_self ..)).symm
    · rw [RegFile.get_set_ne _ _ hr]; exact hrf r

theorem σK_toState (s : MachineState) (known : List (Reg × Word))
    (hk : ∀ p ∈ known, s.getReg p.1 = p.2) : (σK known).toState s s.pc = s := by
  apply MachineState.ext' <;> try rfl
  funext r
  simp only [SymState.toState, σK]
  split
  · rename_i h; subst h; rfl
  · rename_i h
    rw [RegFile.withKnown_eval s known hk r]
    cases r <;> first | exact absurd rfl h | rfl

/-- Soundness of a path run from `σK known`. -/
theorem pathRun_sound {cfg : Config} {image : Image} {look : Nat → Option (BitVec 32)}
    {stops : List Word} {fuel : Nat} {pc : Word} {dirs : List Dir} {known : List (Reg × Word)}
    {r : PRes} (h : pathAux cfg look stops fuel pc dirs (σK known) [] = some r)
    (hl : LookOK image look) (s : MachineState) (hpc : s.pc = pc)
    (hk : ∀ p ∈ known, s.getReg p.1 = p.2) (hobl : ∀ o ∈ r.st.obl, o.holds s)
    (hbr : ∀ b ∈ r.brs, b.holds s) :
    Steps image s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch image (r.toState s) = some (.base .ECALL)) := by
  obtain ⟨h1, -, -, h4⟩ := pathAux_sound cfg image look stops hl s fuel pc dirs _ [] r h hobl hbr
  rw [← hpc, σK_toState s known hk] at h1
  exact ⟨h1, h4⟩

/-! ## Structural equality checks (for kernel-checked families of runs) -/

def listBeq {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && listBeq f as bs
  | _, _ => false

theorem listBeq_eq {α : Type} {f : α → α → Bool} (hf : ∀ a b, f a b = true → a = b) :
    ∀ {l l' : List α}, listBeq f l l' = true → l = l' := by
  intro l
  induction l with
  | nil => intro l' h; cases l' <;> simp_all [listBeq]
  | cons a as ih =>
    intro l' h
    cases l' with
    | nil => simp [listBeq] at h
    | cons b bs =>
      simp only [listBeq, Bool.and_eq_true] at h
      rw [hf _ _ h.1, ih h.2]

def RegFile.beq (a b : RegFile) : Bool := listBeq E.beq a.fields b.fields

theorem RegFile.beq_eq {a b : RegFile} (h : RegFile.beq a b = true) : a = b := by
  have := listBeq_eq (fun _ _ => E.beq_eq) h
  cases a; cases b
  simp only [RegFile.fields, List.cons.injEq] at this
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, -⟩ := this
  subst_vars; rfl

def pairBeq (a b : Addr × E) : Bool := Addr.beq a.1 b.1 && E.beq a.2 b.2

theorem pairBeq_eq {a b : Addr × E} (h : pairBeq a b = true) : a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [pairBeq, Bool.and_eq_true] at h
  rw [Addr.beq_eq h.1, E.beq_eq h.2]

def SymState.beq (a b : SymState) : Bool :=
  RegFile.beq a.regs b.regs && listBeq pairBeq a.mem b.mem && listBeq Oblig.beq a.obl b.obl

theorem SymState.beq_eq {a b : SymState} (h : SymState.beq a b = true) : a = b := by
  obtain ⟨ar, am, ao⟩ := a; obtain ⟨br, bm, bo⟩ := b
  simp only [SymState.beq, Bool.and_eq_true] at h
  rw [RegFile.beq_eq h.1.1, listBeq_eq (fun _ _ => pairBeq_eq) h.1.2,
    listBeq_eq (fun _ _ => Oblig.beq_eq) h.2]

def Br.beq (a b : Br) : Bool :=
  decide (a.op = b.op) && E.beq a.x b.x && E.beq a.y b.y && a.d == b.d

theorem Br.beq_eq {a b : Br} (h : Br.beq a b = true) : a = b := by
  obtain ⟨o, x, y, d⟩ := a; obtain ⟨o', x', y', d'⟩ := b
  simp only [Br.beq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [h1, E.beq_eq h2, E.beq_eq h3, h4]

def optEBeq : Option E → Option E → Bool
  | none, none => true
  | some a, some b => E.beq a b
  | _, _ => false

theorem optEBeq_eq {a b : Option E} (h : optEBeq a b = true) : a = b := by
  cases a <;> cases b <;> simp [optEBeq] at h ⊢
  exact E.beq_eq h

def PRes.beq (a b : PRes) : Bool :=
  SymState.beq a.st b.st && a.pc.toNat == b.pc.toNat && a.ecall == b.ecall &&
    a.steps == b.steps && a.cycles == b.cycles && listBeq Br.beq a.brs b.brs && optEBeq a.spc b.spc

theorem PRes.beq_eq {a b : PRes} (h : PRes.beq a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := a; obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp only [PRes.beq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  rw [SymState.beq_eq h1, BitVec.eq_of_toNat_eq h2, h3, h4, h5, listBeq_eq (fun _ _ => Br.beq_eq) h6,
    optEBeq_eq h7]

/-- `o = some r`, as a Boolean check. -/
def optBeq (o : Option PRes) (r : PRes) : Bool :=
  match o with
  | some r' => PRes.beq r' r
  | none => false

theorem optBeq_eq {o : Option PRes} {r : PRes} (h : optBeq o r = true) : o = some r := by
  cases o with
  | none => simp [optBeq] at h
  | some r' => simp only [optBeq] at h; rw [PRes.beq_eq h]

end SigGolfCandidate.T3M.CanonicalPort.Verify

end CanonicalPortPart2

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart3

namespace SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify (lookup_chunks)

abbrev image : Image := CanonicalNative.fixture
abbrev vChunks := CanonicalNative.chunks
abbrev vSup := CanonicalNative.supers
abbrev vlook := CanonicalNative.look
theorem vChunks_ok : (vChunks.dropLast.all fun c => c.length==256)=true := CanonicalNative.chunks_ok
theorem vSup_ok : (vSup.dropLast.all fun c => c.length==32)=true := CanonicalNative.supers_ok
theorem vSup_flatten : vSup.flatten=vChunks := CanonicalNative.supers_flatten
theorem verifyCode_eq : CanonicalNative.fixture.code=vChunks.flatten := rfl
theorem vlook_ok : LookOK image vlook := CanonicalNative.look_ok
/-! ## Sequential code access -/

/-- `verifyCode.drop i`, computed through the two levels. -/
def codeFrom (i : Nat) : List (BitVec 32) :=
  (((vSup.drop (i / 8192)).flatten.drop (i / 256 % 32)).flatten).drop (i % 256)

theorem drop_chunks {α : Type} (B : Nat) : ∀ (cs : List (List α)) (k : Nat),
    (cs.dropLast.all fun c => c.length == B) = true → k < cs.length →
    cs.flatten.drop (B * k) = (cs.drop k).flatten := by
  intro cs
  induction cs with
  | nil => intro k _ hk; simp at hk
  | cons c cs ih =>
    intro k hall hk
    cases k with
    | zero => simp
    | succ k =>
      cases cs with
      | nil => simp at hk
      | cons c' cs' =>
        have hlen : c.length = B := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
          exact hall.1
        have hall' : ((c' :: cs').dropLast.all fun c => c.length == B) = true := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true] at hall
          exact hall.2
        have := ih k hall' (by simp at hk ⊢; omega)
        simp only [List.flatten_cons, List.drop_succ_cons] at this ⊢
        rw [show B * (k + 1) = c.length + B * k by rw [hlen]; ring, ← List.drop_drop,
          List.drop_left]
        exact this

set_option maxRecDepth 100000 in
theorem vChunks_length : vChunks.length = 910 := by decide +kernel

set_option maxRecDepth 100000 in
theorem vSup_length : vSup.length = 29 := by decide +kernel

theorem codeFrom_eq (i : Nat) (hi : i / 256 < 910) : codeFrom i = CanonicalNative.fixture.code.drop i := by
  unfold codeFrom
  have hs : i / 8192 < vSup.length := by
    rw [vSup_length]; have : i / 8192 = i / 256 / 32 := by rw [Nat.div_div_eq_div_mul]
    omega
  have e1 : vSup.flatten.drop (32 * (i / 8192)) = (vSup.drop (i / 8192)).flatten :=
    drop_chunks 32 vSup (i / 8192) vSup_ok hs
  have e2 : vChunks.flatten.drop (256 * (i / 256)) = (vChunks.drop (i / 256)).flatten :=
    drop_chunks 256 vChunks (i / 256) vChunks_ok (by rw [vChunks_length]; exact hi)
  rw [verifyCode_eq, ← e1, vSup_flatten, List.drop_drop]
  have e3 : vChunks.drop (32 * (i / 8192) + i / 256 % 32) = vChunks.drop (i / 256) := by
    congr 1
    have : i / 8192 = i / 256 / 32 := by rw [Nat.div_div_eq_div_mul]
    omega
  rw [e3, ← e2, List.drop_drop]
  congr 1
  omega

set_option maxRecDepth 100000 in
theorem vChunks_le : (vChunks.all fun c => decide (c.length ≤ 256)) = true := by decide +kernel

theorem flatten_len_le : ∀ (cs : List (List (BitVec 32))),
    (cs.all fun c => decide (c.length ≤ 256)) = true → cs.flatten.length ≤ 256 * cs.length
  | [], _ => by simp
  | c :: cs, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have := flatten_len_le cs h.2
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem verifyCode_length : CanonicalNative.fixture.code.length ≤ 256 * 910 := by
  rw [verifyCode_eq, ← vChunks_length]; exact flatten_len_le _ vChunks_le

/-- Code placement of the image suffix from instruction `i` (at pc `0x1000 + 4 i`, M0's `pcOf i`). -/
theorem codeAt_from (i : Nat) (hi : i / 256 < 910) :
    CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * i)) (codeFrom i) := by
  have hl := verifyCode_length
  have hp : (BitVec.ofNat 64 (0x1000 + 4 * i)).toNat = 0x1000 + 4 * i := by
    simp only [BitVec.toNat_ofNat]; omega
  rw [codeFrom_eq i hi]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hp]; omega
  · rw [hp]; omega
  · rw [hp, List.length_drop]; omega
  · rw [hp, show (0x1000 + 4 * i - 0x1000) / 4 = i by omega]
    try exact List.prefix_refl _

end SigGolfCandidate.T3M.CanonicalPort.Verify

end CanonicalPortPart3

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart4

/-!
# The verify simulation judgment (T3M)

Adapted from the five-layer `Verify/Judg.lean` to the T3M foundation (`T3M.countCalls`, Core's
programs realized by `mrealize 0`, organizer queries `toQ`):

* `Good s N C X` : from `s`, with any fuel `≥ N`, the observable `(exit = success, hashCalls)` of the
  execution is distributed as `X`, and for every fixed oracle the run finishes (`exit ≠ unfinished`)
  within `C` cycles (the **all-oracle bound**);
* `GoodQ s N C Q A X` : moreover every accepting run satisfies `Q` and takes at most `A` cycles (the
  **accepting-run bound**);
* `cc oa K` : run `oa` counting its oracle calls, then continue with `K`; `ccM p K := cc (mrealize 0 p) K`
  for Core programs `p : T3.M α` (`ccM_pure`, `ccM_bind`, `ccM_map`, `ccM_ite`);
* one HASH `ECALL`: `Good.query`/`GoodQ.query` (any query), `*.publicHash_bind`, `*.shortHash_bind`
  (Core's `publicHash input` / `shortHash input` with `hashInput s = toQ (pad64 input)`);
* HALT: `Good.halt`, `GoodQ.halt`, `GoodQ.reject` (HALT(1)), `GoodQ.accept` (HALT(0)).

The final statement of the verify proof is `GoodQ s₀ fuelBound cycleBoundAll True cycleBound
(ccM (verifyP m pk w) Kb)` with `Kb b = pure (b, 0)`, i.e. `cc_Kb`: `ccM p Kb = countCalls (mrealize 0 p)`.
-/

namespace SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M publicHash shortHash pad64 HashOutput Digest)

abbrev Obs := Bool × Nat

def obs (e : Execution) : Obs := (decide (e.exit = .success), e.hashCalls)

def Good (s : MachineState) (N C : Nat) (X : OracleComp HashSpec Obs) : Prop :=
  ∀ F, N ≤ F → obs <$> Riscv.execute F image s = X ∧
    ∀ hash : Hash, (evalWithAnswerFn hash (Riscv.execute F image s)).exit ≠ .unfinished ∧
      (evalWithAnswerFn hash (Riscv.execute F image s)).cycles ≤ C

@[simp] theorem obs_charge (e : Execution) (c b : Nat) :
    obs (e.charge c 0 b) = obs e := by
  cases e; simp [obs, Execution.charge]

theorem obs_charge1 (e : Execution) (c b : Nat) :
    obs (e.charge c 1 b) = ((obs e).1, 1 + (obs e).2) := by
  cases e; rfl

theorem Good.mono {s : MachineState} {N C N' C' : Nat} {X : OracleComp HashSpec Obs}
    (h : Good s N C X) (hN : N ≤ N') (hC : C ≤ C') : Good s N' C' X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F (by omega)
  exact ⟨h1, fun hash => ⟨(h2 hash).1, by have := (h2 hash).2; omega⟩⟩

theorem Good.congr {s : MachineState} {N C : Nat} {X Y : OracleComp HashSpec Obs}
    (h : Good s N C X) (hXY : X = Y) : Good s N C Y := hXY ▸ h

theorem Good.steps {s t : MachineState} {k c N C : Nat} {X : OracleComp HashSpec Obs}
    (hst : Steps image s k c t) (h : Good t N C X) : Good s (N + k) (C + c) X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h (F - k) (by omega)
  have hF' : F = (F - k) + k := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hst.execute_le (by omega : k ≤ F), Functor.map_map]
    simp only [obs_charge]
    exact h1
  · rw [hF', hst.evalWith hash (F - k)]
    simp only [Execution.charge_exit, Execution.charge_cycles]
    exact ⟨(h2 hash).1, by have := (h2 hash).2; omega⟩

theorem Good.steps' {s t : MachineState} {k c N C N' C' : Nat} {X : OracleComp HashSpec Obs}
    (hst : Steps image s k c t) (h : Good t N C X) (hN : N + k ≤ N') (hC : C + c ≤ C') :
    Good s N' C' X := (h.steps hst).mono hN hC

/-! ## The counting continuation -/

def cc {α : Type} (oa : OracleComp HashSpec α) (K : α → OracleComp HashSpec Obs) :
    OracleComp HashSpec Obs :=
  countCalls oa >>= fun p => (fun q => (q.1, p.2 + q.2)) <$> K p.1

@[simp] theorem cc_pure {α : Type} (a : α) (K : α → OracleComp HashSpec Obs) :
    cc (pure a) K = K a := by
  simp only [cc, countCalls, countWith_pure, pure_bind, Nat.zero_add]
  exact id_map' _

theorem cc_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β)
    (K : β → OracleComp HashSpec Obs) : cc (oa >>= f) K = cc oa (fun a => cc (f a) K) := by
  simp only [cc, countCalls_bind, bind_assoc, map_bind, Functor.map_map, bind_map_left]
  congr 1; funext p; congr 1; funext r
  simp only [Nat.add_assoc]

theorem cc_map {α β : Type} (f : α → β) (oa : OracleComp HashSpec α)
    (K : β → OracleComp HashSpec Obs) : cc (f <$> oa) K = cc oa (fun a => K (f a)) := by
  rw [map_eq_bind_pure_comp, cc_bind]
  simp only [Function.comp, cc_pure]

theorem cc_query (q : Query) (K : BitVec 256 → OracleComp HashSpec Obs) :
    cc (liftM (HashSpec.query q) : OracleComp HashSpec _) K = (do
      let a ← (liftM (HashSpec.query q) : OracleComp HashSpec _)
      (fun r => (r.1, 1 + r.2)) <$> K a) := by
  simp only [cc, countCalls_query, bind_map_left]

/-- The final continuation: report the verdict, no further calls. -/
def Kb : Bool → OracleComp HashSpec Obs := fun b => pure (b, 0)

theorem cc_Kb (oa : OracleComp HashSpec Bool) : cc oa Kb = countCalls oa := by
  simp only [cc, Kb, map_pure, Nat.add_zero]
  exact bind_pure _

/-! ## Core programs -/

/-- The counting continuation of a Core program realized on the machine (verify is public-only,
the secret is `0`). -/
def ccM {α : Type} (p : M α) (K : α → OracleComp HashSpec Obs) : OracleComp HashSpec Obs :=
  cc (mrealize 0 p) K

@[simp] theorem ccM_pure {α : Type} (a : α) (K : α → OracleComp HashSpec Obs) :
    ccM (pure a : M α) K = K a := by
  simp only [ccM, mrealize_pure, cc_pure]

theorem ccM_bind {α β : Type} (p : M α) (f : α → M β) (K : β → OracleComp HashSpec Obs) :
    ccM (p >>= f) K = ccM p (fun a => ccM (f a) K) := by
  simp only [ccM, mrealize_bind, cc_bind]

theorem ccM_map {α β : Type} (f : α → β) (p : M α) (K : β → OracleComp HashSpec Obs) :
    ccM (f <$> p) K = ccM p (fun a => K (f a)) := by
  simp only [ccM, mrealize_map, cc_map]

theorem ccM_ite {α : Type} (c : Prop) [Decidable c] (p q : M α) (K : α → OracleComp HashSpec Obs) :
    ccM (if c then p else q) K = if c then ccM p K else ccM q K := by
  split <;> rfl

theorem ccM_Kb (p : M Bool) : ccM p Kb = countCalls (mrealize 0 p) := cc_Kb _

theorem ccM_publicHash_bind {β : Type} (input : List UInt8) (f : HashOutput → M β)
    (K : β → OracleComp HashSpec Obs) :
    ccM (publicHash input >>= f) K = (do
      let a ← (liftM (HashSpec.query (toQ (pad64 input))) : OracleComp HashSpec _)
      (fun r => (r.1, 1 + r.2)) <$> ccM (f a) K) := by
  rw [ccM_bind]
  simp only [ccM, mrealize_publicHash, cc_query]

theorem ccM_shortHash_bind {β : Type} (input : List UInt8) (f : Digest → M β)
    (K : β → OracleComp HashSpec Obs) :
    ccM (shortHash input >>= f) K = (do
      let a ← (liftM (HashSpec.query (toQ (pad64 input))) : OracleComp HashSpec _)
      (fun r => (r.1, 1 + r.2)) <$> ccM (f (a.extractLsb' 0 128)) K) := by
  have : shortHash input >>= f = publicHash input >>= fun a => f (a.extractLsb' 0 128) := by
    unfold shortHash; rw [bind_assoc]; simp only [pure_bind]
  rw [this, ccM_publicHash_bind]

/-! ## HASH and HALT -/

/-- One HASH `ECALL` answering the query `q`. -/
theorem Good.query {s : MachineState} {N C : Nat} {q : Query}
    {K : BitVec 256 → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = q)
    (h : ∀ a, Good (writeHash s a) N C (K a)) :
    Good s (N + 1) (C + 8 * q.blocks) (cc (liftM (HashSpec.query q) : OracleComp HashSpec _) K) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_hash (F - 1) hf ht0 hv, cc_query, map_bind, hin]
    congr 1; funext a
    rw [Functor.map_map, ← (h a (F - 1) (by omega)).1, Functor.map_map]
    congr 1
  · rw [hF', evalWith_hash hash (F - 1) hf ht0 hv, hin]
    obtain ⟨h1, h2⟩ := (h (hash q) (F - 1) (by omega)).2 hash
    simp only [Execution.charge_exit, Execution.charge_cycles]
    exact ⟨h1, by omega⟩

theorem Good.publicHash_bind {β : Type} {s : MachineState} {N C : Nat} {input : List UInt8}
    {f : HashOutput → M β} {K : β → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = toQ (pad64 input))
    (h : ∀ a, Good (writeHash s a) N C (ccM (f a) K)) :
    Good s (N + 1) (C + 8 * (toQ (pad64 input)).blocks) (ccM (publicHash input >>= f) K) := by
  have := Good.query (K := fun a => ccM (f a) K) hf ht0 hv hin h
  rw [cc_query] at this
  rwa [ccM_publicHash_bind]

theorem Good.shortHash_bind {β : Type} {s : MachineState} {N C : Nat} {input : List UInt8}
    {f : Digest → M β} {K : β → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, Good (writeHash s a) N C (ccM (f (a.extractLsb' 0 128)) K)) :
    Good s (N + 1) (C + 8 * (toQ (pad64 input)).blocks) (ccM (shortHash input >>= f) K) := by
  have := Good.query (K := fun a => ccM (f (a.extractLsb' 0 128)) K) hf ht0 hv hin h
  rw [cc_query] at this
  rwa [ccM_shortHash_bind]

theorem Good.halt {s : MachineState} (hf : fetch image s = some (.base .ECALL))
    (ht0 : s.getReg .x5 = 1) : Good s 1 1 (pure (decide (s.getReg .x10 = 0), 0)) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_halt (F - 1) hf ht0, map_pure]
    by_cases hx : s.getReg .x10 = 0
    · simp only [obs, hx, if_true]
    · simp only [obs, hx, if_false]; rfl
  · rw [hF', evalWith_halt hash (F - 1) hf ht0]
    refine ⟨?_, le_refl _⟩
    by_cases hx : s.getReg .x10 = 0
    · simp only [hx, if_true]; decide
    · simp only [hx, if_false]; decide

/-! ## The judgment with an acceptance bound

`GoodQ s N C Q A X`: as `Good s N C X`, and moreover every accepting run (exit `success`) satisfies
`Q` and takes at most `A` cycles. -/

def GoodQ (s : MachineState) (N C : Nat) (Q : Prop) (A : Nat) (X : OracleComp HashSpec Obs) : Prop :=
  ∀ F, N ≤ F → obs <$> Riscv.execute F image s = X ∧
    ∀ hash : Hash, (evalWithAnswerFn hash (Riscv.execute F image s)).exit ≠ .unfinished ∧
      (evalWithAnswerFn hash (Riscv.execute F image s)).cycles ≤ C ∧
      ((evalWithAnswerFn hash (Riscv.execute F image s)).exit = .success →
        Q ∧ (evalWithAnswerFn hash (Riscv.execute F image s)).cycles ≤ A)

theorem Good.toQ {s : MachineState} {N C : Nat} {X : OracleComp HashSpec Obs} (h : Good s N C X) :
    GoodQ s N C True C X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F hF
  exact ⟨h1, fun hash => ⟨(h2 hash).1, (h2 hash).2, fun _ => ⟨trivial, (h2 hash).2⟩⟩⟩

theorem GoodQ.toGood {s : MachineState} {N C : Nat} {Q : Prop} {A : Nat} {X : OracleComp HashSpec Obs}
    (h : GoodQ s N C Q A X) : Good s N C X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F hF
  exact ⟨h1, fun hash => ⟨(h2 hash).1, (h2 hash).2.1⟩⟩

theorem GoodQ.mono {s : MachineState} {N C A N' C' A' : Nat} {Q Q' : Prop} {X : OracleComp HashSpec Obs}
    (h : GoodQ s N C Q A X) (hN : N ≤ N') (hC : C ≤ C') (hQ : Q → Q' ∧ A ≤ A') :
    GoodQ s N' C' Q' A' X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F (by omega)
  refine ⟨h1, fun hash => ⟨(h2 hash).1, by have := (h2 hash).2.1; omega, fun hs => ?_⟩⟩
  obtain ⟨hq, ha⟩ := (h2 hash).2.2 hs
  exact ⟨(hQ hq).1, by have := (hQ hq).2; omega⟩

theorem GoodQ.congr {s : MachineState} {N C A : Nat} {Q : Prop} {X Y : OracleComp HashSpec Obs}
    (h : GoodQ s N C Q A X) (hXY : X = Y) : GoodQ s N C Q A Y := hXY ▸ h

theorem GoodQ.steps {s t : MachineState} {k c N C A : Nat} {Q : Prop} {X : OracleComp HashSpec Obs}
    (hst : Steps image s k c t) (h : GoodQ t N C Q A X) : GoodQ s (N + k) (C + c) Q (A + c) X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h (F - k) (by omega)
  have hF' : F = (F - k) + k := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hst.execute_le (by omega : k ≤ F), Functor.map_map]
    simp only [obs_charge]
    exact h1
  · rw [hF', hst.evalWith hash (F - k)]
    simp only [Execution.charge_exit, Execution.charge_cycles]
    refine ⟨(h2 hash).1, by have := (h2 hash).2.1; omega, fun hs => ?_⟩
    obtain ⟨hq, ha⟩ := (h2 hash).2.2 hs
    exact ⟨hq, by omega⟩

theorem GoodQ.steps' {s t : MachineState} {k c N C A N' C' A' : Nat} {Q Q' : Prop}
    {X : OracleComp HashSpec Obs} (hst : Steps image s k c t) (h : GoodQ t N C Q A X)
    (hN : N + k ≤ N') (hC : C + c ≤ C') (hQ : Q → Q' ∧ A + c ≤ A') : GoodQ s N' C' Q' A' X :=
  (h.steps hst).mono hN hC hQ

/-- One HASH `ECALL` answering the query `q`. -/
theorem GoodQ.query {s : MachineState} {N C A : Nat} {Q : Prop} {q : Query}
    {K : BitVec 256 → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = q)
    (h : ∀ a, GoodQ (writeHash s a) N C Q A (K a)) :
    GoodQ s (N + 1) (C + 8 * q.blocks) Q (A + 8 * q.blocks)
      (cc (liftM (HashSpec.query q) : OracleComp HashSpec _) K) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_hash (F - 1) hf ht0 hv, cc_query, map_bind, hin]
    congr 1; funext a
    rw [Functor.map_map, ← (h a (F - 1) (by omega)).1, Functor.map_map]
    congr 1
  · rw [hF', evalWith_hash hash (F - 1) hf ht0 hv, hin]
    obtain ⟨h1, h2, h3⟩ := (h (hash q) (F - 1) (by omega)).2 hash
    simp only [Execution.charge_exit, Execution.charge_cycles]
    refine ⟨h1, by omega, fun hs => ?_⟩
    obtain ⟨hq, ha⟩ := h3 hs
    exact ⟨hq, by omega⟩

theorem GoodQ.publicHash_bind {β : Type} {s : MachineState} {N C A : Nat} {Q : Prop}
    {input : List UInt8} {f : HashOutput → M β} {K : β → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = toQ (pad64 input))
    (h : ∀ a, GoodQ (writeHash s a) N C Q A (ccM (f a) K)) :
    GoodQ s (N + 1) (C + 8 * (toQ (pad64 input)).blocks) Q (A + 8 * (toQ (pad64 input)).blocks)
      (ccM (publicHash input >>= f) K) := by
  have := GoodQ.query (K := fun a => ccM (f a) K) hf ht0 hv hin h
  rw [cc_query] at this
  rwa [ccM_publicHash_bind]

theorem GoodQ.shortHash_bind {β : Type} {s : MachineState} {N C A : Nat} {Q : Prop}
    {input : List UInt8} {f : Digest → M β} {K : β → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, GoodQ (writeHash s a) N C Q A (ccM (f (a.extractLsb' 0 128)) K)) :
    GoodQ s (N + 1) (C + 8 * (toQ (pad64 input)).blocks) Q (A + 8 * (toQ (pad64 input)).blocks)
      (ccM (shortHash input >>= f) K) := by
  have := GoodQ.query (K := fun a => ccM (f (a.extractLsb' 0 128)) K) hf ht0 hv hin h
  rw [cc_query] at this
  rwa [ccM_shortHash_bind]

/-- HALT with exit code `x10` (`success` iff `x10 = 0`). -/
theorem GoodQ.halt {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch image s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (hQ : s.getReg .x10 = 0 → Q ∧ 1 ≤ A) :
    GoodQ s 1 1 Q A (pure (decide (s.getReg .x10 = 0), 0)) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_halt (F - 1) hf h5, map_pure]
    by_cases hx : s.getReg .x10 = 0
    · simp only [obs, hx, if_true]
    · simp only [obs, hx, if_false]; rfl
  · rw [hF', evalWith_halt hash (F - 1) hf h5]
    by_cases hx : s.getReg .x10 = 0
    · simp only [hx, if_true]
      exact ⟨by decide, le_refl _, fun _ => hQ hx⟩
    · simp only [hx, if_false]
      exact ⟨by decide, le_refl _, fun h => absurd h (by decide)⟩

/-- HALT(1): a rejecting run (any acceptance condition). -/
theorem GoodQ.reject {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch image s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (h10 : s.getReg .x10 = 1) : GoodQ s 1 1 Q A (pure (false, 0)) := by
  have := GoodQ.halt (Q := Q) (A := A) hf h5 (fun h => absurd (h10.symm.trans h) (by decide))
  rwa [h10] at this

/-- HALT(0): an accepting run. -/
theorem GoodQ.accept {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch image s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (h10 : s.getReg .x10 = 0) (hQ : Q) (hA : 1 ≤ A) :
    GoodQ s 1 1 Q A (pure (true, 0)) := by
  have := GoodQ.halt (Q := Q) (A := A) hf h5 (fun _ => ⟨hQ, hA⟩)
  rwa [h10] at this

end SigGolfCandidate.T3M.CanonicalPort.Verify

end CanonicalPortPart4

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart5

/-!
# Doublewords of the verify image's hash inputs and of the witness

* `dlo d`, `dhi d` : the two little-endian doublewords of a 16-byte digest;
* `wword w j` : witness doubleword `j` (bytes `8 j .. 8 j + 8`; **zero past the witness**, as the machine's
  memory after `WIT + W` during verify), `wdig_lo`, `wdig_hi` (`wdig w (8 j)` = `wword w j`, `wword w (j+1)`);
* `blk4 a b c d` : a 64-byte block of four 16-byte fields, `wordsOf_blk4`, `pad64_blk4`, `blocks_blk4`;
* Core's and `verifyP`'s formats as `blk4` (`ftsLeafP_eq`, `nodeHashP_eq`, `nodeHash_eq`, `chainInputP_eq`) and the
  doublewords of the other inputs: `wordsOf_digestInput`, `wordsOf_encodingInput`, `wordsOf_forestInput`,
  `wordsOf_pad64` (for `leafHash`);
* `hashInput_words8` : a one-block HASH input given by its eight doublewords (`hashInput_toQ` of M0 at `n = 0`).
-/

namespace SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (header pad64 zero16 Digest HashOutput HashInput Layer)
open SphincsSecurity (bytesLE bytesLE_length)

/-! ## Digests and witness words -/

/-- Low doubleword of a digest. -/
abbrev dlo (d : BitVec 128) : Word := d.extractLsb' 0 64
/-- High doubleword of a digest. -/
abbrev dhi (d : BitVec 128) : Word := d.extractLsb' 64 64

/-- Witness doubleword `j` (zero for `8 j ≥ 25240`). -/
def wword (w : WBytes) (j : Nat) : Word := w.extractLsb' (64 * j) 64

theorem wword_toNat (w : WBytes) (j : Nat) : (wword w j).toNat = w.toNat / 2 ^ (64 * j) % 2 ^ 64 := by
  simp only [wword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem wword_zero (w : WBytes) (j : Nat) (h : 3155 ≤ j) : wword w j = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [wword_toNat]
  have hw : w.toNat < 2 ^ (64 * j) :=
    lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Nat.div_eq_of_lt hw]; rfl

theorem wdig_lo (w : WBytes) (j : Nat) : dlo (wdig w (8 * j)) = wword w j := by
  apply BitVec.eq_of_toNat_eq
  simp only [wdig, wword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  rw [show 8 * (8 * j) = 64 * j by ring, Nat.mod_mod_of_dvd _ (by norm_num)]

theorem wdig_hi (w : WBytes) (j : Nat) : dhi (wdig w (8 * j)) = wword w (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [wdig, wword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self,
    Nat.div_div_eq_div_mul, ← Nat.pow_add, show 8 * (8 * j) + 64 = 64 * (j + 1) by ring, Nat.mod_mod]

/-- The digest stored at witness offset `8 j`. -/
theorem wdig_words (w : WBytes) (j : Nat) :
    wordsOf (bytesLE 16 (wdig w (8 * j))) = [wword w j, wword w (j + 1)] := by
  rw [wordsOf_bytesLE16, ← wdig_lo, ← wdig_hi]

/-! ## Blocks of four 16-byte fields -/

/-- A 64-byte block `[a | b | c | d]`. -/
def blk4 (a b c d : BitVec 128) : List UInt8 := bytesLE 16 a ++ bytesLE 16 b ++ bytesLE 16 c ++ bytesLE 16 d

theorem blk4_length (a b c d : BitVec 128) : (blk4 a b c d).length = 64 := by
  simp only [blk4, List.length_append, bytesLE_length]

theorem pad64_blk4 (a b c d : BitVec 128) : pad64 (blk4 a b c d) = blk4 a b c d :=
  pad64_of_aligned _ (by rw [blk4_length])

theorem wordsOf_blk4 (a b c d : BitVec 128) :
    wordsOf (blk4 a b c d) = [dlo a, dhi a, dlo b, dhi b, dlo c, dhi c, dlo d, dhi d] := by
  unfold blk4
  rw [wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]),
    wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16]
  rfl

theorem aligned_blk4 (a b c d : BitVec 128) : Aligned (blk4 a b c d) := by
  rw [Aligned, blk4_length]; omega

theorem blocks_blk4 (a b c d : BitVec 128) : (toQ (pad64 (blk4 a b c d))).blocks = 1 := by
  rw [pad64_blk4, blocks_toQ (aligned_blk4 a b c d), blk4_length]

/-- `bytesLE 16 0` is Core's `zero16`. -/
theorem bytesLE16_zero : bytesLE 16 (0 : BitVec 128) = zero16 := by decide

/-! ## Formats as blocks -/

theorem ftsLeafP_eq (index coord leaf : Nat) (pad0 secret pad1 : Digest) :
    T3M.ftsLeafP index coord leaf pad0 secret pad1 =
      T3.shortHash (blk4 pad0 (header 9 coord index 0 leaf) secret pad1) := rfl

theorem nodeHashP_eq (tag lay tree heap : Nat) (left pad right : Digest) :
    T3M.nodeHashP tag lay tree heap left pad right =
      T3.shortHash (blk4 left (header tag lay tree 0 heap) pad right) := rfl

theorem nodeHash_eq (tag lay tree heap : Nat) (left right : Digest) :
    T3.nodeHash tag lay tree heap left right =
      T3.shortHash (blk4 left (header tag lay tree 0 heap) 0 right) := by
  unfold T3.nodeHash blk4
  rw [bytesLE16_zero]

theorem ftsLeaf_eq (index coord leaf : Nat) (secret : Digest) :
    T3.ftsLeaf index coord leaf secret = T3.shortHash (blk4 0 (header 9 coord index 0 leaf) secret 0) := by
  unfold T3.ftsLeaf blk4
  rw [bytesLE16_zero]

theorem chainInputP_eq (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 value : Digest) :
    T3M.chainInputP lay tree leaf i step pad0 pad1 value =
      blk4 pad0 (header 1 lay.val tree (step + 256 * i) leaf) pad1 value := rfl

/-! ## Other inputs -/

/-- The digest block `[rho | T(12, dc) | m]`. -/
theorem digestInput_length (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    (T3.digestInput rho m c).length = 64 := by
  simp only [T3.digestInput, List.length_append, bytesLE_length]

theorem wordsOf_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    wordsOf (T3.digestInput rho m c) =
      [dlo rho, dhi rho, BitVec.ofNat 64 (hdr0 12 0 0 0), BitVec.ofNat 64 (hdr1 0 c.toNat),
        m.extractLsb' 0 64, m.extractLsb' 64 64, m.extractLsb' 128 64, m.extractLsb' 192 64] := by
  unfold T3.digestInput
  rw [wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_bytesLE16, wordsOf_header,
    wordsOf_bytesLE32]
  rfl

theorem pad64_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    pad64 (T3.digestInput rho m c) = T3.digestInput rho m c :=
  pad64_of_aligned _ (by rw [digestInput_length])

theorem blocks_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    (toQ (pad64 (T3.digestInput rho m c))).blocks = 1 := by
  rw [pad64_digestInput, blocks_toQ (by rw [Aligned, digestInput_length]; omega), digestInput_length]

/-- The encoding block `[M | T(4) | LE32 c | 0^28]` (one block after `pad64`). -/
theorem pad64_encodingInput (lay : Layer) (tree leaf : Nat) (msg : Digest) (c : BitVec 32) :
    pad64 (T3.encodingInput lay tree leaf msg c) =
      T3.encodingInput lay tree leaf msg c ++ List.replicate 28 0 := by
  unfold pad64
  simp only [T3.encodingInput, List.length_append, bytesLE_length]

theorem readLE_bytesLE4_pad (c : BitVec 32) : T3.readLE (bytesLE 4 c ++ List.replicate 4 0) = c.toNat := by
  rw [readLE_append, readLE_bytesLE, readLE_replicate_zero]
  simp

theorem wordsOf_encodingInput (lay : Layer) (tree leaf : Nat) (msg : Digest) (c : BitVec 32) :
    wordsOf (pad64 (T3.encodingInput lay tree leaf msg c)) =
      [dlo msg, dhi msg, BitVec.ofNat 64 (hdr0 4 lay.val tree 0), BitVec.ofNat 64 (hdr1 tree leaf),
        BitVec.ofNat 64 c.toNat, 0, 0, 0] := by
  rw [pad64_encodingInput]
  unfold T3.encodingInput
  have e : bytesLE 16 msg ++ bytesLE 16 (header 4 lay.val tree 0 leaf) ++ bytesLE 4 c ++ List.replicate 28 0 =
      bytesLE 16 msg ++ bytesLE 16 (header 4 lay.val tree 0 leaf) ++
        ((bytesLE 4 c ++ List.replicate 4 0) ++ List.replicate 24 0) := by
    simp only [List.append_assoc]
    rfl
  rw [e, wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_bytesLE16, wordsOf_header,
    wordsOf_append8 _ _ (by simp only [List.length_append, bytesLE_length, List.length_replicate]),
    readLE_bytesLE4_pad, show (24 : Nat) = 8 * 3 by rfl, wordsOf_replicate_zero]
  rfl

theorem blocks_encodingInput (lay : Layer) (tree leaf : Nat) (msg : Digest) (c : BitVec 32) :
    (toQ (pad64 (T3.encodingInput lay tree leaf msg c))).blocks = 1 := by
  have hl : (pad64 (T3.encodingInput lay tree leaf msg c)).length = 64 := by
    rw [pad64_encodingInput]
    simp only [T3.encodingInput, List.length_append, bytesLE_length, List.length_replicate]
  rw [blocks_toQ (by rw [Aligned, hl]; omega), hl]

/-- The forest-pk input `[root_0 | T(11) | root_1 .. root_6]` (two blocks). -/
def forestInput (index : Nat) (roots : List Digest) : HashInput :=
  bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 11 0 index 0 0) ++ (roots.drop 1).flatMap (bytesLE 16)

theorem forestPk_eq (index : Nat) (roots : List Digest) :
    T3.forestPk index roots = T3.shortHash (forestInput index roots) := rfl

theorem sum_map_16 : ∀ l : List Digest, (l.map fun _ => (16 : Nat)).sum = 16 * l.length
  | [] => rfl
  | _ :: l => by simp only [List.map_cons, List.sum_cons, sum_map_16 l, List.length_cons]; ring

theorem forestInput_length (index : Nat) (roots : List Digest) (h : roots.length = 7) :
    (forestInput index roots).length = 128 := by
  unfold forestInput
  simp only [List.length_append, bytesLE_length, List.length_flatMap]
  rw [sum_map_16, List.length_drop, h]

theorem wordsOf_forestInput (index : Nat) (roots : List Digest) :
    wordsOf (forestInput index roots) =
      [dlo (roots.getD 0 0), dhi (roots.getD 0 0), BitVec.ofNat 64 (hdr0 11 0 index 0),
        BitVec.ofNat 64 (hdr1 index 0)] ++ (roots.drop 1).flatMap (fun d => [dlo d, dhi d]) := by
  unfold forestInput
  rw [wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_bytesLE16, wordsOf_header,
    wordsOf_flatMap16]
  rfl

theorem pad64_forestInput (index : Nat) (roots : List Digest) (h : roots.length = 7) :
    pad64 (forestInput index roots) = forestInput index roots :=
  pad64_of_aligned _ (by rw [forestInput_length index roots h])

theorem blocks_forestInput (index : Nat) (roots : List Digest) (h : roots.length = 7) :
    (toQ (pad64 (forestInput index roots))).blocks = 2 := by
  rw [pad64_forestInput index roots h,
    blocks_toQ (by rw [Aligned, forestInput_length index roots h]; omega), forestInput_length index roots h]

/-- `pad64` of an input of whole doublewords appends zero doublewords. -/
theorem wordsOf_pad64 (l : HashInput) (h : l.length % 8 = 0) :
    wordsOf (pad64 l) = wordsOf l ++ List.replicate ((64 - l.length % 64) % 64 / 8) 0 := by
  unfold pad64
  rw [wordsOf_append _ _ h]
  congr 1
  have : (64 - l.length % 64) % 64 = 8 * ((64 - l.length % 64) % 64 / 8) := by omega
  rw [this, wordsOf_replicate_zero]
  congr 1
  omega

/-! ## One-block HASH inputs from memory -/

theorem readWords_ofNat (t : MachineState) (a : Nat) : ∀ m, a + 8 * m < 2 ^ 64 →
    t.readWords (BitVec.ofNat 64 a) m =
      (List.range m).map fun j => t.getMem (BitVec.ofNat 64 (a + 8 * j)) := by
  intro m
  induction m generalizing a with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    rw [MachineState.readWords_succ, ofNat_add8, ih (a + 8) (by omega), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.mul_zero, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    congr 2; omega

theorem readWords_eight (t : MachineState) (A : Nat) (hA : A + 64 < 2 ^ 64) :
    t.readWords (BitVec.ofNat 64 A) 8 =
      [t.getMem (BitVec.ofNat 64 A), t.getMem (BitVec.ofNat 64 (A + 8)),
        t.getMem (BitVec.ofNat 64 (A + 16)), t.getMem (BitVec.ofNat 64 (A + 24)),
        t.getMem (BitVec.ofNat 64 (A + 32)), t.getMem (BitVec.ofNat 64 (A + 40)),
        t.getMem (BitVec.ofNat 64 (A + 48)), t.getMem (BitVec.ofNat 64 (A + 56))] := by
  rw [readWords_ofNat t A 8 (by omega)]
  rfl

/-- A one-block HASH input at `A` whose eight doublewords are those of the 64-byte list `l`. -/
theorem hashInput_words8 (t : MachineState) (l : List UInt8) (A : Nat) (hl : l.length = 64)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 64 < 2 ^ 64)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (hw : [t.getMem (BitVec.ofNat 64 A), t.getMem (BitVec.ofNat 64 (A + 8)),
        t.getMem (BitVec.ofNat 64 (A + 16)), t.getMem (BitVec.ofNat 64 (A + 24)),
        t.getMem (BitVec.ofNat 64 (A + 32)), t.getMem (BitVec.ofNat 64 (A + 40)),
        t.getMem (BitVec.ofNat 64 (A + 48)), t.getMem (BitVec.ofNat 64 (A + 56))] = wordsOf l) :
    hashInput t = toQ l :=
  hashInput_toQ t l 0 A hl h10 hA (by omega) h11 (by norm_num) (by rw [readWords_eight t A hA']; exact hw)

end SigGolfCandidate.T3M.CanonicalPort.Verify

end CanonicalPortPart5

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart6

/-!
# Verify memory: global invariant, witness predicates, checked writes (T3M)

The T3 verifier hashes the witness **in place**: it writes the header slot `T` of every leaf, fold, chain and
Merkle block it hashes and the current-node slot the previous hash output lands in (MACH-PLAN §3.1). So there is
no phase-independent "witness unchanged" invariant (W2 pattern, WC2 `Mem`); what is common to all phases:

* `Glob gk w pk s` : the phase's constant registers `gk` (always `t0 = 0`, `s2 = 4095` = `baseK`), the witness
  header `[0, 64)` (rho, dc, counters; never written: `WitHdr`), the public key, the zero words `0x128..0x140`
  of the encoding block (`PZero`) and the zero high half of its counter word `0x120` (written by `sw`, `PHalf`);
* `WitAll w s` : the whole witness region **and the zero memory after it** (up to `WX = 2^17` bytes above `WIT`)
  holds `wword w j` (= the witness doublewords, **zero past W**: `wword_zero`); `Orig w P s` : the same for the
  offsets satisfying `P` (the per-phase frontier invariants are built from it).

Every checked run (`Spec.specB`) writes only (a) constant addresses that are safe low-memory words (`safeAddr`), the
counter word by a low-half `sw`, or explicitly allowed witness words (`allow`, `≥ WLO = WIT + 64`), or
(b) **pointer-relative** addresses `r + off` (`r ∈ rel`, `off < 4096`; the FTS stream pointer `a4`), with
`RelOK rel s` (the pointer is `≥ WLO` and `< 2^23`) supplied by the caller. The caller accounts for the
witness writes through the run's exact memory (`SpecRes.mem`, `Orig_toState`).

T3K: the verify image embeds twelve doublewords at `DATA = 2^24 - 96` (`DataOK`, part of `Glob`). Every checked
write (allowed witness words `< 2^23`, pointer-relative writes below `2^23 + 4096`) and every hash destination
(`safeDest`: `d + 32 ≤ 2^23`) stays below them, so `Glob` keeps them (`memOKA_data`).
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)

/-! ## Layout -/

/-- The witness base. -/
def WIT : Nat := 0x800
/-- The witness size in bytes (`T3M.wsize`). -/
def WSZ : Nat := 25240
/-- The extent (bytes above `WIT`) of the witness predicates: the fold stream of an adversarial witness may run
past `W` (at most 35 segments of 11 folds: `< 32,232` bytes) before the pointer cap rejects; memory there is zero. -/
def WX : Nat := 2 ^ 17
/-- Allowed witness writes start here: the witness header `[0, 64)` is never written. -/
def WLO : Nat := WIT + 64

/-! ## Addresses -/

theorem ofNat_eq_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a = BitVec.ofNat 64 b) ↔ a = b := by
  constructor
  · intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · intro h; rw [h]

theorem ofNat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun h' => h ((ofNat_eq_iff ha hb).mp h')

theorem ofNat_toNat_lt (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## `writeHash` -/

theorem getMem_setMem (s : MachineState) (a v A : Word) :
    (s.setMem a v).getMem A = if A = a then v else s.getMem A := by
  simp [MachineState.setMem, MachineState.getMem]

theorem writeHash_getMem (s : MachineState) (ans : BitVec 256) (A : Word) :
    (writeHash s ans).getMem A =
      if A = s.getReg .x12 + 8 + 8 + 8 then ans.extractLsb' 192 64
      else if A = s.getReg .x12 + 8 + 8 then ans.extractLsb' 128 64
      else if A = s.getReg .x12 + 8 then ans.extractLsb' 64 64
      else if A = s.getReg .x12 then ans.extractLsb' 0 64
      else s.getMem A := by
  simp only [writeHash, MachineState.writeWords]
  show ((((s.setMem _ _).setMem _ _).setMem _ _).setMem _ _).getMem A = _
  simp only [getMem_setMem]

/-- `writeHash` at a constant destination `d`. -/
theorem writeHash_getMem_ofNat (s : MachineState) (ans : BitVec 256) (d A : Nat)
    (hd : s.getReg .x12 = BitVec.ofNat 64 d) (hA : A < 2 ^ 64) (hd' : d + 24 < 2 ^ 64) :
    (writeHash s ans).getMem (BitVec.ofNat 64 A) =
      if A = d + 24 then ans.extractLsb' 192 64
      else if A = d + 16 then ans.extractLsb' 128 64
      else if A = d + 8 then ans.extractLsb' 64 64
      else if A = d then ans.extractLsb' 0 64
      else s.getMem (BitVec.ofNat 64 A) := by
  rw [writeHash_getMem, hd]
  simp only [show (8 : Word) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat,
    ofNat_eq_iff hA (by omega : d + 8 + 8 + 8 < 2 ^ 64), ofNat_eq_iff hA (by omega : d + 8 + 8 < 2 ^ 64),
    ofNat_eq_iff hA (by omega : d + 8 < 2 ^ 64), ofNat_eq_iff hA (by omega : d < 2 ^ 64)]

theorem writeWords_regs : ∀ (ws : List Word) (s : MachineState) (base : Word),
    (s.writeWords base ws).regs = s.regs ∧ (s.writeWords base ws).pc = s.pc
  | [], _, _ => ⟨rfl, rfl⟩
  | w :: ws, s, base => by
    simp only [MachineState.writeWords]
    obtain ⟨h1, h2⟩ := writeWords_regs ws (s.setMem base w) (base + 8)
    exact ⟨h1.trans rfl, h2.trans rfl⟩

theorem writeHash_getReg (s : MachineState) (ans : BitVec 256) (r : Reg) :
    (writeHash s ans).getReg r = s.getReg r := getReg_writeHash s ans r

theorem writeHash_pc (s : MachineState) (ans : BitVec 256) :
    (writeHash s ans).pc = s.pc + 4 := pc_writeHash s ans

theorem writeHash_frame (t : MachineState) (ans : BitVec 256) (d A : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hA : A < 2 ^ 64) (hd' : d + 24 < 2 ^ 64)
    (h : A + 8 ≤ d ∨ d + 32 ≤ A) :
    (writeHash t ans).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
  rw [writeHash_getMem_ofNat t ans d A hd hA hd', if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

theorem writeHash_at0 (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 24 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 d) = ans.extractLsb' 0 64 := by
  rw [writeHash_getMem_ofNat t ans d d hd (by omega) hd', if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]

theorem writeHash_at8 (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 24 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 (d + 8)) = ans.extractLsb' 64 64 := by
  rw [writeHash_getMem_ofNat t ans d _ hd (by omega) hd', if_neg (by omega), if_neg (by omega),
    if_pos rfl]

theorem writeHash_at16 (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 24 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 (d + 16)) = ans.extractLsb' 128 64 := by
  rw [writeHash_getMem_ofNat t ans d _ hd (by omega) hd', if_neg (by omega), if_pos rfl]

theorem writeHash_at24 (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 24 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 (d + 24)) = ans.extractLsb' 192 64 := by
  rw [writeHash_getMem_ofNat t ans d _ hd (by omega) hd', if_pos rfl]

/-- The digest answer (low 16 bytes) written at `d` (`DigAt` of M0). -/
theorem writeHash_lo (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 d) = dlo (ans.extractLsb' 0 128) ∧
      (writeHash t ans).getMem (BitVec.ofNat 64 (d + 8)) = dhi (ans.extractLsb' 0 128) :=
  DigAt.writeHash_lo t ans d hd hd'

/-! ## Sub-word stores -/

theorem land_split (n M w s : Nat) (hws : w ≤ s) :
    n &&& (2 ^ s * M + (2 ^ w - 1)) = 2 ^ s * ((n / 2 ^ s) &&& M) + n % 2 ^ w := by
  have hw : 2 ^ w - 1 < 2 ^ s := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hws
    have : 0 < 2 ^ w := Nat.two_pow_pos _
    omega
  have hm : n % 2 ^ w < 2 ^ s := lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) hws)
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, Nat.testBit_two_pow_mul_add _ hw, Nat.testBit_two_pow_mul_add _ hm]
  split
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    cases n.testBit j <;> simp
  · rw [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]

theorem replaceWord32_0_toNat (w : BitVec 64) (v : BitVec 32) :
    (replaceWord32 w 0 v).toNat = w.toNat / 2 ^ 32 % 2 ^ 32 * 2 ^ 32 + v.toNat := by
  unfold replaceWord32
  have hm : (~~~(0xFFFFFFFF#64 <<< (0 * 32)) : BitVec 64) =
      BitVec.ofNat 64 (2 ^ 32 * (2 ^ 32 - 1) + (2 ^ 0 - 1)) := by decide
  rw [hm, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, Nat.zero_mul,
    Nat.shiftLeft_zero]
  have hv := v.isLt
  have hw := w.isLt
  rw [Nat.mod_eq_of_lt (show v.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show v.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 2 ^ 32 * (2 ^ 32 - 1) + (2 ^ 0 - 1) < 2 ^ 64 by norm_num),
    land_split _ _ 0 32 (by decide), Nat.and_two_pow_sub_one_eq_mod, Nat.pow_zero, Nat.mod_one, Nat.add_zero,
    ← Nat.two_pow_add_eq_or_of_lt hv]
  ring

/-- `sw v, a` (low half): the high half of the word is kept. -/
theorem merge_w0_toNat (w v : BitVec 64) :
    (StoreKind.merge .w w 0 v).toNat = w.toNat / 2 ^ 32 % 2 ^ 32 * 2 ^ 32 + v.toNat % 2 ^ 32 := by
  simp only [StoreKind.merge, show (0 : Nat) / 4 = 0 from rfl]
  rw [replaceWord32_0_toNat]
  simp [BitVec.toNat_setWidth]

theorem merge_w0_high (w v : BitVec 64) :
    (StoreKind.merge .w w 0 v).toNat / 2 ^ 32 = w.toNat / 2 ^ 32 % 2 ^ 32 := by
  rw [merge_w0_toNat]; omega

/-! ## The global invariant -/

/-- Registers constant in every phase after the prologue: `t0 = 0` (HASH selector), `s2 = 4095` (the witness base
of the short-offset accesses, `WIT + off - 2047`; also the SWAR modulus of the layers). -/
def baseK : List (Reg × Word) := [(.x5, 0), (.x18, 0xFFF)]

/-- Constants carried from the forest into the lower-layer initializer. -/
def carryK : List (Reg × Word) := baseK ++ [(.x2,0x1000000),(.x7,2),(.x8,3),(.x9,4),(.x13,5)]

/-- The zero words of the encoding block `[M | T | LE32 c | 0^28]` at `0x100` that no instruction writes. -/
def pSlots : List Nat := [0x128, 0x130, 0x138]

/-- The counter word of the encoding block: its high half (`0x124 .. 0x128`) is never written. -/
def CTRW : Nat := 0x120

def PkOK (pk : Digest) (s : MachineState) : Prop :=
  s.getMem 0xA0 = dlo pk ∧ s.getMem 0xA8 = dhi pk

def PZero (s : MachineState) : Prop := ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0

/-- The high half of the counter word is zero. -/
def PHalf (s : MachineState) : Prop := (s.getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0

/-- The witness header words `[0, 64)` (rho, dc, the four counters, zero), never written by the verifier. -/
def WitHdr (w : WBytes) (s : MachineState) : Prop :=
  ∀ j, j < 8 → s.getMem (BitVec.ofNat 64 (WIT + 8 * j)) = wword w j

/-- The verify image's embedded doublewords (`Images.verifyData`, little endian): the layer-3 constants `2^40`,
`M2c`, `M1c`, `0x30101`, `0x3fe00`, the FTS setup constants `A4_0`, `A4_LIMIT`, `0xa01`, `0x901`, `tbN`, `tbL`, a zero
pad. -/
def dataWords : List Nat :=
  [2 ^ 40, 17311559823019733055, 8198552921648689607, 0x30101, 0x3fe00, 2256, 11736, 0xa01, 0x901, 7072, 15264, 0]

/-- The data section's base: `dataBase` of the verify image (`16 ⌊(2^24 - 96) / 16⌋`). -/
def DATA : Nat := 16777120

/-- Public WOTS header table precedes the existing immutable lookup data. -/
def HDATA : Nat := 16726016
/-- Reversed FTS heap-label table, preceding both lower header and packed tables. -/
def TAB : Nat := 16709632

def headerWord (k : Nat) : Nat :=
  0x101 + 65536 * (k / 512) + 2 ^ 40 * (k % 512 / 8) + 2 ^ 32 * (k % 8)

def headerBank (lay koff : Nat) : Nat := HDATA + 4096 * lay + 2048 + 64 * koff

/-- Both the embedded constants and the checksum lookup bytes are in place. -/
structure DataOK (s : MachineState) : Prop where
  constants : ∀ k, k < 12 → s.getMem (BitVec.ofNat 64 (DATA + 8 * k)) = BitVec.ofNat 64 (dataWords.getD k 0)
  sum : Search.SumTableOK s
  packed : Nonbinary.PackedTables s
  headers : ∀ k, k < 2048 → s.getMem (BitVec.ofNat 64 (HDATA + 8 * k)) = BitVec.ofNat 64 (headerWord k)
  tab : ∀ j, j < 2048 → s.getMem (BitVec.ofNat 64 (TAB + 8 * j)) = BitVec.ofNat 64 (T3.Rev.revBits 64 (2048 + j))

instance {s : MachineState} : CoeFun (DataOK s) (fun _ => ∀ k, k < 12 →
    s.getMem (BitVec.ofNat 64 (DATA + 8 * k)) = BitVec.ofNat 64 (dataWords.getD k 0)) := ⟨DataOK.constants⟩

/-- The complete data invariant is preserved when all image-data doublewords stay unchanged. -/
theorem DataOK.congr {s t : MachineState} (h : DataOK s)
    (hm : ∀ A, TAB ≤ A → A + 8 ≤ 2 ^ 24 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : DataOK t := by
  constructor
  · intro k hk
    rw [hm _ (by unfold DATA TAB; omega) (by unfold DATA; omega)]
    exact h.constants k hk
  · intro i hi
    rw [T3M.getByte_eq_word _ _ (by unfold Search.TOP_DATA; omega),
      hm _ (by unfold Search.TOP_DATA TAB; omega) (by unfold Search.TOP_DATA; omega),
      ← T3M.getByte_eq_word _ _ (by unfold Search.TOP_DATA; omega)]
    exact h.sum i hi
  · exact h.packed.congr (fun A hA hA' => hm A (by unfold Nonbinary.PAIR_DATA TAB at *; omega) hA')
  · intro k hk
    rw [hm _ (by unfold HDATA TAB; omega) (by unfold HDATA; omega)]
    exact h.headers k hk

  · intro j hj
    rw [hm _ (by omega) (by unfold TAB; omega)]
    exact h.tab j hj

/-- Exact public header loaded by the lower WOTS chains. -/
theorem DataOK.header {s : MachineState} (h : DataOK s) (lay i d : Nat)
    (hl : lay < 4) (hi : i < 64) (hd : d < 8) :
    s.getMem (BitVec.ofNat 64 (HDATA + 4096 * lay + 64 * i + 8 * d)) =
      BitVec.ofNat 64 (0x101 + 65536 * lay + 2 ^ 40 * i + 2 ^ 32 * d) := by
  have H := h.headers (512 * lay + 8 * i + d) (by omega)
  simp only [headerWord] at H
  have e1 : (512 * lay + 8 * i + d) / 512 = lay := by omega
  have e2 : (512 * lay + 8 * i + d) % 512 / 8 = i := by omega
  have e3 : (512 * lay + 8 * i + d) % 8 = d := by omega
  rw [e1,e2,e3,show HDATA + 8 * (512 * lay + 8 * i + d) = HDATA + 4096 * lay + 64 * i + 8 * d by ring] at H
  exact H

def Glob (gk : List (Reg × Word)) (w : WBytes) (pk : Digest) (s : MachineState) : Prop :=
  (∀ p ∈ gk, s.getReg p.1 = p.2) ∧ WitHdr w s ∧ PkOK pk s ∧ PZero s ∧ PHalf s ∧ DataOK s

/-! ## Witness predicates (reads past the witness see zero memory) -/

/-- The witness region and the memory after it (up to `WX`) hold the witness doublewords (zero past `W`). -/
def WitAll (w : WBytes) (s : MachineState) : Prop :=
  ∀ j, 8 * j < WX → s.getMem (BitVec.ofNat 64 (WIT + 8 * j)) = wword w j

/-- The witness doublewords at (word-aligned) offsets `o < WX` with `P o` are original. -/
def Orig (w : WBytes) (P : Nat → Prop) (s : MachineState) : Prop :=
  ∀ j, 8 * j < WX → P (8 * j) → s.getMem (BitVec.ofNat 64 (WIT + 8 * j)) = wword w j

theorem WitAll.orig {w : WBytes} {s : MachineState} (h : WitAll w s) (P : Nat → Prop) : Orig w P s :=
  fun j hj _ => h j hj

theorem WitAll.hdr {w : WBytes} {s : MachineState} (h : WitAll w s) : WitHdr w s :=
  fun j hj => h j (by unfold WX; omega)

theorem Orig.mono {w : WBytes} {s : MachineState} {P P' : Nat → Prop} (h : Orig w P s)
    (hP : ∀ o, P' o → P o) : Orig w P' s :=
  fun j h1 h2 => h j h1 (hP _ h2)

theorem Orig.frame {w : WBytes} {s t : MachineState} {P : Nat → Prop} (h : Orig w P s)
    (hf : ∀ j, 8 * j < WX → P (8 * j) →
      t.getMem (BitVec.ofNat 64 (WIT + 8 * j)) = s.getMem (BitVec.ofNat 64 (WIT + 8 * j))) :
    Orig w P t :=
  fun j h1 h2 => (hf j h1 h2).trans (h j h1 h2)

/-- A doubleword at witness offset `off` (`8 ∣ off`, `off < WX`, `P off`). -/
theorem Orig.word {w : WBytes} {s : MachineState} {P : Nat → Prop} (hO : Orig w P s) (off : Nat)
    (h8 : off % 8 = 0) (hoff : off < WX) (hp : P off) :
    s.getMem (BitVec.ofNat 64 (WIT + off)) = wword w (off / 8) := by
  have := hO (off / 8) (by omega) (by rwa [show 8 * (off / 8) = off by omega])
  rwa [show 8 * (off / 8) = off by omega] at this

/-- The two doublewords of the witness digest at offset `off` (`wdig w off`). -/
theorem Orig.dig {w : WBytes} {s : MachineState} {P : Nat → Prop} (hO : Orig w P s) (off : Nat)
    (h8 : off % 8 = 0) (hoff : off + 8 < WX) (hp0 : P off) (hp1 : P (off + 8)) :
    s.getMem (BitVec.ofNat 64 (WIT + off)) = dlo (wdig w off) ∧
      s.getMem (BitVec.ofNat 64 (WIT + off + 8)) = dhi (wdig w off) := by
  obtain ⟨j, rfl⟩ : ∃ j, off = 8 * j := ⟨off / 8, by omega⟩
  refine ⟨?_, ?_⟩
  · rw [hO.word (8 * j) h8 (by omega) hp0, wdig_lo]; congr 1; omega
  · rw [show WIT + 8 * j + 8 = WIT + (8 * j + 8) by ring, hO.word (8 * j + 8) (by omega) hoff hp1, wdig_hi]
    congr 1; omega

/-! ## Checked memory writes -/

/-- A doubleword address below the witness that no protected word occupies. -/
def safeAddr (n : Nat) : Bool :=
  decide (n + 8 ≤ WIT) && !(pSlots.contains n) && n != 0xA0 && n != 0xA8 && n != CTRW

/-- A `sw` into the low half of the word at `a`. -/
def isLowW (a : Nat) : E → Bool
  | .bin (.st .w 0) (.ld (.c k)) _ => k.toNat == a
  | _ => false

/-- A write relative to a pointer register of `rel` with a small offset. -/
def relOK (rel : List Reg) (a : Addr) : Bool :=
  match a.base with
  | some (.reg r) => rel.any (fun x => Reg.beqN x r) && decide (a.off.toNat < 4096)
  | _ => false

/-- Every write is (a) at a constant address that is safe, or the counter word by a low-half `sw`, or in `allow`
(a witness address `≥ WLO`), or (b) relative to a pointer register of `rel` (offset `< 4096`). -/
def memOKA (allow : List Nat) (rel : List Reg) (ws : SymMem) : Bool :=
  ws.all fun p => relOK rel p.1 || (p.1.base.isNone &&
    (safeAddr p.1.off.toNat || (p.1.off.toNat == CTRW && isLowW CTRW p.2) ||
      (allow.contains p.1.off.toNat && decide (WLO ≤ p.1.off.toNat ∧ p.1.off.toNat < 2 ^ 23))))

/-- No witness write at all. -/
def memOK (ws : SymMem) : Bool := memOKA [] [] ws

def regsOK (gk : List (Reg × Word)) (rf : RegFile) : Bool := gk.all fun p => E.beq (rf.get p.1) (.c p.2)

/-- The pointer registers of relative writes point into the witness area (`≥ WLO`) and are small. -/
def RelOK (rel : List Reg) (s : MachineState) : Prop :=
  ∀ r ∈ rel, WLO ≤ (s.getReg r).toNat ∧ (s.getReg r).toNat < 2 ^ 23

theorem RelOK.nil (s : MachineState) : RelOK [] s := fun _ h => by simp at h

/-- The words a run never writes: the low protected words and the witness header. -/
def Prot (A : Nat) : Prop := A ∈ pSlots ∨ A = 0xA0 ∨ A = 0xA8 ∨ (WIT ≤ A ∧ A < WLO)

theorem safeAddr_spec {n : Nat} (h : safeAddr n = true) :
    n + 8 ≤ WIT ∧ n ∉ pSlots ∧ n ≠ 0xA0 ∧ n ≠ 0xA8 ∧ n ≠ CTRW := by
  unfold safeAddr at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, fun hm => ?_, h3, h4, h5⟩
  rw [List.contains_iff_mem.mpr hm] at h2; cases h2

theorem relOK_spec {rel : List Reg} : ∀ {a : Addr}, relOK rel a = true →
    ∃ r ∈ rel, a.base = some (.reg r) ∧ a.off.toNat < 4096
  | ⟨some (.reg r), off⟩, h => by
    simp only [relOK, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨x, hx, hxr⟩, hoff⟩ := h
    obtain rfl := Reg.beqN_eq hxr
    exact ⟨x, hx, rfl, hoff⟩
  | ⟨none, _⟩, h => by simp [relOK] at h
  | ⟨some (.c _), _⟩, h => by simp [relOK] at h
  | ⟨some (.ld _), _⟩, h => by simp [relOK] at h
  | ⟨some (.un _ _), _⟩, h => by simp [relOK] at h
  | ⟨some (.bin _ _ _), _⟩, h => by simp [relOK] at h
  | ⟨some (.ite _ _ _ _ _), _⟩, h => by simp [relOK] at h

/-- The shapes a `memOKA allow rel` write can have. -/
theorem memOKA_cases {allow : List Nat} {rel : List Reg} {ws : SymMem} (h : memOKA allow rel ws = true)
    {p : Addr × E} (hp : p ∈ ws) :
    (∃ r ∈ rel, p.1.base = some (.reg r) ∧ p.1.off.toNat < 4096) ∨
    (p.1.base = none ∧
      (safeAddr p.1.off.toNat = true ∨ (p.1.off.toNat = CTRW ∧ isLowW CTRW p.2 = true) ∨
        (p.1.off.toNat ∈ allow ∧ WLO ≤ p.1.off.toNat ∧ p.1.off.toNat < 2 ^ 23))) := by
  have := List.all_eq_true.mp h p hp
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    Option.isNone_iff_eq_none] at this
  rcases this with hr | ⟨hb, hc⟩
  · exact Or.inl (relOK_spec hr)
  · right
    refine ⟨hb, ?_⟩
    rcases hc with (h1 | h2) | ⟨h3, h4⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨List.contains_iff_mem.mp h3, h4⟩)

/-- A relative write lands at `≥ WLO`. -/
theorem relWrite_ge {rel : List Reg} {s : MachineState} (hrel : RelOK rel s) {a : Addr} {r : Reg}
    (hr : r ∈ rel) (hb : a.base = some (.reg r)) (hoff : a.off.toNat < 4096) :
    (a.eval s).toNat = (s.getReg r).toNat + a.off.toNat ∧ WLO ≤ (a.eval s).toNat := by
  obtain ⟨h1, h2⟩ := hrel r hr
  obtain ⟨b, off⟩ := a
  simp only at hb hoff ⊢
  subst hb
  simp only [Addr.eval, E.eval, BitVec.toNat_add]
  rw [Nat.mod_eq_of_lt (by omega)]
  exact ⟨rfl, by omega⟩

/-- A `memOKA` write list leaves every protected word alone. -/
theorem memOKA_prot {allow : List Nat} {rel : List Reg} {ws : SymMem} (h : memOKA allow rel ws = true)
    (s : MachineState) (hrel : RelOK rel s) (A : Nat) (hA : A < 2 ^ 64) (hp : Prot A) :
    ∀ p ∈ ws, BitVec.ofNat 64 A ≠ p.1.eval s := by
  intro p hp'
  have hps : ∀ a ∈ pSlots, a < WIT := by decide
  rcases memOKA_cases h hp' with ⟨r, hr, hb, hoff⟩ | ⟨hb, hc⟩
  · obtain ⟨_, hge⟩ := relWrite_ge hrel hr hb hoff
    intro heq
    have : (p.1.eval s).toNat = A := by rw [← heq, ofNat_toNat_lt _ hA]
    rcases hp with h1 | h1 | h1 | ⟨_, h1⟩
    · have := hps A h1; unfold WLO at hge; omega
    · unfold WLO WIT at hge; omega
    · unfold WLO WIT at hge; omega
    · omega
  · obtain ⟨⟨b, off⟩, v⟩ := p
    simp only at hb; subst hb
    simp only [Addr.eval]
    intro heq
    have hoff : off.toNat = A := by rw [← heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA]
    simp only [hoff] at hc
    rcases hc with h1 | ⟨h2, -⟩ | ⟨-, h4⟩
    · obtain ⟨s1, s2, s3, s4, -⟩ := safeAddr_spec h1
      rcases hp with h | h | h | ⟨h, -⟩
      · exact s2 h
      · exact s3 h
      · exact s4 h
      · omega
    · rcases hp with h | h | h | ⟨h, -⟩
      · rw [h2] at h; unfold CTRW at h; simp [pSlots] at h
      · unfold CTRW at h2; omega
      · unfold CTRW at h2; omega
      · unfold CTRW WIT at *; omega
    · rcases hp with h | h | h | ⟨-, h'⟩
      · have := hps A h; unfold WLO WIT at *; omega
      · unfold WLO WIT at h4; omega
      · unfold WLO WIT at h4; omega
      · omega

/-- The counter word after a `memOKA` write list: untouched or written by a low-half `sw`. -/
theorem memOKA_ctr {allow : List Nat} {rel : List Reg} {ws : SymMem} (h : memOKA allow rel ws = true)
    (s : MachineState) (hrel : RelOK rel s) :
    (memEval s ws (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = (s.getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 := by
  induction ws with
  | nil => rfl
  | cons p ws ih =>
    have hp := memOKA_cases h (List.mem_cons_self ..)
    have hws : memOKA allow rel ws = true := by
      simp only [memOKA, List.all_cons, Bool.and_eq_true] at h; simpa [memOKA] using h.2
    have ih' := ih hws
    rw [memEval_cons]
    by_cases he : BitVec.ofNat 64 CTRW = p.1.eval s
    · rw [if_pos he]
      rcases hp with ⟨r, hr, hb, hoff⟩ | ⟨hb, hc⟩
      · obtain ⟨_, hge⟩ := relWrite_ge hrel hr hb hoff
        rw [← he, ofNat_toNat_lt _ (by unfold CTRW; omega)] at hge
        unfold CTRW WLO WIT at hge; omega
      · obtain ⟨⟨b, off⟩, v⟩ := p
        simp only at hb; subst hb
        have hoff : off.toNat = CTRW := by
          simp only [Addr.eval] at he; rw [← he, BitVec.toNat_ofNat]; rfl
        simp only [hoff] at hc
        rcases hc with h1 | ⟨-, h2⟩ | ⟨-, h3⟩
        · exact absurd rfl (safeAddr_spec h1).2.2.2.2
        · unfold isLowW at h2
          split at h2
          · rename_i k x
            simp only [beq_iff_eq] at h2
            have hk : k = BitVec.ofNat 64 CTRW := by
              apply BitVec.eq_of_toNat_eq; rw [h2, BitVec.toNat_ofNat]; rfl
            subst hk
            show (StoreKind.merge .w (s.getMem (BitVec.ofNat 64 CTRW)) 0 (x.eval s)).toNat / 2 ^ 32 = _
            rw [merge_w0_high]
            have := (s.getMem (BitVec.ofNat 64 CTRW)).isLt
            omega
          · cases h2
        · unfold WLO WIT CTRW at h3; omega
    · rw [if_neg he]; exact ih'

/-- A `memOKA` write list leaves every word at or above `2^23 + 4096` alone (the embedded data). -/
theorem memOKA_data {allow : List Nat} {rel : List Reg} {ws : SymMem} (h : memOKA allow rel ws = true)
    (s : MachineState) (hrel : RelOK rel s) (A : Nat) (hA : 2 ^ 23 + 4096 ≤ A) (hA' : A < 2 ^ 64) :
    ∀ p ∈ ws, BitVec.ofNat 64 A ≠ p.1.eval s := by
  intro p hp'
  rcases memOKA_cases h hp' with ⟨r, hr, hb, hoff⟩ | ⟨hb, hc⟩
  · obtain ⟨hev, -⟩ := relWrite_ge hrel hr hb hoff
    have h2 := (hrel r hr).2
    intro heq
    have : (p.1.eval s).toNat = A := by rw [← heq, ofNat_toNat_lt _ hA']
    omega
  · obtain ⟨⟨b, off⟩, v⟩ := p
    simp only at hb; subst hb
    simp only [Addr.eval]
    intro heq
    have hoff : off.toNat = A := by rw [← heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA']
    simp only [hoff] at hc
    rcases hc with h1 | ⟨h2, -⟩ | ⟨-, h4⟩
    · have := (safeAddr_spec h1).1; unfold WIT at this; omega
    · unfold CTRW at h2; omega
    · omega

theorem DATA_ge (k : Nat) (hk : k < 12) : 2 ^ 23 + 4096 ≤ DATA + 8 * k ∧ DATA + 8 * k + 8 ≤ 2 ^ 24 := by
  unfold DATA; omega

/-- One embedded doubleword, at a given address with a given value. -/
theorem DataOK.word {s : MachineState} (h : DataOK s) (k : Nat) (hk : k < 12) (v : Nat)
    (hv : dataWords.getD k 0 = v) (a : Nat) (ha : a = DATA + 8 * k) :
    s.getMem (BitVec.ofNat 64 a) = BitVec.ofNat 64 v := by
  subst hv ha; exact h k hk

theorem Glob_toState_allow {gk0 gk : List (Reg × Word)} {w : WBytes} {pk : Digest} {s : MachineState}
    {allow : List Nat} {rel : List Reg}
    (hG : Glob gk0 w pk s) (σ : SymState) (pc : Word) (hm : memOKA allow rel σ.mem = true)
    (hrel : RelOK rel s) (hr : regsOK gk σ.regs = true) : Glob gk w pk (σ.toState s pc) := by
  obtain ⟨-, h0, h2, h3, h4, h5⟩ := hG
  have fr : ∀ A, A < 2 ^ 64 → Prot A →
      (σ.toState s pc).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hp
    rw [SymState.toState_getMem]
    exact memEval_frame s _ _ (memOKA_prot hm s hrel A hA hp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have := List.all_eq_true.mp hr p hp
    rw [SymState.toState_getReg, E.beq_eq this]; rfl
  · intro j hj
    rw [fr _ (by unfold WIT; omega) (Or.inr (Or.inr (Or.inr ⟨by unfold WIT; omega, by unfold WLO WIT; omega⟩)))]
    exact h0 j hj
  · exact ⟨(fr 0xA0 (by omega) (by simp [Prot])).trans h2.1, (fr 0xA8 (by omega) (by simp [Prot])).trans h2.2⟩
  · intro a ha
    have : a < 2 ^ 64 := by simp [pSlots] at ha; omega
    rw [fr a this (Or.inl ha)]; exact h3 a ha
  · show (memEval s σ.mem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
    rw [memOKA_ctr hm s hrel]; exact h4
  · apply h5.congr
    intro A hA hAend
    rw [SymState.toState_getMem, memEval_frame s _ _
      (memOKA_data hm s hrel _ (by unfold TAB at hA; omega) (by omega))]

theorem Glob_toState {gk0 gk : List (Reg × Word)} {w : WBytes} {pk : Digest} {s : MachineState}
    (hG : Glob gk0 w pk s) (σ : SymState) (pc : Word) (hm : memOK σ.mem = true)
    (hr : regsOK gk σ.regs = true) : Glob gk w pk (σ.toState s pc) :=
  Glob_toState_allow hG σ pc hm (RelOK.nil s) hr

/-- **General witness frame**: the witness words a run does not write stay original. -/
theorem Orig_toState {w : WBytes} {s : MachineState} {P P' : Nat → Prop} (hO : Orig w P s)
    (σ : SymState) (pc : Word)
    (hfr : ∀ o, o < WX → P' o → P o ∧ ∀ p ∈ σ.mem, BitVec.ofNat 64 (WIT + o) ≠ p.1.eval s) :
    Orig w P' (σ.toState s pc) := by
  intro j h1 h2
  obtain ⟨hp, hne⟩ := hfr (8 * j) h1 h2
  rw [SymState.toState_getMem, memEval_frame s _ _ hne]
  exact hO j h1 hp

/-- A run with constant writes only: the witness words outside `allow` stay original. -/
theorem Orig_toState_const {w : WBytes} {s : MachineState} {P : Nat → Prop} {allow : List Nat}
    (hO : Orig w P s) (σ : SymState) (pc : Word) (hm : memOKA allow [] σ.mem = true) :
    Orig w (fun o => P o ∧ WIT + o ∉ allow) (σ.toState s pc) := by
  refine Orig_toState hO σ pc (fun o ho ⟨hp, hna⟩ => ⟨hp, fun p hp' heq => ?_⟩)
  rcases memOKA_cases hm hp' with ⟨r, hr, -⟩ | ⟨hb, hc⟩
  · simp at hr
  · obtain ⟨⟨b, off⟩, v⟩ := p
    simp only at hb; subst hb
    simp only [Addr.eval] at heq
    have hoff : off.toNat = WIT + o := by
      rw [← heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold WIT WX at *; omega)]
    simp only [hoff] at hc
    rcases hc with h1 | ⟨h2, -⟩ | ⟨h3, -⟩
    · have := (safeAddr_spec h1).1; omega
    · unfold CTRW WIT at h2; omega
    · exact hna h3

/-- A run without witness writes keeps the whole witness. -/
theorem WitAll_toState {w : WBytes} {s : MachineState} (hW : WitAll w s) (σ : SymState)
    (pc : Word) (hm : memOK σ.mem = true) : WitAll w (σ.toState s pc) := by
  have := Orig_toState_const (hW.orig (fun _ => True)) σ pc hm
  intro j hj
  exact this j hj ⟨trivial, by simp⟩

theorem Orig_writeHash {w : WBytes} {s : MachineState} {P : Nat → Prop} (hO : Orig w P s)
    (ans : BitVec 256) (d : Nat) (hd : s.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) :
    Orig w (fun o => P o ∧ (WIT + o + 8 ≤ d ∨ d + 32 ≤ WIT + o)) (writeHash s ans) := by
  intro j h1 ⟨h2, h3⟩
  rw [writeHash_frame s ans d _ hd (by unfold WIT WX at *; omega) (by omega) h3]
  exact hO j h1 h2

theorem WitAll_writeHash {w : WBytes} {s : MachineState} (hW : WitAll w s)
    (ans : BitVec 256) (d : Nat) (hd : s.getReg .x12 = BitVec.ofNat 64 d)
    (hlow : d + 32 ≤ WIT) : WitAll w (writeHash s ans) := by
  intro j hj
  rw [writeHash_frame s ans d _ hd (by unfold WIT WX at *; omega) (by unfold WIT at hlow; omega)
    (Or.inr (by unfold WIT at *; omega))]
  exact hW j hj

/-- A hash destination (32 bytes) that no protected word occupies. -/
def safeDest (d : Nat) : Bool :=
  decide (d % 8 = 0) && decide (d + 32 ≤ 2 ^ 23) &&
    (pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 8).map (fun j => WIT + 8 * j)).all
      (fun q => decide (q + 8 ≤ d ∨ d + 32 ≤ q))

/-- Every aligned destination in the witness area past the header is safe. -/
theorem safeDest_hi (d : Nat) (h : WLO ≤ d) (h8 : d % 8 = 0) (hm : d + 32 ≤ 2 ^ 23) :
    safeDest d = true := by
  simp only [safeDest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, MEMORY_BYTES]
  refine ⟨⟨by simpa using h8, by simpa using hm⟩, fun q hq => Or.inl ?_⟩
  simp only [List.mem_append, List.mem_map, List.mem_range, pSlots, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  unfold WLO WIT CTRW at *
  rcases hq with ((h1 | h1 | h1) | h1 | h1 | h1) | ⟨j, hj, rfl⟩ <;> omega

theorem Glob_writeHash {gk : List (Reg × Word)} {w : WBytes} {pk : Digest} {s : MachineState}
    (hG : Glob gk w pk s) (ans : BitVec 256) (d : Nat) (hd : s.getReg .x12 = BitVec.ofNat 64 d)
    (hsafe : safeDest d = true) : Glob gk w pk (writeHash s ans) := by
  obtain ⟨h1, h0, h2, h3, h4, h5⟩ := hG
  simp only [safeDest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hsafe
  obtain ⟨⟨-, hd1⟩, hd2⟩ := hsafe
  have hd1' : d + 32 ≤ 2 ^ 24 := by omega
  have fr : ∀ A, A < 2 ^ 64 → (A + 8 ≤ d ∨ d + 32 ≤ A) →
      (writeHash s ans).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hp
    rw [writeHash_getMem_ofNat s ans d A hd hA (by omega)]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hps : ∀ a ∈ pSlots, a < WIT := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp; rw [writeHash_getReg]; exact h1 p hp
  · intro j hj
    have hm : WIT + 8 * j ∈ pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 8).map (fun j => WIT + 8 * j) :=
      List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
    rw [fr (WIT + 8 * j) (by unfold WIT; omega) (hd2 _ hm)]
    exact h0 j hj
  · have m0 : (0xA0 : Nat) ∈ pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 8).map (fun j => WIT + 8 * j) := by
      simp
    have m8 : (0xA8 : Nat) ∈ pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 8).map (fun j => WIT + 8 * j) := by
      simp
    exact ⟨(fr 0xA0 (by omega) (hd2 _ m0)).trans h2.1, (fr 0xA8 (by omega) (hd2 _ m8)).trans h2.2⟩
  · intro a ha
    have hm : a ∈ pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 8).map (fun j => WIT + 8 * j) :=
      List.mem_append_left _ (List.mem_append_left _ ha)
    have := hps a ha
    rw [fr a (by unfold WIT at this; omega) (hd2 _ hm)]; exact h3 a ha
  · have mc : CTRW ∈ pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 8).map (fun j => WIT + 8 * j) := by simp
    show ((writeHash s ans).getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
    rw [fr CTRW (by unfold CTRW; omega) (hd2 _ mc)]; exact h4
  · apply h5.congr
    intro A hA hAend
    exact fr A (by omega) (Or.inr (by unfold TAB at hA; omega))

theorem Known_writeHash {known : List (Reg × Word)} {s : MachineState}
    (h : ∀ p ∈ known, s.getReg p.1 = p.2) (a : BitVec 256) : ∀ p ∈ known, (writeHash s a).getReg p.1 = p.2 := by
  intro p hp; rw [writeHash_getReg]; exact h p hp

end SigGolfCandidate.T3M.CanonicalPort.Verify

end CanonicalPortPart6

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart7

/-!
# Generic consequences of a checked path run (T3M)

* `cfg0`, `runAt known stops n dirs` : the path run from instruction `n` (M0's `pcOf n`) with the registers
  `known` replaced by constants, through `vlook`;
* `KnownOK`, `knownB`, `keepB`, `resOK`, `run_post` (steps, ECALL fetch, `Glob` preserved);
* branch-obligation helpers `br_ne_zero`, `br_eq_zero`;
* HASH arguments at constant registers (`hashArgsB`, `hashArgs_ofNat`), frames at constant addresses.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)

def cfg0 : Config := {}

/-- The path run from instruction `n` (stops: instruction indices). -/
def runAt (known : List (Reg × Word)) (stops : List Nat) (n : Nat) (dirs : List Dir) : Option PRes :=
  pathAux cfg0 vlook (stops.map pcOf) 2000 (pcOf n) dirs (σK known) []

def KnownOK (known : List (Reg × Word)) (s : MachineState) : Prop := ∀ p ∈ known, s.getReg p.1 = p.2

/-- Side-condition-free, preserves the global invariant. -/
def resOK (allow : List Nat) (rel : List Reg) (gk : List (Reg × Word)) (r : PRes) : Bool :=
  memOKA allow rel r.st.mem && regsOK gk r.st.regs && r.st.obl.isEmpty

def knownB (known : List (Reg × Word)) (r : PRes) : Bool :=
  known.all fun p => E.beq (r.st.regs.get p.1) (.c p.2)

def keepB (rs : List Reg) (r : PRes) : Bool := rs.all fun x => E.beq (r.st.regs.get x) (.reg x)

theorem PRes.toState_getReg (r : PRes) (s : MachineState) (x : Reg) :
    (r.toState s).getReg x = (r.st.regs.get x).eval s := SymState.toState_getReg _ _ _ _

theorem PRes.toState_getMem (r : PRes) (s : MachineState) (a : Word) :
    (r.toState s).getMem a = memEval s r.st.mem a := rfl

theorem PRes.toState_pc (r : PRes) (s : MachineState) (h : r.spc = none := by rfl) :
    (r.toState s).pc = r.pc := by
  simp [PRes.toState, PRes.finalPc, h]

theorem knownB_ok {known : List (Reg × Word)} {r : PRes} (h : knownB known r = true)
    (s : MachineState) : KnownOK known (r.toState s) := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  rw [PRes.toState_getReg, E.beq_eq this]; rfl

theorem keepB_ok {rs : List Reg} {r : PRes} (h : keepB rs r = true) (s : MachineState) :
    ∀ x ∈ rs, (r.toState s).getReg x = s.getReg x := by
  intro x hx
  have := List.all_eq_true.mp h x hx
  rw [PRes.toState_getReg, E.beq_eq this]; rfl

theorem run_post {known : List (Reg × Word)} {stops : List Nat} {n : Nat} {dirs : List Dir}
    {r : PRes} {allow : List Nat} {rel : List Reg} {gk : List (Reg × Word)}
    (hrun : runAt known stops n dirs = some r) (hok : resOK allow rel gk r = true)
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ r.brs, b.holds s) :
    Steps image s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch image (r.toState s) = some (.base .ECALL)) ∧
      (∀ gk0 w pk, Glob gk0 w pk s → RelOK rel s → Glob gk w pk (r.toState s)) := by
  simp only [resOK, Bool.and_eq_true, List.isEmpty_iff] at hok
  obtain ⟨⟨hm, hr⟩, ho⟩ := hok
  obtain ⟨h1, h2⟩ := pathRun_sound hrun vlook_ok s hpc hk (by rw [ho]; simp) hbr
  exact ⟨h1, h2, fun gk0 w pk hG hrel => Glob_toState_allow hG r.st _ hm hrel hr⟩

theorem br_ne_zero (x : E) (d : Bool) (s : MachineState) :
    Br.holds s ⟨.ne, x, .c 0, d⟩ ↔ (decide (x.eval s ≠ 0) = d) := by
  simp only [Br.holds, CmpOp.eval, E.eval]
  cases d <;> simp [bne_iff_ne]

theorem br_eq_zero (x : E) (d : Bool) (s : MachineState) :
    Br.holds s ⟨.eq, x, .c 0, d⟩ ↔ (decide (x.eval s = 0) = d) := by
  simp only [Br.holds, CmpOp.eval, E.eval]
  cases d <;> simp

/-! ## HASH arguments at constant registers -/

def hashArgsB (a n d : Nat) : Bool :=
  decide (a % 8 = 0) && decide (0 < n ∧ n % 64 = 0) && decide (a + n ≤ MEMORY_BYTES) &&
    decide (d + 8 ≤ MEMORY_BYTES ∧ d % 8 = 0) && decide (d + 32 ≤ MEMORY_BYTES)

theorem hashArgs_ofNat (t : MachineState) (a n d : Nat) (h10 : t.getReg .x10 = BitVec.ofNat 64 a)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 n) (h12 : t.getReg .x12 = BitVec.ofNat 64 d)
    (ha : a < 2 ^ 64) (hn : n < 2 ^ 64) (hd : d < 2 ^ 64) (h : hashArgsB a n d = true) :
    hashArgumentsValid t = true := by
  simp only [hashArgsB, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [hashArgumentsValid, h10, h11, h12, rangeValid, accessValid, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, Bool.and_eq_true,
    decide_eq_true_eq]
  omega

/-- HASH arguments for a destination at any aligned address with room for 32 bytes. -/
theorem hashArgs_of (t : MachineState) (a n d : Nat) (h10 : t.getReg .x10 = BitVec.ofNat 64 a)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 n) (h12 : t.getReg .x12 = BitVec.ofNat 64 d)
    (ha8 : a % 8 = 0) (hn : 0 < n ∧ n % 64 = 0) (han : a + n ≤ 2 ^ 24) (hd8 : d % 8 = 0)
    (hd : d + 32 ≤ 2 ^ 24) : hashArgumentsValid t = true :=
  hashArgs_ofNat t a n d h10 h11 h12 (by omega) (by omega) (by omega) (by
    unfold hashArgsB
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨decide_eq_true ha8, decide_eq_true hn⟩, decide_eq_true ?_⟩, decide_eq_true ⟨?_, hd8⟩⟩,
      decide_eq_true ?_⟩ <;> unfold MEMORY_BYTES <;> omega)

/-! ## Frames at constant addresses -/

theorem memEval_frame_ofNat (s : MachineState) (ws : SymMem) (A : Nat) (hA : A < 2 ^ 64)
    (h : ∀ p ∈ ws, p.1.base = none ∧ p.1.off.toNat ≠ A) :
    memEval s ws (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  apply memEval_frame
  intro p hp heq
  obtain ⟨h1, h2⟩ := h p hp
  obtain ⟨⟨b, off⟩, v⟩ := p
  simp only at h1; subst h1
  simp only [Addr.eval] at heq
  apply h2; rw [← heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA]

/-- One constant-address write of a symbolic memory, read at a constant address. -/
theorem memEval_cons_ofNat (s : MachineState) (k A : Nat) (v : E) (ws : SymMem) (hA : A < 2 ^ 64)
    (hk : k < 2 ^ 64) :
    memEval s ((⟨none, BitVec.ofNat 64 k⟩, v) :: ws) (BitVec.ofNat 64 A) =
      if A = k then v.eval s else memEval s ws (BitVec.ofNat 64 A) := by
  rw [memEval_cons]
  have e : Addr.eval s ⟨none, BitVec.ofNat 64 k⟩ = BitVec.ofNat 64 k := rfl
  by_cases h : A = k
  · subst h; rw [if_pos e.symm, if_pos rfl]
  · have hne : BitVec.ofNat 64 A ≠ Addr.eval s ⟨none, BitVec.ofNat 64 k⟩ := by
      rw [e]; exact ofNat_ne hA hk h
    rw [if_neg hne, if_neg h]

theorem memEval_cons_ne (s : MachineState) (k : Word) (v : E) (ws : SymMem) (A : Word)
    (h : A ≠ k) : memEval s ((⟨none, k⟩, v) :: ws) A = memEval s ws A := by
  rw [memEval_cons, if_neg (by simpa [Addr.eval] using h)]

theorem memEval_cons_eq (s : MachineState) (k : Word) (v : E) (ws : SymMem) (A : Word)
    (h : A = k) : memEval s ((⟨none, k⟩, v) :: ws) A = v.eval s := by
  rw [memEval_cons, if_pos (by simpa [Addr.eval] using h)]

end SigGolfCandidate.T3M.CanonicalPort.Verify

end CanonicalPortPart7

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart8

/-!
# Checked path runs (T3M)

`specB allow rel gk (runAt known stops n dirs) sp obl post keep = true` (checked by `decide +kernel`) says: the path
run from instruction `n` has exactly the register values `sp.regs` (symbolic over the initial state), the memory
writes `sp.mem`, the final pc (`sp.pc`, or the symbolic target `sp.spc`), stops at an `ECALL` iff `sp.ecall`, takes
`sp.steps` steps and `sp.cycles` cycles, assumes exactly the branch outcomes `sp.brs` and emits exactly the side
conditions `obl` (accesses at symbolic addresses); its writes pass `memOKA allow rel` (constant safe/allowed
addresses, `rel`-relative pointer writes), it sets the constant registers `gk`, the registers of `post` to the given
constants and keeps the registers of `keep`.

`spec_run` turns a checked run into a `SpecRes` on every concrete state satisfying the known registers, the branch
outcomes and the side conditions. Witness frames: `SpecRes.orig` (general), `SpecRes.orig_const` (no relative
writes), `SpecRes.witAll` (no witness writes).
-/

namespace SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)

structure Spec where
  regs : List (Reg × E)
  mem : List (Addr × E)
  pc : Nat
  ecall : Bool
  steps : Nat
  brs : List Br
  spc : Option E := none
  /-- RV64M instructions can cost more than one cycle per step. -/
  cycles : Nat := steps

def regsB (r : PRes) (l : List (Reg × E)) : Bool := l.all fun p => E.beq (r.st.regs.get p.1) p.2

def specB (allow : List Nat) (rel : List Reg) (gk : List (Reg × Word)) (o : Option PRes) (sp : Spec)
    (obl : List Oblig) (post : List (Reg × Word)) (keep : List Reg) : Bool :=
  match o with
  | none => false
  | some r =>
    regsB r sp.regs && listBeq pairBeq r.st.mem sp.mem &&
      (sp.spc.isSome || r.pc.toNat == (pcOf sp.pc).toNat) &&
      r.ecall == sp.ecall && r.steps == sp.steps && r.cycles == sp.cycles &&
      listBeq Br.beq r.brs sp.brs && optEBeq r.spc sp.spc && listBeq Oblig.beq r.st.obl obl &&
      memOKA allow rel r.st.mem && regsOK gk r.st.regs && knownB post r && keepB keep r

/-- What a checked run gives on a concrete state. -/
structure SpecRes (allow : List Nat) (rel : List Reg) (gk : List (Reg × Word)) (sp : Spec)
    (post : List (Reg × Word)) (keep : List Reg) (s t : MachineState) : Prop where
  steps : Steps image s sp.steps sp.cycles t
  ecall : sp.ecall = true → fetch image t = some (.base .ECALL)
  glob : ∀ gk0 w pk, Glob gk0 w pk s → RelOK rel s → Glob gk w pk t
  known : KnownOK post t
  keep : ∀ x ∈ keep, t.getReg x = s.getReg x
  regs : ∀ p ∈ sp.regs, t.getReg p.1 = p.2.eval s
  mem : ∀ A, t.getMem A = memEval s sp.mem A
  memc : memOKA allow rel sp.mem = true
  pc : sp.spc = none → t.pc = pcOf sp.pc
  spc : ∀ e, sp.spc = some e → t.pc = e.eval s

theorem spec_run {allow : List Nat} {rel : List Reg} {gk known post : List (Reg × Word)} {stops : List Nat}
    {n : Nat} {dirs : List Dir} {sp : Spec} {obl : List Oblig} {keep : List Reg}
    (h : specB allow rel gk (runAt known stops n dirs) sp obl post keep = true)
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ sp.brs, b.holds s) (hob : ∀ o ∈ obl, o.holds s) :
    ∃ t, SpecRes allow rel gk sp post keep s t := by
  unfold specB at h
  split at h
  · cases h
  rename_i r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hregs, hmem⟩, hpc'⟩, hec⟩, hst⟩, hcy⟩, hbrs⟩, hspc⟩, hobl⟩, hmok⟩, hrok⟩, hkn⟩,
    hkeep⟩ := h
  have hbrs' := listBeq_eq (fun _ _ => Br.beq_eq) hbrs
  have hmem' := listBeq_eq (fun _ _ => pairBeq_eq) hmem
  have hspc' := optEBeq_eq hspc
  have hobl' := listBeq_eq (fun _ _ => Oblig.beq_eq) hobl
  obtain ⟨hst', hec'⟩ := pathRun_sound hr vlook_ok s hpc hk (by rw [hobl']; exact hob)
    (by rw [hbrs']; exact hbr)
  refine ⟨r.toState s, ⟨?_, ?_, ?_, knownB_ok hkn s, keepB_ok hkeep s, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hcy, hst] at hst'; exact hst'
  · intro he; exact hec' (hec.trans he)
  · intro gk0 w pk hG hrel; exact Glob_toState_allow hG r.st _ hmok hrel hrok
  · intro p hp
    rw [PRes.toState_getReg, E.beq_eq (List.all_eq_true.mp hregs p hp)]
  · intro A; rw [PRes.toState_getMem, hmem']
  · rw [← hmem']; exact hmok
  · intro hn
    rw [hn] at hpc'
    simp only [Option.isSome_none, Bool.false_or, beq_iff_eq] at hpc'
    rw [PRes.toState_pc _ _ (hspc'.trans hn), BitVec.eq_of_toNat_eq hpc']
  · intro e he; simp [PRes.toState, PRes.finalPc, hspc'.trans he]

section specres
variable {allow : List Nat} {rel : List Reg} {gk post : List (Reg × Word)} {sp : Spec} {keep : List Reg}
  {s t : MachineState}

/-- The witness words a checked run does not write stay original. -/
theorem SpecRes.orig (hr : SpecRes allow rel gk sp post keep s t) {w : WBytes} {P P' : Nat → Prop}
    (hO : Orig w P s)
    (hfr : ∀ o, o < WX → P' o → P o ∧ ∀ p ∈ sp.mem, BitVec.ofNat 64 (WIT + o) ≠ p.1.eval s) :
    Orig w P' t := by
  intro j h1 h2
  obtain ⟨hp, hne⟩ := hfr (8 * j) h1 h2
  rw [hr.mem, memEval_frame s _ _ hne]
  exact hO j h1 hp

/-- Without relative writes, the witness words outside `allow` stay original. -/
theorem SpecRes.orig_const (hr : SpecRes allow [] gk sp post keep s t) {w : WBytes} {P : Nat → Prop}
    (hO : Orig w P s) : Orig w (fun o => P o ∧ WIT + o ∉ allow) t := by
  have h := Orig_toState_const (σ := ⟨RegFile.init, sp.mem, []⟩) (pc := 0) hO hr.memc
  intro j h1 h2
  have := h j h1 h2
  rw [hr.mem]
  exact this

/-- Without witness writes, the whole witness (and the zero memory after it) stays original. -/
theorem SpecRes.witAll (hr : SpecRes [] [] gk sp post keep s t) {w : WBytes} (hW : WitAll w s) :
    WitAll w t := by
  intro j hj
  have := hr.orig_const (hW.orig (fun _ => True)) j hj ⟨trivial, by simp⟩
  exact this

theorem SpecRes.reg (hr : SpecRes allow rel gk sp post keep s t) {x : Reg} {v : Word} (h : (x, v) ∈ post) :
    t.getReg x = v := hr.known _ h

end specres

end SigGolfCandidate.T3M.CanonicalPort.Verify

end CanonicalPortPart8

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart9

/-!
# Bit-level facts about the verify image's stores (T3M)

* `replaceWord32_1_toNat`, `merge_w4_toNat` (`sw v, a + 4`: the high half), `merge_w0_toNat` (in `Mem`);
* `merge_sw2_toNat` / `merge_sw2` : two `sw` into both halves of a doubleword (the T3 header word 1
  `tree | index << 32` of the FTS blocks, written `sw s6, 24(a0); sw E, 28(a0)`), = `ofNat (hdr1 a b)`;
* `hdr0_small`, `hdr1_small` : Core's header words for small fields.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

theorem replaceWord32_1_toNat (w : BitVec 64) (p : Nat) (hp : p < 2 ^ 32) :
    (replaceWord32 w 1 ((BitVec.ofNat 64 p).truncate 32)).toNat = w.toNat % 2 ^ 32 + 2 ^ 32 * p := by
  unfold replaceWord32
  have hm : (~~~(0xFFFFFFFF#64 <<< (1 * 32)) : BitVec 64) = BitVec.ofNat 64 (2 ^ 32 - 1) := by
    decide
  rw [hm, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have e1 : (2 ^ 32 - 1) % 2 ^ 64 = 2 ^ 32 - 1 := by norm_num
  have e2 : p % 2 ^ 64 % 2 ^ 32 = p := by omega
  have e3 : p % 2 ^ 64 * 2 ^ (1 * 32) % 2 ^ 64 = 2 ^ 32 * p := by
    rw [Nat.mod_eq_of_lt (by omega : p < 2 ^ 64)]; rw [Nat.mod_eq_of_lt (by norm_num; omega)]; ring
  rw [e1, e2, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, e3]
  rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by norm_num))]
  omega

theorem merge_w4_toNat (w v : BitVec 64) :
    (StoreKind.merge .w w 4 v).toNat = w.toNat % 2 ^ 32 + 2 ^ 32 * (v.toNat % 2 ^ 32) := by
  have := replaceWord32_1_toNat w (v.toNat % 2 ^ 32) (Nat.mod_lt _ (by decide))
  simp only [StoreKind.merge, show (4 : Nat) / 4 = 1 from rfl]
  have e : (BitVec.ofNat 64 (v.toNat % 2 ^ 32)).truncate 32 = v.truncate 32 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  rw [← e, this]

theorem merge_hi (a b : Nat) :
    StoreKind.merge .w (BitVec.ofNat 64 a) 4 (BitVec.ofNat 64 b) = BitVec.ofNat 64 (hdr1 a b) := by
  apply BitVec.eq_of_toNat_eq
  rw [merge_w4_toNat]
  have h := hdr1_lt a b
  simp only [BitVec.toNat_ofNat]
  unfold hdr1 at h ⊢
  omega

/-- Both halves of a doubleword written by two `sw`. -/
theorem merge_sw2_toNat (old a b : BitVec 64) :
    (StoreKind.merge .w (StoreKind.merge .w old 0 a) 4 b).toNat = a.toNat % 2 ^ 32 + 2 ^ 32 * (b.toNat % 2 ^ 32) := by
  rw [merge_w4_toNat, merge_w0_toNat]
  omega

theorem merge_sw2 (old : BitVec 64) (a b : Nat) :
    StoreKind.merge .w (StoreKind.merge .w old 0 (BitVec.ofNat 64 a)) 4 (BitVec.ofNat 64 b) =
      BitVec.ofNat 64 (hdr1 a b) := by
  apply BitVec.eq_of_toNat_eq
  have hl := hdr1_lt a b
  rw [merge_sw2_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hl]
  have h1 : a % 2 ^ 64 % 2 ^ 32 = a % 2 ^ 32 := Nat.mod_mod_of_dvd _ (by norm_num)
  have h2 : b % 2 ^ 64 % 2 ^ 32 = b % 2 ^ 32 := Nat.mod_mod_of_dvd _ (by norm_num)
  rw [h1, h2, hdr1]; ring

/-- Header word 0 for small fields. -/
theorem hdr0_small (tag lay tree position : Nat) (ht : tag < 256) (hl : lay < 256) (htr : tree < 2 ^ 32)
    (hp : position < 2 ^ 32) :
    hdr0 tag lay tree position = 1 + 256 * tag + 65536 * lay + 2 ^ 32 * position :=
  hdr0_eq tag lay tree position ht hl htr hp

theorem hdr1_small (tree index : Nat) (htr : tree < 2 ^ 32) (hi : index < 2 ^ 32) :
    hdr1 tree index = tree + 2 ^ 32 * index := hdr1_eq tree index htr hi

end SigGolfCandidate.T3M.CanonicalPort.Verify

end CanonicalPortPart9

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart10

/-! # V1 chains: code access, label tables and the expected symbolic results of the chain code

The chain code of the verify image (`t3m/ver/gen_t3.py`: `chains_code`, `_ttab`, `_ctab`, `_qtab`, `_q48tab`) is
layer-shared and entered by `jalr` dispatch on the digits:

* **lower layers** (3, 2, 1; 43 chains of width 3): 14 triples `(3t, 3t+1, 3t+2)`; the table `ttab` (512 rows
  `k = dA + 8 dB + 64 dC` of 16 slots of 8 words) holds in slot `t` the head of chain `A = 3t` (digit `dA < 7`)
  or its max-digit copy, then `j` into the shared block `tc_t_dB_dC`: `A`'s rungs `r0 .. r6` (entered at
  `r_dA`), then `B` and `C` (head and rungs `d .. 6`, or the copy), then the extraction and `jalr` of triple
  `t + 1`, or for `t = 13` the dispatch `ctab[t4]` of the checksum chain 42 (`ck_r0 .. ck_r6`, `ck_done`);
* **top layer** (58 chains: 49 of width 2, 9 of width 3): 12 quads `(4q .. 4q+3)` through `qtab` (256 rows of 12
  slots) and the blocks `tq_q_dB_dC_dD`, chain 48 through `q48tab`, then `q48_done` dispatches into the lower
  code's triples 11..13 (the top's chains 49..57 run as the lower chains 33..41), and `ctab[8] = jr ra`.

Chain blocks are addressed from a base register (`s6 = x22`: the lower chains and the top's 49..57; `s3 = x19`:
the top's 0..48). A head is `addi a0, base, off; addi a2, a0, 48; mv s9, s11 | add s9, s9, t3; sd s9, 16(a0);
sd tp, 24(a0)`, a rung `sb POS_d, 20(a0); [li a2, slot]; ecall`, a max-digit copy `ld gp, off+48(base);
ld a4, off+56(base); sd gp, slot; sd a4, slot+8; [mv s9, s11 | add s9, s9, t3]`.

Every expected result is the executor's (`Rv.symRun` from the identity state) on the image words at the given
pc; `ChainCheck*` verifies them by `decide +kernel`. -/

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! ## Code access for the new image -/

abbrev lChunks := SigGolfCandidate.T3M.CanonicalPort.Verify.vChunks
def lcode (i : Nat) := SigGolfCandidate.T3M.CanonicalPort.Verify.codeFrom i

theorem lcodeAt (i : Nat) (hi : i<221830) :
    CodeAt CanonicalNative.fixture (pcOf i) (lcode i) :=
  SigGolfCandidate.T3M.CanonicalPort.Verify.codeAt_from i (by omega)

/-! ## Boolean comparison of executor results -/

def lstBeq {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && lstBeq f as bs
  | _, _ => false

theorem lstBeq_eq {α : Type} {f : α → α → Bool} (hf : ∀ a b, f a b = true → a = b) :
    ∀ {l l' : List α}, lstBeq f l l' = true → l = l' := by
  intro l
  induction l with
  | nil => intro l' h; cases l' <;> simp_all [lstBeq]
  | cons a as ih =>
    intro l' h
    cases l' with
    | nil => simp [lstBeq] at h
    | cons b bs =>
      simp only [lstBeq, Bool.and_eq_true] at h
      rw [hf _ _ h.1, ih h.2]

def rfBeq (a b : RegFile) : Bool := lstBeq E.beq a.fields b.fields

theorem rfBeq_eq {a b : RegFile} (h : rfBeq a b = true) : a = b := by
  have := lstBeq_eq (fun _ _ => E.beq_eq) h
  cases a; cases b
  simp only [RegFile.fields, List.cons.injEq] at this
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, -⟩ := this
  subst_vars; rfl

def wBeq (a b : Addr × E) : Bool := Addr.beq a.1 b.1 && E.beq a.2 b.2

theorem wBeq_eq {a b : Addr × E} (h : wBeq a b = true) : a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [wBeq, Bool.and_eq_true] at h
  rw [Addr.beq_eq h.1, E.beq_eq h.2]

def stBeq (a b : SymState) : Bool :=
  rfBeq a.regs b.regs && lstBeq wBeq a.mem b.mem && lstBeq Oblig.beq a.obl b.obl

theorem stBeq_eq {a b : SymState} (h : stBeq a b = true) : a = b := by
  obtain ⟨ar, am, ao⟩ := a; obtain ⟨br, bm, bo⟩ := b
  simp only [stBeq, Bool.and_eq_true] at h
  rw [rfBeq_eq h.1.1, lstBeq_eq (fun _ _ => wBeq_eq) h.1.2, lstBeq_eq (fun _ _ => Oblig.beq_eq) h.2]

def resBeq (a b : Result) : Bool :=
  stBeq a.st b.st && E.beq a.pc b.pc && decide (a.stop = b.stop) && a.steps == b.steps &&
    a.cycles == b.cycles

theorem resBeq_eq {a b : Result} (h : resBeq a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := a; obtain ⟨b1, b2, b3, b4, b5⟩ := b
  simp only [resBeq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [stBeq_eq h1, E.beq_eq h2, h3, h4, h5]

/-- `o = some r`, as a Boolean check. -/
def rOK (o : Option Result) (r : Result) : Bool :=
  match o with
  | some r' => resBeq r' r
  | none => false

theorem rOK_eq {o : Option Result} {r : Result} (h : rOK o r = true) : o = some r := by
  cases o with
  | none => simp [rOK] at h
  | some r' => simp only [rOK] at h; rw [resBeq_eq h]

/-- The executor on the image words from instruction `p` (at most `f` instructions). -/
def vrun (p f : Nat) : Option Result := symRun {} (lcode p) (pcOf p) f

/-! ## Label tables (word indices of `t3m/images/verify.labels`) -/

/-- `ctab` (checksum chain dispatch, 9 slots of 8 words). -/
def ctabIdx : Nat := 111104
/-- `ttab` (lower triple table, 512 rows of 16 slots of 8 words). -/
def ttabIdx : Nat := 111176
/-- `q48tab` (chain 48 of the top, 4 slots). -/
def q48tabIdx : Nat := 176712
/-- `qtab` (top quad table, 256 rows of 16 slots of 8 words). -/
def qtabIdx : Nat := 176744
def ckR0 : Nat := 82059
def ckDone : Nat := 82074
def q48R0 : Nat := 110683
def q48Done : Nat := 110690

/-- `tc_t_dB_dC_r0` at `64 t + 8 dB + dC`. -/
def triBaseTab : List Nat :=
  [42027, 42086, 42143, 42198, 42251, 42302, 42351, 42398, 42442, 42499, 42554, 42607, 42658, 42707, 42754, 42799,
  42841, 42896, 42949, 43000, 43049, 43096, 43141, 43184, 43224, 43277, 43328, 43377, 43424, 43469, 43512, 43553,
  43591, 43642, 43691, 43738, 43783, 43826, 43867, 43906, 43942, 43991, 44038, 44083, 44126, 44167, 44206, 44243,
  44277, 44324, 44369, 44412, 44453, 44492, 44529, 44564, 44596, 44640, 44682, 44722, 44760, 44796, 44830, 44862,
  44891, 44950, 45007, 45062, 45115, 45166, 45215, 45262, 45306, 45363, 45418, 45471, 45522, 45571, 45618, 45663,
  45705, 45760, 45813, 45864, 45913, 45960, 46005, 46048, 46088, 46141, 46192, 46241, 46288, 46333, 46376, 46417,
  46455, 46506, 46555, 46602, 46647, 46690, 46731, 46770, 46806, 46855, 46902, 46947, 46990, 47031, 47070, 47107,
  47141, 47188, 47233, 47276, 47317, 47356, 47393, 47428, 47460, 47504, 47546, 47586, 47624, 47660, 47694, 47726,
  47755, 47814, 47871, 47926, 47979, 48030, 48079, 48126, 48170, 48227, 48282, 48335, 48386, 48435, 48482, 48527,
  48569, 48624, 48677, 48728, 48777, 48824, 48869, 48912, 48952, 49005, 49056, 49105, 49152, 49197, 49240, 49281,
  49319, 49370, 49419, 49466, 49511, 49554, 49595, 49634, 49670, 49719, 49766, 49811, 49854, 49895, 49934, 49971,
  50005, 50052, 50097, 50140, 50181, 50220, 50257, 50292, 50324, 50368, 50410, 50450, 50488, 50524, 50558, 50590,
  50619, 50678, 50735, 50790, 50843, 50894, 50943, 50990, 51034, 51091, 51146, 51199, 51250, 51299, 51346, 51391,
  51433, 51488, 51541, 51592, 51641, 51688, 51733, 51776, 51816, 51869, 51920, 51969, 52016, 52061, 52104, 52145,
  52183, 52234, 52283, 52330, 52375, 52418, 52459, 52498, 52534, 52583, 52630, 52675, 52718, 52759, 52798, 52835,
  52869, 52916, 52961, 53004, 53045, 53084, 53121, 53156, 53188, 53232, 53274, 53314, 53352, 53388, 53422, 53454,
  53483, 53542, 53599, 53654, 53707, 53758, 53807, 53854, 53898, 53955, 54010, 54063, 54114, 54163, 54210, 54255,
  54297, 54352, 54405, 54456, 54505, 54552, 54597, 54640, 54680, 54733, 54784, 54833, 54880, 54925, 54968, 55009,
  55047, 55098, 55147, 55194, 55239, 55282, 55323, 55362, 55398, 55447, 55494, 55539, 55582, 55623, 55662, 55699,
  55733, 55780, 55825, 55868, 55909, 55948, 55985, 56020, 56052, 56096, 56138, 56178, 56216, 56252, 56286, 56318,
  56347, 56406, 56463, 56518, 56571, 56622, 56671, 56718, 56762, 56819, 56874, 56927, 56978, 57027, 57074, 57119,
  57161, 57216, 57269, 57320, 57369, 57416, 57461, 57504, 57544, 57597, 57648, 57697, 57744, 57789, 57832, 57873,
  57911, 57962, 58011, 58058, 58103, 58146, 58187, 58226, 58262, 58311, 58358, 58403, 58446, 58487, 58526, 58563,
  58597, 58644, 58689, 58732, 58773, 58812, 58849, 58884, 58916, 58960, 59002, 59042, 59080, 59116, 59150, 59182,
  59211, 59270, 59327, 59382, 59435, 59486, 59535, 59582, 59626, 59683, 59738, 59791, 59842, 59891, 59938, 59983,
  60025, 60080, 60133, 60184, 60233, 60280, 60325, 60368, 60408, 60461, 60512, 60561, 60608, 60653, 60696, 60737,
  60775, 60826, 60875, 60922, 60967, 61010, 61051, 61090, 61126, 61175, 61222, 61267, 61310, 61351, 61390, 61427,
  61461, 61508, 61553, 61596, 61637, 61676, 61713, 61748, 61780, 61824, 61866, 61906, 61944, 61980, 62014, 62046,
  62075, 62134, 62191, 62246, 62299, 62350, 62399, 62446, 62490, 62547, 62602, 62655, 62706, 62755, 62802, 62847,
  62889, 62944, 62997, 63048, 63097, 63144, 63189, 63232, 63272, 63325, 63376, 63425, 63472, 63517, 63560, 63601,
  63639, 63690, 63739, 63786, 63831, 63874, 63915, 63954, 63990, 64039, 64086, 64131, 64174, 64215, 64254, 64291,
  64325, 64372, 64417, 64460, 64501, 64540, 64577, 64612, 64644, 64688, 64730, 64770, 64808, 64844, 64878, 64910,
  64939, 64998, 65055, 65110, 65163, 65214, 65263, 65310, 65354, 65411, 65466, 65519, 65570, 65619, 65666, 65711,
  65753, 65808, 65861, 65912, 65961, 66008, 66053, 66096, 66136, 66189, 66240, 66289, 66336, 66381, 66424, 66465,
  66503, 66554, 66603, 66650, 66695, 66738, 66779, 66818, 66854, 66903, 66950, 66995, 67038, 67079, 67118, 67155,
  67189, 67236, 67281, 67324, 67365, 67404, 67441, 67476, 67508, 67552, 67594, 67634, 67672, 67708, 67742, 67774,
  67803, 67862, 67919, 67974, 68027, 68078, 68127, 68174, 68218, 68275, 68330, 68383, 68434, 68483, 68530, 68575,
  68617, 68672, 68725, 68776, 68825, 68872, 68917, 68960, 69000, 69053, 69104, 69153, 69200, 69245, 69288, 69329,
  69367, 69418, 69467, 69514, 69559, 69602, 69643, 69682, 69718, 69767, 69814, 69859, 69902, 69943, 69982, 70019,
  70053, 70100, 70145, 70188, 70229, 70268, 70305, 70340, 70372, 70416, 70458, 70498, 70536, 70572, 70606, 70638,
  70667, 70726, 70783, 70838, 70891, 70942, 70991, 71038, 71082, 71139, 71194, 71247, 71298, 71347, 71394, 71439,
  71481, 71536, 71589, 71640, 71689, 71736, 71781, 71824, 71864, 71917, 71968, 72017, 72064, 72109, 72152, 72193,
  72231, 72282, 72331, 72378, 72423, 72466, 72507, 72546, 72582, 72631, 72678, 72723, 72766, 72807, 72846, 72883,
  72917, 72964, 73009, 73052, 73093, 73132, 73169, 73204, 73236, 73280, 73322, 73362, 73400, 73436, 73470, 73502,
  73531, 73590, 73647, 73702, 73755, 73806, 73855, 73902, 73946, 74003, 74058, 74111, 74162, 74211, 74258, 74303,
  74345, 74400, 74453, 74504, 74553, 74600, 74645, 74688, 74728, 74781, 74832, 74881, 74928, 74973, 75016, 75057,
  75095, 75146, 75195, 75242, 75287, 75330, 75371, 75410, 75446, 75495, 75542, 75587, 75630, 75671, 75710, 75747,
  75781, 75828, 75873, 75916, 75957, 75996, 76033, 76068, 76100, 76144, 76186, 76226, 76264, 76300, 76334, 76366,
  76395, 76454, 76511, 76566, 76619, 76670, 76719, 76766, 76810, 76867, 76922, 76975, 77026, 77075, 77122, 77167,
  77209, 77264, 77317, 77368, 77417, 77464, 77509, 77552, 77592, 77645, 77696, 77745, 77792, 77837, 77880, 77921,
  77959, 78010, 78059, 78106, 78151, 78194, 78235, 78274, 78310, 78359, 78406, 78451, 78494, 78535, 78574, 78611,
  78645, 78692, 78737, 78780, 78821, 78860, 78897, 78932, 78964, 79008, 79050, 79090, 79128, 79164, 79198, 79230,
  79259, 79317, 79373, 79427, 79479, 79529, 79577, 79623, 79666, 79722, 79776, 79828, 79878, 79926, 79972, 80016,
  80057, 80111, 80163, 80213, 80261, 80307, 80351, 80393, 80432, 80484, 80534, 80582, 80628, 80672, 80714, 80754,
  80791, 80841, 80889, 80935, 80979, 81021, 81061, 81099, 81134, 81182, 81228, 81272, 81314, 81354, 81392, 81428,
  81461, 81507, 81551, 81593, 81633, 81671, 81707, 81741, 81772, 81815, 81856, 81895, 81932, 81967, 82000, 82031]

/-- `tq_q_dB_dC_dD_r0` at `64 q + 16 dB + 4 dC + dD`. -/
def quadBaseTab : List Nat :=
  [82075, 82122, 82167, 82210, 82250, 82295, 82338, 82379, 82417, 82460, 82501, 82540, 82576, 82616, 82654, 82690,
  82723, 82768, 82811, 82852, 82890, 82933, 82974, 83013, 83049, 83090, 83129, 83166, 83200, 83238, 83274, 83308,
  83339, 83382, 83423, 83462, 83498, 83539, 83578, 83615, 83649, 83688, 83725, 83760, 83792, 83828, 83862, 83894,
  83923, 83963, 84001, 84037, 84070, 84108, 84144, 84178, 84209, 84245, 84279, 84311, 84340, 84373, 84404, 84433,
  84459, 84506, 84551, 84594, 84634, 84679, 84722, 84763, 84801, 84844, 84885, 84924, 84960, 85000, 85038, 85074,
  85107, 85152, 85195, 85236, 85274, 85317, 85358, 85397, 85433, 85474, 85513, 85550, 85584, 85622, 85658, 85692,
  85723, 85766, 85807, 85846, 85882, 85923, 85962, 85999, 86033, 86072, 86109, 86144, 86176, 86212, 86246, 86278,
  86307, 86347, 86385, 86421, 86454, 86492, 86528, 86562, 86593, 86629, 86663, 86695, 86724, 86757, 86788, 86817,
  86843, 86890, 86935, 86978, 87018, 87063, 87106, 87147, 87185, 87228, 87269, 87308, 87344, 87384, 87422, 87458,
  87491, 87536, 87579, 87620, 87658, 87701, 87742, 87781, 87817, 87858, 87897, 87934, 87968, 88006, 88042, 88076,
  88107, 88150, 88191, 88230, 88266, 88307, 88346, 88383, 88417, 88456, 88493, 88528, 88560, 88596, 88630, 88662,
  88691, 88731, 88769, 88805, 88838, 88876, 88912, 88946, 88977, 89013, 89047, 89079, 89108, 89141, 89172, 89201,
  89227, 89274, 89319, 89362, 89402, 89447, 89490, 89531, 89569, 89612, 89653, 89692, 89728, 89768, 89806, 89842,
  89875, 89920, 89963, 90004, 90042, 90085, 90126, 90165, 90201, 90242, 90281, 90318, 90352, 90390, 90426, 90460,
  90491, 90534, 90575, 90614, 90650, 90691, 90730, 90767, 90801, 90840, 90877, 90912, 90944, 90980, 91014, 91046,
  91075, 91115, 91153, 91189, 91222, 91260, 91296, 91330, 91361, 91397, 91431, 91463, 91492, 91525, 91556, 91585,
  91611, 91658, 91703, 91746, 91786, 91831, 91874, 91915, 91953, 91996, 92037, 92076, 92112, 92152, 92190, 92226,
  92259, 92304, 92347, 92388, 92426, 92469, 92510, 92549, 92585, 92626, 92665, 92702, 92736, 92774, 92810, 92844,
  92875, 92918, 92959, 92998, 93034, 93075, 93114, 93151, 93185, 93224, 93261, 93296, 93328, 93364, 93398, 93430,
  93459, 93499, 93537, 93573, 93606, 93644, 93680, 93714, 93745, 93781, 93815, 93847, 93876, 93909, 93940, 93969,
  93995, 94042, 94087, 94130, 94170, 94215, 94258, 94299, 94337, 94380, 94421, 94460, 94496, 94536, 94574, 94610,
  94643, 94688, 94731, 94772, 94810, 94853, 94894, 94933, 94969, 95010, 95049, 95086, 95120, 95158, 95194, 95228,
  95259, 95302, 95343, 95382, 95418, 95459, 95498, 95535, 95569, 95608, 95645, 95680, 95712, 95748, 95782, 95814,
  95843, 95883, 95921, 95957, 95990, 96028, 96064, 96098, 96129, 96165, 96199, 96231, 96260, 96293, 96324, 96353,
  96379, 96426, 96471, 96514, 96554, 96599, 96642, 96683, 96721, 96764, 96805, 96844, 96880, 96920, 96958, 96994,
  97027, 97072, 97115, 97156, 97194, 97237, 97278, 97317, 97353, 97394, 97433, 97470, 97504, 97542, 97578, 97612,
  97643, 97686, 97727, 97766, 97802, 97843, 97882, 97919, 97953, 97992, 98029, 98064, 98096, 98132, 98166, 98198,
  98227, 98267, 98305, 98341, 98374, 98412, 98448, 98482, 98513, 98549, 98583, 98615, 98644, 98677, 98708, 98737,
  98763, 98810, 98855, 98898, 98938, 98983, 99026, 99067, 99105, 99148, 99189, 99228, 99264, 99304, 99342, 99378,
  99411, 99456, 99499, 99540, 99578, 99621, 99662, 99701, 99737, 99778, 99817, 99854, 99888, 99926, 99962, 99996,
  100027, 100070, 100111, 100150, 100186, 100227, 100266, 100303, 100337, 100376, 100413, 100448, 100480, 100516, 100550, 100582,
  100611, 100651, 100689, 100725, 100758, 100796, 100832, 100866, 100897, 100933, 100967, 100999, 101028, 101061, 101092, 101121,
  101147, 101194, 101239, 101282, 101322, 101367, 101410, 101451, 101489, 101532, 101573, 101612, 101648, 101688, 101726, 101762,
  101795, 101840, 101883, 101924, 101962, 102005, 102046, 102085, 102121, 102162, 102201, 102238, 102272, 102310, 102346, 102380,
  102411, 102454, 102495, 102534, 102570, 102611, 102650, 102687, 102721, 102760, 102797, 102832, 102864, 102900, 102934, 102966,
  102995, 103035, 103073, 103109, 103142, 103180, 103216, 103250, 103281, 103317, 103351, 103383, 103412, 103445, 103476, 103505,
  103531, 103578, 103623, 103666, 103706, 103751, 103794, 103835, 103873, 103916, 103957, 103996, 104032, 104072, 104110, 104146,
  104179, 104224, 104267, 104308, 104346, 104389, 104430, 104469, 104505, 104546, 104585, 104622, 104656, 104694, 104730, 104764,
  104795, 104838, 104879, 104918, 104954, 104995, 105034, 105071, 105105, 105144, 105181, 105216, 105248, 105284, 105318, 105350,
  105379, 105419, 105457, 105493, 105526, 105564, 105600, 105634, 105665, 105701, 105735, 105767, 105796, 105829, 105860, 105889,
  105915, 105962, 106007, 106050, 106090, 106135, 106178, 106219, 106257, 106300, 106341, 106380, 106416, 106456, 106494, 106530,
  106563, 106608, 106651, 106692, 106730, 106773, 106814, 106853, 106889, 106930, 106969, 107006, 107040, 107078, 107114, 107148,
  107179, 107222, 107263, 107302, 107338, 107379, 107418, 107455, 107489, 107528, 107565, 107600, 107632, 107668, 107702, 107734,
  107763, 107803, 107841, 107877, 107910, 107948, 107984, 108018, 108049, 108085, 108119, 108151, 108180, 108213, 108244, 108273,
  108299, 108346, 108391, 108434, 108474, 108519, 108562, 108603, 108641, 108684, 108725, 108764, 108800, 108840, 108878, 108914,
  108947, 108992, 109035, 109076, 109114, 109157, 109198, 109237, 109273, 109314, 109353, 109390, 109424, 109462, 109498, 109532,
  109563, 109606, 109647, 109686, 109722, 109763, 109802, 109839, 109873, 109912, 109949, 109984, 110016, 110052, 110086, 110118,
  110147, 110187, 110225, 110261, 110294, 110332, 110368, 110402, 110433, 110469, 110503, 110535, 110564, 110597, 110628, 110657]

/-! ## Expected results -/

/-- The registers holding the step bytes `0 .. 6`: `zero, t1, t2, s0, s1, a3, s10`. -/
def posReg (d : Nat) : Reg :=
  match d with
  | 0 => .x0 | 1 => .x6 | 2 => .x7 | 3 => .x8 | 4 => .x9 | 5 => .x13 | _ => .x26

/-- The step byte as the executor reads it (`zero` is the constant 0). -/
def posE (d : Nat) : E := RegFile.init.get (posReg d)

/-- The running chain header word: `s9 + t3` (the chain index byte 5 bumped). -/
def bumpE : E := .bin .add (.reg .x25) (.reg .x28)
/-- `mv s9, s11` (the first chain of a layer) or the bump. -/
def s9E (first : Bool) : E := if first then .reg .x27 else bumpE

/-- The doubleword key `base + off + k`. -/
def kAt (rb : Reg) (off : Word) (k : Nat) : Addr := ⟨some (.reg rb), off + BitVec.ofNat 64 k⟩
/-- The initial memory word at `base + off + k`. -/
def lAt (rb : Reg) (off : Word) (k : Nat) : E := .ld (addC (.reg rb) (off + BitVec.ofNat 64 k))

/-- A chain head in a table slot: `addi a0, base, off; addi a2, a0, 48; s9 := …; sd s9, 16(a0); sd tp, 24(a0)`,
then `j tgt` (6 steps). -/
def headJ (rb : Reg) (off : Word) (first : Bool) (tgt : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12 (addC (addC (.reg rb) off) 48)).set .x25 (s9E first),
    [(kAt rb off 24, .reg .x4), (kAt rb off 16, s9E first)],
    [.valid (kAt rb off 24) 8, .valid (kAt rb off 16) 8]⟩, .c (pcOf tgt), .jump, 6, 6⟩

/-- An inline chain head (with the bump) and its first rung, step `d` (`slot` = the leaf-pk slot when `d` is
the last step), up to the rung's `ecall` (6 or 7 steps from `p`). -/
def headR (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p : Nat) : Result :=
  let n := if slot.isSome then 7 else 6
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12
      (match slot with
       | some a => .c (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) off) 48)).set .x25 bumpE,
    [(kAt rb off 16, .bin (.st .b 4) bumpE (posE d)), (kAt rb off 24, .reg .x4)],
    [.align8 (.reg rb), .valid (kAt rb off 20) 1, .valid (kAt rb off 24) 8, .valid (kAt rb off 16) 8]⟩,
    .c (pcOf (p + n)), .ecall, n, n⟩

/-- A rung at `p`: `sb POS_d, 20(a0)`, `[li a2, slot]`, up to the `ecall` (1 or 2 steps). -/
def rungR (d : Nat) (slot : Option Nat) (p : Nat) : Result :=
  let n := if slot.isSome then 2 else 1
  ⟨⟨(match slot with
      | some a => RegFile.init.set .x12 (.c (BitVec.ofNat 64 a))
      | none => RegFile.init),
    [(⟨some (.reg .x10), 16⟩, .bin (.st .b 4) (.ld (addC (.reg .x10) 16)) (posE d))],
    [.align8 (.reg .x10), .valid ⟨some (.reg .x10), 20⟩ 1]⟩, .c (pcOf (p + n)), .ecall, n, n⟩

/-- The registers after a max-digit copy (`gp`, `a4` = the two value words). -/
def copyRegs (rb : Reg) (off : Word) : RegFile :=
  (RegFile.init.set .x3 (lAt rb off 48)).set .x14 (lAt rb off 56)

/-- The copy's stores into the leaf-pk slot. -/
def copyMem (rb : Reg) (off : Word) (slot : Nat) : SymMem :=
  [(⟨none, BitVec.ofNat 64 (slot + 8)⟩, lAt rb off 56), (⟨none, BitVec.ofNat 64 slot⟩, lAt rb off 48)]

def copyObl (rb : Reg) (off : Word) : List Oblig := [.valid (kAt rb off 56) 8, .valid (kAt rb off 48) 8]

/-- A max-digit copy in a table slot (with `s9 := …`), then `j tgt` (6 steps). -/
def copyJ (rb : Reg) (off : Word) (slot : Nat) (first : Bool) (tgt : Nat) : Result :=
  ⟨⟨(copyRegs rb off).set .x25 (s9E first), copyMem rb off slot, copyObl rb off⟩, .c (pcOf tgt), .jump, 6, 6⟩

/-- An inline max-digit copy (with the bump), stopped after its 5 instructions. -/
def copyF (rb : Reg) (off : Word) (slot : Nat) (p : Nat) : Result :=
  ⟨⟨(copyRegs rb off).set .x25 bumpE, copyMem rb off slot, copyObl rb off⟩, .c (pcOf (p + 5)), .fuel, 5, 5⟩

/-- The checksum chain's copy (no `s9` update), then `j tgt` (5 steps). -/
def copyN (rb : Reg) (off : Word) (slot : Nat) (tgt : Nat) : Result :=
  ⟨⟨copyRegs rb off, copyMem rb off slot, copyObl rb off⟩, .c (pcOf tgt), .jump, 5, 5⟩

/-! ### T3X: the lower chain code's heads read the WOTS header table

(erickeigen 59cbf8ec's design, lower layers only.) During a lower layer's chain phase `x28` holds the midpoint of
the layer's 4096-byte header bank (`SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank`); a head loads its chain/digit header word with one `ld`
instead of the running `s9` bump and the first step's byte store. A table-slot max-digit copy is then `copyN`.
The top layer's chain code (`Nonbinary`) keeps `headJ` / `headR` / `copyJ` / `copyF` above. -/

/-- Byte offset of the header of chain `i`, digit `d` from the bank midpoint. -/
def hOff (i d : Nat) : Word := BitVec.ofNat 64 (64 * i + 8 * d) - 2048

def hKey (i d : Nat) : Addr := ⟨some (.reg .x28), hOff i d⟩
def hLoad (i d : Nat) : E := .ld (addC (.reg .x28) (hOff i d))

/-- A table-slot head (V1): `addi a0, base, off; addi a2, a0, 48` (or, at digit 6, `addi a2, zero, slot`);
`ld s9, hOff i d(t3); sd s9, 16(a0); sd tp, 24(a0)`, then `j tgt` (6 steps) straight onto the `ecall` of the first
rung (the header already carries the step `d`, so the rung's byte store is skipped). -/
def headJH (rb : Reg) (off : Word) (tgt i d : Nat) (slot : Option Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12
      (match slot with
       | some a => .c (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) off) 48)).set .x25 (hLoad i d),
    [(kAt rb off 24, .reg .x4), (kAt rb off 16, hLoad i d)],
    [.valid (kAt rb off 24) 8, .valid (kAt rb off 16) 8, .valid (hKey i d) 8]⟩,
    .c (pcOf tgt), .jump, 6, 6⟩

/-- A lone `ecall` at `p` (the landing word of a table-slot head). -/
def ecallR (p : Nat) : Result := ⟨SymState.init, .c (pcOf p), .ecall, 0, 0⟩

/-- The landing offset of a table-slot head at digit `d` inside rung `d`: past the byte store (and the `li a2`). -/
def landOff (d : Nat) : Nat := if d = 6 then 2 else 1

/-- An inline head loading the header with its first digit `d` already set (no byte store), up to the first
`ecall` (5 or 6 steps from `p`). -/
def headRH (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) : Result :=
  let n := if slot.isSome then 6 else 5
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12
      (match slot with
       | some a => .c (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) off) 48)).set .x25 (hLoad i d),
    [(kAt rb off 24, .reg .x4), (kAt rb off 16, hLoad i d)],
    [.valid (kAt rb off 24) 8, .valid (kAt rb off 16) 8, .valid (hKey i d) 8]⟩,
    .c (pcOf (p + n)), .ecall, n, n⟩

/-- An inline max-digit copy without the bump, stopped after its 4 instructions. -/
def copyFH (rb : Reg) (off : Word) (slot : Nat) (p : Nat) : Result :=
  ⟨⟨copyRegs rb off, copyMem rb off slot, copyObl rb off⟩, .c (pcOf (p + 4)), .fuel, 4, 4⟩

/-- `slli/srli/mv a4, w, ·`: bit `b` of `w` to bit 9. -/
def shE (w : Reg) (b : Nat) : E :=
  if b < 9 then .bin .sll (.reg w) (.c (BitVec.ofNat 64 (9 - b)))
  else if 9 < b then .bin .srl (.reg w) (.c (BitVec.ofNat 64 (b - 9)))
  else .reg w

/-- The dispatch into a table slot: `a4 = (shE w b &&& mreg) + a5`, `jalr zero, imm(a4)` (4 steps). -/
def xJ (w : Reg) (b : Nat) (mreg : Reg) (imm : Word) : Result :=
  ⟨⟨RegFile.init.set .x14 (.bin .add (.bin .and (shE w b) (.reg mreg)) (.reg .x15)), [], []⟩,
    .bin .and (.bin .add (.bin .add (.bin .and (shE w b) (.reg mreg)) (.reg .x15)) (.c imm)) (.c (~~~1#64)),
    .jump, (if b = 9 then 3 else 4), (if b = 9 then 3 else 4)⟩

/-- After triple 13: `slli a4, t4, 5; sub a4, a5, a4; jalr zero, -1824(a4)` into `ctab` (3 steps; `t4 = 7 - ck`). -/
def ctabX : Result :=
  ⟨⟨RegFile.init.set .x14 (.bin .sub (.reg .x15) (.bin .sll (.reg .x29) (.c 5))), [], []⟩,
    .bin .and (.bin .add (.bin .sub (.reg .x15) (.bin .sll (.reg .x29) (.c 5))) (.c (-1824))) (.c (~~~1#64)),
    .jump, 3, 3⟩

/-- After quad 11: `srli a4, a7, 29; andi a4, a4, 0x60; add a4, a4, a5; jalr zero, -1760(a4)` into `q48tab`. -/
def q48X : Result :=
  ⟨⟨RegFile.init.set .x14 (.bin .add (.bin .and (.bin .srl (.reg .x17) (.c 29)) (.c 0x60)) (.reg .x15)), [], []⟩,
    .bin .and (.bin .add (.bin .add (.bin .and (.bin .srl (.reg .x17) (.c 29)) (.c 0x60)) (.reg .x15)) (.c (-1760)))
      (.c (~~~1#64)), .jump, 4, 4⟩

/-- `q48_done`: `lui a5, 0x6e; srli a4, a7, 27; and a4, a4, sp; add a4, a4, a5; jalr zero, -1408(a4)` into the
lower table's slot 11 (5 steps). -/
def q48D : Result :=
  ⟨⟨(RegFile.init.set .x15 (.c 0x6e000)).set .x14
      (.bin .add (.bin .and (.bin .srl (.reg .x17) (.c 27)) (.reg .x2)) (.c 0x6e000)), [], []⟩,
    .bin .and (.bin .add (.bin .and (.bin .srl (.reg .x17) (.c 27)) (.reg .x2)) (.c (0x6e000 - 1408)))
      (.c (~~~1#64)), .jump, 5, 5⟩

/-- `jr ra` (1 step). -/
def retR : Result := ⟨⟨RegFile.init, [], []⟩, .bin .and (.reg .x1) (.c (~~~1#64)), .jump, 1, 1⟩

/-! ## The lower chain code (triples, checksum) -/

/-- Chain block `i` of a lower layer relative to `s6 = x22`: `64 (42 - i) - 1024`. -/
def offL (i : Nat) : Word := BitVec.ofNat 64 (64 * (42 - i)) - BitVec.ofNat 64 1024
/-- The lower leaf-pk slot of chain `i` (`0x300` for chain 0, `0x310 + 16 i` else). -/
def slotL (i : Nat) : Nat := if i = 0 then 768 else 784 + 16 * i

/-- The slot argument of a head at digit `d` of chain `i`. -/
def hSlot (i d : Nat) : Option Nat := if d = 6 then some (slotL i) else none


def triBase (t dB dC : Nat) : Nat := triBaseTab.getD (64 * t + 8 * dB + dC) 0
/-- Words of an inline chain at digit `d` (width 3): the copy 4, else the head 4 + rungs `2 (7 - d) + 1` (T3X:
the header `ld` replaces the bump and the first byte store). -/
def partLen (d : Nat) : Nat := if d = 7 then 4 else 19 - 2 * d
def pcB (t dB dC : Nat) : Nat := triBase t dB dC + 15
def pcC (t dB dC : Nat) : Nat := pcB t dB dC + partLen dB
def pcX (t dB dC : Nat) : Nat := pcC t dB dC + partLen dC
/-- Slot `t` of row `k` of `ttab`. -/
def entW (t k : Nat) : Nat := ttabIdx + 128 * k + 8 * t

/-- The rungs `d0 .. 6` (width 3) starting at `p`, the last one into `slot`. -/
def rungsOK (d0 slot p : Nat) : Bool :=
  (List.range' d0 (7 - d0)).all fun m =>
    rOK (vrun (p + 2 * (m - d0)) 3) (rungR m (if m = 6 then some slot else none) (p + 2 * (m - d0)))

/-- The inline code of lower chain `i` at digit `d`, from `p`. -/
def partOK (i d p : Nat) : Bool :=
  if d = 7 then rOK (vrun p 4) (copyFH .x22 (offL i) (slotL i) p)
  else rOK (vrun p 8) (headRH .x22 (offL i) d (if d = 6 then some (slotL i) else none) p i) &&
    rungsOK (d + 1) (slotL i) (p + 6)

/-- Slot `(t, k)` of `ttab`: chain `3t`'s head into rung `dA` of the shared block, or its copy. -/
def entCheck (t k : Nat) : Bool :=
  if k % 8 = 7 then
    rOK (vrun (entW t k) 7) (copyN .x22 (offL (3 * t)) (slotL (3 * t)) (pcB t (k / 8 % 8) (k / 64)))
  else rOK (vrun (entW t k) 7) (headJH .x22 (offL (3 * t))
      (triBase t (k / 8 % 8) (k / 64) + 2 * (k % 8) + landOff (k % 8)) (3 * t) (k % 8) (hSlot (3 * t) (k % 8))) &&
    rOK (vrun (triBase t (k / 8 % 8) (k / 64) + 2 * (k % 8) + landOff (k % 8)) 1)
      (ecallR (triBase t (k / 8 % 8) (k / 64) + 2 * (k % 8) + landOff (k % 8)))

/-- After chain `C` of triple `t`: the dispatch of triple `t + 1` or (`t = 13`) of the checksum chain. -/
def xOK (t dB dC : Nat) : Bool :=
  if t = 13 then rOK (vrun (pcX t dB dC) 4) ctabX
  else rOK (vrun (pcX t dB dC) 5)
    (xJ (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7)) .x2
      (BitVec.ofNat 64 (32 * (t + 1)) - BitVec.ofNat 64 1760))

/-- The shared block `tc_t_dB_dC`: `A`'s rungs, `B`, `C`, the next dispatch. -/
def blkCheck (t dB dC : Nat) : Bool :=
  rungsOK 0 (slotL (3 * t)) (triBase t dB dC) && partOK (3 * t + 1) dB (pcB t dB dC) &&
    partOK (3 * t + 2) dC (pcC t dB dC) && xOK t dB dC

/-- Everything of triple `t`: table rows `lo .. lo + n` and the code blocks `lo / 8 .. (lo + n) / 8`. -/
def triCheck (t lo n : Nat) : Bool :=
  ((List.range' lo n).all fun k => entCheck t k) &&
    ((List.range' (lo / 8) (n / 8)).all fun q => blkCheck t (q / 8) (q % 8))

/-- The checksum chain: `ctab` (digit `c < 7` head, `c = 7` copy, slot 8 `jr ra`), its rungs, `ck_done`. -/
def ckCheck : Bool :=
  ((List.range 7).all fun c => rOK (vrun (ctabIdx + 8 * c) 7)
      (headJH .x22 (offL 42) (ckR0 + 2 * c + landOff c) 42 c (hSlot 42 c)) &&
    rOK (vrun (ckR0 + 2 * c + landOff c) 1) (ecallR (ckR0 + 2 * c + landOff c))) &&
    rOK (vrun (ctabIdx + 56) 6) (copyN .x22 (offL 42) (slotL 42) ckDone) &&
    rOK (vrun (ctabIdx + 64) 2) retR && rungsOK 0 (slotL 42) ckR0 && rOK (vrun ckDone 2) retR

/-! ## The top chain code (quads, chain 48) -/

/-- Chain block `i < 49` of the top relative to `s3 = x19`: `64 (57 - i) - 1664`. -/
def offT (i : Nat) : Word := BitVec.ofNat 64 (64 * (57 - i)) - BitVec.ofNat 64 1664
/-- The top leaf-pk slot of chain `i` (`0x200` for chain 0, `0x210 + 16 i` else). -/
def slotT (i : Nat) : Nat := if i = 0 then 512 else 528 + 16 * i

def quadBase (q dB dC dD : Nat) : Nat := quadBaseTab.getD (64 * q + 16 * dB + 4 * dC + dD) 0
/-- Words of an inline chain at digit `d` (width 2): the copy 5, else the head 5 + rungs `2 (3 - d) + 1`. -/
def partLen2 (d : Nat) : Nat := if d = 3 then 5 else 12 - 2 * d
def qpcB (q dB dC dD : Nat) : Nat := quadBase q dB dC dD + 7
def qpcC (q dB dC dD : Nat) : Nat := qpcB q dB dC dD + partLen2 dB
def qpcD (q dB dC dD : Nat) : Nat := qpcC q dB dC dD + partLen2 dC
def qpcX (q dB dC dD : Nat) : Nat := qpcD q dB dC dD + partLen2 dD
/-- Slot `q` of row `k` of `qtab`. -/
def qentW (q k : Nat) : Nat := qtabIdx + 128 * k + 8 * q

/-- The rungs `d0 .. 2` (width 2) starting at `p`, the last one into `slot`. -/
def rungsOK2 (d0 slot p : Nat) : Bool :=
  (List.range' d0 (3 - d0)).all fun m =>
    rOK (vrun (p + 2 * (m - d0)) 3) (rungR m (if m = 2 then some slot else none) (p + 2 * (m - d0)))

/-- The inline code of top chain `i < 49` at digit `d`, from `p`. -/
def partOK2 (i d p : Nat) : Bool :=
  if d = 3 then rOK (vrun p 5) (copyF .x19 (offT i) (slotT i) p)
  else rOK (vrun p 8) (headR .x19 (offT i) d (if d = 2 then some (slotT i) else none) p) &&
    rungsOK2 (d + 1) (slotT i) (p + 7)

/-- Slot `(q, k)` of `qtab`: chain `4q`'s head into rung `dA` of the shared block, or its copy. -/
def qentCheck (q k : Nat) : Bool :=
  if k % 4 = 3 then
    rOK (vrun (qentW q k) 7)
      (copyJ .x19 (offT (4 * q)) (slotT (4 * q)) (q == 0) (qpcB q (k / 4 % 4) (k / 16 % 4) (k / 64)))
  else rOK (vrun (qentW q k) 7)
    (headJ .x19 (offT (4 * q)) (q == 0) (quadBase q (k / 4 % 4) (k / 16 % 4) (k / 64) + 2 * (k % 4)))

/-- After chain `D` of quad `q`: the dispatch of quad `q + 1` or (`q = 11`) of chain 48. -/
def qxOK (q dB dC dD : Nat) : Bool :=
  if q = 11 then rOK (vrun (qpcX q dB dC dD) 5) q48X
  else rOK (vrun (qpcX q dB dC dD) 5)
    (xJ (if q + 1 < 8 then .x16 else .x17) (if q + 1 < 8 then 8 * (q + 1) else 2 + 8 * (q + 1 - 8)) .x24
      (BitVec.ofNat 64 (32 * (q + 1)) - BitVec.ofNat 64 1632))

/-- The shared block `tq_q_dB_dC_dD`: `A`'s rungs, `B`, `C`, `D`, the next dispatch. -/
def qblkCheck (q dB dC dD : Nat) : Bool :=
  rungsOK2 0 (slotT (4 * q)) (quadBase q dB dC dD) && partOK2 (4 * q + 1) dB (qpcB q dB dC dD) &&
    partOK2 (4 * q + 2) dC (qpcC q dB dC dD) && partOK2 (4 * q + 3) dD (qpcD q dB dC dD) && qxOK q dB dC dD

/-- Everything of quad `q`: table rows `lo .. lo + n` and the code blocks `lo / 4 .. (lo + n) / 4`. -/
def quadCheck (q lo n : Nat) : Bool :=
  ((List.range' lo n).all fun k => qentCheck q k) &&
    ((List.range' (lo / 4) (n / 4)).all fun x => qblkCheck q (x / 16) (x / 4 % 4) (x % 4))

/-- Chain 48 of the top: `q48tab` (digit `< 3` head, 3 copy), its rungs, `q48_done`. -/
def q48Check : Bool :=
  ((List.range 3).all fun d => rOK (vrun (q48tabIdx + 8 * d) 7) (headJ .x19 (offT 48) false (q48R0 + 2 * d))) &&
    rOK (vrun (q48tabIdx + 24) 7) (copyJ .x19 (offT 48) (slotT 48) false q48Done) &&
    rungsOK2 0 (slotT 48) q48R0 && rOK (vrun q48Done 6) q48D

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart10

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart11

/-! Kernel check of the lower chain code, triples 0 and 1: their `ttab` slots and shared blocks, in
halves (the import chain serializes the check files to bound parallel build memory). -/

namespace SigGolfCandidate.T3M.CanonicalPort

set_option maxRecDepth 100000

theorem triCheck_0_0 : triCheck 0 0 256 = true := by decide +kernel
theorem triCheck_0_1 : triCheck 0 256 256 = true := by decide +kernel
theorem triCheck_1_0 : triCheck 1 0 256 = true := by decide +kernel
theorem triCheck_1_1 : triCheck 1 256 256 = true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart11

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart12

/-! Kernel check of the lower chain code, triples 2 and 3: their `ttab` slots and shared blocks, in
halves (the import chain serializes the check files to bound parallel build memory). -/

namespace SigGolfCandidate.T3M.CanonicalPort

set_option maxRecDepth 100000

theorem triCheck_2_0 : triCheck 2 0 256 = true := by decide +kernel
theorem triCheck_2_1 : triCheck 2 256 256 = true := by decide +kernel
theorem triCheck_3_0 : triCheck 3 0 256 = true := by decide +kernel
theorem triCheck_3_1 : triCheck 3 256 256 = true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart12

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart13

/-! Kernel check of the lower chain code, triples 4 and 5: their `ttab` slots and shared blocks, in
halves (the import chain serializes the check files to bound parallel build memory). -/

namespace SigGolfCandidate.T3M.CanonicalPort

set_option maxRecDepth 100000

theorem triCheck_4_0 : triCheck 4 0 256 = true := by decide +kernel
theorem triCheck_4_1 : triCheck 4 256 256 = true := by decide +kernel
theorem triCheck_5_0 : triCheck 5 0 256 = true := by decide +kernel
theorem triCheck_5_1 : triCheck 5 256 256 = true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart13

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart14

/-! Kernel check of the lower chain code, triples 6 and 7: their `ttab` slots and shared blocks, in
halves (the import chain serializes the check files to bound parallel build memory). -/

namespace SigGolfCandidate.T3M.CanonicalPort

set_option maxRecDepth 100000

theorem triCheck_6_0 : triCheck 6 0 256 = true := by decide +kernel
theorem triCheck_6_1 : triCheck 6 256 256 = true := by decide +kernel
theorem triCheck_7_0 : triCheck 7 0 256 = true := by decide +kernel
theorem triCheck_7_1 : triCheck 7 256 256 = true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart14

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart15

/-! Kernel check of the lower chain code, triples 8 and 9: their `ttab` slots and shared blocks, in
halves (the import chain serializes the check files to bound parallel build memory). -/

namespace SigGolfCandidate.T3M.CanonicalPort

set_option maxRecDepth 100000

theorem triCheck_8_0 : triCheck 8 0 256 = true := by decide +kernel
theorem triCheck_8_1 : triCheck 8 256 256 = true := by decide +kernel
theorem triCheck_9_0 : triCheck 9 0 256 = true := by decide +kernel
theorem triCheck_9_1 : triCheck 9 256 256 = true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart15

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart16

/-! Kernel check of the lower chain code, triples 10 and 11: their `ttab` slots and shared blocks, in
halves (the import chain serializes the check files to bound parallel build memory). -/

namespace SigGolfCandidate.T3M.CanonicalPort

set_option maxRecDepth 100000

theorem triCheck_10_0 : triCheck 10 0 256 = true := by decide +kernel
theorem triCheck_10_1 : triCheck 10 256 256 = true := by decide +kernel
theorem triCheck_11_0 : triCheck 11 0 256 = true := by decide +kernel
theorem triCheck_11_1 : triCheck 11 256 256 = true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart16

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart17

/-! Kernel check of the lower chain code, triples 12 and 13: their `ttab` slots and shared blocks, in
halves (the import chain serializes the check files to bound parallel build memory). -/

namespace SigGolfCandidate.T3M.CanonicalPort

set_option maxRecDepth 100000

theorem triCheck_12_0 : triCheck 12 0 256 = true := by decide +kernel
theorem triCheck_12_1 : triCheck 12 256 256 = true := by decide +kernel
theorem triCheck_13_0 : triCheck 13 0 256 = true := by decide +kernel
theorem triCheck_13_1 : triCheck 13 256 256 = true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart17

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart18

/-! All chain families of the verify image: every `ttab`/`qtab` slot and every shared block. -/

namespace SigGolfCandidate.T3M.CanonicalPort

theorem triCheck_at (t : Nat) (ht : t < 14) : triCheck t 0 256 = true ∧ triCheck t 256 256 = true := by
  interval_cases t
  exacts [⟨triCheck_0_0, triCheck_0_1⟩,
    ⟨triCheck_1_0, triCheck_1_1⟩,
    ⟨triCheck_2_0, triCheck_2_1⟩,
    ⟨triCheck_3_0, triCheck_3_1⟩,
    ⟨triCheck_4_0, triCheck_4_1⟩,
    ⟨triCheck_5_0, triCheck_5_1⟩,
    ⟨triCheck_6_0, triCheck_6_1⟩,
    ⟨triCheck_7_0, triCheck_7_1⟩,
    ⟨triCheck_8_0, triCheck_8_1⟩,
    ⟨triCheck_9_0, triCheck_9_1⟩,
    ⟨triCheck_10_0, triCheck_10_1⟩,
    ⟨triCheck_11_0, triCheck_11_1⟩,
    ⟨triCheck_12_0, triCheck_12_1⟩,
    ⟨triCheck_13_0, triCheck_13_1⟩]

theorem entCheck_at (t k : Nat) (ht : t < 14) (hk : k < 512) : entCheck t k = true := by
  obtain ⟨h0, h1⟩ := triCheck_at t ht
  simp only [triCheck, Bool.and_eq_true] at h0 h1
  by_cases h : k < 256
  · exact List.all_eq_true.mp h0.1 k (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  · exact List.all_eq_true.mp h1.1 k (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

theorem blkCheck_at (t dB dC : Nat) (ht : t < 14) (hB : dB < 8) (hC : dC < 8) :
    blkCheck t dB dC = true := by
  obtain ⟨h0, h1⟩ := triCheck_at t ht
  simp only [triCheck, Bool.and_eq_true] at h0 h1
  have e1 : (8 * dB + dC) / 8 = dB := by omega
  have e2 : (8 * dB + dC) % 8 = dC := by omega
  by_cases h : 8 * dB + dC < 32
  · have := List.all_eq_true.mp h0.2 (8 * dB + dC) (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    rwa [e1, e2] at this
  · have := List.all_eq_true.mp h1.2 (8 * dB + dC) (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    rwa [e1, e2] at this

theorem ckCheck_ok : ckCheck = true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart18

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart19

/-! # V1 chains: semantics of the chain code (`Steps` level)

From a state at a chain's code (`ChainIn`), the machine performs the chain's steps: the head writes the header
words into the block's header slot (`+16`, `+24`), each rung writes the step byte (`+20`) and stops at the HASH
`ecall` (`PreHash`: the input is `chainInputP` with the block's two pads and the current value read from the
block); a step's answer is written in place (`+48`) or, for the last step, into the leaf-pk slot; a max digit
copies the witness value into the slot. Everything is stated relative to the state `s0` at the start of the
chain phase: registers outside `chainRegs` and memory outside the area already written are those of `s0`.

The witness is the organizer's `WBytes`; `OrigW w s A` says that the doubleword at the machine address `A`
(`0x800 ≤ A`, 8-aligned) still holds the witness bytes `A - 0x800 .. A - 0x800 + 8`. -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

/-- The verify image. -/
abbrev vimage : Image := CanonicalNative.fixture

/-! ## Checked pieces -/

theorem piece_steps {p f : Nat} {r : Result} (h : vrun p f = some r) (hp : p < 209920) (s : MachineState)
    (hpc : s.pc = pcOf p) (ho : ∀ o ∈ r.st.obl, o.holds s) :
    Steps vimage s r.steps r.cycles (r.toState s) :=
  symRun_sound h (lcodeAt p (by omega)) s hpc ((Oblig.all_iff _ _).mpr ho)

theorem piece_ecall {p f : Nat} {r : Result} (h : vrun p f = some r) (hp : p < 209920) (s : MachineState)
    (ho : ∀ o ∈ r.st.obl, o.holds s) (hst : r.stop = .ecall) :
    fetch vimage (r.toState s) = some (.base .ECALL) :=
  symRun_ecall h (lcodeAt p (by omega)) s ((Oblig.all_iff _ _).mpr ho) hst

/-! ## Word arithmetic -/

theorem ofNat_add_off (x a b k : Nat) (h : b ≤ x + a) (h2 : x + a + k < 2 ^ 64) :
    BitVec.ofNat 64 x + (BitVec.ofNat 64 a - BitVec.ofNat 64 b + BitVec.ofNat 64 k) =
      BitVec.ofNat 64 (x + a - b + k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem ofNat_add_off0 (x a b : Nat) (h : b ≤ x + a) (h2 : x + a < 2 ^ 64) :
    BitVec.ofNat 64 x + (BitVec.ofNat 64 a - BitVec.ofNat 64 b) = BitVec.ofNat 64 (x + a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem ofNat_add_off48 (x a b : Nat) (h : b ≤ x + a) (h2 : x + a + 48 < 2 ^ 64) :
    BitVec.ofNat 64 x + (BitVec.ofNat 64 a - BitVec.ofNat 64 b) + 48 = BitVec.ofNat 64 (x + a - b + 48) := by
  rw [ofNat_add_off0 x a b h (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (48 : Word).toNat = 48 from rfl]
  omega

theorem valid_ofNat (A w : Nat) (hA : A + w ≤ 2 ^ 24) (ha : A % w = 0) :
    accessValid (BitVec.ofNat 64 A) w = true := by
  rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by simp only [MEMORY_BYTES]; omega, ha⟩

/-! ## The witness in memory -/

/-- The doubleword at machine address `A` holds the witness bytes `A - 0x800 .. + 8`. -/
def OrigW (w : WBytes) (s : MachineState) (A : Nat) : Prop :=
  s.getMem (BitVec.ofNat 64 A) = w.extractLsb' (8 * (A - 0x800)) 64

theorem wdig_lo (w : WBytes) (off : Nat) : (wdig w off).extractLsb' 0 64 = w.extractLsb' (8 * off) 64 := by
  unfold wdig
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.pow_zero, Nat.div_one, Nat.mod_mod_of_dvd _ (by norm_num)]

theorem wdig_hi (w : WBytes) (off : Nat) :
    (wdig w off).extractLsb' 64 64 = w.extractLsb' (8 * (off + 8)) 64 := by
  unfold wdig
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 8 * (off + 8) = 8 * off + 64 by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize w.toNat / 2 ^ (8 * off) = X
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod]

/-- Two original doublewords hold the witness digest at `A - 0x800`. -/
theorem DigAt_origW {w : WBytes} {s : MachineState} {A : Nat} (h0 : OrigW w s A) (h1 : OrigW w s (A + 8))
    (hA : 0x800 ≤ A) : DigAt s A (wdig w (A - 0x800)) := by
  refine ⟨?_, ?_⟩
  · rw [h0, wdig_lo]
  · rw [h1, wdig_hi, show A + 8 - 0x800 = A - 0x800 + 8 by omega]

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

/-! ## Registers kept by a piece -/

/-- The registers written by the chain code. -/
def chainRegs : List Reg := [.x10, .x12, .x25, .x3, .x14]

/-- `r` leaves the registers outside `ws` unchanged. -/
def Keeps (r : Result) (ws : List Reg) : Prop := ∀ x, x ∉ ws → r.st.regs.get x = RegFile.init.get x

theorem Keeps.reg {r : Result} {ws : List Reg} (h : Keeps r ws) (s : MachineState) {x : Reg} (hx : x ∉ ws) :
    (r.toState s).getReg x = s.getReg x := by
  rw [Result.toState_getReg, h x hx, RegFile.init_get_eval]

theorem ne_of_not_mem {x r : Reg} {ws : List Reg} (hx : x ∉ ws) (hr : r ∈ ws) : x ≠ r := by
  rintro rfl; exact hx hr

theorem headJ_keeps (rb : Reg) (off : Word) (first : Bool) (tgt : Nat) :
    Keeps (headJ rb off first tgt) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headJ]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem headR_keeps (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p : Nat) :
    Keeps (headR rb off d slot p) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headR]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem rungR_keeps (d : Nat) (slot : Option Nat) (p : Nat) : Keeps (rungR d slot p) [.x12] := by
  intro x hx
  simp only [rungR]
  split
  · rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
  · rfl

theorem copyJ_keeps (rb : Reg) (off : Word) (slot : Nat) (first : Bool) (tgt : Nat) :
    Keeps (copyJ rb off slot first tgt) [.x3, .x14, .x25] := by
  intro x hx
  simp only [copyJ, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem copyF_keeps (rb : Reg) (off : Word) (slot p : Nat) : Keeps (copyF rb off slot p) [.x3, .x14, .x25] := by
  intro x hx
  simp only [copyF, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem copyN_keeps (rb : Reg) (off : Word) (slot tgt : Nat) : Keeps (copyN rb off slot tgt) [.x3, .x14] := by
  intro x hx
  simp only [copyN, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

/-! T3X: the lower chain code's header-table pieces. -/

theorem headJH_keeps (rb : Reg) (off : Word) (tgt i d : Nat) (slot : Option Nat) :
    Keeps (headJH rb off tgt i d slot) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headJH]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem headRH_keeps (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) :
    Keeps (headRH rb off d slot p i) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headRH]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem copyFH_keeps (rb : Reg) (off : Word) (slot p : Nat) : Keeps (copyFH rb off slot p) [.x3, .x14] := by
  intro x hx
  simp only [copyFH, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem xJ_keeps (w : Reg) (b : Nat) (mreg : Reg) (imm : Word) : Keeps (xJ w b mreg imm) [.x14] := by
  intro x hx
  simp only [xJ]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem ctabX_keeps : Keeps ctabX [.x14] := by
  intro x hx
  simp only [ctabX]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem retR_keeps : Keeps retR [] := fun _ _ => rfl

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

/-! ## The lower chain code: context and invariants -/

/-- A run of the lower chain code (`ttab`, `tc_*`, `ctab`, `ck_*`) over the code chains `i0 ≤ i ≤ 42`: the
witness and the layer of the chain blocks, the Core chain index `i + koff` of code chain `i` (`koff = 16` for the
top layer's radix-8 chains 49..57, which run as the code chains 33..41), the header fields, `s6`, the digit words
`a6`, `a7`, the checksum digit `t4` (8 = no checksum chain), and the return pc (the transition copy's leaf-pk
block). -/
structure LCtx where
  w : WBytes
  lay : Layer
  i0 : Nat
  koff : Nat
  tree : Nat
  leaf : Nat
  S6 : Nat
  d0 : Word
  d1 : Word
  ck : Nat
  ret : Nat

namespace LCtx

/-- The machine address of code chain `i`'s block (`s6 + 64 (42 - i) - 1024`; written `s6 - 1024 + …`: `omega`
fails with a recursion-depth error on `x + 64 * (a - b) - k`). -/
def blk (c : LCtx) (i : Nat) : Nat := c.S6 - 1024 + 64 * (42 - i)
/-- The digit of code chain `i`: the radix-8 digits of `a6` (`i < 21`) and `a7` (`21 ≤ i < 42`), and `t4`. -/
def dig (c : LCtx) (i : Nat) : Nat :=
  if i < 21 then c.d0.toNat / 8 ^ i % 8 else if i < 42 then c.d1.toNat / 8 ^ (i - 21) % 8 else c.ck
/-- Header word 0 of code chain `i` with step byte 0: tag 1, the layer, position `256 (i + koff)`. -/
def w0 (c : LCtx) (i : Nat) : Nat := 0x101 + 65536 * c.lay.val + 2 ^ 40 * (i + c.koff)
/-- Header word 1: `tree | leaf << 32`. -/
def w1 (c : LCtx) : Nat := hdr1 c.tree c.leaf
/-- The two pads of code chain `i`'s block. -/
def pad0 (c : LCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800)
def pad1 (c : LCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800 + 32)
/-- The witness value of code chain `i`. -/
def val (c : LCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800 + 48)

/-- Well-formedness. -/
def ok (c : LCtx) : Prop :=
  c.tree < 2 ^ 32 ∧ c.leaf < 2 ^ 32 ∧ c.koff ≤ 16 ∧ c.S6 % 8 = 0 ∧ 0x800 + 11288 + 1024 ≤ c.S6 ∧
    c.S6 + 2688 + 80 ≤ 0x7000 ∧ c.ck ≤ 8 ∧ c.ret < 209920 ∧ c.i0 ≤ 42

/-- The registers the lower chain code reads. -/
def known (c : LCtx) : List (Reg × Word) :=
  [(.x5, 0), (.x11, 64), (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6),
   (.x28, BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank c.lay.val c.koff)), (.x2, 0x3fe00), (.x15, 0x6e000),
   (.x22, BitVec.ofNat 64 c.S6),
   (.x4, BitVec.ofNat 64 c.w1), (.x27, BitVec.ofNat 64 (0x101 + 65536 * c.lay.val)),
   (.x16, c.d0), (.x17, c.d1), (.x29, 7#64 - BitVec.ofNat 64 c.ck), (.x1, pcOf c.ret)]

/-- The table row of triple `t`. -/
def kOf (c : LCtx) (t : Nat) : Nat := c.dig (3 * t) + 8 * c.dig (3 * t + 1) + 64 * c.dig (3 * t + 2)
/-- The shared block of code chain `i`'s triple, and its `B`, `C`, dispatch parts. -/
def tb (c : LCtx) (i : Nat) : Nat := triBase (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
def tB (c : LCtx) (i : Nat) : Nat := pcB (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
def tC (c : LCtx) (i : Nat) : Nat := pcC (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
def tX (c : LCtx) (i : Nat) : Nat := pcX (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))

/-- Where code chain `i`'s code starts: `A` in its table slot, `B`, `C` in the shared block, chain 42 in `ctab`. -/
def startPc (c : LCtx) (i : Nat) : Nat :=
  if i = 42 then ctabIdx + 8 * c.ck
  else if i % 3 = 0 then entW (i / 3) (c.kOf (i / 3)) else if i % 3 = 1 then c.tB i else c.tC i
/-- The first word of rung `m` (step `m`) of code chain `i`. -/
def rungPc (c : LCtx) (i m : Nat) : Nat :=
  if i = 42 then ckR0 + 2 * m
  else if i % 3 = 0 then c.tb i + 2 * m
  else (if i % 3 = 1 then c.tB i else c.tC i) + 4 + 2 * (m - c.dig i)
/-- Where code chain `i`'s code ends: the next chain's code, the dispatch after `C`, `ck_done`. -/
def endPc (c : LCtx) (i : Nat) : Nat :=
  if i = 42 then ckDone else if i % 3 = 0 then c.tB i else if i % 3 = 1 then c.tC i else c.tX i

/-- The memory written by the code chains `i0 .. i - 1`: the leaf-pk area from chain `i0`'s slot on (the top's
quad slots below it survive) and their blocks (with the spill of chain `i0`). -/
def Wr (c : LCtx) (i : Nat) (A : Nat) : Prop :=
  (slotL c.i0 ≤ A ∧ A < 0x5D0) ∨ (c.S6 - 1024 + 64 * (43 - i) ≤ A ∧ A < c.blk c.i0 + 80)
/-- ... and chain `i`'s header slot and value slot (with its spill). -/
def WrIn (c : LCtx) (i : Nat) (A : Nat) : Prop :=
  c.Wr i A ∨ (c.blk i + 16 ≤ A ∧ A < c.blk i + 32) ∨ (c.blk i + 48 ≤ A ∧ A < c.blk i + 80)

/-- The phase's chain blocks hold the witness at the start `s0`. -/
def Orig0 (c : LCtx) (s0 : MachineState) : Prop :=
  ∀ i, c.i0 ≤ i → i ≤ 42 → ∀ k < 8, OrigW c.w s0 (c.blk i + 8 * k)

/-- Common to all invariants: registers outside `chainRegs` as at `s0`, memory outside `W` as at `s0`, the ends
`acc` of the finished chains in their leaf-pk slots. -/
def Base (c : LCtx) (s0 : MachineState) (W : Nat → Prop) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → s.getReg x = s0.getReg x) ∧ Frame s0 s W ∧
    (∀ j < acc.length, DigAt s (slotL (c.i0 + j)) (acc.getD j 0))

/-- Before code chain `i`'s code (T3X: the header table is intact at the phase start `s0`; no running `x25`). -/
def ChainIn (c : LCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr i) acc s ∧ acc.length = i - c.i0 ∧ SigGolfCandidate.T3M.CanonicalPort.Verify.DataOK s0 ∧
    s.pc = pcOf (c.startPc i)

/-- The header slot of code chain `i`: word 0 with the layer and the chain (the step byte is free), word 1. -/
def HdrOk (c : LCtx) (i : Nat) (s : MachineState) : Prop :=
  (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat % 2 ^ 32 = 0x101 + 65536 * c.lay.val ∧
    (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat / 2 ^ 40 = i + c.koff ∧
    s.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1

/-- At rung `m` of code chain `i`, the value `v` in the block's value slot. -/
def StepInv (c : LCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (s : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc s ∧ acc.length = i - c.i0 ∧ SigGolfCandidate.T3M.CanonicalPort.Verify.DataOK s0 ∧
    c.HdrOk i s ∧ DigAt s (c.blk i + 48) v ∧ s.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    s.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48) ∧ s.pc = pcOf (c.rungPc i m)

/-- Just before the `ecall` of step `m` of code chain `i` (value `v`; the header with step `m` written; `a2` =
the value slot, or the leaf-pk slot for the last step). -/
def PreHash (c : LCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (t : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc t ∧ acc.length = i - c.i0 ∧ SigGolfCandidate.T3M.CanonicalPort.Verify.DataOK s0 ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 2 ^ 32 * m) ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1 ∧ DigAt t (c.blk i + 48) v ∧
    t.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    t.getReg .x12 = BitVec.ofNat 64 (if m = 6 then slotL i else c.blk i + 48) ∧
    t.pc = pcOf (c.rungPc i m + (if m = 6 then 2 else 1)) ∧ fetch vimage t = some (.base .ECALL)

/-- After code chain `i` (its end is the last element of `acc`). -/
def EndInv (c : LCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (i + 1)) acc s ∧ acc.length = i + 1 - c.i0 ∧
    SigGolfCandidate.T3M.CanonicalPort.Verify.DataOK s0 ∧ s.pc = pcOf (c.endPc i)

end LCtx

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

/-! ## Memory of a piece -/

theorem memEval_one (s : MachineState) (k : Addr) (v : E) (a A : Nat) (h : k.eval s = BitVec.ofNat 64 a)
    (ha : a < 2 ^ 64) (hA : A < 2 ^ 64) :
    memEval s [(k, v)] (BitVec.ofNat 64 A) = if A = a then v.eval s else s.getMem (BitVec.ofNat 64 A) := by
  rw [memEval_cons, h, memEval_nil]
  by_cases e : A = a
  · subst e; simp
  · rw [if_neg (fun h' => e ((ofNat_inj hA ha).mp h')), if_neg e]

theorem memEval_two (s : MachineState) (k1 k2 : Addr) (v1 v2 : E) (a1 a2 A : Nat)
    (h1 : k1.eval s = BitVec.ofNat 64 a1) (h2 : k2.eval s = BitVec.ofNat 64 a2) (ha1 : a1 < 2 ^ 64)
    (ha2 : a2 < 2 ^ 64) (hA : A < 2 ^ 64) :
    memEval s [(k1, v1), (k2, v2)] (BitVec.ofNat 64 A) =
      if A = a1 then v1.eval s else if A = a2 then v2.eval s else s.getMem (BitVec.ofNat 64 A) := by
  rw [memEval_cons, h1, memEval_one s k2 v2 a2 A h2 ha2 hA]
  by_cases e : A = a1
  · subst e; simp
  · rw [if_neg (fun h' => e ((ofNat_inj hA ha1).mp h')), if_neg e]

/-! ## Header words -/

theorem replaceByte_toNat (w : BitVec 64) (pos : Nat) (hp : pos < 8) (b : BitVec 8) :
    (replaceByte w pos b).toNat =
      w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) := by
  have hb := b.isLt
  have hw := w.isLt
  have hlt : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) < 2 ^ 64 := by
    have h1 : w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) + w.toNat % 2 ^ (8 * pos + 8) = w.toNat := Nat.div_add_mod _ _
    have h3 : 2 ^ (8 * pos + 8) = 2 ^ (8 * pos) * 256 := by rw [Nat.pow_add]
    have h4 : w.toNat % 2 ^ (8 * pos) ≤ w.toNat % 2 ^ (8 * pos + 8) := by
      rw [h3, Nat.mod_mul]; omega
    have h5 : 2 ^ (8 * pos) * b.toNat + w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos + 8) := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos)) (show b.toNat ≤ 255 by omega)
      rw [h3]; omega
    have h6 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) ≤ w.toNat := by omega
    have h7 : 2 ^ (8 * pos + 8) ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
    have h8 : w.toNat / 2 ^ (8 * pos + 8) < 2 ^ 64 / 2 ^ (8 * pos + 8) := by
      apply Nat.div_lt_div_of_lt_of_dvd h7 hw
    have h9 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8) + 1) ≤ 2 ^ 64 := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos + 8)) (show w.toNat / 2 ^ (8 * pos + 8) + 1 ≤ 2 ^ 64 / 2 ^ (8 * pos + 8) by omega)
      rwa [Nat.mul_div_cancel' h7] at this
    rw [Nat.mul_add, Nat.mul_one] at h9
    omega
  have key : replaceByte w pos b = BitVec.ofNat 64
      (w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8))) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    unfold replaceByte
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ofNat, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
    have e : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) =
        2 ^ (8 * pos) * (2 ^ 8 * (w.toNat / 2 ^ (8 * pos + 8)) + b.toNat) + w.toNat % 2 ^ (8 * pos) := by
      rw [Nat.pow_add]; ring
    rw [e, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _)),
      Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp only [← BitVec.testBit_toNat]
    by_cases h1 : j < 8 * pos
    · simp [h1, show j < pos * 8 by omega]
    · by_cases h2 : j - 8 * pos < 8
      · have : Nat.testBit 255 (j - pos * 8) = true := by
          have : j - pos * 8 < 8 := by omega
          interval_cases (j - pos * 8) <;> decide
        simp [h1, show ¬ j < pos * 8 by omega, show j - pos * 8 < 64 by omega, this,
          show j - 8 * pos = j - pos * 8 by omega]
        intro h; omega
      · have : Nat.testBit 255 (j - pos * 8) = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le (show 255 < 2 ^ 8 by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hb' : b.toNat.testBit (j - pos * 8) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, h2, show ¬ j < pos * 8 by omega, this, hb', show j - 8 * pos - 8 + (8 * pos + 8) = j by omega]
  rw [key, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- The step byte `sb POS, 20(a0)` on a header word with the low 32 bits `L` and the bits `40 ..` equal to `J`. -/
theorem stepByte (w : Word) (L J m : Nat) (hL : L < 2 ^ 32) (hm : m < 256) (hJ : J < 2 ^ 24)
    (h1 : w.toNat % 2 ^ 32 = L) (h2 : w.toNat / 2 ^ 40 = J) :
    StoreKind.merge .b w 4 (BitVec.ofNat 64 m) = BitVec.ofNat 64 (L + 2 ^ 32 * m + 2 ^ 40 * J) := by
  apply BitVec.eq_of_toNat_eq
  simp only [StoreKind.merge]
  rw [replaceByte_toNat _ _ (by omega)]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show L + 2 ^ 32 * m + 2 ^ 40 * J < 2 ^ 64 by omega)]
  generalize w.toNat = x at *
  norm_num at h1 h2 ⊢
  omega

/-- The chain step input as doublewords: `[pad0 | header 1 | pad1 | value]`. -/
theorem wordsOf_chainInputP (lay : Layer) (tree leaf i step : Nat) (p0 p1 v : Digest) :
    wordsOf (chainInputP lay tree leaf i step p0 p1 v) =
      [p0.extractLsb' 0 64, p0.extractLsb' 64 64, BitVec.ofNat 64 (hdr0 1 lay.val tree (step + 256 * i)),
        BitVec.ofNat 64 (hdr1 tree leaf), p1.extractLsb' 0 64, p1.extractLsb' 64 64, v.extractLsb' 0 64,
        v.extractLsb' 64 64] := by
  unfold chainInputP
  rw [wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_bytesLE16, wordsOf_header, wordsOf_bytesLE16, wordsOf_bytesLE16]
  rfl

theorem chainInputP_length (lay : Layer) (tree leaf i step : Nat) (p0 p1 v : Digest) :
    (chainInputP lay tree leaf i step p0 p1 v).length = 64 * (0 + 1) := by
  simp [chainInputP, SphincsSecurity.bytesLE_length]

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

namespace LCtx

theorem blk_props (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) :
    c.blk i % 8 = 0 ∧ 0x800 + 11288 ≤ c.blk i ∧ c.blk i + 80 ≤ 0x7000 := by
  obtain ⟨-, -, -, h64, hlo, hhi, -⟩ := hc
  unfold blk; refine ⟨?_, ?_, ?_⟩ <;> omega

theorem blk_succ (c : LCtx) (hc : c.ok) (i : Nat) (hi : i < 42) : c.blk (i + 1) + 64 = c.blk i := by
  obtain ⟨-, -, -, -, hlo, -⟩ := hc
  unfold blk; omega

theorem blk_le (c : LCtx) (hc : c.ok) (i j : Nat) (hij : i ≤ j) (hj : j ≤ 42) : c.blk j + 64 * (j - i) = c.blk i := by
  obtain ⟨-, -, -, -, hlo, -⟩ := hc
  unfold blk; omega

theorem slotL_mono (i j : Nat) (h : i ≤ j) : slotL i ≤ slotL j := by unfold slotL; split_ifs <;> omega

theorem slotL_props (i : Nat) (hi : i ≤ 42) : slotL i % 16 = 0 ∧ 768 ≤ slotL i ∧ slotL i + 32 ≤ 0x5D0 := by
  unfold slotL; split <;> omega

/-- `s6 + offL i + k` is the block address plus `k`. -/
theorem base_off (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) (k : Nat) (hk : k ≤ 80) :
    BitVec.ofNat 64 c.S6 + (offL i + BitVec.ofNat 64 k) = BitVec.ofNat 64 (c.blk i + k) := by
  obtain ⟨-, -, -, -, hlo, hhi, -⟩ := hc
  unfold offL blk
  rw [ofNat_add_off _ _ _ _ (by omega) (by omega), show c.S6 + 64 * (42 - i) - 1024 = c.S6 - 1024 + 64 * (42 - i) by
    omega]

theorem base_off0 (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) :
    BitVec.ofNat 64 c.S6 + offL i = BitVec.ofNat 64 (c.blk i) := by
  obtain ⟨-, -, -, -, hlo, hhi, -⟩ := hc
  unfold offL blk
  rw [ofNat_add_off0 _ _ _ (by omega) (by omega), show c.S6 + 64 * (42 - i) - 1024 = c.S6 - 1024 + 64 * (42 - i) by
    omega]

theorem known_get (c : LCtx) {s : MachineState} (h : ∀ p ∈ c.known, s.getReg p.1 = p.2) {r : Reg} {v : Word}
    (hm : (r, v) ∈ c.known) : s.getReg r = v := h _ hm

/-- The header word 0 of step `m` of code chain `i` is Core's `hdr0`. -/
theorem w0_hdr0 (c : LCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 42) (hm : m < 256) :
    c.w0 i + 2 ^ 32 * m = hdr0 1 c.lay.val c.tree (m + 256 * (i + c.koff)) := by
  obtain ⟨htr, -, hk, -⟩ := hc
  have hl := c.lay.isLt
  rw [hdr0_eq _ _ _ _ (by norm_num) (by omega) htr (by omega)]
  unfold w0; ring

theorem w0_lt (c : LCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 42) (hm : m < 256) : c.w0 i + 2 ^ 32 * m < 2 ^ 64 := by
  obtain ⟨-, -, hk, -⟩ := hc
  have hl := c.lay.isLt
  unfold w0; omega

theorem w1_lt (c : LCtx) : c.w1 < 2 ^ 64 := hdr1_lt _ _

/-- The machine's hash input at a step of code chain `i`: `chainInputP` with the block's pads. -/
theorem chain_hashInput (c : LCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 42) (hm : m < 256) (v : Digest)
    (t : MachineState) (h10 : t.getReg .x10 = BitVec.ofNat 64 (c.blk i))
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)))
    (hp0 : DigAt t (c.blk i) (c.pad0 i)) (hp1 : DigAt t (c.blk i + 32) (c.pad1 i))
    (h16 : t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 2 ^ 32 * m))
    (h24 : t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1)
    (hv : DigAt t (c.blk i + 48) v) :
    hashInput t = toQ (chainInputP c.lay c.tree c.leaf (i + c.koff) m (c.pad0 i) (c.pad1 i) v) := by
  obtain ⟨h64, hlo, hhi⟩ := c.blk_props hc i hi
  apply hashInput_toQ t _ 0 (c.blk i) (chainInputP_length _ _ _ _ _ _ _ _) h10 (by omega) (by omega) h11
    (by norm_num)
  rw [wordsOf_chainInputP, show 8 * (0 + 1) = 2 + (2 + (2 + 2)) from rfl, readWords_add, readWords_add,
    readWords_add, readWords_two, readWords_two, readWords_two, readWords_two, hp0.1, hp0.2,
    show c.blk i + 8 * 2 = c.blk i + 16 by ring, h16,
    show c.blk i + 16 + 8 = c.blk i + 24 by ring, h24,
    show c.blk i + 16 + 8 * 2 = c.blk i + 32 by ring, hp1.1, hp1.2,
    show c.blk i + 32 + 8 * 2 = c.blk i + 48 by ring, hv.1, hv.2, w0_hdr0 c hc i m hi hm]
  rfl

end LCtx

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

namespace LCtx

theorem orig_frame {c : LCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i k : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42) (hk : k < 8) (hW : ¬ W (c.blk i + 8 * k)) :
    OrigW c.w t (c.blk i + 8 * k) := by
  have := (c.blk_props hc i hi.2)
  unfold OrigW
  rw [hF _ (by omega) hW]
  exact h0 i hi.1 hi.2 k hk

/-- The pads of code chain `i` in a state that has not written block `i`'s pads. -/
theorem pads_at {c : LCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat}
    (hi : c.i0 ≤ i ∧ i ≤ 42) (hF : Frame s0 t (c.WrIn i)) :
    DigAt t (c.blk i) (c.pad0 i) ∧ DigAt t (c.blk i + 32) (c.pad1 i) := by
  have hb := c.blk_props hc i hi.2
  have nW : ∀ k, k = 0 ∨ k = 1 ∨ k = 4 ∨ k = 5 → ¬ c.WrIn i (c.blk i + 8 * k) := by
    intro k hk hw
    have := c.blk_le hc c.i0 i hi.1 hi.2
    have hlo := hc.2.2.2.2.1
    unfold WrIn Wr blk at *
    omega
  have o0 := orig_frame hF h0 hc hi (k := 0) (by omega) (nW 0 (by omega))
  have o1 := orig_frame hF h0 hc hi (k := 1) (by omega) (nW 1 (by omega))
  have o4 := orig_frame hF h0 hc hi (k := 4) (by omega) (nW 4 (by omega))
  have o5 := orig_frame hF h0 hc hi (k := 5) (by omega) (nW 5 (by omega))
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at o0 o1
  rw [show 8 * 4 = 32 by rfl] at o4
  rw [show c.blk i + 8 * 5 = c.blk i + 32 + 8 by ring] at o5
  refine ⟨DigAt_origW o0 o1 (by omega), ?_⟩
  have := DigAt_origW o4 o5 (by omega)
  rwa [show c.blk i + 32 - 0x800 = c.blk i - 0x800 + 32 by omega] at this

/-- Consecutive rungs are two words apart. -/
theorem rungPc_succ (c : LCtx) (i m : Nat) (hd : c.dig i ≤ m) : c.rungPc i (m + 1) = c.rungPc i m + 2 := by
  unfold rungPc; split_ifs <;> omega

theorem dig_lt (c : LCtx) (hc : c.ok) (i : Nat) (hi : i < 42) : c.dig i < 8 := by
  unfold dig; split_ifs <;> omega

/-- The last rung's `ecall` + 1 is the chain's end. -/
theorem rungPc_end (c : LCtx) (i : Nat) (hi : i ≤ 42) (hd : c.dig i < 7) : c.rungPc i 6 + 3 = c.endPc i := by
  by_cases h42 : i = 42
  · subst h42; unfold rungPc endPc; simp [ckR0, ckDone]
  · have e1 : i % 3 = 1 → c.dig (3 * (i / 3) + 1) = c.dig i := fun h => by rw [show 3 * (i / 3) + 1 = i by omega]
    have e2 : i % 3 = 2 → c.dig (3 * (i / 3) + 2) = c.dig i := fun h => by rw [show 3 * (i / 3) + 2 = i by omega]
    unfold rungPc endPc tb tB tC tX pcX pcC pcB partLen
    simp only [if_neg h42]
    split_ifs <;> omega

/-- **The HASH of step `m` of code chain `i`**: its input is `chainInputP` with the block's pads and the current
value; the answer continues with rung `m + 1` or ends the chain (the last step's answer is the chain's end, in its
leaf-pk slot). -/
theorem prehash_step (c : LCtx) (hc : c.ok) (s0 : MachineState) (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i m : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hm : m ≤ 6) (hd : c.dig i ≤ m)
    (acc : List Digest) (v : Digest) (t : MachineState) (ht : c.PreHash s0 i acc m v t) :
    t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = toQ (chainInputP c.lay c.tree c.leaf (i + c.koff) m (c.pad0 i) (c.pad1 i) v) ∧
      ∀ a : BitVec 256,
        (m < 6 → c.StepInv s0 i acc (m + 1) (a.extractLsb' 0 128) (writeHash t a)) ∧
        (m = 6 → c.EndInv s0 i (acc ++ [a.extractLsb' 0 128]) (writeHash t a)) := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, h16, h24, hv, h10, h12, hpc, -⟩ := ht
  have hb := c.blk_props hc i hi.2
  have hs := slotL_props i hi.2
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → t.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have t5 : t.getReg .x5 = 0 := kr _ _ (by simp [known]) (by decide)
  have t11 : t.getReg .x11 = BitVec.ofNat 64 64 := kr _ _ (by simp [known]) (by decide)
  obtain ⟨p0, p1⟩ := pads_at hc h0 hi hF
  refine ⟨t5, ?_, ?_, ?_⟩
  · apply hashArgs_const t (c.blk i) 64 (if m = 6 then slotL i else c.blk i + 48) h10 t11 h12 (by omega)
      (by omega) (by omega)
    · split <;> omega
    · split <;> omega
  · exact c.chain_hashInput hc i m hi.2 (by omega) v t h10 t11 p0 p1 h16 h24 hv
  · intro a
    have hdst : ∀ (B : Nat), t.getReg .x12 = BitVec.ofNat 64 B → B + 32 < 2 ^ 64 →
        Frame t (writeHash t a) (fun A => B ≤ A ∧ A < B + 32) := fun B hB hB' => Frame.writeHash t a B hB hB'
    refine ⟨fun hm6 => ?_, fun hm6 => ?_⟩
    · -- the next rung
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48) := by rw [h12, if_neg (by omega)]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.WrIn i) := (hF.trans fr).mono (by
        intro A _ h; rcases h with h | h
        · exact h
        · right; right; omega)
      have fget : ∀ A, A < 2 ^ 64 → ¬ (c.blk i + 48 ≤ A ∧ A < c.blk i + 48 + 32) →
          (writeHash t a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A hA hn => fr A hA hn
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, hlen,
        h25, ⟨?_, ?_, ?_⟩, DigAt.writeHash_lo t a _ d12 (by omega),
        by rw [getReg_writeHash]; exact h10, by rw [getReg_writeHash]; exact d12, ?_⟩
      · have hj' := hS j hj
        have hsj := slotL_props (c.i0 + j) (by omega)
        exact hj'.frame fr (by omega) (by omega) (by omega)
      · rw [fget _ (by omega) (by omega), h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.w0_lt hc i m hi.2 (by omega))]
        unfold w0; have := c.lay.isLt; omega
      · rw [fget _ (by omega) (by omega), h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.w0_lt hc i m hi.2 (by omega))]
        unfold w0; have := c.lay.isLt; omega
      · rw [fget _ (by omega) (by omega)]; exact h24
      · rw [pc_writeHash, hpc, if_neg (by omega), c.rungPc_succ i m hd, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1
    · -- the chain's end in its leaf-pk slot
      subst hm6
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (slotL i) := by rw [h12, if_pos rfl]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.Wr (i + 1)) := (hF.trans fr).mono (by
        intro A _ h
        have := c.blk_le hc c.i0 i hi.1 hi.2
        have hlo := hc.2.2.2.2.1
        have hsm := slotL_mono c.i0 i hi.1
        unfold WrIn Wr blk at *
        omega)
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, by simp [hlen]; omega,
        h25, ?_⟩
      · rw [List.length_append, List.length_singleton] at hj
        by_cases hjl : j < acc.length
        · have hj' := hS j hjl
          have hsj := slotL_props (c.i0 + j) (by omega)
          have hmono : slotL (c.i0 + j) + 16 ≤ slotL i := by unfold slotL; split_ifs <;> omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
          exact hj'.frame fr (by omega) (by omega) (by omega)
        · have hj2 : j = acc.length := by omega
          subst hj2
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
            show c.i0 + acc.length = i by omega]
          exact DigAt.writeHash_lo t a _ d12 (by omega)
      · have hd7 : c.dig i < 7 := by omega
        rw [pc_writeHash, hpc, if_pos rfl, ← c.rungPc_end i hi.2 hd7, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1

end LCtx

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

namespace LCtx

/-- The step registers hold the steps. -/
theorem posE_eval (c : LCtx) {s0 s : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x) (m : Nat) (hm : m ≤ 6) :
    (posE m).eval s = BitVec.ofNat 64 m := by
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  interval_cases m
  · rfl
  · exact kr .x6 1 (by simp [known]) (by decide)
  · exact kr .x7 2 (by simp [known]) (by decide)
  · exact kr .x8 3 (by simp [known]) (by decide)
  · exact kr .x9 4 (by simp [known]) (by decide)
  · exact kr .x13 5 (by simp [known]) (by decide)
  · exact kr .x26 6 (by simp [known]) (by decide)

theorem w0_low (c : LCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 42) (hm : m < 256) :
    (BitVec.ofNat 64 (c.w0 i + 2 ^ 32 * m)).toNat % 2 ^ 32 = 0x101 + 65536 * c.lay.val ∧
      (BitVec.ofNat 64 (c.w0 i + 2 ^ 32 * m)).toNat / 2 ^ 40 = i + c.koff := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.w0_lt hc i m hi hm)]
  have := c.lay.isLt
  unfold w0; constructor <;> omega

/-- **One rung**: `sb POS_m, 20(a0)` (and `li a2, slot` for the last step), up to the `ecall`. -/
theorem rung_piece (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m p : Nat) (hi : i ≤ 42) (hm : m ≤ 6) (hp : p < 209920)
    (hrun : vrun p 3 = some (rungR m (if m = 6 then some (slotL i) else none) p)) (s : MachineState)
    (hpc : s.pc = pcOf p) (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (c.blk i)) (hH : c.HdrOk i s) :
    ∃ t, Steps vimage s (if m = 6 then 2 else 1) (if m = 6 then 2 else 1) t ∧ fetch vimage t = some (.base .ECALL) ∧
      (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = 6 → t.getReg .x12 = BitVec.ofNat 64 (slotL i)) ∧ (m < 6 → t.getReg .x12 = s.getReg .x12) ∧
      t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 2 ^ 32 * m) ∧
      Frame s t (fun A => A = c.blk i + 16) ∧ t.pc = pcOf (p + (if m = 6 then 2 else 1)) := by
  have hb := c.blk_props hc i hi
  set r := rungR m (if m = 6 then some (slotL i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, rungR, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show ((E.reg .x10).eval s).toNat % 8 = 0
      simp only [E.eval, h10, BitVec.toNat_ofNat]; omega
    · show accessValid (Addr.eval s ⟨some (.reg .x10), 20⟩) 1 = true
      simp only [Addr.eval, E.eval, h10]
      rw [show (20 : Word) = BitVec.ofNat 64 20 from rfl, ofNat_add_ofNat]
      exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps hrun hp s hpc hobl
  have hec := piece_ecall hrun hp s hobl (by simp [hr, rungR])
  have hn : r.steps = (if m = 6 then 2 else 1) ∧ r.cycles = (if m = 6 then 2 else 1) := by
    simp only [hr, rungR]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := rungR_keeps m (if m = 6 then some (slotL i) else none) p
  have key : (⟨some (.reg .x10), 16⟩ : Addr).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
    simp only [Addr.eval, E.eval, h10]
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then
        StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (c.blk i + 16))) 4 (BitVec.ofNat 64 m)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, rungR]
    rw [memEval_one s _ _ (c.blk i + 16) A key (by omega) hA]
    split
    · have e1 : (addC (E.reg .x10) 16).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
        rw [addC_eval]; simp only [E.eval, h10]
        rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
      simp only [E.eval, BinOp.eval]
      rw [e1, c.posE_eval hk hR m hm]
    · rfl
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h6 => ?_, fun h6 => ?_, ?_,
    fun A hA hn => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_pos h6]
    rw [RegFile.get_set_self _ _ (by decide)]; rfl
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_neg (show m ≠ 6 by omega)]
    rw [RegFile.init_get_eval]
  · rw [tmem _ (by omega), if_pos rfl]
    obtain ⟨hl, hj, -⟩ := hH
    have := c.lay.isLt
    have hkoff := hc.2.2.1
    rw [stepByte _ _ _ _ (by omega) (by omega) (by omega) hl hj]
    congr 1; unfold w0; ring
  · rw [tmem _ hA, if_neg hn]
  · rw [Result.toState_pc]; simp only [hr, rungR]
    by_cases h6 : m = 6 <;> simp [h6, E.eval]

end LCtx

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

namespace LCtx

theorem not_mem_sub {x : Reg} {ws : List Reg} (hx : x ∉ chainRegs) (h : ws ⊆ chainRegs) : x ∉ ws :=
  fun hm => hx (h hm)

theorem w0_low0 (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) :
    (BitVec.ofNat 64 (c.w0 i)).toNat % 2 ^ 32 = 0x101 + 65536 * c.lay.val ∧
      (BitVec.ofNat 64 (c.w0 i)).toNat / 2 ^ 40 = i + c.koff := by
  have := c.w0_low hc i 0 hi (by omega)
  rwa [Nat.mul_zero, Nat.add_zero] at this

/-- **A rung after a step's hash** (`StepInv` at rung `m`): up to the `ecall` of step `m`. -/
theorem rung_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hm : m ≤ 6) (hp : c.rungPc i m < 209920)
    (hrun : vrun (c.rungPc i m) 3 = some (rungR m (if m = 6 then some (slotL i) else none) (c.rungPc i m)))
    (acc : List Digest) (v : Digest) (s : MachineState) (hs : c.StepInv s0 i acc m v s) :
    ∃ t, Steps vimage s (if m = 6 then 2 else 1) (if m = 6 then 2 else 1) t ∧ c.PreHash s0 i acc m v t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hH, hv, h10, h12, hpc⟩ := hs
  have hb := c.blk_props hc i hi.2
  obtain ⟨t, hst, hec, hreg, h12a, h12b, h16, hfr, hpc'⟩ :=
    c.rung_piece hc hk i m (c.rungPc i m) hi.2 hm hp hrun s hpc hR h10 hH
  have hs := slotL_props i hi.2
  refine ⟨t, hst, ⟨⟨fun x hx => ?_, (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, h16, ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR x hx
  · intro A _ h; rcases h with h | h
    · exact h
    · right; left; omega
  · have hsj := slotL_props (c.i0 + j) (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · exact h25
  · rw [hfr _ (by omega) (by omega)]; exact hH.2.2
  · exact hv.frame hfr (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide)]; exact h10
  · by_cases h6 : m = 6
    · rw [h12a h6, if_pos h6]
    · rw [h12b (by omega), h12, if_neg h6]
  · rw [hpc']

/-- The value slot of code chain `i` holds the witness value while block `i` is not written. -/
theorem val_at {c : LCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42)
    (hF : Frame s0 t (c.Wr i)) : DigAt t (c.blk i + 48) (c.val i) := by
  have hb := c.blk_props hc i hi.2
  have nW : ∀ k, k = 6 ∨ k = 7 → ¬ c.Wr i (c.blk i + 8 * k) := by
    intro k hk hw
    have := c.blk_le hc c.i0 i hi.1 hi.2
    have hlo := hc.2.2.2.2.1
    unfold Wr blk at *
    omega
  have o6 := orig_frame hF h0 hc hi (k := 6) (by omega) (nW 6 (by omega))
  have o7 := orig_frame hF h0 hc hi (k := 7) (by omega) (nW 7 (by omega))
  rw [show c.blk i + 8 * 6 = c.blk i + 48 by ring] at o6
  rw [show c.blk i + 8 * 7 = c.blk i + 48 + 8 by ring] at o7
  have := DigAt_origW o6 o7 (by omega)
  rwa [show c.blk i + 48 - 0x800 = c.blk i - 0x800 + 48 by omega] at this

theorem Wr_mono (c : LCtx) (i : Nat) (A : Nat) (h : c.Wr i A) : c.WrIn i A := Or.inl h

/-- T3X (59cbf8ec's `header_load`): a head's header load reads the image's header table, which the chain phase
never writes (its frame lies below `2^23`). -/
theorem header_load (c : LCtx) (hc : c.ok) {s0 s : MachineState}
    (hD : SigGolfCandidate.T3M.CanonicalPort.Verify.DataOK s0) (i d : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hd : d < 8)
    (hF : Frame s0 s (c.Wr i))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank c.lay.val c.koff)) :
    (Oblig.valid (hKey i d) 8).holds s ∧
      (hLoad i d).eval s = BitVec.ofNat 64 (c.w0 i + 2 ^ 32 * d) := by
  have hl := c.lay.isLt
  have hko := hc.2.2.1
  have hib : i + c.koff < 64 := by omega
  have hb := c.blk_props hc c.i0 (by omega)
  let A := SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * c.lay.val + 64 * (i + c.koff) + 8 * d
  have hA : 2 ^ 23 + 4096 ≤ A ∧ A + 8 ≤ 2 ^ 24 := by dsimp [A, SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA]; omega
  have key : (hKey i d).eval s = BitVec.ofNat 64 A := by
    simp only [hKey, Addr.eval, E.eval, h28, hOff]
    change BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank c.lay.val c.koff) +
      (BitVec.ofNat 64 (64 * i + 8 * d) - BitVec.ofNat 64 2048) = BitVec.ofNat 64 A
    rw [ofNat_add_off0 (SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank c.lay.val c.koff) (64 * i + 8 * d) 2048
      (by unfold SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA; omega)
      (by unfold SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA; omega)]
    apply congrArg (BitVec.ofNat 64)
    dsimp [A, SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank, SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA]
    omega
  have fr : s.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) := by
    apply hF A (by omega)
    unfold Wr
    intro h
    rcases h with h | h <;> omega
  refine ⟨?_, ?_⟩
  · show accessValid ((hKey i d).eval s) 8 = true
    rw [key]; exact valid_ofNat A 8 (by dsimp [A, SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA]; omega) (by dsimp [A, SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA]; omega)
  · have he : (addC (.reg .x28) (hOff i d)).eval s = BitVec.ofNat 64 A := by
      simpa only [hKey, Addr.eval, addC_eval, E.eval] using key
    change s.getMem ((addC (.reg .x28) (hOff i d)).eval s) = _
    rw [he, fr]
    have H := hD.header c.lay.val (i + c.koff) d hl hib hd
    simpa only [A, w0] using H

/-- Fetch depends on the pc only. -/
theorem fetch_pc_congr {u v : MachineState} (h : u.pc = v.pc) : fetch vimage u = fetch vimage v := by
  unfold fetch; rw [h]

/-- **The head of a table-slot chain** (`A = 3t`, or the checksum chain 42 in `ctab`), V1: one piece loading the
header word of step `d = dig i` and jumping onto the `ecall` of rung `d` (its byte store is skipped). -/
theorem headJ_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hd : c.dig i < 7)
    (hp0 : c.startPc i < 209920) (hp1 : c.rungPc i (c.dig i) + landOff (c.dig i) < 209920)
    (hrun1 : vrun (c.startPc i) 7 = some (headJH .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i
      (c.dig i) (hSlot i (c.dig i))))
    (hrun2 : vrun (c.rungPc i (c.dig i) + landOff (c.dig i)) 1 =
      some (ecallR (c.rungPc i (c.dig i) + landOff (c.dig i))))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 6 6 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have hb := c.blk_props hc i hi.2
  have hs := slotL_props i hi.2
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide)
  have keyE : ∀ k, k ≤ 80 → (kAt .x22 (offL i) k).eval s = BitVec.ofNat 64 (c.blk i + k) := by
    intro k hk'
    simp only [kAt, Addr.eval, E.eval, h22]
    exact c.base_off hc i hi.2 k hk'
  set r := headJH .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i (c.dig i) (hSlot i (c.dig i)) with hr
  have htable := c.header_load hc h25 i (c.dig i) hi (by omega) hF
    (kr _ _ (by simp [known]) (by decide))
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJH, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl)
    · show accessValid ((kAt .x22 (offL i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x22 (offL i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · exact htable.1
  have hst := piece_steps hrun1 hp0 s hpc hobl
  have hn : r.steps = 6 ∧ r.cycles = 6 := ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headJH_keeps .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i (c.dig i) (hSlot i (c.dig i))
  have a0e : (addC (E.reg .x22) (offL i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h22]; exact c.base_off0 hc i hi.2
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 2 ^ 32 * c.dig i)
      else if A = c.blk i + 24 then BitVec.ofNat 64 c.w1 else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headJH]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    change (if A = c.blk i + 24 then s.getReg .x4 else if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), htable.2]
    split_ifs <;> simp_all
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16 ∨ A = c.blk i + 24) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  have hpcT : (r.toState s).pc = pcOf (c.rungPc i (c.dig i) + landOff (c.dig i)) := by
    rw [Result.toState_pc]; simp only [hr, headJH, E.eval]
  have hec : fetch vimage (r.toState s) = some (.base .ECALL) := by
    have hE := piece_ecall hrun2 hp1 (r.toState s) (by simp [ecallR, SymState.init]) rfl
    rw [← hE]
    apply fetch_pc_congr
    rw [hpcT, Result.toState_pc]; simp only [ecallR, E.eval]
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slotL_props (c.i0 + j) (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · exact h25
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [Result.toState_getReg]; simp only [hr, headJH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headJH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    by_cases h6 : c.dig i = 6
    · simp only [hSlot, h6, if_true, E.eval]
    · simp only [hSlot, h6, if_false]
      rw [addC_eval, a0e, show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  · rw [hpcT]; simp only [landOff]

end LCtx

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

namespace LCtx

theorem kAt_eval (c : LCtx) (hc : c.ok) {s : MachineState} (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6) (i : Nat)
    (hi : i ≤ 42) (k : Nat) (hk : k ≤ 80) : (kAt .x22 (offL i) k).eval s = BitVec.ofNat 64 (c.blk i + k) := by
  simp only [kAt, Addr.eval, E.eval, h22]
  exact c.base_off hc i hi k hk

theorem lAt_eval (c : LCtx) (hc : c.ok) {s : MachineState} (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6) (i : Nat)
    (hi : i ≤ 42) (k : Nat) (hk : k ≤ 80) : (lAt .x22 (offL i) k).eval s = s.getMem (BitVec.ofNat 64 (c.blk i + k)) := by
  simp only [lAt, E.eval, addC_eval, h22]
  rw [c.base_off hc i hi k hk]

theorem copy_mem (c : LCtx) (hc : c.ok) {s : MachineState} (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6) (i : Nat)
    (hi : i ≤ 42) (A : Nat) (hA : A < 2 ^ 64) :
    memEval s (copyMem .x22 (offL i) (slotL i)) (BitVec.ofNat 64 A) =
      if A = slotL i + 8 then s.getMem (BitVec.ofNat 64 (c.blk i + 56))
      else if A = slotL i then s.getMem (BitVec.ofNat 64 (c.blk i + 48)) else s.getMem (BitVec.ofNat 64 A) := by
  have hs := slotL_props i hi
  unfold copyMem
  rw [memEval_two s _ _ _ _ (slotL i + 8) (slotL i) A rfl rfl (by omega) (by omega) hA,
    c.lAt_eval hc h22 i hi 56 (by omega), c.lAt_eval hc h22 i hi 48 (by omega)]

theorem copy_obl (c : LCtx) (hc : c.ok) {s : MachineState} (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6) (i : Nat)
    (hi : i ≤ 42) : ∀ o ∈ copyObl .x22 (offL i), o.holds s := by
  have hb := c.blk_props hc i hi
  simp only [copyObl, List.mem_cons, List.not_mem_nil, or_false]
  rintro o (rfl | rfl)
  · show accessValid ((kAt .x22 (offL i) 56).eval s) 8 = true
    rw [c.kAt_eval hc h22 i hi 56 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid ((kAt .x22 (offL i) 48).eval s) 8 = true
    rw [c.kAt_eval hc h22 i hi 48 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)

/-- The common post-state of the three copies: the witness value in the slot, everything else of `ChainIn`'s
memory kept. -/
theorem copy_post (c : LCtx) (hc : c.ok) {s0 s t : MachineState} (h0 : c.Orig0 s0) (i : Nat)
    (hi : c.i0 ≤ i ∧ i ≤ 42) (acc : List Digest) (hlen : acc.length = i - c.i0) (hF : Frame s0 s (c.Wr i))
    (hS : ∀ j < acc.length, DigAt s (slotL (c.i0 + j)) (acc.getD j 0))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6)
    (htm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) = memEval s (copyMem .x22 (offL i) (slotL i)) (BitVec.ofNat 64 A)) :
    Frame s0 t (c.Wr (i + 1)) ∧ ∀ j < (acc ++ [c.val i]).length,
      DigAt t (slotL (c.i0 + j)) ((acc ++ [c.val i]).getD j 0) := by
  have hb := c.blk_props hc i hi.2
  have hs := slotL_props i hi.2
  have tm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = slotL i + 8 then s.getMem (BitVec.ofNat 64 (c.blk i + 56))
      else if A = slotL i then s.getMem (BitVec.ofNat 64 (c.blk i + 48)) else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (htm A hA).trans (c.copy_mem hc h22 i hi.2 A hA)
  have hfr : Frame s t (fun A => A = slotL i + 8 ∨ A = slotL i) := by
    intro A hA hn
    rw [tm A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  refine ⟨(hF.trans hfr).mono ?_, fun j hj => ?_⟩
  · intro A _ h
    have := c.blk_le hc c.i0 i hi.1 hi.2
    have hlo := hc.2.2.2.2.1
    have hsm := slotL_mono c.i0 i hi.1
    rcases h with h | h
    · unfold Wr at h ⊢; unfold blk at h this ⊢; omega
    · left; omega
  · rw [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < acc.length
    · have hsj := slotL_props (c.i0 + j) (by omega)
      have hmono : slotL (c.i0 + j) + 16 ≤ slotL i := by unfold slotL; split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
      exact (hS j hjl).frame hfr (by omega) (by omega) (by omega)
    · have hj2 : j = acc.length := by omega
      subst hj2
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
        show c.i0 + acc.length = i by omega]
      have hv := val_at hc h0 hi hF
      refine ⟨?_, ?_⟩
      · rw [tm _ (by omega), if_neg (by omega), if_pos rfl]; exact hv.1
      · rw [tm _ (by omega), if_pos rfl]; exact hv.2

/-- **The max-digit copy of a table-slot chain** (`A = 3t`): the witness value into the slot, then `j` past
the shared block's `A` rungs. -/
theorem copyJ_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i < 42) (first : Bool)
    (hfirst : first = true → i = 0 ∧ c.koff = 0) (hfirst' : first = false → i ≠ 0)
    (hp0 : c.startPc i < 209920)
    (hrun : vrun (c.startPc i) 7 = some (copyN .x22 (offL i) (slotL i) (c.endPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide)
  set r := copyN .x22 (offL i) (slotL i) (c.endPc i) with hr
  have hst := piece_steps hrun hp0 s hpc (by simpa [hr, copyN] using c.copy_obl hc h22 i (by omega))
  have hkeep := copyN_keeps .x22 (offL i) (slotL i) (c.endPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i ⟨hi.1, by omega⟩ acc hlen hF hS h22
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen]; omega, h25, ?_⟩⟩
  rw [Result.toState_pc]; rfl

/-- **The max-digit copy of an inline chain** (`B`, `C`): 4 instructions, then the next chain's code. -/
theorem copyF_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i < 42) (hi0 : i ≠ 0) (hp0 : c.startPc i < 209920)
    (hend : c.startPc i + 4 = c.endPc i)
    (hrun : vrun (c.startPc i) 4 = some (copyFH .x22 (offL i) (slotL i) (c.startPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 4 4 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide)
  set r := copyFH .x22 (offL i) (slotL i) (c.startPc i) with hr
  have hst := piece_steps hrun hp0 s hpc (by simpa [hr, copyFH] using c.copy_obl hc h22 i (by omega))
  have hkeep := copyFH_keeps .x22 (offL i) (slotL i) (c.startPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i ⟨hi.1, by omega⟩ acc hlen hF hS h22
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen]; omega, h25, ?_⟩⟩
  rw [Result.toState_pc]; simp only [hr, copyFH, E.eval]; rw [hend]

/-- **The checksum chain's copy** (`ctab` slot 7): no `s9` update, then `j ck_done`. -/
theorem copyN_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hi : c.i0 ≤ 42) (hp0 : c.startPc 42 < 209920)
    (hrun : vrun (c.startPc 42) 6 = some (copyN .x22 (offL 42) (slotL 42) (c.endPc 42)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 42 acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.EndInv s0 42 (acc ++ [c.val 42]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide)
  set r := copyN .x22 (offL 42) (slotL 42) (c.endPc 42) with hr
  have hst := piece_steps hrun hp0 s hpc (by simpa [hr, copyN] using c.copy_obl hc h22 42 (by omega))
  have hkeep := copyN_keeps .x22 (offL 42) (slotL 42) (c.endPc 42)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 42 ⟨hi, le_refl _⟩ acc hlen hF hS h22
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen]; omega, h25, ?_⟩⟩
  rw [Result.toState_pc]; rfl

end LCtx

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

namespace LCtx

/-- **The head of an inline chain** (`B`, `C`) with its first rung (step `d = dig i`), one piece. -/
theorem headR_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i < 42) (hi0 : i ≠ 0) (hd : c.dig i < 7)
    (hp0 : c.startPc i < 209920) (hrp : c.rungPc i (c.dig i) = c.startPc i + 4)
    (hrun : vrun (c.startPc i) 8 =
      some (headRH .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s (if c.dig i = 6 then 6 else 5) (if c.dig i = 6 then 6 else 5) t ∧
      c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have hb := c.blk_props hc i (by omega)
  have hs := slotL_props i (by omega)
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h22 i (by omega)
  set r := headRH .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i with hr
  have htable := c.header_load hc h25 i (c.dig i) ⟨hi.1, by omega⟩ (by omega) hF
    (kr _ _ (by simp [known]) (by decide))
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headRH, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl)
    · show accessValid ((kAt .x22 (offL i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x22 (offL i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · exact htable.1
  have hst := piece_steps hrun hp0 s hpc hobl
  have hec := piece_ecall hrun hp0 s hobl (by simp [hr, headRH])
  have hn : r.steps = (if c.dig i = 6 then 6 else 5) ∧ r.cycles = (if c.dig i = 6 then 6 else 5) := by
    simp only [hr, headRH]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := headRH_keeps .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i
  have a0e : (addC (E.reg .x22) (offL i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h22]; exact c.base_off0 hc i (by omega)
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 2 ^ 32 * c.dig i)
      else if A = c.blk i + 24 then BitVec.ofNat 64 c.w1 else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headRH]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    change (if A = c.blk i + 24 then s.getReg .x4 else if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), htable.2]
    split_ifs <;> simp_all
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16 ∨ A = c.blk i + 24) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 ⟨hi.1, by omega⟩ hF
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slotL_props (c.i0 + j) (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · exact h25
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [Result.toState_getReg]; simp only [hr, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    by_cases h6 : c.dig i = 6
    · simp only [h6, if_true, E.eval]
    · simp only [h6, if_false]
      rw [addC_eval, a0e, show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  · rw [Result.toState_pc]; simp only [hr, headRH, hrp]
    by_cases h6 : c.dig i = 6 <;> simp [h6, E.eval]

end LCtx

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

/-! ## Table dispatch arithmetic -/

theorem land_mask (n k : Nat) (hk : k ≤ 9) :
    n &&& (512 * (2 ^ k - 1)) = 512 * (n / 512 % 2 ^ k) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, show (512 : Nat) = 2 ^ 9 by norm_num, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h9 : 9 ≤ j
  · simp only [h9, decide_true, Bool.true_and, show j - 9 + 9 = j by omega]
    by_cases hj : j - 9 < k
    · simp [hj]
    · simp [hj]
  · simp [h9]

theorem even_andNot1' (n : Nat) (h : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases h0 : j = 0
  · subst h0; simp; rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit_zero]; simp [h]
  · simp [h0, hj]

/-- A table target `a + base + (b - off)` (all small). -/
theorem tab_target (a base b off : Nat) (h : off ≤ base) (ha : a + base + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 base + (BitVec.ofNat 64 b - BitVec.ofNat 64 off) =
      BitVec.ofNat 64 (a + (base - off) + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- A field of `W * 2^s mod 2^64` above bit 9 is a field of `W` above bit `9 - s`. -/
theorem field_shl (W s k : Nat) (hs : s ≤ 9) (hk : k ≤ 9) :
    W * 2 ^ s % 2 ^ 64 / 512 % 2 ^ k = W / 2 ^ (9 - s) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, show (512 : Nat) = 2 ^ 9 by norm_num,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow]
  by_cases hj : j < k
  · simp only [hj, decide_true, Bool.true_and, show j + 9 < 64 by omega, show s ≤ j + 9 by omega]
    rw [show j + 9 - s = j + (9 - s) by omega]
  · simp [hj]

/-- `(shE w b &&& mask_k)` for a `k`-bit field moved to bit 9: `512 (W / 2^b mod 2^k)`. -/
theorem shE_mask (s : MachineState) (w : Reg) (W : Word) (hw : s.getReg w = W) (b k : Nat) (hb : b < 64)
    (hk : k ≤ 9) :
    ((shE w b).eval s &&& BitVec.ofNat 64 (512 * (2 ^ k - 1))).toNat = 512 * (W.toNat / 2 ^ b % 2 ^ k) := by
  have hm : 512 * (2 ^ k - 1) < 2 ^ 64 := by
    have : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hk
    omega
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, land_mask _ _ hk]
  congr 1
  unfold shE
  split_ifs with h1 h2
  · simp only [E.eval, BinOp.eval, hw, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show 9 - b < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 9 - b < 64 by omega),
      Nat.shiftLeft_eq, field_shl _ _ _ (by omega) hk, show 9 - (9 - b) = b by omega]
  · simp only [E.eval, BinOp.eval, hw, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show b - 9 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b - 9 < 64 by omega),
      Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      show 2 ^ (b - 9) * 512 = 2 ^ b by rw [show (512 : Nat) = 2 ^ 9 by norm_num, ← Nat.pow_add]; congr 1; omega]
  · have : b = 9 := by omega
    subst this
    simp only [E.eval, hw]
    rfl

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

namespace LCtx

/-- Radix-8 digit `3 t' + m` of `X` is digit `m` of `X / 2^(9 t')`. -/
theorem dig8_shift (X t' m : Nat) : X / 8 ^ (3 * t' + m) % 8 = X / 2 ^ (9 * t') / 8 ^ m % 8 := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_add, show (8 : Nat) ^ (3 * t') = 2 ^ (9 * t') by
    rw [show (8 : Nat) = 2 ^ 3 by rfl, ← Nat.pow_mul]; ring_nf]

/-- The table row of triple `t` from its digit word. -/
theorem kOf_eq (c : LCtx) (t : Nat) (ht : t < 14) :
    c.kOf t = (if t < 7 then c.d0 else c.d1).toNat / 2 ^ (9 * (t % 7)) % 512 := by
  unfold kOf dig
  by_cases h7 : t < 7
  · simp only [h7, if_true, show 3 * t < 21 by omega, show 3 * t + 1 < 21 by omega, show 3 * t + 2 < 21 by omega]
    rw [show t % 7 = t by omega]
    have e0 : c.d0.toNat / 8 ^ (3 * t) % 8 = c.d0.toNat / 2 ^ (9 * t) % 8 := by
      have := dig8_shift c.d0.toNat t 0; simpa using this
    rw [e0, dig8_shift, dig8_shift]
    generalize c.d0.toNat / 2 ^ (9 * t) = Y
    norm_num
    omega
  · simp only [h7, if_false, show ¬ 3 * t < 21 by omega, show ¬ 3 * t + 1 < 21 by omega,
      show ¬ 3 * t + 2 < 21 by omega, show 3 * t < 42 by omega, show 3 * t + 1 < 42 by omega,
      show 3 * t + 2 < 42 by omega, if_true]
    rw [show t % 7 = t - 7 by omega, show 3 * t + 1 - 21 = 3 * (t - 7) + 1 by omega,
      show 3 * t + 2 - 21 = 3 * (t - 7) + 2 by omega, show 3 * t - 21 = 3 * (t - 7) by omega]
    have e0 : c.d1.toNat / 8 ^ (3 * (t - 7)) % 8 = c.d1.toNat / 2 ^ (9 * (t - 7)) % 8 := by
      have := dig8_shift c.d1.toNat (t - 7) 0; simpa using this
    rw [e0, dig8_shift, dig8_shift]
    generalize c.d1.toNat / 2 ^ (9 * (t - 7)) = Y
    norm_num
    omega

theorem kOf_lt (c : LCtx) (t : Nat) (ht : t < 14) : c.kOf t < 512 := by
  rw [c.kOf_eq t ht]; exact Nat.mod_lt _ (by norm_num)

/-- **The dispatch after a triple's `C`** (`t < 13`): `jalr` into slot `t + 1` of `ttab` row `kOf (t + 1)`. -/
theorem x_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (t : Nat) (ht : t < 13) (hi : c.i0 ≤ 3 * t + 2) (hp : c.tX (3 * t + 2) < 209920)
    (hrun : vrun (c.tX (3 * t + 2)) 5 = some (xJ (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7)) .x2
      (BitVec.ofNat 64 (32 * (t + 1)) - BitVec.ofNat 64 1760)))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 (3 * t + 2) acc s) :
    ∃ u, Steps vimage s (if 9 * ((t + 1) % 7) = 9 then 3 else 4)
      (if 9 * ((t + 1) % 7) = 9 then 3 else 4) u ∧ c.ChainIn s0 (3 * t + 3) acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hpc' : s.pc = pcOf (c.tX (3 * t + 2)) := by
    rw [hpc]; unfold endPc; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  set r := xJ (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7)) .x2
    (BitVec.ofNat 64 (32 * (t + 1)) - BitVec.ofNat 64 1760) with hr
  have hst := piece_steps hrun hp s hpc' (by simp [hr, xJ])
  have hkeep := xJ_keeps (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7)) .x2
    (BitVec.ofNat 64 (32 * (t + 1)) - BitVec.ofNat 64 1760)
  have hW : s.getReg (if t + 1 < 7 then .x16 else .x17) = (if t + 1 < 7 then c.d0 else c.d1) := by
    split
    · exact kr .x16 c.d0 (by simp [known]) (by decide)
    · exact kr .x17 c.d1 (by simp [known]) (by decide)
  have h2 : s.getReg .x2 = BitVec.ofNat 64 (512 * (2 ^ 9 - 1)) := kr .x2 0x3fe00 (by simp [known]) (by decide)
  have h15 : s.getReg .x15 = BitVec.ofNat 64 0x6e000 := kr .x15 0x6e000 (by simp [known]) (by decide)
  have hm := shE_mask s _ _ hW (9 * ((t + 1) % 7)) 9 (by omega) (le_refl _)
  have hk1 := c.kOf_lt (t + 1) (by omega)
  have hrow : ((if t + 1 < 7 then c.d0 else c.d1).toNat / 2 ^ (9 * ((t + 1) % 7)) % 2 ^ 9) = c.kOf (t + 1) := by
    rw [c.kOf_eq (t + 1) (by omega)]; rfl
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx),
    hF.mono (fun A _ h => by
      have hlo := hc.2.2.2.2.1
      unfold Wr at h ⊢; rcases h with h | h
      · exact Or.inl h
      · right; refine ⟨?_, h.2⟩; omega), hS⟩, by omega, h25, ?_⟩⟩
  · rw [Result.toState_pc]
    simp only [hr, xJ, E.eval, BinOp.eval]
    rw [h2, h15]
    have e : ((shE (if t + 1 < 7 then Reg.x16 else Reg.x17) (9 * ((t + 1) % 7))).eval s &&&
        BitVec.ofNat 64 (512 * (2 ^ 9 - 1))) = BitVec.ofNat 64 (512 * c.kOf (t + 1)) := by
      apply BitVec.eq_of_toNat_eq; rw [hm, hrow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [e]
    have e2 : BitVec.ofNat 64 (512 * c.kOf (t + 1)) + BitVec.ofNat 64 0x6e000 +
        (BitVec.ofNat 64 (32 * (t + 1)) - BitVec.ofNat 64 1760) =
        BitVec.ofNat 64 (0x1000 + 4 * entW (t + 1) (c.kOf (t + 1))) := by
      rw [tab_target _ _ _ _ (by omega) (by omega)]
      congr 1
      unfold entW ttabIdx; omega
    rw [e2, even_andNot1' _ (by omega)]
    unfold startPc
    rw [if_neg (by omega), if_pos (by omega), show (3 * t + 3) / 3 = t + 1 by omega]

end LCtx

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

namespace LCtx

/-- After the chain code's return (`jr ra`): the ends of the code chains `i0 .. n - 1` in their slots (the blocks
of the chains `i0 .. n - 1` written: `n = 42` for a run without the checksum chain leaves block 42 untouched). -/
def ChainOut (c : LCtx) (s0 : MachineState) (n : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr n) acc s ∧ acc.length = n - c.i0 ∧ s.pc = pcOf c.ret

/-- `A` and `B` of a triple fall through to the next chain's code. -/
theorem next_inline (c : LCtx) (s0 : MachineState) (i : Nat) (hi : i < 42) (h2 : i % 3 ≠ 2)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) : c.ChainIn s0 (i + 1) acc s := by
  obtain ⟨hB, hlen, h25, hpc⟩ := hs
  refine ⟨hB, hlen.trans (by omega), h25, ?_⟩
  rw [hpc]
  simp only [endPc, startPc, show i ≠ 42 by omega, show i + 1 ≠ 42 by omega, if_false]
  by_cases h0 : i % 3 = 0
  · rw [if_pos h0, if_neg (show (i + 1) % 3 ≠ 0 by omega), if_pos (show (i + 1) % 3 = 1 by omega)]
    unfold tB; rw [show (i + 1) / 3 = i / 3 by omega]
  · rw [if_neg h0, if_pos (show i % 3 = 1 by omega), if_neg (show (i + 1) % 3 ≠ 0 by omega),
      if_neg (show (i + 1) % 3 ≠ 1 by omega)]
    unfold tC; rw [show (i + 1) / 3 = i / 3 by omega]

/-- **After triple 13** (`C` = chain 41): the dispatch into `ctab[t4]`. -/
theorem x13_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (_hi : c.i0 ≤ 41) (hp : c.tX 41 < 209920) (hrun : vrun (c.tX 41) 4 = some ctabX)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 41 acc s) :
    ∃ u, Steps vimage s 3 3 u ∧ c.ChainIn s0 42 acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hpc' : s.pc = pcOf (c.tX 41) := by rw [hpc]; unfold endPc; simp
  have hst := piece_steps hrun hp s hpc' (by simp [ctabX])
  have h15 : s.getReg .x15 = BitVec.ofNat 64 0x6e000 := kr .x15 0x6e000 (by simp [known]) (by decide)
  have h29 : s.getReg .x29 = 7#64 - BitVec.ofNat 64 c.ck := kr .x29 _ (by simp [known]) (by decide)
  have hck := hc.2.2.2.2.2.2.1
  refine ⟨ctabX.toState s, hst, ⟨⟨fun x hx => (ctabX_keeps.reg s (not_mem_sub hx (by decide))).trans (hR x hx),
    hF.mono (fun A _ h => by
      have hlo := hc.2.2.2.2.1
      unfold Wr at h ⊢; rcases h with h | h
      · exact Or.inl h
      · right; refine ⟨?_, h.2⟩; omega), hS⟩, by omega, h25, ?_⟩⟩
  · rw [Result.toState_pc]
    simp only [ctabX, E.eval, BinOp.eval, h15, h29]
    have e2 : BitVec.ofNat 64 0x6e000 - (7#64 - BitVec.ofNat 64 c.ck) <<< ((5 : Word).toNat % 64) + (-1824 : Word) =
        BitVec.ofNat 64 (0x1000 + 4 * (ctabIdx + 8 * c.ck)) := by
      have hk : c.ck ≤ 8 := hck
      generalize c.ck = k at hk ⊢
      unfold ctabIdx
      interval_cases k <;> decide
    rw [e2, even_andNot1' _ (by omega)]
    unfold startPc; simp

/-- `jr ra` (`ctab` slot 8 or `ck_done`): the return to the transition copy's leaf-pk block. -/
theorem ret_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2) (p : Nat)
    (hp : p < 209920) (hrun : vrun p 2 = some retR) (s : MachineState) (hpc : s.pc = pcOf p)
    (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x) :
    ∃ u, Steps vimage s 1 1 u ∧ (∀ x, u.getReg x = s.getReg x) ∧ (∀ A, u.getMem A = s.getMem A) ∧
      u.pc = pcOf c.ret := by
  have hst := piece_steps hrun hp s hpc (by simp [retR])
  have h1 : s.getReg .x1 = pcOf c.ret := (hR .x1 (by decide)).trans (hk (.x1, pcOf c.ret) (by simp [known]))
  refine ⟨retR.toState s, hst, fun x => retR_keeps.reg s (by simp), fun A => rfl, ?_⟩
  rw [Result.toState_pc]
  simp only [retR, E.eval, BinOp.eval, h1]
  exact even_andNot1' _ (by have := hc.2.2.2.2.2.2.2.1; omega)

/-- The checksum chain's end (`ck_done: jr ra`). -/
theorem ckdone_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hrun : vrun ckDone 2 = some retR) (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 42 acc s) :
    ∃ u, Steps vimage s 1 1 u ∧ c.ChainOut s0 43 acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, -, hpc⟩ := hs
  obtain ⟨u, hst, hreg, hmem, hpcu⟩ := c.ret_step hc hk ckDone (by decide) hrun s (by rw [hpc]; rfl) hR
  refine ⟨u, hst, ⟨⟨fun x hx => (hreg x).trans (hR x hx), fun A hA hn => (hmem _).trans (hF A hA hn),
    fun j hj => ?_⟩, hlen, hpcu⟩⟩
  exact ⟨(hmem _).trans (hS j hj).1, (hmem _).trans (hS j hj).2⟩

/-- No checksum chain (`t4 = 8`, the top layer): `ctab` slot 8 returns. -/
theorem ck8_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h8 : c.ck = 8) (hrun : vrun (ctabIdx + 64) 2 = some retR) (acc : List Digest) (s : MachineState)
    (hs : c.ChainIn s0 42 acc s) : ∃ u, Steps vimage s 1 1 u ∧ c.ChainOut s0 42 acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, -, hpc⟩ := hs
  obtain ⟨u, hst, hreg, hmem, hpcu⟩ := c.ret_step hc hk (ctabIdx + 64) (by decide) hrun s
    (by rw [hpc]; unfold startPc; simp [h8]) hR
  refine ⟨u, hst, ⟨⟨fun x hx => (hreg x).trans (hR x hx), fun A hA hn => (hmem _).trans (hF A hA hn),
    fun j hj => ?_⟩, hlen, hpcu⟩⟩
  exact ⟨(hmem _).trans (hS j hj).1, (hmem _).trans (hS j hj).2⟩

end LCtx

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart19

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart20

/-! # V1 chains: the simulation judgment for one chain and for all chains of a lower-code run

From `ChainIn c s0 i` (code chain `i`'s code start: its `ttab` slot for `A = 3t`, the shared block for `B`, `C`,
`ctab[t4]` for the checksum chain 42) the machine performs Core's `chainP` with the block's pads and witness value
(`GoodQ` of V2's `Judg`), then the dispatch of the next triple (`ChainNext`).

Cycle cost of code chain `i` at digit `d` (`chainCost`): V1: the table heads load their digit header and land on the first rung's `ecall`, `69 - 9 d`
(max-digit copy 6, checksum copy 5); T3X inline heads (`B`, `C`) load their header from the image table and cost
`68 - 9 d` (max-digit copy 4); then the dispatch after `C` (`xCost`: 4, after triple 13: 3) and after chain 42 the
return (1). (Cost split of erickeigen 59cbf8ec.) -/

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace LCtx

/-! ## The kernel checks at a context -/

theorem kOf_digits (c : LCtx) (t : Nat) (ht : t < 14) :
    c.kOf t % 8 = c.dig (3 * t) ∧ c.kOf t / 8 % 8 = c.dig (3 * t + 1) ∧ c.kOf t / 64 = c.dig (3 * t + 2) := by
  unfold kOf
  have h0 : c.dig (3 * t) < 8 := by unfold dig; split_ifs <;> omega
  have h1 : c.dig (3 * t + 1) < 8 := by unfold dig; split_ifs <;> omega
  have h2 : c.dig (3 * t + 2) < 8 := by unfold dig; split_ifs <;> omega
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem dig_lt8 (c : LCtx) (i : Nat) (hi : i < 42) : c.dig i < 8 := by unfold dig; split_ifs <;> omega

/-- The shared block of triple `i / 3` is checked. -/
theorem blk_at (c : LCtx) (i : Nat) (hi : i < 42) :
    blkCheck (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2)) = true :=
  blkCheck_at _ _ _ (by omega) (c.dig_lt8 _ (by omega)) (c.dig_lt8 _ (by omega))

theorem chk_headJ (c : LCtx) (i : Nat) (hi : i < 42) (h0 : i % 3 = 0) (hd : c.dig i < 7) :
    vrun (c.startPc i) 7 = some (headJH .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i (c.dig i)
      (hSlot i (c.dig i))) ∧
    vrun (c.rungPc i (c.dig i) + landOff (c.dig i)) 1 = some (ecallR (c.rungPc i (c.dig i) + landOff (c.dig i))) := by
  obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t := ⟨i / 3, by omega⟩
  have et : 3 * t / 3 = t := by omega
  have he := entCheck_at t (c.kOf t) (by omega) (c.kOf_lt t (by omega))
  obtain ⟨k1, k2, k3⟩ := c.kOf_digits t (by omega)
  unfold entCheck at he
  rw [k1, k2, k3, if_neg (by omega), Bool.and_eq_true] at he
  have hs : c.startPc (3 * t) = entW t (c.kOf t) := by
    unfold startPc; rw [if_neg (by omega), if_pos h0, et]
  have hr : c.rungPc (3 * t) (c.dig (3 * t)) = triBase t (c.dig (3 * t + 1)) (c.dig (3 * t + 2)) + 2 * c.dig (3 * t) := by
    unfold rungPc tb; rw [if_neg (by omega), if_pos h0, et]
  rw [hs, hr]
  exact ⟨rOK_eq he.1, rOK_eq he.2⟩

theorem chk_copyJ (c : LCtx) (i : Nat) (hi : i < 42) (h0 : i % 3 = 0) (hd : c.dig i = 7) :
    vrun (c.startPc i) 7 = some (copyN .x22 (offL i) (slotL i) (c.endPc i)) := by
  obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t := ⟨i / 3, by omega⟩
  have et : 3 * t / 3 = t := by omega
  have he := entCheck_at t (c.kOf t) (by omega) (c.kOf_lt t (by omega))
  obtain ⟨k1, k2, k3⟩ := c.kOf_digits t (by omega)
  unfold entCheck at he
  rw [k1, k2, k3, if_pos hd] at he
  have hs : c.startPc (3 * t) = entW t (c.kOf t) := by
    unfold startPc; rw [if_neg (by omega), if_pos h0, et]
  have hq : c.endPc (3 * t) = pcB t (c.dig (3 * t + 1)) (c.dig (3 * t + 2)) := by
    unfold endPc tB; rw [if_neg (by omega), if_pos h0, et]
  rw [hs, hq]
  exact rOK_eq he

/-- The inline part (`B`, `C`) check of chain `i` at its digit. -/
theorem part_at (c : LCtx) (i : Nat) (hi : i < 42) (h0 : i % 3 ≠ 0) :
    partOK i (c.dig i) (c.startPc i) = true := by
  obtain ⟨t, r, rfl, hr⟩ : ∃ t r, i = 3 * t + r ∧ r < 3 := ⟨i / 3, i % 3, by omega, by omega⟩
  have et : (3 * t + r) / 3 = t := by omega
  have hb := c.blk_at (3 * t + r) hi
  rw [et] at hb
  unfold blkCheck at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨-, hB⟩, hC⟩, -⟩ := hb
  unfold startPc tB tC
  rw [if_neg (by omega), et, if_neg (by omega)]
  rcases (show r = 1 ∨ r = 2 by omega) with rfl | rfl
  · rw [if_pos (by omega)]; exact hB
  · rw [if_neg (by omega)]; exact hC

theorem chk_headR (c : LCtx) (i : Nat) (hi : i < 42) (h0 : i % 3 ≠ 0) (hd : c.dig i < 7) :
    vrun (c.startPc i) 8 =
      some (headRH .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i) := by
  have hp := c.part_at i hi h0
  unfold partOK at hp
  rw [if_neg (by omega), Bool.and_eq_true] at hp
  exact rOK_eq hp.1

theorem chk_copyF (c : LCtx) (i : Nat) (hi : i < 42) (h0 : i % 3 ≠ 0) (hd : c.dig i = 7) :
    vrun (c.startPc i) 4 = some (copyFH .x22 (offL i) (slotL i) (c.startPc i)) := by
  have hp := c.part_at i hi h0
  unfold partOK at hp
  rw [if_pos hd] at hp
  exact rOK_eq hp

theorem rungPc_inline (c : LCtx) (i : Nat) (hi : i < 42) (h0 : i % 3 ≠ 0) :
    c.rungPc i (c.dig i) = c.startPc i + 4 := by
  simp only [rungPc, startPc, show i ≠ 42 by omega, h0, if_false]
  split_ifs <;> omega

theorem chk_rung (c : LCtx) (i m : Nat) (hi : i < 42) (hm : c.dig i ≤ m) (hm6 : m ≤ 6)
    (hfirst : i % 3 ≠ 0 → c.dig i < m) :
    vrun (c.rungPc i m) 3 = some (rungR m (if m = 6 then some (slotL i) else none) (c.rungPc i m)) := by
  by_cases h0 : i % 3 = 0
  · obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t := ⟨i / 3, by omega⟩
    have et : 3 * t / 3 = t := by omega
    have hb := c.blk_at (3 * t) hi
    rw [et] at hb
    unfold blkCheck at hb
    simp only [Bool.and_eq_true] at hb
    have := List.all_eq_true.mp hb.1.1.1 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    have hr : c.rungPc (3 * t) m = triBase t (c.dig (3 * t + 1)) (c.dig (3 * t + 2)) + 2 * m := by
      unfold rungPc tb; rw [if_neg (by omega), if_pos h0, et]
    rw [hr]
    simpa using rOK_eq this
  · have hp := c.part_at i hi h0
    have hd := hfirst h0
    unfold partOK at hp
    rw [if_neg (by have := c.dig_lt8 i hi; omega), Bool.and_eq_true] at hp
    have := List.all_eq_true.mp hp.2 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    have hr : c.rungPc i m = c.startPc i + 6 + 2 * (m - (c.dig i + 1)) := by
      simp only [rungPc, startPc, show i ≠ 42 by omega, h0, if_false]
      split_ifs <;> omega
    rw [hr]
    exact rOK_eq this

end LCtx

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace LCtx

/-! ## The checksum chain's checks -/

theorem ck_parts : (∀ c, c < 7 → vrun (ctabIdx + 8 * c) 7 =
      some (headJH .x22 (offL 42) (ckR0 + 2 * c + landOff c) 42 c (hSlot 42 c)) ∧
      vrun (ckR0 + 2 * c + landOff c) 1 = some (ecallR (ckR0 + 2 * c + landOff c))) ∧
    vrun (ctabIdx + 56) 6 = some (copyN .x22 (offL 42) (slotL 42) ckDone) ∧
    vrun (ctabIdx + 64) 2 = some retR ∧
    (∀ m, m < 7 → vrun (ckR0 + 2 * m) 3 = some (rungR m (if m = 6 then some (slotL 42) else none) (ckR0 + 2 * m))) ∧
    vrun ckDone 2 = some retR := by
  have h := ckCheck_ok
  unfold ckCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun c hc => by
      have h1c := List.all_eq_true.mp h1 c (List.mem_range.mpr hc)
      rw [Bool.and_eq_true] at h1c
      exact ⟨rOK_eq h1c.1, rOK_eq h1c.2⟩, rOK_eq h2, rOK_eq h3,
    fun m hm => ?_, rOK_eq h5⟩
  have := List.all_eq_true.mp h4 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  simpa using rOK_eq this

/-- Every rung after the first of a chain is checked (chain 42: the `ck_r*` rungs). -/
theorem chk_rung' (c : LCtx) (i m : Nat) (hi : i ≤ 42) (hm : c.dig i < m) (hm6 : m ≤ 6) (hm1 : 1 ≤ m)
    (hck : i = 42 → c.ck < 8) :
    vrun (c.rungPc i m) 3 = some (rungR m (if m = 6 then some (slotL i) else none) (c.rungPc i m)) := by
  by_cases h42 : i = 42
  · subst h42
    have := ck_parts.2.2.2.1 m (by omega)
    have hr : c.rungPc 42 m = ckR0 + 2 * m := by unfold rungPc; simp
    rw [hr]; exact this
  · exact c.chk_rung i m (by omega) (by omega) hm6 (fun _ => hm)

/-! ## The abstract chain steps -/

/-- Steps `m .. 6` of code chain `i` from the value `v`, with the block's pads (Core's fold). -/
def rest (c : LCtx) (i m : Nat) (v : Digest) : M Digest :=
  (List.range' m (7 - m)).foldlM
    (fun v step => shortHash (chainInputP c.lay c.tree c.leaf (i + c.koff) step (c.pad0 i) (c.pad1 i) v)) v

theorem rest_succ (c : LCtx) (i m : Nat) (h : m ≤ 6) (v : Digest) :
    c.rest i m v =
      shortHash (chainInputP c.lay c.tree c.leaf (i + c.koff) m (c.pad0 i) (c.pad1 i) v) >>= c.rest i (m + 1) := by
  unfold rest
  rw [show 7 - m = (7 - (m + 1)) + 1 by omega, List.range'_succ, List.foldlM_cons]

theorem rest_7 (c : LCtx) (i : Nat) (v : Digest) : c.rest i 7 v = pure v := rfl

theorem chainP_rest (c : LCtx) (i d : Nat) (v : Digest) :
    chainP c.lay c.tree c.leaf (i + c.koff) d (7 - d) (c.pad0 i) (c.pad1 i) v = c.rest i d v := rfl

theorem chainInputP_pad (lay : Layer) (tree leaf i step : Nat) (p0 p1 v : Digest) :
    pad64 (chainInputP lay tree leaf i step p0 p1 v) = chainInputP lay tree leaf i step p0 p1 v :=
  pad64_of_aligned _ (by rw [chainInputP_length])

theorem chainInputP_blocks (lay : Layer) (tree leaf i step : Nat) (p0 p1 v : Digest) :
    (toQ (chainInputP lay tree leaf i step p0 p1 v)).blocks = 1 := by
  rw [blocks_toQ ⟨by rw [chainInputP_length]; omega, by rw [chainInputP_length]⟩, chainInputP_length]

/-! ## Code bounds -/

theorem triBaseTab_all : (triBaseTab.all fun x => decide (x < 82100)) = true := by decide +kernel

theorem triBase_lt (t dB dC : Nat) : triBase t dB dC < 82100 := by
  unfold triBase
  rw [List.getD_eq_getElem?_getD]
  cases hn : triBaseTab[64 * t + 8 * dB + dC]? with
  | none => simp
  | some x => simpa using List.all_eq_true.mp triBaseTab_all x (List.mem_of_getElem? hn)

theorem partLen_le (d : Nat) : partLen d ≤ 20 := by unfold partLen; split <;> omega

theorem tX_lt (c : LCtx) (i : Nat) : c.tX i < 82200 := by
  have := triBase_lt (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
  have := partLen_le (c.dig (3 * (i / 3) + 1)); have := partLen_le (c.dig (3 * (i / 3) + 2))
  unfold tX pcX pcC pcB; omega

theorem startPc_lt (c : LCtx) (i : Nat) (hi : i ≤ 42) (hck : c.ck ≤ 8) : c.startPc i < 209920 := by
  unfold startPc
  split_ifs with h1 h2 h3
  · unfold ctabIdx; omega
  · have := c.kOf_lt (i / 3) (by omega); unfold entW ttabIdx; omega
  · have := triBase_lt (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
    unfold tB pcB; omega
  · have := triBase_lt (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
    have := partLen_le (c.dig (3 * (i / 3) + 1))
    unfold tC pcC pcB; omega

theorem rungPc_land_lt (c : LCtx) (i m : Nat) (hm : m ≤ 6) : c.rungPc i m + landOff m < 209920 := by
  have := triBase_lt (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
  have := partLen_le (c.dig (3 * (i / 3) + 1))
  unfold rungPc tb tB tC pcC pcB landOff
  split_ifs <;> (try unfold ckR0) <;> omega

theorem rungPc_lt (c : LCtx) (i m : Nat) (hm : m ≤ 6) : c.rungPc i m < 209920 := by
  have := triBase_lt (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
  have := partLen_le (c.dig (3 * (i / 3) + 1))
  unfold rungPc tb tB tC pcC pcB
  split_ifs <;> (try unfold ckR0) <;> omega

/-! ## After a chain: the next chain's code, the dispatch, or the return -/

/-- The state before code chain `j` (`j ≤ 42`), or after the chain code's return (`j = 43`). -/
def ChainNext (c : LCtx) (s0 : MachineState) (j : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  if j ≤ 42 then c.ChainIn s0 j acc s else c.ChainOut s0 43 acc s

/-- The dispatch after code chain `i`: after a triple's `C` 4 (after triple 13: 3), after chain 42 the return 1. -/
def xCost (i : Nat) : Nat := if i = 42 then 1 else if i % 3 = 2 then (if i = 41 ∨ i = 2 ∨ i = 23 then 3 else 4) else 0

theorem xCost_le (i : Nat) : xCost i ≤ 4 := by unfold xCost; split_ifs <;> omega

theorem end_next (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2) (i : Nat)
    (hi : c.i0 ≤ i ∧ i ≤ 42) (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) :
    ∃ u, Steps vimage s (xCost i) (xCost i) u ∧ c.ChainNext s0 (i + 1) acc u := by
  by_cases h42 : i = 42
  · subst h42
    obtain ⟨u, hst, hu⟩ := c.ckdone_step hc hk ck_parts.2.2.2.2 acc s hs
    refine ⟨u, by simpa [xCost] using hst, ?_⟩
    unfold ChainNext; rw [if_neg (by omega)]; exact hu
  · by_cases h2 : i % 3 = 2
    · by_cases h41 : i = 41
      · subst h41
        have hx := c.blk_at 41 (by omega)
        unfold blkCheck xOK at hx
        simp only [Bool.and_eq_true] at hx
        have hrun : vrun (c.tX 41) 4 = some ctabX := by
          have := rOK_eq hx.2; exact this
        obtain ⟨u, hst, hu⟩ := c.x13_step hc hk (by omega) (by have := c.tX_lt 41; omega) hrun acc s hs
        refine ⟨u, by simpa [xCost] using hst, ?_⟩
        unfold ChainNext; rw [if_pos (by omega)]; exact hu
      · obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t + 2 := ⟨i / 3, by omega⟩
        have hx := c.blk_at (3 * t + 2) (by omega)
        rw [show (3 * t + 2) / 3 = t by omega] at hx
        unfold blkCheck xOK at hx
        simp only [Bool.and_eq_true] at hx
        rw [if_neg (by omega)] at hx
        have hrun := rOK_eq hx.2
        have htx : c.tX (3 * t + 2) = pcX t (c.dig (3 * t + 1)) (c.dig (3 * t + 2)) := by
          unfold tX; rw [show (3 * t + 2) / 3 = t by omega]
        rw [← htx] at hrun
        obtain ⟨u, hst, hu⟩ := c.x_step hc hk t (by omega) hi.1 (by have := c.tX_lt (3 * t + 2); omega) hrun acc s hs
        have he : (9 * ((t + 1) % 7) = 9) ↔ (3 * t + 2 = 2 ∨ 3 * t + 2 = 23) := by omega
        refine ⟨u, by simpa [xCost, h42, h41, he] using hst, ?_⟩
        unfold ChainNext; rw [if_pos (by omega), show 3 * t + 2 + 1 = 3 * t + 3 by ring]; exact hu
    · refine ⟨s, by simpa [xCost, h42, h2] using Steps.refl s, ?_⟩
      unfold ChainNext; rw [if_pos (by omega)]
      exact c.next_inline s0 i (by omega) h2 acc s hs

end LCtx

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace LCtx

/-- Cycles from just before step `m`'s `ecall` to the chain's last hash. -/
def preCost (m : Nat) : Nat := 8 + 9 * (6 - m) + (if m < 6 then 1 else 0)

/-- **The steps of a chain** from `PreHash` at step `m`: Core's remaining fold, then the dispatch. -/
theorem steps_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hck : i = 42 → c.ck < 8) (acc : List Digest)
    (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ v t, c.ChainNext s0 (i + 1) (acc ++ [v]) t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K (acc ++ [v]))) :
    ∀ k m, m + k = 6 → c.dig i ≤ m → ∀ v s, c.PreHash s0 i acc m v s →
      SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N + 3 * (7 - m) + 4) (C + preCost m + xCost i) Q (A + preCost m + xCost i)
        (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM (c.rest i m v) (fun v => K (acc ++ [v]))) := by
  have hrc : ∀ m, m ≤ 6 → c.rungPc i m < 209920 := fun m hm => c.rungPc_lt i m hm
  have hx4 := xCost_le i
  intro k
  induction k with
  | zero =>
    intro m hm hd v s hs
    obtain rfl : m = 6 := by omega
    obtain ⟨h5, hv, hin, hpost⟩ := c.prehash_step hc s0 hk h0 i 6 hi (le_refl _) hd acc v s hs
    rw [rest_succ c i 6 (le_refl _)]
    have hf := hs.2.2.2.2.2.2.2.2.2
    have H : ∀ a : BitVec 256, SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ (writeHash s a) (N + xCost i) (C + xCost i) Q (A + xCost i)
        (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM (c.rest i 7 (a.extractLsb' 0 128)) (fun v => K (acc ++ [v]))) := by
      intro a
      rw [rest_7, SigGolfCandidate.T3M.CanonicalPort.Verify.ccM_pure]
      obtain ⟨u, hu, hn⟩ := c.end_next hc hk i hi _ _ ((hpost a).2 rfl)
      exact SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hu (hK _ _ hn) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
    have h3 := SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.shortHash_bind (f := c.rest i 7) (K := fun v => K (acc ++ [v])) hf h5 hv
      (by rw [chainInputP_pad]; exact hin) H
    rw [chainInputP_pad, chainInputP_blocks] at h3
    exact h3.mono (by omega) (by simp [preCost]; omega) (fun hq => ⟨hq, by simp [preCost]; omega⟩)
  | succ k ih =>
    intro m hm hd v s hs
    obtain ⟨h5, hv, hin, hpost⟩ := c.prehash_step hc s0 hk h0 i m hi (by omega) hd acc v s hs
    rw [rest_succ c i m (by omega)]
    have hf := hs.2.2.2.2.2.2.2.2.2
    have H : ∀ a : BitVec 256, SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ (writeHash s a) (N + 3 * (7 - (m + 1)) + 4 + 2)
        (C + preCost (m + 1) + xCost i + (if m + 1 = 6 then 2 else 1)) Q
        (A + preCost (m + 1) + xCost i + (if m + 1 = 6 then 2 else 1))
        (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM (c.rest i (m + 1) (a.extractLsb' 0 128)) (fun v => K (acc ++ [v]))) := by
      intro a
      have hrun := c.chk_rung' i (m + 1) hi.2 (by omega) (by omega) (by omega) hck
      obtain ⟨u, hu, hp⟩ := c.rung_step hc hk i (m + 1) hi (by omega) (hrc _ (by omega)) hrun acc _ _
        ((hpost a).1 (by omega))
      have := ih (m + 1) (by omega) (by omega) _ _ hp
      exact SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hu this (by split <;> omega) (by omega) (fun hq => ⟨hq, by omega⟩)
    have h3 := SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.shortHash_bind (f := c.rest i (m + 1)) (K := fun v => K (acc ++ [v])) hf h5 hv
      (by rw [chainInputP_pad]; exact hin) H
    rw [chainInputP_pad, chainInputP_blocks] at h3
    refine h3.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
    · unfold preCost
      by_cases h6 : m + 1 = 6
      · rw [if_pos h6, if_neg (by omega), if_pos (by omega)]; omega
      · rw [if_neg h6, if_pos (by omega), if_pos (by omega)]; omega
    · unfold preCost
      by_cases h6 : m + 1 = 6
      · rw [if_pos h6, if_neg (by omega), if_pos (by omega)]; omega
      · rw [if_neg h6, if_pos (by omega), if_pos (by omega)]; omega

end LCtx

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace LCtx

/-- Cycle cost of code chain `i` at digit `d`, including the dispatch after it. -/
def chainCost (i d : Nat) : Nat :=
  (if i % 3 = 0 then (if d = 7 then (if i = 42 then 5 else 6) else 69 - 9 * d)
   else (if d = 7 then 4 else 68 - 9 * d)) + xCost i

theorem dig42 (c : LCtx) : c.dig 42 = c.ck := by unfold dig; simp

/-- **One code chain**: from `ChainIn` to the next chain (or the return), Core's `chainP` with the block's
pads and witness value. -/
theorem chain_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hko : c.i0 = 0 → c.koff = 0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hck : i = 42 → c.ck < 8)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ v t, c.ChainNext s0 (i + 1) (acc ++ [v]) t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K (acc ++ [v])))
    (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N + 40) (C + chainCost i (c.dig i)) Q (A + chainCost i (c.dig i))
      (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM (chainP c.lay c.tree c.leaf (i + c.koff) (c.dig i) (7 - c.dig i) (c.pad0 i) (c.pad1 i) (c.val i))
        (fun v => K (acc ++ [v]))) := by
  have hx4 := xCost_le i
  have hdl : c.dig i < 8 := by
    by_cases h42 : i = 42
    · subst h42; rw [dig42]; exact hck rfl
    · exact c.dig_lt8 i (by omega)
  have hsp := c.startPc_lt i hi.2 hc.2.2.2.2.2.2.1
  by_cases h7 : c.dig i = 7
  · -- the max-digit copy
    rw [h7, show 7 - 7 = 0 from rfl]
    have hspec : chainP c.lay c.tree c.leaf (i + c.koff) 7 0 (c.pad0 i) (c.pad1 i) (c.val i) = pure (c.val i) := rfl
    rw [hspec, SigGolfCandidate.T3M.CanonicalPort.Verify.ccM_pure]
    by_cases h42 : i = 42
    · subst h42
      have hrun : vrun (c.startPc 42) 6 = some (copyN .x22 (offL 42) (slotL 42) (c.endPc 42)) := by
        have := ck_parts.2.1
        rw [dig42] at h7
        unfold startPc endPc; simp only [if_true, h7]; exact this
      obtain ⟨t, hst, hE⟩ := c.copyN_step hc hk h0 hi.1 hsp hrun acc s hs
      obtain ⟨u, hu, hn⟩ := c.end_next hc hk 42 hi _ _ hE
      refine SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hst (SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hu (hK _ u hn) (le_refl _) (le_refl _)
        (fun hq => ⟨hq, le_refl _⟩)) (by omega) (by unfold chainCost; simp; omega) (fun hq => ⟨hq, by unfold chainCost; simp; omega⟩)
    · by_cases h0' : i % 3 = 0
      · have hrun := c.chk_copyJ i (by omega) h0' h7
        obtain ⟨t, hst, hE⟩ := c.copyJ_step hc hk h0 i ⟨hi.1, by omega⟩ (i / 3 == 0)
          (fun h => by
            have : i = 0 := by simp at h; omega
            exact ⟨this, hko (by omega)⟩)
          (fun h => by simp at h; omega) hsp hrun acc s hs
        obtain ⟨u, hu, hn⟩ := c.end_next hc hk i hi _ _ hE
        refine SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hst (SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hu (hK _ u hn) (le_refl _) (le_refl _)
          (fun hq => ⟨hq, le_refl _⟩)) (by omega) (by unfold chainCost; simp [h0', h7, h42]; omega)
          (fun hq => ⟨hq, by unfold chainCost; simp [h0', h7, h42]; omega⟩)
      · have hrun := c.chk_copyF i (by omega) h0' h7
        have hend : c.startPc i + 4 = c.endPc i := by
          simp only [startPc, endPc, if_neg h42, if_neg h0']
          by_cases h1 : i % 3 = 1
          · have e1 : c.dig (3 * (i / 3) + 1) = 7 := by rw [show 3 * (i / 3) + 1 = i by omega, h7]
            rw [if_pos h1, if_pos h1]; unfold tB tC pcC; rw [e1]; rfl
          · have e2 : c.dig (3 * (i / 3) + 2) = 7 := by rw [show 3 * (i / 3) + 2 = i by omega, h7]
            rw [if_neg h1, if_neg h1]; unfold tC tX pcX; rw [e2]; rfl
        obtain ⟨t, hst, hE⟩ := c.copyF_step hc hk h0 i ⟨hi.1, by omega⟩ (by omega) hsp hend hrun acc s hs
        obtain ⟨u, hu, hn⟩ := c.end_next hc hk i hi _ _ hE
        refine SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hst (SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hu (hK _ u hn) (le_refl _) (le_refl _)
          (fun hq => ⟨hq, le_refl _⟩)) (by omega) (by unfold chainCost; simp [h0', h7]; omega)
          (fun hq => ⟨hq, by unfold chainCost; simp [h0', h7]; omega⟩)
  · -- a head and its rungs
    have hd : c.dig i < 7 := by omega
    rw [chainP_rest]
    have hsteps := c.steps_good hc hk h0 i hi hck acc K N C A Q hK (6 - c.dig i) (c.dig i) (by omega) (le_refl _)
    have hrp := c.rungPc_lt i (c.dig i) (by omega)
    by_cases h0' : i % 3 = 0
    · have hruns : vrun (c.startPc i) 7 = some (headJH .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i
            (c.dig i) (hSlot i (c.dig i))) ∧
          vrun (c.rungPc i (c.dig i) + landOff (c.dig i)) 1 =
            some (ecallR (c.rungPc i (c.dig i) + landOff (c.dig i))) := by
        by_cases h42 : i = 42
        · subst h42
          have := ck_parts.1 c.ck (by rw [dig42] at hd; exact hd)
          have hst42 : c.startPc 42 = ctabIdx + 8 * c.ck := by unfold startPc; simp
          have hrp42 : c.rungPc 42 (c.dig 42) = ckR0 + 2 * c.ck := by unfold rungPc; simp [dig42]
          rw [hst42, hrp42, dig42]; exact this
        · exact c.chk_headJ i (by omega) h0' hd
      obtain ⟨t, hst, hP⟩ := c.headJ_step hc hk h0 i hi hd hsp (c.rungPc_land_lt i (c.dig i) (by omega))
        hruns.1 hruns.2 acc s hs
      refine SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hst (hsteps _ _ hP) (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
      · unfold chainCost preCost; rw [if_pos h0', if_neg h7]
        split_ifs <;> omega
      · unfold chainCost preCost; rw [if_pos h0', if_neg h7]
        split_ifs <;> omega
    · have hrun := c.chk_headR i (by omega) h0' hd
      obtain ⟨t, hst, hP⟩ := c.headR_step hc hk h0 i ⟨hi.1, by omega⟩ (by omega) hd hsp
        (c.rungPc_inline i (by omega) h0') hrun acc s hs
      refine SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hst (hsteps _ _ hP) (by split <;> omega) ?_ (fun hq => ⟨hq, ?_⟩)
      · unfold chainCost preCost; rw [if_neg h0', if_neg h7]
        by_cases h6 : c.dig i = 6
        · rw [if_pos h6, h6]; norm_num; omega
        · rw [if_neg h6, if_pos (by omega)]; omega
      · unfold chainCost preCost; rw [if_neg h0', if_neg h7]
        by_cases h6 : c.dig i = 6
        · rw [if_pos h6, h6]; norm_num; omega
        · rw [if_neg h6, if_pos (by omega)]; omega

end LCtx

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace LCtx

/-! ## All code chains of a run -/

/-- Core's chain of code chain `i` (with the block's pads and witness value), appended to the ends so far. -/
def chainF (c : LCtx) (ends : List Digest) (i : Nat) : M (List Digest) := do
  let v ← chainP c.lay c.tree c.leaf (i + c.koff) (c.dig i) (7 - c.dig i) (c.pad0 i) (c.pad1 i) (c.val i)
  pure (ends ++ [v])

/-- The cycles of the code chains `i .. i + k - 1`. -/
def chainsCost (c : LCtx) (i k : Nat) : Nat := ((List.range' i k).map fun j => chainCost j (c.dig j)).sum

/-- **The code chains `i .. 41`** from `ChainIn i`, up to `ChainIn 42` (before the checksum dispatch). -/
theorem chains_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hko : c.i0 = 0 → c.koff = 0) (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs)
    (N C A : Nat) (Q : Prop) (hK : ∀ ends t, c.ChainIn s0 42 ends t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K ends)) :
    ∀ k i, i + k = 42 → c.i0 ≤ i → ∀ acc s, c.ChainIn s0 i acc s →
      SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N + 40 * k) (C + c.chainsCost i k) Q (A + c.chainsCost i k)
        (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM ((List.range' i k).foldlM c.chainF acc) K) := by
  intro k
  induction k with
  | zero =>
    intro i hik _ acc s hs
    obtain rfl : i = 42 := by omega
    simpa [chainsCost] using hK acc s hs
  | succ k ih =>
    intro i hik hi0 acc s hs
    rw [List.range'_succ, List.foldlM_cons]
    simp only [chainF, bind_assoc, pure_bind, SigGolfCandidate.T3M.CanonicalPort.Verify.ccM_bind]
    have := c.chain_good hc hk h0 hko i ⟨hi0, by omega⟩ (fun h => absurd h (by omega)) acc
      (fun ends => SigGolfCandidate.T3M.CanonicalPort.Verify.ccM ((List.range' (i + 1) k).foldlM c.chainF ends) K)
      (N + 40 * k) (C + c.chainsCost (i + 1) k) (A + c.chainsCost (i + 1) k) Q
      (fun v t ht => by
        have ht' : c.ChainIn s0 (i + 1) (acc ++ [v]) t := by
          unfold ChainNext at ht; rwa [if_pos (by omega)] at ht
        exact ih (i + 1) (by omega) (by omega) (acc ++ [v]) t ht') s hs
    refine this.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
    · simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons]; omega
    · simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons]; omega

/-- **The checksum chain and the return** (`ck < 8`), from `ChainIn 42`. -/
theorem ck_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hko : c.i0 = 0 → c.koff = 0) (hck : c.ck < 8)
    (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t, c.ChainOut s0 43 ends t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K ends))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 42 acc s) :
    SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N + 40) (C + chainCost 42 c.ck) Q (A + chainCost 42 c.ck)
      (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM (c.chainF acc 42) K) := by
  have := c.chain_good hc hk h0 hko 42 ⟨hc.2.2.2.2.2.2.2.2, le_refl _⟩ (fun _ => hck) acc K N C A Q
    (fun v t ht => by
      have ht' : c.ChainOut s0 43 (acc ++ [v]) t := by unfold ChainNext at ht; rwa [if_neg (by omega)] at ht
      exact hK _ t ht') s hs
  simp only [chainF, SigGolfCandidate.T3M.CanonicalPort.Verify.ccM_bind, SigGolfCandidate.T3M.CanonicalPort.Verify.ccM_pure]
  rw [dig42] at this ⊢
  exact this

/-- **No checksum chain** (`ck = 8`, the top layer's run of the code chains 33..41): `ctab[8]` returns. -/
theorem ck8_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h8 : c.ck = 8) (X : OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs) (N C A : Nat) (Q : Prop) (acc : List Digest)
    (hK : ∀ t, c.ChainOut s0 42 acc t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A X)
    (s : MachineState) (hs : c.ChainIn s0 42 acc s) : SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N + 1) (C + 1) Q (A + 1) X := by
  obtain ⟨u, hst, hu⟩ := c.ck8_step hc hk h8 ck_parts.2.2.1 acc s hs
  exact SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps hst (hK u hu)

end LCtx

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace LCtx

/-! ## The cost of the chain phase -/

/-- The digit-independent cost of code chain `i` (as if no digit were maximal). -/
def cbase (i : Nat) : Nat := (if i % 3 = 0 then 69 else 68) + xCost i

/-- The saving of a maximal digit (the copy instead of a head and the last rung): 1, the checksum chain 2. -/
def zc (i d : Nat) : Nat := if d = 7 then (if i = 42 then 1 else if i % 3 = 0 then 0 else 1) else 0

theorem chainCost_add (i d : Nat) (hd : d < 8) : chainCost i d + 9 * d + zc i d = cbase i := by
  unfold chainCost zc cbase
  by_cases h7 : d = 7
  · subst h7
    by_cases h42 : i = 42
    · subst h42; simp [xCost]
    · by_cases h0 : i % 3 = 0
      · simp [h0, h42]; omega
      · simp [h0, h42]; omega
  · split_ifs <;> omega

theorem chainsCost_add (c : LCtx) (hck : c.ck < 8) : ∀ k i, i + k ≤ 43 →
    c.chainsCost i k + 9 * ((List.range' i k).map c.dig).sum + ((List.range' i k).map fun j => zc j (c.dig j)).sum =
      ((List.range' i k).map cbase).sum := by
  intro k
  induction k with
  | zero => intro i _; simp [chainsCost]
  | succ k ih =>
    intro i hik
    have h := ih (i + 1) (by omega)
    have hd : c.dig i < 8 := by
      by_cases h42 : i = 42
      · subst h42; rw [dig42]; exact hck
      · exact c.dig_lt8 i (by omega)
    have := chainCost_add i (c.dig i) hd
    simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons] at h ⊢
    omega

theorem cbase_sum43 : ((List.range' 0 43).map cbase).sum = 2993 := by decide
theorem cbase_sum_top : ((List.range' 33 9).map cbase).sum = 626 := by decide

/-- The weighted number of maximal digits of the code chains `i .. i + k - 1`. -/
def zSum (c : LCtx) (i k : Nat) : Nat := ((List.range' i k).map fun j => zc j (c.dig j)).sum

/-- **The chain phase of a lower layer**: `2993 - 9 target - Z` (the 43 digits sum to the target). -/
theorem chainsCost_lower (c : LCtx) (hck : c.ck < 8) (T : Nat) (hT : ((List.range' 0 43).map c.dig).sum = T) :
    c.chainsCost 0 42 + chainCost 42 c.ck + 9 * T + c.zSum 0 43 = 2993 := by
  have h := c.chainsCost_add hck 43 0 (le_refl _)
  rw [hT, cbase_sum43] at h
  have e : c.chainsCost 0 43 = c.chainsCost 0 42 + chainCost 42 c.ck := by
    unfold chainsCost
    rw [show (43 : Nat) = 42 + 1 from rfl, List.range'_concat, List.map_append, List.sum_append]
    simp [dig42]
  unfold zSum
  omega

/-- **The top layer's code chains 33..41** (the radix-8 chains 49..57) and the return: `626 + 1 - 9 S - Z`. -/
theorem chainsCost_top (c : LCtx) (hck : c.ck < 8) (S : Nat) (hS : ((List.range' 33 9).map c.dig).sum = S) :
    c.chainsCost 33 9 + 9 * S + c.zSum 33 9 = 626 := by
  have h := c.chainsCost_add hck 9 33 (by omega)
  rw [hS, cbase_sum_top] at h
  unfold zSum
  omega

end LCtx

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart20

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart21

/-! # The verify image's decode of the encoding answer (stream V1, pure)

The transition of layer `lay` hashes the encoding block and decodes the 128-bit answer `value` held in the
doublewords `v0 = value % 2^64` (`a6`) and `v1 = value / 2^64` (`a7`) by straight-line SWAR code
(`t3m/ver/gen_t3.py`, `decode_lower`, `decode_top`):

* **lower layers** (radix 8, 42 data digits + the checksum digit): reject unless `v1 >>> 62 = 0`
  (`value < 2^126`); `a = v0`, `b = v1 <<< 1`; `s9 = ((a >>> 3) &&& M1) + (a &&& M1) + ((b >>> 3) &&& M1) +
  (b &&& M1)`, `s9 += s9 >>> 6`, `s9 &&& M2`, `remu 4095` = the sum of the 42 digits (`lowSwar_digits`;
  digit 21 straddles bit 63: its low bit is lane 10 of `a >>> 3`); the checksum digit `c = target - sum`
  (64-bit wrap), reject unless `c < 8` (`sltiu`);
* **top layer** (49 radix-4 digits + 9 radix-8 digits): reject unless `v1 >>> 61 = 0` (`value < 2^125`);
  3-bit SWAR on `g = v1 >>> 34` (`remu 4095`), 2-bit SWAR on `v0` and `v1 % 2^34` with the masks `M4`, `M8`
  (`remu 255`); reject unless the total is 125 (`topSwar_digits`).

`decode_lower_iff` / `decode_top_iff` state that the machine's decision and digits are Core's `decode`. -/

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.T3

/-! ## Lane splitting of `&&&` (Nat level) -/

theorem land_split (n M w s : Nat) (hws : w ≤ s) :
    n &&& (2 ^ s * M + (2 ^ w - 1)) = 2 ^ s * ((n / 2 ^ s) &&& M) + n % 2 ^ w := by
  have hw : 2 ^ w - 1 < 2 ^ s := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hws
    have : 0 < 2 ^ w := Nat.two_pow_pos _
    omega
  have hm : n % 2 ^ w < 2 ^ s := lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) hws)
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, Nat.testBit_two_pow_mul_add _ hw, Nat.testBit_two_pow_mul_add _ hm]
  split
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    cases n.testBit j <;> simp
  · rw [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]

theorem split3 (n M : Nat) : n &&& (64 * M + 7) = 64 * ((n / 64) &&& M) + n % 8 :=
  land_split n M 3 6 (by decide)
theorem split6 (n M : Nat) : n &&& (4096 * M + 63) = 4096 * ((n / 4096) &&& M) + n % 64 :=
  land_split n M 6 12 (by decide)
theorem split2 (n M : Nat) : n &&& (16 * M + 3) = 16 * ((n / 16) &&& M) + n % 4 :=
  land_split n M 2 4 (by decide)
theorem split4 (n M : Nat) : n &&& (256 * M + 15) = 256 * ((n / 256) &&& M) + n % 16 :=
  land_split n M 4 8 (by decide)
theorem and7 (n : Nat) : n &&& 7 = n % 8 := Nat.and_two_pow_sub_one_eq_mod n 3
theorem and15 (n : Nat) : n &&& 15 = n % 16 := Nat.and_two_pow_sub_one_eq_mod n 4
theorem and3 (n : Nat) : n &&& 3 = n % 4 := Nat.and_two_pow_sub_one_eq_mod n 2

/-- `0x71C71C71C71C71C7`: the 3-bit fields at bits `6k`, `k ≤ 10` (`s4` of the lower decode). -/
def mask3 : Nat := 8198552921648689607
/-- `0xF03F03F03F03F03F`: the 6-bit fields at bits `12k`, `k ≤ 4`, and bits `60..63` (`s5`). -/
def mask6 : Nat := 17311559823019733055
/-- `0x3333333333333333`: the 2-bit fields at bits `4k` (`s4` of the top decode). -/
def mask2 : Nat := 3689348814741910323
/-- `0x0F0F0F0F0F0F0F0F`: the 4-bit fields at bits `8k` (`s5` of the top decode). -/
def mask4 : Nat := 1085102592571150095

theorem landM1 (n : Nat) : n &&& mask3 =
    64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8)
    + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8)
    + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 / 64 / 64 % 8)
    + n / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 % 8) + n / 64 / 64 % 8) + n / 64 % 8) + n % 8 := by
  rw [show mask3 = 64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * 7 + 7) + 7) + 7) + 7) + 7) + 7) + 7) + 7) + 7) + 7 by
    norm_num [mask3]]
  simp only [split3, and7]

theorem landM2 (n : Nat) : n &&& mask6 =
    4096 * (4096 * (4096 * (4096 * (4096 * (n / 4096 / 4096 / 4096 / 4096 / 4096 % 16)
    + n / 4096 / 4096 / 4096 / 4096 % 64) + n / 4096 / 4096 / 4096 % 64) + n / 4096 / 4096 % 64)
    + n / 4096 % 64) + n % 64 := by
  rw [show mask6 = 4096 * (4096 * (4096 * (4096 * (4096 * 15 + 63) + 63) + 63) + 63) + 63 by norm_num [mask6]]
  simp only [split6, and15]

/-! ## The 3-bit SWAR digit sum (Nat level) -/

/-- The four masked partial sums of the lower decode (64-bit wrapping adds, as the machine adds). -/
def sw1 (a b : Nat) : Nat :=
  ((((a / 8 &&& mask3) + (a &&& mask3)) % 18446744073709551616 + (b / 8 &&& mask3)) % 18446744073709551616 +
    (b &&& mask3)) % 18446744073709551616

/-- The lower decode's digit sum: `x + (x >>> 6)`, `&&& mask6`, `remu 4095`. -/
def lowSwar (a b : Nat) : Nat := ((sw1 a b + sw1 a b / 64) % 18446744073709551616 &&& mask6) % 4095

theorem hdiv64 (c R : Nat) (h : c < 64) : (c + 64 * R) / 64 = R := by omega
theorem hmod64 (c R : Nat) (h : c < 64) : (c + 64 * R) % 64 = c := by omega

theorem landM2' (n : Nat) : n &&& mask6 =
    4096 * (4096 * (4096 * (4096 * (4096 * (n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 16)
    + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 64) + n / 64 / 64 / 64 / 64 / 64 / 64 % 64)
    + n / 64 / 64 / 64 / 64 % 64) + n / 64 / 64 % 64) + n % 64 := by
  rw [landM2]; simp only [Nat.div_div_eq_div_mul]

theorem fold_mod4095 (a b c d e f : Nat) :
    (a + 4096 * (b + 4096 * (c + 4096 * (d + 4096 * (e + 4096 * f))))) % 4095 =
      (a + b + c + d + e + f) % 4095 := by
  omega

/-- The lane sums: eleven 6-bit lanes `L_k` (the 4 partial sums' fields), folded pairwise by `x + x / 64`,
masked to the even lanes and the top 4 bits, reduced mod 4095. -/
theorem swarLanes (L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 : Nat) (h0 : L0 ≤ 28) (h1 : L1 ≤ 28) (h2 : L2 ≤ 28)
    (h3 : L3 ≤ 28) (h4 : L4 ≤ 28) (h5 : L5 ≤ 28) (h6 : L6 ≤ 28) (h7 : L7 ≤ 28) (h8 : L8 ≤ 28) (h9 : L9 ≤ 28)
    (h10 : L10 ≤ 15) (X : Nat)
    (hX : X = L0 + 64 * (L1 + 64 * (L2 + 64 * (L3 + 64 * (L4 + 64 * (L5 + 64 * (L6 + 64 * (L7 + 64 * (L8 +
      64 * (L9 + 64 * L10)))))))))) :
    ((X + X / 64) % 18446744073709551616 &&& mask6) % 4095 =
      L0 + L1 + L2 + L3 + L4 + L5 + L6 + L7 + L8 + L9 + L10 := by
  have e1 : X / 64 = L1 + 64 * (L2 + 64 * (L3 + 64 * (L4 + 64 * (L5 + 64 * (L6 + 64 * (L7 + 64 * (L8 +
      64 * (L9 + 64 * L10)))))))) := by rw [hX]; exact hdiv64 _ _ (by omega)
  have e2 : X + X / 64 = (L0 + L1) + 64 * ((L1 + L2) + 64 * ((L2 + L3) + 64 * ((L3 + L4) + 64 * ((L4 + L5) +
      64 * ((L5 + L6) + 64 * ((L6 + L7) + 64 * ((L7 + L8) + 64 * ((L8 + L9) + 64 * ((L9 + L10) +
      64 * L10))))))))) := by
    omega
  have e3 : X + X / 64 < 18446744073709551616 := by rw [e2]; omega
  have e4 : (X + X / 64) % 18446744073709551616 &&& mask6 = (L0 + L1) + 4096 * ((L2 + L3) + 4096 * ((L4 + L5) +
      4096 * ((L6 + L7) + 4096 * ((L8 + L9) + 4096 * L10)))) := by
    rw [Nat.mod_eq_of_lt e3, e2, landM2']
    simp (disch := omega) only [hdiv64, hmod64]
    rw [Nat.mod_eq_of_lt (show L10 < 16 by omega)]
    omega
  rw [e4]
  clear e1 e2 e3 e4 hX
  have hlt : L0 + L1 + (L2 + L3) + (L4 + L5) + (L6 + L7) + (L8 + L9) + L10 < 4095 := by omega
  rw [fold_mod4095, Nat.mod_eq_of_lt hlt]
  ac_rfl

/-- The 21 radix-8 digits of a doubleword, as explicit terms. -/
def dsum21 (a : Nat) : Nat :=
  a % 8 + a / 8 % 8 + a / 64 % 8 + a / 512 % 8 + a / 4096 % 8 + a / 32768 % 8 + a / 262144 % 8 +
    a / 2097152 % 8 + a / 16777216 % 8 + a / 134217728 % 8 + a / 1073741824 % 8 +
    a / 8589934592 % 8 + a / 68719476736 % 8 + a / 549755813888 % 8 + a / 4398046511104 % 8 +
    a / 35184372088832 % 8 + a / 281474976710656 % 8 + a / 2251799813685248 % 8 +
    a / 18014398509481984 % 8 + a / 144115188075855872 % 8 + a / 1152921504606846976 % 8

theorem dsum21_eq (a : Nat) : dsum21 a = ((List.range 21).map fun i => a / 8 ^ i % 8).sum := by
  simp only [dsum21, List.range, List.range.loop, List.map, List.sum_cons, List.sum_nil]
  norm_num [Nat.add_assoc]

/-- **The lower decode's SWAR sum**: for `a < 2^64` (`v0`) and `b < 2^63` (`v1 <<< 1`), the 21 digits of
`a`, the bit `a / 2^63`, and the 21 digits of `b`. -/
theorem lowSwar_eq (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 63) :
    lowSwar a b = dsum21 a + a / 2 ^ 63 + dsum21 b := by
  have hat : a / 9223372036854775808 ≤ 1 := by omega
  have ha' : a / 9223372036854775808 % 8 = a / 9223372036854775808 := Nat.mod_eq_of_lt (by omega)
  have hb' : b / 9223372036854775808 = 0 := Nat.div_eq_of_lt hb
  unfold lowSwar dsum21
  generalize hX : sw1 a b = X
  unfold sw1 at hX
  simp only [landM1, Nat.div_div_eq_div_mul] at hX
  norm_num at hX
  rw [ha'] at hX
  simp only [hb', Nat.zero_mod, Nat.mul_zero] at hX
  norm_num
  clear ha'
  generalize a / 9223372036854775808 = a21 at *
  have ha0 : a % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a % 8 = a0 at *
  have ha1 : a / 8 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 8 % 8 = a1 at *
  have ha2 : a / 64 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 64 % 8 = a2 at *
  have ha3 : a / 512 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 512 % 8 = a3 at *
  have ha4 : a / 4096 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 4096 % 8 = a4 at *
  have ha5 : a / 32768 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 32768 % 8 = a5 at *
  have ha6 : a / 262144 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 262144 % 8 = a6 at *
  have ha7 : a / 2097152 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 2097152 % 8 = a7 at *
  have ha8 : a / 16777216 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 16777216 % 8 = a8 at *
  have ha9 : a / 134217728 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 134217728 % 8 = a9 at *
  have ha10 : a / 1073741824 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 1073741824 % 8 = a10 at *
  have ha11 : a / 8589934592 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 8589934592 % 8 = a11 at *
  have ha12 : a / 68719476736 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 68719476736 % 8 = a12 at *
  have ha13 : a / 549755813888 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 549755813888 % 8 = a13 at *
  have ha14 : a / 4398046511104 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 4398046511104 % 8 = a14 at *
  have ha15 : a / 35184372088832 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 35184372088832 % 8 = a15 at *
  have ha16 : a / 281474976710656 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 281474976710656 % 8 = a16 at *
  have ha17 : a / 2251799813685248 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 2251799813685248 % 8 = a17 at *
  have ha18 : a / 18014398509481984 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 18014398509481984 % 8 = a18 at *
  have ha19 : a / 144115188075855872 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 144115188075855872 % 8 = a19 at *
  have ha20 : a / 1152921504606846976 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 1152921504606846976 % 8 = a20 at *
  have hb0 : b % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b % 8 = b0 at *
  have hb1 : b / 8 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 8 % 8 = b1 at *
  have hb2 : b / 64 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 64 % 8 = b2 at *
  have hb3 : b / 512 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 512 % 8 = b3 at *
  have hb4 : b / 4096 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 4096 % 8 = b4 at *
  have hb5 : b / 32768 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 32768 % 8 = b5 at *
  have hb6 : b / 262144 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 262144 % 8 = b6 at *
  have hb7 : b / 2097152 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 2097152 % 8 = b7 at *
  have hb8 : b / 16777216 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 16777216 % 8 = b8 at *
  have hb9 : b / 134217728 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 134217728 % 8 = b9 at *
  have hb10 : b / 1073741824 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 1073741824 % 8 = b10 at *
  have hb11 : b / 8589934592 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 8589934592 % 8 = b11 at *
  have hb12 : b / 68719476736 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 68719476736 % 8 = b12 at *
  have hb13 : b / 549755813888 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 549755813888 % 8 = b13 at *
  have hb14 : b / 4398046511104 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 4398046511104 % 8 = b14 at *
  have hb15 : b / 35184372088832 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 35184372088832 % 8 = b15 at *
  have hb16 : b / 281474976710656 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 281474976710656 % 8 = b16 at *
  have hb17 : b / 2251799813685248 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 2251799813685248 % 8 = b17 at *
  have hb18 : b / 18014398509481984 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 18014398509481984 % 8 = b18 at *
  have hb19 : b / 144115188075855872 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 144115188075855872 % 8 = b19 at *
  have hb20 : b / 1152921504606846976 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 1152921504606846976 % 8 = b20 at *
  clear ha hb hb'
  rw [swarLanes (a0 + a1 + b0 + b1) (a2 + a3 + b2 + b3) (a4 + a5 + b4 + b5) (a6 + a7 + b6 + b7)
    (a8 + a9 + b8 + b9) (a10 + a11 + b10 + b11) (a12 + a13 + b12 + b13) (a14 + a15 + b14 + b15)
    (a16 + a17 + b16 + b17) (a18 + a19 + b18 + b19) (a20 + a21 + b20) (by clear hX; omega)
    (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) (by clear hX; omega)
    (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) X (by
    rw [← hX]
    clear hX
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    omega)]
  clear hX
  ac_rfl


/-! ## The 42 digits of a 126-bit value across the doubleword boundary -/

theorem div_mod_add_pow (x y k m w : Nat) (h : k + w ≤ m) :
    (x + 2 ^ m * y) / 2 ^ k % 2 ^ w = x / 2 ^ k % 2 ^ w := by
  have e : 2 ^ m * y = 2 ^ k * (2 ^ w * (2 ^ (m - k - w) * y)) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]; congr 2; omega
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.add_mul_mod_self_left]

theorem div_add_pow (x y k m : Nat) (h : k ≤ m) :
    (x + 2 ^ m * y) / 2 ^ k = x / 2 ^ k + 2 ^ (m - k) * y := by
  have e : 2 ^ m * y = 2 ^ k * (2 ^ (m - k) * y) := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k)]

/-- An even number plus a bit: the radix-8 digits `j ≥ 1` are those of the even number. -/
theorem dig_carry (b c j : Nat) (hb : b % 2 = 0) (hc : c ≤ 1) (hj : 0 < j) :
    (b + c) / 2 ^ (3 * j) % 8 = b / 2 ^ (3 * j) % 8 := by
  have e : (b + c) / 2 = b / 2 := by omega
  have p : 2 ^ (3 * j) = 2 * 2 ^ (3 * j - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  rw [p, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, e]

theorem dig_carry0 (b c : Nat) (hb : b % 2 = 0) (hc : c ≤ 1) : (b + c) % 8 = b % 8 + c := by omega

theorem sum_range_add (f : Nat → Nat) (m n : Nat) :
    ((List.range (m + n)).map f).sum = ((List.range m).map f).sum + ((List.range n).map fun j => f (m + j)).sum := by
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  rfl

theorem sum_range_succ' (f : Nat → Nat) (n : Nat) :
    ((List.range (n + 1)).map f).sum = f 0 + ((List.range n).map fun j => f (j + 1)).sum := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  rfl

theorem sum_congr_range (f g : Nat → Nat) (n : Nat) (h : ∀ i < n, f i = g i) :
    ((List.range n).map f).sum = ((List.range n).map g).sum := by
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

/-- The radix-8 digits `0 .. 20` of a doubleword (`dsum21`), as Core writes them. -/
theorem dsum21_pow (a : Nat) : dsum21 a = ((List.range 21).map fun i => a / 2 ^ (3 * i) % 2 ^ 3).sum := by
  rw [dsum21_eq]
  apply sum_congr_range
  intro i _
  rw [Nat.pow_mul]; rfl

/-- **The 42 radix-8 digits of `v0 + 2^64 v1`** (`v0 < 2^64`): the 21 digits of `v0`, the bit `v0 / 2^63`, and the
21 digits of `2 v1` (digit 21 straddles bit 63). -/
theorem lowDigits_sum (v0 v1 : Nat) (h0 : v0 < 2 ^ 64) :
    ((List.range 42).map fun i => (v0 + 2 ^ 64 * v1) / 2 ^ (3 * i) % 2 ^ 3).sum =
      dsum21 v0 + v0 / 2 ^ 63 + dsum21 (2 * v1) := by
  rw [show 42 = 21 + 21 from rfl, sum_range_add, dsum21_pow, dsum21_pow]
  have hlow : ∀ i < 21, (v0 + 2 ^ 64 * v1) / 2 ^ (3 * i) % 2 ^ 3 = v0 / 2 ^ (3 * i) % 2 ^ 3 :=
    fun i hi => div_mod_add_pow _ _ _ _ _ (by omega)
  rw [sum_congr_range _ _ 21 hlow]
  have hc : v0 / 2 ^ 63 ≤ 1 := by
    have : v0 / 2 ^ 63 < 2 := Nat.div_lt_of_lt_mul (by rw [show 2 ^ 63 * 2 = 2 ^ 64 by norm_num]; exact h0)
    omega
  have hW : ∀ j, (v0 + 2 ^ 64 * v1) / 2 ^ (3 * (21 + j)) % 2 ^ 3 = (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * j) % 8 := by
    intro j
    rw [show 3 * (21 + j) = 63 + 3 * j by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      div_add_pow _ _ _ _ (by omega)]
    norm_num
    rw [Nat.add_comm]
  simp only [hW]
  have e1 : ((List.range 21).map fun j => (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * j) % 8).sum =
      v0 / 2 ^ 63 + ((List.range 21).map fun j => 2 * v1 / 2 ^ (3 * j) % 2 ^ 3).sum := by
    have s1 : ((List.range 21).map fun j => (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * j) % 8).sum =
        (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * 0) % 8 +
          ((List.range 20).map fun j => (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * (j + 1)) % 8).sum :=
      sum_range_succ' (fun j => (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * j) % 8) 20
    have s2 : ((List.range 21).map fun j => 2 * v1 / 2 ^ (3 * j) % 2 ^ 3).sum =
        2 * v1 / 2 ^ (3 * 0) % 2 ^ 3 + ((List.range 20).map fun j => 2 * v1 / 2 ^ (3 * (j + 1)) % 2 ^ 3).sum :=
      sum_range_succ' (fun j => 2 * v1 / 2 ^ (3 * j) % 2 ^ 3) 20
    have hj : ∀ j < 20, (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * (j + 1)) % 8 = 2 * v1 / 2 ^ (3 * (j + 1)) % 2 ^ 3 :=
      fun j _ => dig_carry _ _ _ (by omega) hc (by omega)
    rw [s1, s2, sum_congr_range _ _ 20 hj]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    rw [dig_carry0 _ _ (by omega) hc]
    norm_num
    omega
  rw [e1]
  omega


/-! ## The top decode's SWAR sums (2-bit and 3-bit lanes; generated by checks/gen/topswar.py) -/

theorem landM4 (n : Nat) : n &&& mask2 =
    16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 % 4) + n / 16 / 16 % 4) + n / 16 % 4) + n % 4 := by
  rw [show mask2 = 16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3 by norm_num [mask2]]
  simp only [split2, and3]

theorem landM8' (n : Nat) : n &&& mask4 =
    256 * (256 * (256 * (256 * (256 * (256 * (256 * (n / 256 / 256 / 256 / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 % 16) + n / 256 / 256 % 16) + n / 256 % 16) + n % 16 := by
  rw [show mask4 = 256 * (256 * (256 * (256 * (256 * (256 * (256 * (15) + 15) + 15) + 15) + 15) + 15) + 15) + 15 by norm_num [mask4]]
  simp only [split4, and15]

theorem landM8 (n : Nat) : n &&& mask4 =
    256 * (256 * (256 * (256 * (256 * (256 * (256 * (n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 % 16) + n % 16 := by
  rw [landM8']; simp only [Nat.div_div_eq_div_mul]

theorem hdiv16 (c R : Nat) (h : c < 16) : (c + 16 * R) / 16 = R := by omega
theorem hmod16 (c R : Nat) (h : c < 16) : (c + 16 * R) % 16 = c := by omega

theorem fold_mod255 (x0 x1 x2 x3 x4 x5 x6 x7 : Nat) :
    (x0 + 256 * (x1 + 256 * (x2 + 256 * (x3 + 256 * (x4 + 256 * (x5 + 256 * (x6 + 256 * (x7)))))))) % 255 =
      (x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7) % 255 := by
  omega

theorem lanes4 (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 : Nat) (h0 : q0 ≤ 12) (h1 : q1 ≤ 12) (h2 : q2 ≤ 12) (h3 : q3 ≤ 12) (h4 : q4 ≤ 12) (h5 : q5 ≤ 12) (h6 : q6 ≤ 12) (h7 : q7 ≤ 12) (h8 : q8 ≤ 12) (h9 : q9 ≤ 12) (h10 : q10 ≤ 12) (h11 : q11 ≤ 12) (h12 : q12 ≤ 12) (h13 : q13 ≤ 12) (h14 : q14 ≤ 12) (h15 : q15 ≤ 12) (L : Nat)
    (hL : L = q0 + 16 * (q1 + 16 * (q2 + 16 * (q3 + 16 * (q4 + 16 * (q5 + 16 * (q6 + 16 * (q7 + 16 * (q8 + 16 * (q9 + 16 * (q10 + 16 * (q11 + 16 * (q12 + 16 * (q13 + 16 * (q14 + 16 * (q15)))))))))))))))) :
    ((L / 16 &&& mask4) + (L &&& mask4)) % 18446744073709551616 % 255 = q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 := by
  have e : (L / 16 &&& mask4) + (L &&& mask4) = (q1 + q0) + 256 * ((q3 + q2) + 256 * ((q5 + q4) + 256 * ((q7 + q6) + 256 * ((q9 + q8) + 256 * ((q11 + q10) + 256 * ((q13 + q12) + 256 * ((q15 + q14)))))))) := by
    rw [landM8, landM8, hL]
    simp (disch := omega) only [hdiv16, hmod16, Nat.mod_eq_of_lt]
    ring
  rw [e]
  clear e hL
  have hlt : (q1 + q0) + 256 * ((q3 + q2) + 256 * ((q5 + q4) + 256 * ((q7 + q6) + 256 * ((q9 + q8) + 256 * ((q11 + q10) + 256 * ((q13 + q12) + 256 * ((q15 + q14)))))))) < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hlt, fold_mod255]
  have hlt2 : (q1 + q0) + (q3 + q2) + (q5 + q4) + (q7 + q6) + (q9 + q8) + (q11 + q10) + (q13 + q12) + (q15 + q14) < 255 := by omega
  rw [Nat.mod_eq_of_lt hlt2]
  ring

/-- The 32 radix-4 digits of a doubleword. -/
def qsum32 (a : Nat) : Nat :=
  a % 4 + a / 4 % 4 + a / 16 % 4 + a / 64 % 4 + a / 256 % 4 + a / 1024 % 4 + a / 4096 % 4 + a / 16384 % 4 + a / 65536 % 4 + a / 262144 % 4 + a / 1048576 % 4 + a / 4194304 % 4 + a / 16777216 % 4 + a / 67108864 % 4 + a / 268435456 % 4 + a / 1073741824 % 4 + a / 4294967296 % 4 + a / 17179869184 % 4 + a / 68719476736 % 4 + a / 274877906944 % 4 + a / 1099511627776 % 4 + a / 4398046511104 % 4 + a / 17592186044416 % 4 + a / 70368744177664 % 4 + a / 281474976710656 % 4 + a / 1125899906842624 % 4 + a / 4503599627370496 % 4 + a / 18014398509481984 % 4 + a / 72057594037927936 % 4 + a / 288230376151711744 % 4 + a / 1152921504606846976 % 4 + a / 4611686018427387904 % 4

/-- The 17 radix-4 digits of a 34-bit number. -/
def qsum17 (c : Nat) : Nat :=
  c % 4 + c / 4 % 4 + c / 16 % 4 + c / 64 % 4 + c / 256 % 4 + c / 1024 % 4 + c / 4096 % 4 + c / 16384 % 4 + c / 65536 % 4 + c / 262144 % 4 + c / 1048576 % 4 + c / 4194304 % 4 + c / 16777216 % 4 + c / 67108864 % 4 + c / 268435456 % 4 + c / 1073741824 % 4 + c / 4294967296 % 4

/-- The 9 radix-8 digits of a 27-bit number. -/
def dsum9 (g : Nat) : Nat :=
  g % 8 + g / 8 % 8 + g / 64 % 8 + g / 512 % 8 + g / 4096 % 8 + g / 32768 % 8 + g / 262144 % 8 + g / 2097152 % 8 + g / 16777216 % 8

/-- The lane sums of the 2-bit SWAR (`L = (a >>> 2 &&& M4) + (a &&& M4) + (c >>> 2 &&& M4) + (c &&& M4)`). -/
def topL (a c : Nat) : Nat :=
  (((a / 4 &&& mask2) + (a &&& mask2)) % 18446744073709551616 +
    ((c / 4 &&& mask2) + (c &&& mask2)) % 18446744073709551616) % 18446744073709551616

/-- The 2-bit digit sum of the top decode: `(L >>> 4 &&& M8) + (L &&& M8)`, `remu 255`. -/
def topSwar2 (a c : Nat) : Nat :=
  ((topL a c / 16 &&& mask4) + (topL a c &&& mask4)) % 18446744073709551616 % 255

theorem topSwar2_eq (a c : Nat) (hc : c < 2 ^ 34) :
    topSwar2 a c = qsum32 a + qsum17 c := by
  have hc17 : c / 17179869184 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc18 : c / 68719476736 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc19 : c / 274877906944 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc20 : c / 1099511627776 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc21 : c / 4398046511104 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc22 : c / 17592186044416 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc23 : c / 70368744177664 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc24 : c / 281474976710656 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc25 : c / 1125899906842624 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc26 : c / 4503599627370496 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc27 : c / 18014398509481984 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc28 : c / 72057594037927936 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc29 : c / 288230376151711744 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc30 : c / 1152921504606846976 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc31 : c / 4611686018427387904 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  unfold topSwar2 qsum32 qsum17
  generalize hL : topL a c = L
  unfold topL at hL
  simp only [landM4, Nat.div_div_eq_div_mul] at hL
  norm_num at hL
  simp only [hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at hL
  clear hc17
  clear hc18
  clear hc19
  clear hc20
  clear hc21
  clear hc22
  clear hc23
  clear hc24
  clear hc25
  clear hc26
  clear hc27
  clear hc28
  clear hc29
  clear hc30
  clear hc31
  have ha0 : a % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a % 4 = a0 at *
  have ha1 : a / 4 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4 % 4 = a1 at *
  have ha2 : a / 16 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 16 % 4 = a2 at *
  have ha3 : a / 64 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 64 % 4 = a3 at *
  have ha4 : a / 256 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 256 % 4 = a4 at *
  have ha5 : a / 1024 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1024 % 4 = a5 at *
  have ha6 : a / 4096 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4096 % 4 = a6 at *
  have ha7 : a / 16384 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 16384 % 4 = a7 at *
  have ha8 : a / 65536 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 65536 % 4 = a8 at *
  have ha9 : a / 262144 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 262144 % 4 = a9 at *
  have ha10 : a / 1048576 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1048576 % 4 = a10 at *
  have ha11 : a / 4194304 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4194304 % 4 = a11 at *
  have ha12 : a / 16777216 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 16777216 % 4 = a12 at *
  have ha13 : a / 67108864 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 67108864 % 4 = a13 at *
  have ha14 : a / 268435456 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 268435456 % 4 = a14 at *
  have ha15 : a / 1073741824 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1073741824 % 4 = a15 at *
  have ha16 : a / 4294967296 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4294967296 % 4 = a16 at *
  have ha17 : a / 17179869184 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 17179869184 % 4 = a17 at *
  have ha18 : a / 68719476736 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 68719476736 % 4 = a18 at *
  have ha19 : a / 274877906944 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 274877906944 % 4 = a19 at *
  have ha20 : a / 1099511627776 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1099511627776 % 4 = a20 at *
  have ha21 : a / 4398046511104 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4398046511104 % 4 = a21 at *
  have ha22 : a / 17592186044416 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 17592186044416 % 4 = a22 at *
  have ha23 : a / 70368744177664 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 70368744177664 % 4 = a23 at *
  have ha24 : a / 281474976710656 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 281474976710656 % 4 = a24 at *
  have ha25 : a / 1125899906842624 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1125899906842624 % 4 = a25 at *
  have ha26 : a / 4503599627370496 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4503599627370496 % 4 = a26 at *
  have ha27 : a / 18014398509481984 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 18014398509481984 % 4 = a27 at *
  have ha28 : a / 72057594037927936 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 72057594037927936 % 4 = a28 at *
  have ha29 : a / 288230376151711744 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 288230376151711744 % 4 = a29 at *
  have ha30 : a / 1152921504606846976 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1152921504606846976 % 4 = a30 at *
  have ha31 : a / 4611686018427387904 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4611686018427387904 % 4 = a31 at *
  have hc0 : c % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c % 4 = c0 at *
  have hc1 : c / 4 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 4 % 4 = c1 at *
  have hc2 : c / 16 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 16 % 4 = c2 at *
  have hc3 : c / 64 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 64 % 4 = c3 at *
  have hc4 : c / 256 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 256 % 4 = c4 at *
  have hc5 : c / 1024 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 1024 % 4 = c5 at *
  have hc6 : c / 4096 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 4096 % 4 = c6 at *
  have hc7 : c / 16384 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 16384 % 4 = c7 at *
  have hc8 : c / 65536 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 65536 % 4 = c8 at *
  have hc9 : c / 262144 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 262144 % 4 = c9 at *
  have hc10 : c / 1048576 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 1048576 % 4 = c10 at *
  have hc11 : c / 4194304 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 4194304 % 4 = c11 at *
  have hc12 : c / 16777216 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 16777216 % 4 = c12 at *
  have hc13 : c / 67108864 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 67108864 % 4 = c13 at *
  have hc14 : c / 268435456 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 268435456 % 4 = c14 at *
  have hc15 : c / 1073741824 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 1073741824 % 4 = c15 at *
  have hc16 : c / 4294967296 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 4294967296 % 4 = c16 at *
  clear hc
  rw [lanes4 (a1 + a0 + c1 + c0) (a3 + a2 + c3 + c2) (a5 + a4 + c5 + c4) (a7 + a6 + c7 + c6) (a9 + a8 + c9 + c8) (a11 + a10 + c11 + c10) (a13 + a12 + c13 + c12) (a15 + a14 + c15 + c14) (a17 + a16 + c16) (a19 + a18) (a21 + a20) (a23 + a22) (a25 + a24) (a27 + a26) (a29 + a28) (a31 + a30) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) L (by
    rw [← hL]
    clear hL
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    ring)]
  clear hL
  ring

/-- The 3-bit digit sum of the top decode (`g = v1 >>> 34`): `y = (g >>> 3 &&& M1) + (g &&& M1)`, `y + (y >>> 6)`,
`&&& M2`, `remu 4095`. -/
def topSwar3 (g : Nat) : Nat :=
  ((((g / 8 &&& mask3) + (g &&& mask3)) % 18446744073709551616 +
    ((g / 8 &&& mask3) + (g &&& mask3)) % 18446744073709551616 / 64) % 18446744073709551616 &&& mask6) % 4095

theorem topSwar3_eq (g : Nat) (hg : g < 2 ^ 27) : topSwar3 g = dsum9 g := by
  have e : topSwar3 g = lowSwar g 0 := by
    unfold topSwar3 lowSwar sw1
    simp only [Nat.zero_div, Nat.zero_and, Nat.add_zero, Nat.mod_mod]
  rw [e, lowSwar_eq _ _ (by omega) (by norm_num)]
  have h63 : g / 2 ^ 63 = 0 := Nat.div_eq_of_lt (by omega)
  rw [h63]
  unfold dsum21 dsum9
  have hg9 : g / 134217728 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg10 : g / 1073741824 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg11 : g / 8589934592 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg12 : g / 68719476736 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg13 : g / 549755813888 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg14 : g / 4398046511104 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg15 : g / 35184372088832 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg16 : g / 281474976710656 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg17 : g / 2251799813685248 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg18 : g / 18014398509481984 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg19 : g / 144115188075855872 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg20 : g / 1152921504606846976 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  simp only [hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, Nat.zero_div, Nat.zero_mod, Nat.add_zero]

/-! ## Digit sums as Core writes them -/

theorem qsum32_eq (a : Nat) : qsum32 a = ((List.range 32).map fun i => a / 2 ^ (2 * i) % 2 ^ 2).sum := by
  simp only [qsum32, List.range, List.range.loop, List.map, List.sum_cons, List.sum_nil]
  norm_num [Nat.add_assoc]

theorem qsum17_eq (c : Nat) : qsum17 c = ((List.range 17).map fun i => c / 2 ^ (2 * i) % 2 ^ 2).sum := by
  simp only [qsum17, List.range, List.range.loop, List.map, List.sum_cons, List.sum_nil]
  norm_num [Nat.add_assoc]

theorem dsum9_eq (g : Nat) : dsum9 g = ((List.range 9).map fun j => g / 2 ^ (3 * j) % 2 ^ 3).sum := by
  simp only [dsum9, List.range, List.range.loop, List.map, List.sum_cons, List.sum_nil]
  norm_num [Nat.add_assoc]

/-! ## Core's `decode` in the machine's terms -/

theorem dataDigits_lower (lay : Layer) (hlay : lay ≠ 0) (value : Digest) :
    dataDigits lay value = (List.range 42).map fun i => value.toNat / 2 ^ (3 * i) % 2 ^ 3 := by
  have h42 : dataCount lay = 42 := by simp [dataCount, hlay]
  unfold dataDigits
  rw [h42]
  apply List.map_congr_left
  intro i _
  simp [hlay, coreDigit]

def lowSum (V : Nat) : Nat := lowSwar (V % 2 ^ 64) (2 * (V / 2 ^ 64))

theorem lowSum_lt (V : Nat) : lowSum V < 4095 := Nat.mod_lt _ (by norm_num)

theorem lowSum_eq (V : Nat) (h : V / 2 ^ 64 < 2 ^ 62) :
    lowSum V = ((List.range 42).map fun i => V / 2 ^ (3 * i) % 2 ^ 3).sum := by
  unfold lowSum
  rw [lowSwar_eq _ _ (Nat.mod_lt _ (by norm_num)) (by omega)]
  have hV : V = V % 2 ^ 64 + 2 ^ 64 * (V / 2 ^ 64) := (Nat.mod_add_div V (2 ^ 64)).symm
  have := lowDigits_sum (V % 2 ^ 64) (V / 2 ^ 64) (Nat.mod_lt _ (by norm_num))
  rw [← hV] at this
  exact this.symm

theorem target_le (lay : Layer) : target lay ≤ 195 := by
  fin_cases lay <;> decide

/-- **Core's lower decode, as the machine computes it** (`lay ≠ 0`): reject when `v1 >>> 62 ≠ 0`; otherwise the
checksum digit is `c = (target + 2^64 - S) mod 2^64` (`sub t4, gp, s9`, `S` = the SWAR sum), reject unless
`c < 8` (`sltiu`); the digits are the 42 radix-8 digits followed by `c`. -/
theorem decode_lower (lay : Layer) (hlay : lay ≠ 0) (value : Digest) :
    decode lay value =
      if value.toNat / 2 ^ 64 / 2 ^ 62 ≠ 0 then none
      else if (target lay + 2 ^ 64 - lowSum value.toNat) % 2 ^ 64 < 8 then
        some (((List.range 42).map fun i => value.toNat / 2 ^ (3 * i) % 2 ^ 3) ++
          [(target lay + 2 ^ 64 - lowSum value.toNat) % 2 ^ 64])
      else none := by
  have ht := target_le lay
  have hS := lowSum_lt value.toNat
  have hb : encodedBits lay = 126 := by simp [encodedBits, hlay]
  unfold decode
  rw [hb, dataDigits_lower lay hlay]
  simp only [if_neg hlay]
  by_cases h : value.toNat / 2 ^ 64 / 2 ^ 62 ≠ 0
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega), ← lowSum_eq _ (by omega)]
    by_cases hc : lowSum value.toNat ≤ target lay ∧ target lay - lowSum value.toNat < 8
    · rw [if_pos hc, if_pos (by omega)]
      congr 3
      omega
    · rw [if_neg hc, if_neg (by omega)]

/-- The machine's digit sum of the top decode: the 2-bit SWAR on `v0`, `v1 % 2^34` plus the 3-bit SWAR on
`v1 >>> 34`. -/
def topSum (V : Nat) : Nat := topSwar2 (V % 2 ^ 64) (V / 2 ^ 64 % 2 ^ 34) + topSwar3 (V / 2 ^ 64 / 2 ^ 34)

theorem topSum_eq (V : Nat) (h : V / 2 ^ 64 < 2 ^ 61) :
    topSum V = ((List.range 49).map fun i => V / 2 ^ (2 * i) % 2 ^ 2).sum +
      ((List.range 9).map fun j => V / 2 ^ (98 + 3 * j) % 2 ^ 3).sum := by
  unfold topSum
  rw [topSwar2_eq _ _ (Nat.mod_lt _ (by norm_num)),
    topSwar3_eq _ (by omega), qsum32_eq, qsum17_eq, dsum9_eq, show 49 = 32 + 17 from rfl, sum_range_add]
  have hV : ∀ i < 32, V / 2 ^ (2 * i) % 2 ^ 2 = V % 2 ^ 64 / 2 ^ (2 * i) % 2 ^ 2 := by
    intro i hi
    have hV : V = V % 2 ^ 64 + 2 ^ 64 * (V / 2 ^ 64) := (Nat.mod_add_div V (2 ^ 64)).symm
    conv_lhs => rw [hV]
    exact div_mod_add_pow _ _ _ _ _ (by omega)
  have hW : ∀ j < 17, V / 2 ^ (2 * (32 + j)) % 2 ^ 2 = V / 2 ^ 64 % 2 ^ 34 / 2 ^ (2 * j) % 2 ^ 2 := by
    intro j hj
    have hU : V / 2 ^ 64 = V / 2 ^ 64 % 2 ^ 34 + 2 ^ 34 * (V / 2 ^ 64 / 2 ^ 34) :=
      (Nat.mod_add_div _ (2 ^ 34)).symm
    rw [show 2 * (32 + j) = 64 + 2 * j by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    conv_lhs => rw [hU]
    exact div_mod_add_pow _ _ _ _ _ (by omega)
  have hG : ∀ j < 9, V / 2 ^ (98 + 3 * j) % 2 ^ 3 = V / 2 ^ 64 / 2 ^ 34 / 2 ^ (3 * j) % 2 ^ 3 := by
    intro j _
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← Nat.pow_add, ← Nat.pow_add,
      show 64 + (34 + 3 * j) = 98 + 3 * j by omega]
  rw [sum_congr_range _ _ 32 hV, sum_congr_range _ _ 17 hW, sum_congr_range _ _ 9 hG]

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart21

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart22
namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.T3 OracleComp
theorem mapM_congr' {α β : Type} {f g : α → M β} : ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h x (by simp), mapM_congr' l (fun y hy => h y (by simp [hy]))]

theorem finRange_mapM {β : Type} (n : Nat) (g : Nat → M β) :
    (List.finRange n).mapM (fun i => g i.val) = (List.range n).mapM g := by
  have e : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem (by simp)
    intro i h1 h2; simp
  rw [← e, List.mapM_map]; rfl

/-- A fold that appends one result per index is the `mapM` of the indices. -/
theorem foldlM_app_mapM (f : Nat → M Digest) : ∀ (n a : Nat) (acc : List Digest),
    (List.range' a n).foldlM (fun e i => do let v ← f i; pure (e ++ [v])) acc =
      (fun l => acc ++ l) <$> (List.range' a n).mapM f
  | 0, a, acc => by simp
  | n + 1, a, acc => by
    rw [List.range'_succ, List.foldlM_cons, List.mapM_cons]
    simp only [bind_assoc, pure_bind, foldlM_app_mapM f n (a + 1), map_bind, bind_map_left, map_pure]
    congr 1; funext v
    rw [← bind_pure_comp]
    congr 1; funext l; simp

namespace QCtx
theorem sum_range'_eq (f g : Nat → Nat) (a n : Nat) (h : ∀ i, a ≤ i → i < a + n → f i = g i) :
    ((List.range' a n).map f).sum = ((List.range' a n).map g).sum := by
  congr 1
  apply List.map_congr_left
  intro i hi
  have := List.mem_range'_1.mp hi
  exact h i this.1 this.2

end QCtx
end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart22

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart23

/-! # V1 lower chains: the whole chain phase of a lower layer

For a lower-layer run of the chain code (`LCtx` with `i0 = 0`, `koff = 0`, a checksum digit `ck < 8`):

* `LCtx.lower_good` : from `ChainIn 0 []` to the return (`ChainOut 43`), the 43 chains (`chains_good` + `ck_good`);
* `LCtx.lowP_eq` : the program is Core's `mapM` over `finRange 43` (`layerP`'s chain term) when the digits are `D`
  and the chain blocks are the witness's (`s6 = 0x800 + chainBlock lay 42 + 1024`);
* `LCtx.lowCost_accept` : the cycles `lowCost + Z = 2993 - 9 · target lay` when the 43 digits sum to the target
  (`decode_lower_sum`: every decoded lower digit list does). -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3

namespace LCtx

/-- The lower chain phase as a program: code chains `0 .. 41`, then the checksum chain 42. -/
def lowP (c : LCtx) : M (List Digest) := (List.range' 0 42).foldlM c.chainF [] >>= fun e => c.chainF e 42

/-- The cycles of the lower chain phase (with the dispatches and the return). -/
def lowCost (c : LCtx) : Nat := c.chainsCost 0 42 + chainCost 42 c.ck

/-- **The chain phase of a lower layer**: from `ChainIn 0 []` to the return, Core's 43 chains. -/
theorem lower_good (c : LCtx) (hc : c.ok) (hi0 : c.i0 = 0) (hko : c.koff = 0) (hck : c.ck < 8) {s0 : MachineState}
    (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2) (h0 : c.Orig0 s0)
    (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t, c.ChainOut s0 43 ends t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K ends))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N + 1720) (C + c.lowCost) Q (A + c.lowCost) (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM c.lowP K) := by
  unfold lowP
  rw [SigGolfCandidate.T3M.CanonicalPort.Verify.ccM_bind]
  have H := c.chains_good hc hk h0 (fun _ => hko) (fun e => SigGolfCandidate.T3M.CanonicalPort.Verify.ccM (c.chainF e 42) K)
    (N + 40) (C + chainCost 42 c.ck) (A + chainCost 42 c.ck) Q
    (fun ends t ht => c.ck_good hc hk h0 (fun _ => hko) hck K N C A Q hK ends t ht) 42 0 (by omega) (by omega) [] s hs
  refine H.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
  · unfold lowCost; omega
  · unfold lowCost; omega

/-! ## Core's form -/

/-- Core's chain `i` of layer `c.lay` with the digits `D` and the witness's pads and value (`layerP`'s term). -/
def coreChain (c : LCtx) (D : List Nat) (i : Nat) : M Digest :=
  chainP c.lay c.tree c.leaf i (D.getD i 0) (maxDigit c.lay i - D.getD i 0) (wchainPads c.w c.lay i).1
    (wchainPads c.w c.lay i).2 (wvalue c.w c.lay i)

theorem chainCount_lower (lay : Layer) (h : lay ≠ 0) : chainCount lay = 43 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals rfl

theorem fit_chain (c : LCtx) (hlay : c.lay ≠ 0) (hko : c.koff = 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0) (hS6 : c.S6 = 0x800 + chainBlock c.lay 42 + 1024) (i : Nat) (hi : i < 43) :
    chainP c.lay c.tree c.leaf (i + c.koff) (c.dig i) (7 - c.dig i) (c.pad0 i) (c.pad1 i) (c.val i) =
      c.coreChain D i := by
  unfold coreChain
  have hw : maxDigit c.lay i = 7 := by simp [maxDigit, hlay]
  rw [← hD i hi, hw, hko, Nat.add_zero]
  have hn := chainCount_lower c.lay hlay
  have e : c.blk i - 0x800 = chainBlock c.lay i := by
    unfold blk chainBlock at *; rw [hS6]; rw [hn] at *; simp only at *; omega
  unfold pad0 pad1 val wchainPads wvalue
  rw [e]

/-- **The lower chain phase is Core's**: `lowP` = the 43 chains of `layerP` (`mapM` over `finRange 43`). -/
theorem lowP_eq (c : LCtx) (hlay : c.lay ≠ 0) (hko : c.koff = 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0) (hS6 : c.S6 = 0x800 + chainBlock c.lay 42 + 1024) :
    c.lowP = (List.finRange 43).mapM fun i => c.coreChain D i.val := by
  rw [finRange_mapM, List.range_eq_range', show (43 : Nat) = 42 + 1 from rfl, List.range'_append_1.symm,
    List.mapM_append]
  unfold lowP
  have hF : (List.range' 0 42).foldlM c.chainF [] = (fun l => [] ++ l) <$> (List.range' 0 42).mapM
      (fun i => chainP c.lay c.tree c.leaf (i + c.koff) (c.dig i) (7 - c.dig i) (c.pad0 i) (c.pad1 i) (c.val i)) :=
    foldlM_app_mapM _ 42 0 []
  rw [hF, mapM_congr' (List.range' 0 42) (fun i hi => c.fit_chain hlay hko D hD hS6 i (by
    have := List.mem_range'_1.mp hi; omega))]
  have h42 := c.fit_chain hlay hko D hD hS6 42 (by omega)
  unfold chainF
  rw [h42]
  simp [List.range'_one]

/-! ## The cost -/

/-- Every lower decode yields 43 digits summing to the target. -/
theorem decode_lower_sum (lay : Layer) (hlay : lay ≠ 0) (value : Digest) (ds : List Nat)
    (h : decode lay value = some ds) : ds.length = 43 ∧ ds.sum = target lay := by
  unfold decode at h
  split at h
  · cases h
  · simp only [if_neg hlay] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      have hl : (dataDigits lay value).length = 42 := by simp [dataDigits, dataCount, hlay]
      refine ⟨by simp [hl], ?_⟩
      rw [List.sum_append, List.sum_cons, List.sum_nil]
      omega
    · cases h

theorem sum_dig (c : LCtx) (D : List Nat) (hD : ∀ i < 43, c.dig i = D.getD i 0) (hl : D.length = 43) :
    ((List.range' 0 43).map c.dig).sum = D.sum := by
  have hE : D = (List.range' 0 43).map fun i => D.getD i 0 := by
    apply List.ext_getElem (by simp [hl])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range']
    rw [show 0 + 1 * i = i by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  conv_rhs => rw [hE]
  exact QCtx.sum_range'_eq _ _ 0 43 (fun i _ hi => hD i (by omega))

/-- **The cost of an accepting lower chain phase**: `2993 - 9 · target - Z` (`Z` = the max-digit savings). -/
theorem lowCost_accept (c : LCtx) (hck : c.ck < 8) (D : List Nat) (hD : ∀ i < 43, c.dig i = D.getD i 0)
    (hl : D.length = 43) (T : Nat) (hT : D.sum = T) : c.lowCost + c.zSum 0 43 + 9 * T = 2993 := by
  have := c.chainsCost_lower hck T (by rw [c.sum_dig D hD hl, hT])
  unfold lowCost
  omega

end LCtx

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart23

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart24

/-! # V1: the leaf-pk HASH input

The leaf-pk block (`xlpk*`) hashes `[end_0 | T(2, lay, tree, 0, leaf) | end_1 .. end_{n-1}]` in place: the lower
block at `0x300` (`n = 43`, 704 bytes = 11 blocks), the top block at `0x200` (`n = 58`, 944 bytes and the two zero
words `0x5B0`, `0x5B8` = `pad64`'s padding, 960 bytes = 15 blocks). `leafInput` is the argument of Core's `leafHash`
(`leafHash_eq`, by `rfl`); `lowLeaf_hashInput` / `topLeaf_hashInput` state the machine's input. -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

/-- The input of Core's `leafHash`. -/
def leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) : HashInput :=
  SphincsSecurity.bytesLE 16 (ends.getD 0 0) ++ SphincsSecurity.bytesLE 16 (header 2 lay.val tree 0 leaf) ++
    (ends.drop 1).flatMap (SphincsSecurity.bytesLE 16)

theorem leafHash_eq (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    leafHash lay tree leaf ends = shortHash (leafInput lay tree leaf ends) := rfl

/-- The two doublewords of a digest. -/
def dw (e : Digest) : List (BitVec 64) := [e.extractLsb' 0 64, e.extractLsb' 64 64]

theorem flatMap_length16 : ∀ (L : List Digest), (L.flatMap (SphincsSecurity.bytesLE 16)).length = 16 * L.length
  | [] => rfl
  | e :: L => by
    rw [List.flatMap_cons, List.length_append, flatMap_length16 L, SphincsSecurity.bytesLE_length]; simp; ring

theorem leafInput_length (lay : Layer) (tree leaf : Nat) (ends : List Digest) (h : 1 ≤ ends.length) :
    (leafInput lay tree leaf ends).length = 16 * (ends.length + 1) := by
  unfold leafInput
  rw [List.length_append, List.length_append, flatMap_length16, SphincsSecurity.bytesLE_length,
    SphincsSecurity.bytesLE_length, List.length_drop]
  omega

theorem wordsOf_leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    wordsOf (leafInput lay tree leaf ends) =
      dw (ends.getD 0 0) ++ [BitVec.ofNat 64 (hdr0 2 lay.val tree 0), BitVec.ofNat 64 (hdr1 tree leaf)] ++
        (ends.drop 1).flatMap dw := by
  unfold leafInput
  rw [wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]), wordsOf_bytesLE16, wordsOf_header,
    wordsOf_flatMap16]
  rfl

/-- Consecutive 16-byte slots read as doublewords. -/
theorem readWords_digs (t : MachineState) : ∀ (L : List Digest) (A : Nat),
    (∀ j < L.length, DigAt t (A + 16 * j) (L.getD j 0)) →
      t.readWords (BitVec.ofNat 64 A) (2 * L.length) = L.flatMap dw
  | [], _, _ => rfl
  | e :: L, A, h => by
    rw [List.length_cons, show 2 * (L.length + 1) = 2 + 2 * L.length by ring, readWords_add, readWords_two,
      show A + 8 * 2 = A + 16 by ring, readWords_digs t L (A + 16) (fun j hj => by
        have := h (j + 1) (by simp; omega)
        rwa [show A + 16 * (j + 1) = A + 16 + 16 * j by ring, List.getD_cons_succ] at this),
      List.flatMap_cons]
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] at h0
    rw [h0.1, h0.2]; rfl

theorem getD_drop1 (L : List Digest) (j : Nat) : (L.drop 1).getD j 0 = L.getD (j + 1) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2; omega

/-- **The lower leaf-pk HASH input** (`a0 = 0x300`, `a1 = 704`): the 43 ends in `slotL`, `T` at `0x310`. -/
theorem lowLeaf_hashInput (t : MachineState) (lay : Layer) (tree leaf : Nat) (ends : List Digest)
    (hn : ends.length = 43) (h10 : t.getReg .x10 = BitVec.ofNat 64 0x300)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 704) (hS : ∀ j < 43, DigAt t (slotL j) (ends.getD j 0))
    (hT0 : t.getMem (BitVec.ofNat 64 0x310) = BitVec.ofNat 64 (hdr0 2 lay.val tree 0))
    (hT1 : t.getMem (BitVec.ofNat 64 0x318) = BitVec.ofNat 64 (hdr1 tree leaf)) :
    hashInput t = toQ (pad64 (leafInput lay tree leaf ends)) ∧ (toQ (pad64 (leafInput lay tree leaf ends))).blocks = 11 := by
  have hl : (leafInput lay tree leaf ends).length = 64 * (10 + 1) := by
    rw [leafInput_length _ _ _ _ (by omega), hn]
  rw [pad64_of_aligned _ (by simp [hl])]
  refine ⟨?_, by rw [blocks_toQ ⟨by simp [hl], by simp [hl]⟩, hl]⟩
  apply hashInput_toQ t _ 10 0x300 hl h10 (by norm_num) (by norm_num) (by simpa using h11) (by norm_num)
  rw [wordsOf_leafInput, show 8 * (10 + 1) = 2 + (2 + 2 * (ends.drop 1).length) by simp [hn],
    readWords_add, readWords_add, readWords_two, readWords_two]
  have e0 := hS 0 (by omega)
  rw [show slotL 0 = 0x300 from rfl] at e0
  rw [show 0x300 + 8 * 2 = 0x310 by rfl, show 0x310 + 8 = 0x318 by rfl, show 0x310 + 8 * 2 = 0x320 by rfl,
    e0.1, show 0x300 + 8 = (0x300 : Nat) + 8 from rfl, e0.2, hT0, hT1,
    readWords_digs t (ends.drop 1) 0x320 (fun j hj => by
      rw [getD_drop1]
      have := hS (j + 1) (by simp at hj; omega)
      rwa [show slotL (j + 1) = 0x320 + 16 * j by unfold slotL; simp; omega] at this)]
  rfl

/-- **The top leaf-pk HASH input** (`a0 = 0x200`, `a1 = 896`): the 54 ends in `slotT`, `T` at `0x210`, the zero
words at `0x570`, `0x578`. -/
theorem topLeaf_hashInput (t : MachineState) (tree leaf : Nat) (ends : List Digest)
    (hn : ends.length = 54) (h10 : t.getReg .x10 = BitVec.ofNat 64 0x200)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 896) (hS : ∀ j < 54, DigAt t (slotT j) (ends.getD j 0))
    (hT0 : t.getMem (BitVec.ofNat 64 0x210) = BitVec.ofNat 64 (hdr0 2 (0 : Layer).val tree 0))
    (hT1 : t.getMem (BitVec.ofNat 64 0x218) = BitVec.ofNat 64 (hdr1 tree leaf))
    (hZ0 : t.getMem (BitVec.ofNat 64 0x570) = 0) (hZ1 : t.getMem (BitVec.ofNat 64 0x578) = 0) :
    hashInput t = toQ (pad64 (leafInput 0 tree leaf ends)) ∧ (toQ (pad64 (leafInput 0 tree leaf ends))).blocks = 14 := by
  have hl0 : (leafInput 0 tree leaf ends).length = 880 := by
    rw [leafInput_length _ _ _ _ (by omega), hn]
  have hl : (pad64 (leafInput 0 tree leaf ends)).length = 64 * (13 + 1) := by
    unfold pad64; rw [List.length_append, List.length_replicate, hl0]
  refine ⟨?_, by rw [blocks_toQ ⟨by simp [hl], by simp [hl]⟩, hl]⟩
  apply hashInput_toQ t _ 13 0x200 hl h10 (by norm_num) (by norm_num) (by simpa using h11) (by norm_num)
  rw [SigGolfCandidate.T3M.CanonicalPort.Verify.wordsOf_pad64 _ (by rw [hl0]), hl0, wordsOf_leafInput,
    show 8 * (13 + 1) = 2 + (2 + (2 * (ends.drop 1).length + 2)) by simp [hn],
    readWords_add, readWords_add, readWords_add, readWords_two, readWords_two, readWords_two]
  have e0 := hS 0 (by omega)
  rw [show slotT 0 = 0x200 from rfl] at e0
  have hd : (ends.drop 1).length = 53 := by simp [hn]
  rw [show 0x200 + 8 * 2 = 0x210 by rfl, show 0x210 + 8 = 0x218 by rfl, show 0x210 + 8 * 2 = 0x220 by rfl,
    e0.1, e0.2, hT0, hT1,
    readWords_digs t (ends.drop 1) 0x220 (fun j hj => by
      rw [getD_drop1]
      have := hS (j + 1) (by simp at hj; omega)
      rwa [show slotT (j + 1) = 0x220 + 16 * j by unfold slotT; simp; omega] at this),
    hd, show 0x220 + 8 * (2 * 53) = 0x570 by rfl, show 0x570 + 8 = 0x578 by rfl, hZ0, hZ1]
  simp [List.append_assoc, dw]

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart24

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart25

/-! # V1 layers: the transition copies and the leaf-pk blocks (expected path runs)

Every start of layer `lay` runs its own copy of the transition (`trPc lay c`, `xtrTab`): layer 3 one copy after the
forest hash (with the layer constants `hyper`), layers 2, 1 one per shape block of layer `lay + 1`'s Merkle code
(64, 64), layer 0 one per shape block of layer 1 (128). A copy is

* **A** (`specA`, up to the encoding `ecall`): `[sub s11, s8]`, the route (`s7 = 2^h | leaf`, `t5 = tree`,
  `tp = tree | leaf << 32`), the encoding header `T(4, lay, tree, 0, leaf)` at `0x110`, the counter (`lwu` from the
  witness header) checked `< 2^22` and stored at `0x120`, `a0 = 0x100`, `a2 = 0x140`;
* **B** (`specBl` lower / `specBt` top, after the `ecall`, up to the `jalr ra` into the chain code): the decode
  (range `srli 62` / `srli 61`, the SWAR sums of `Decode`, the checksum test `sltiu 8` / the total `126`), the chain
  prologue (`s6`, `s3`, `s8` (top), the table window `a5`, the extraction of triple / quad 0);
* the three rejections (counter, range, checksum / total), each `j reject` to the HALT(1) at word 743;
* the leaf-pk block (`specLf`, at the return pc `trPc + retOff`): the leaf header `T(2)`, the node word `tp = T(3)` for
  the Merkle levels, `a0`, `a1` (= 768, 704 lower; 512, 960 top, which also zeroes `0x5B0 .. 0x5C0`), the dispatch
  `jalr` into the jump table `stab_lay_0` by the leaf's chunk-0 bits.

All runs use V2's `runAt` (path runs with known registers) and `specB`; `copyCheck lay p` checks a copy at `p`. -/

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.CanonicalPort.Verify

/-- The transition copies of layer `lay` (word index of `xtr{lay}_*`, in pc order). -/
def xtrTab : List (List Nat) :=
  [[18460, 18594, 18728, 18862, 18996, 19130, 19264, 19398, 19532, 19666, 19800, 19934, 20068, 20202, 20336, 20470,
    20604, 20738, 20872, 21006, 21140, 21274, 21408, 21542, 21676, 21810, 21944, 22078, 22212, 22346, 22480, 22614,
    22748, 22882, 23016, 23150, 23284, 23418, 23552, 23686, 23820, 23954, 24088, 24222, 24356, 24490, 24624, 24758,
    24892, 25026, 25160, 25294, 25428, 25562, 25696, 25830, 25964, 26098, 26232, 26366, 26500, 26634, 26768, 26902,
    27036, 27170, 27304, 27438, 27572, 27706, 27840, 27974, 28108, 28242, 28376, 28510, 28644, 28778, 28912, 29046,
    29180, 29314, 29448, 29582, 29716, 29850, 29984, 30118, 30252, 30386, 30520, 30654, 30788, 30922, 31056, 31190,
    31324, 31458, 31592, 31726, 31860, 31994, 32128, 32262, 32396, 32530, 32664, 32798, 32932, 33066, 33200, 33334,
    33468, 33602, 33736, 33870, 34004, 34138, 34272, 34406, 34540, 34674, 34808, 34942, 35076, 35210, 35344, 35478],
   [11989, 12090, 12191, 12292, 12393, 12494, 12595, 12696, 12797, 12898, 12999, 13100, 13201, 13302, 13403, 13504,
    13605, 13706, 13807, 13908, 14009, 14110, 14211, 14312, 14413, 14514, 14615, 14716, 14817, 14918, 15019, 15120,
    15221, 15322, 15423, 15524, 15625, 15726, 15827, 15928, 16029, 16130, 16231, 16332, 16433, 16534, 16635, 16736,
    16837, 16938, 17039, 17140, 17241, 17342, 17443, 17544, 17645, 17746, 17847, 17948, 18049, 18150, 18251, 18352],
   [5525, 5626, 5727, 5828, 5929, 6030, 6131, 6232, 6333, 6434, 6535, 6636, 6737, 6838, 6939, 7040,
    7141, 7242, 7343, 7444, 7545, 7646, 7747, 7848, 7949, 8050, 8151, 8252, 8353, 8454, 8555, 8656,
    8757, 8858, 8959, 9060, 9161, 9262, 9363, 9464, 9565, 9666, 9767, 9868, 9969, 10070, 10171, 10272,
    10373, 10474, 10575, 10676, 10777, 10878, 10979, 11080, 11181, 11282, 11383, 11484, 11585, 11686, 11787, 11888],
   [661]]

/-- The number of transition copies of layer `lay`. -/
def nCopy (lay : Nat) : Nat := (xtrTab.getD lay []).length
/-- Start of transition copy `c` of layer `lay`. -/
def trPc (lay c : Nat) : Nat := (xtrTab.getD lay []).getD c 0

/-- A constant word. -/
def kw (k : Nat) : E := .c (BitVec.ofNat 64 k)

/-! ## Layer constants -/

/-- Merkle height. -/
def hL (lay : Nat) : Nat := [12, 7, 6, 6].getD lay 0
/-- Steps of A; layer 3 reuses four constants from the forest. -/
def stepsA (lay : Nat) : Nat := if lay = 3 then 19 else if lay = 0 then 16 else 15
/-- The return pc of the chain code (the leaf-pk block) relative to the copy. -/
def retOff (lay : Nat) : Nat := if lay = 0 then 69 else if lay = 3 then 49 else 45
/-- The chain base register value: lower layers `WIT + chainBase + 1024`; the top `WIT + chainBase + 960`. -/
def s6v (lay : Nat) : Nat := [15064, 19288, 22424, 25560].getD lay 0
/-- The top's base for its chains 0 .. 48 (`s3`). -/
def s3v : Nat := 15768
/-- Core's targets. -/
def tgtL (lay : Nat) : Nat := [126, 195, 195, 194].getD lay 0
/-- Header word 0 of tag `t` and layer `lay` (`1 | t << 8 | lay << 16`). -/
def hw (t lay : Nat) : Nat := 1 + 256 * t + 65536 * lay
/-- The HALT(1) `ecall` of `reject`. -/
def rejEcall : Nat := 743
/-- The jump table `stab_lay_0` of the Merkle shape dispatch. -/
def stabIdx (lay : Nat) : Nat := [209768, 209640, 209576, 209512].getD lay 0
/-- The mask of the leaf's chunk-0 bits in the dispatch (`slli a4, s7, 2; andi a4, …`). -/
def stabMask (lay : Nat) : Nat := if lay = 1 then 508 else 252

/-- The 3-bit SWAR masks and the 2-bit ones (top). -/
def M1c : Nat := 8198552921648689607
def M2c : Nat := 17311559823019733055
def M4c : Nat := 3689348814741910323
def M8c : Nat := 1085102592571150095

/-- Constants carried from the forest after the loader changes `sp`. -/
def afterLoadK : List (Reg × Word) := baseK ++ [(.x7,2),(.x8,3),(.x9,4),(.x13,5)]

/-- The known registers at a transition start (layer 3: `t0`, `s2` and the five constants of the load block
`ld3Spec`; `hyper` sets the rest). -/
def preK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then afterLoadK ++ [(.x28, BitVec.ofNat 64 (2 ^ 40)), (.x21, BitVec.ofNat 64 M2c), (.x20, BitVec.ofNat 64 M1c),
    (.x27, BitVec.ofNat 64 (hw 1 3)), (.x2, BitVec.ofNat 64 0x3fe00)]
  else baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 (lay + 1))), (.x24, 0x10000), (.x2, 0x3fe00),
    (.x20, BitVec.ofNat 64 M1c), (.x21, BitVec.ofNat 64 M2c), (.x11, 64), (.x28, BitVec.ofNat 64 (headerBank 0 0)),
    (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7)]

/-- The constant registers through a layer (after A): `s11 = 0x101 | lay << 16`, the masks, the step registers. -/
def layK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 lay)), (.x24, 0x10000), (.x2, 0x3fe00),
    (.x20, BitVec.ofNat 64 M1c), (.x21, BitVec.ofNat 64 M2c), (.x11, 64), (.x28, BitVec.ofNat 64 (if lay = 3 then 2 ^ 40 else headerBank 0 0)),
    (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7)]

/-- Lower-chain constants after the header-table entry stub. -/
def lowerLayK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 lay)), (.x24, 0x10000), (.x2, 0x3fe00),
    (.x20, BitVec.ofNat 64 M1c), (.x21, BitVec.ofNat 64 M2c), (.x11, 64), (.x28, BitVec.ofNat 64 (headerBank lay 0)),
    (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7)]

/-- Five loads after the forest HASH use the carried `sp = 2^24`, retaining
four other constants. Layer 3 starts at word 661. -/
def ld3Spec : Spec :=
  ⟨[(.x28, .ld (kw DATA)), (.x21, .ld (kw (DATA + 8))), (.x20, .ld (kw (DATA + 16))),
      (.x27, .ld (kw (DATA + 24))), (.x2, .ld (kw (DATA + 32)))],
    [], 661, false, 5, [], none, 5⟩

def ld3Check : Bool := specB [] [] afterLoadK (runAt carryK [661] 656 []) ld3Spec [] afterLoadK [.x22]

/-- ... and the encoding `ecall`'s arguments. -/
def bK (lay : Nat) : List (Reg × Word) := layK lay ++ [(.x10, 256), (.x12, 320)]

/-! ## A: route, header, counter -/

/-- The register holding the remaining index bits (`s6` for layer 3, `t5` below). -/
def rReg (lay : Nat) : Reg := if lay = 3 then .x22 else .x30
def leafE (lay : Nat) : E := if lay = 0 then .reg .x30 else .bin .and (.reg (rReg lay)) (kw (2 ^ hL lay - 1))
def treeE (lay : Nat) : E := .bin .srl (.reg (rReg lay)) (kw (hL lay))
def tpE (lay : Nat) : E := .bin .or (.bin .sll (leafE lay) (kw 32)) (treeE lay)
def s7E (lay : Nat) : E := .bin .or (leafE lay) (kw (2 ^ hL lay))
/-- The counter (`lwu` of the witness header word). -/
def ctrE (lay : Nat) : E := .un (.ld .wu (4 * ((lay + 1) % 2))) (.ld (kw (0x810 + 8 * ((lay + 1) / 2))))
def ctrBr (lay : Nat) (d : Bool) : Br := ⟨.ne, .bin .srl (ctrE lay) (kw 22), kw 0, d⟩

def specA (lay p : Nat) : Spec :=
  ⟨[(.x4, tpE lay), (.x23, s7E lay), (.x30, treeE lay), (.x3, ctrE lay)],
   [(⟨none, BitVec.ofNat 64 288⟩, .bin (.st .w 0) (.ld (kw 288)) (ctrE lay)), (⟨none, BitVec.ofNat 64 280⟩, tpE lay),
    (⟨none, BitVec.ofNat 64 272⟩, kw (hw 4 lay))],
   p + stepsA lay, true, stepsA lay, [ctrBr lay false], none, stepsA lay⟩

def rejA (lay p : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)],
   [(⟨none, BitVec.ofNat 64 280⟩, tpE lay), (⟨none, BitVec.ofNat 64 272⟩, kw (hw 4 lay))],
   rejEcall, true, stepsA lay, [ctrBr lay true], none, stepsA lay⟩

/-! ## B: decode and the chain prologue -/

def a6E : E := .ld (kw 320)
def a7E : E := .ld (kw 328)
def b1E : E := .bin .sll a7E (kw 1)
/-- The lower decode's partial sums (`sw1`) and the digit sum (`remu 4095`). -/
def sw1RefE : E :=
  .bin .add (.bin .add (.bin .add (.bin .and (.bin .srl a6E (kw 3)) (kw M1c)) (.bin .and a6E (kw M1c)))
    (.bin .and (.bin .srl b1E (kw 3)) (kw M1c))) (.bin .and b1E (kw M1c))
def swLowE : E := .bin .add (.bin .and a6E (kw M1c)) (.bin .and b1E (kw M1c))
def sw1E : E := .bin .add swLowE (.bin .srl (.bin .sub (.bin .add a6E b1E) swLowE) (kw 3))
def sumE : E := .bin .remu (.bin .and (.bin .add sw1E (.bin .srl sw1E (kw 6))) (kw M2c)) (kw 4095)
/-- The checksum register `t4 = 7 - ck = sum - (target - 7)` (`addi t4, s9, 7 - target`). -/
def t4E (lay : Nat) : E := .bin .add sumE (kw (2 ^ 64 - (tgtL lay - 7)))
def rngBr (k : Nat) (d : Bool) : Br := ⟨.ne, .bin .srl a7E (kw k), kw 0, d⟩
def ckBr (lay : Nat) (d : Bool) : Br := ⟨.eq, .bin .sltu (t4E lay) (kw 8), kw 0, d⟩
/-- `a7 = (v1 << 1) | v0 >> 63`. -/
def a7lE : E := .bin .or b1E (.bin .srl a6E (kw 63))
/-- The dispatch into `ttab` slot 0 (lower) / `qtab` slot 0 (top). -/
def x14l : E := .bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x3fe00)) (kw 0x6e000)
def tgtl : E := .bin .and (.bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x3fe00)) (kw 448800)) (.c (~~~1#64))

def specBl (lay p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, a7lE), (.x25, sumE), (.x29, t4E lay), (.x3, .bin .srl a6E (kw 63)), (.x14, x14l)],
   [], 0, false, 29, [ckBr lay false, rngBr 62 false], some tgtl, 32⟩

def postBl (lay p : Nat) : List (Reg × Word) :=
  lowerLayK lay ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x15, 0x6e000), (.x1, pcOf (p + retOff lay))]

def rejRng (k : Nat) : Spec := ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 7, [rngBr k true], none, 7⟩
def rejCk (lay : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 22, [ckBr lay true, rngBr 62 false], none, 25⟩

/-- The top decode's sums: the 3-bit SWAR of `g = v1 >>> 34` (`remu 4095` into `t4`), the 2-bit SWAR of `v0` and
`c = v1 mod 2^34` (`remu 255`), the total. -/
def gE : E := .bin .srl a7E (kw 34)
def p3E : E := .bin .add (.bin .and (.bin .srl gE (kw 3)) (kw M1c)) (.bin .and gE (kw M1c))
def s3E : E := .bin .remu (.bin .and (.bin .add p3E (.bin .srl p3E (kw 6))) (kw M2c)) (kw 4095)
def c34E : E := .bin .srl (.bin .sll a7E (kw 30)) (kw 30)
def l1E : E := .bin .add (.bin .and (.bin .srl a6E (kw 2)) (kw M4c)) (.bin .and a6E (kw M4c))
def l2E : E := .bin .add (.bin .and (.bin .srl c34E (kw 2)) (kw M4c)) (.bin .and c34E (kw M4c))
def lRefE : E := .bin .add l1E l2E
def lLowE : E := .bin .add (.bin .and a6E (kw M4c)) (.bin .and c34E (kw M4c))
def lE : E := .bin .add lLowE (.bin .srl (.bin .sub (.bin .add a6E c34E) lLowE) (kw 2))
def pE : E := .bin .add (.bin .and (.bin .srl lE (kw 4)) (kw M8c)) (.bin .and lE (kw M8c))
def totE : E := .bin .add (.bin .remu pE (kw 255)) s3E
def totBr (d : Bool) : Br := ⟨.ne, totE, kw 126, d⟩
def x14t : E := .bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x1fe00)) (kw 0xae000)
def tgtt : E := .bin .and (.bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x1fe00)) (kw 711072)) (.c (~~~1#64))

def specBt (p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, .bin .sll a7E (kw 2)), (.x3, totE), (.x14, x14t), (.x25, .bin .and c34E (kw M4c))],
   [], 0, false, 52, [totBr false, rngBr 61 false], some tgtt, 58⟩

/-- After the top decode: the 2-bit masks, the quad mask in `s8`, `t4 = 8` (no checksum chain). -/
def postBt (p : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 0)), (.x2, 0x3fe00), (.x20, BitVec.ofNat 64 M4c), (.x21, BitVec.ofNat 64 M8c),
    (.x11, 64), (.x28, BitVec.ofNat 64 (headerBank 0 0)), (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7),
    (.x22, BitVec.ofNat 64 (s6v 0)), (.x19, BitVec.ofNat 64 s3v), (.x24, 0x1fe00), (.x29, 8), (.x15, 0xae000),
    (.x1, pcOf (p + retOff 0))]

def rejTot : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 42, [totBr true, rngBr 61 false], none, 48⟩

/-! ## The leaf-pk block -/

/-- At the leaf-pk block: the layer constants and the chain code's leftovers. -/
def leafK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 lay))] ++ (if lay = 0 then [] else [(.x6, 1)])

/-- The dispatch target in `stab_lay_0` (`(s7 << 2 &&& mask) + window + imm`). -/
def x14lf (lay : Nat) : E :=
  if lay = 0 then .bin .add (.bin .and (.bin .sll (.reg .x23) (kw 2)) (kw (stabMask lay))) (kw 0xce000)
  else .bin .add (.bin .sll (.reg .x23) (kw 2)) (kw 0xce000)
def tgtLfOld (lay : Nat) : E :=
  .bin .and (.bin .add (.bin .and (.bin .sll (.reg .x23) (kw 2)) (kw (stabMask lay)))
    (kw (0x1000 + 4 * stabIdx lay))) (.c (~~~1#64))

/-- Lower-layer sentinel bits are absorbed by the jump displacement. -/
def tgtLf (lay : Nat) : E :=
  if lay = 0 then tgtLfOld lay
  else .bin .and (.bin .add (.bin .sll (.reg .x23) (kw 2))
    (kw (0x1000 + 4 * stabIdx lay - 4 * 2 ^ hL lay))) (.c (~~~1#64))

def specLf (lay : Nat) : Spec :=
  if lay = 0 then
    ⟨[(.x14, x14lf lay)],
     [(⟨none, BitVec.ofNat 64 1400⟩, kw 0), (⟨none, BitVec.ofNat 64 1392⟩, kw 0), (⟨none, BitVec.ofNat 64 536⟩, .reg .x4),
      (⟨none, BitVec.ofNat 64 528⟩, kw (hw 2 0))], 0, false, 13, [], some (tgtLf lay), 13⟩
  else
    ⟨[(.x14, x14lf lay)],
     [(⟨none, BitVec.ofNat 64 792⟩, .reg .x4), (⟨none, BitVec.ofNat 64 784⟩, kw (hw 2 lay))], 0, false, 11, [],
     some (tgtLf lay), 11⟩

def postLf (lay : Nat) : List (Reg × Word) :=
  leafK lay ++ [(.x3, BitVec.ofNat 64 (hw 2 lay)), (.x4, BitVec.ofNat 64 (hw 3 lay)),
    (.x10, BitVec.ofNat 64 (if lay = 0 then 512 else 768)), (.x11, BitVec.ofNat 64 (if lay = 0 then 896 else 704)),
    (.x15, 0xce000)] ++ (if lay = 0 then [] else [(.x28, BitVec.ofNat 64 (headerBank 0 0))])

/-! ## The checks of a copy -/

def keepA : List Reg := []
def keepB : List Reg := [.x4, .x23, .x30]
def keepLf : List Reg := [.x23, .x30, .x22]

def keepTopCall : List Reg := [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

/-- The two direct jumps preserve the top leaf return address and enter the shared packed decoder. -/
def specTopCall (p : Nat) : Spec :=
  ⟨[(.x1, kw (0x1000 + 4 * (p + 69)))], [], 96160, false, 2, [], none, 2⟩

/-- All runs of the transition copy at `p` of layer `lay` and of its leaf-pk block. -/
def copyCheck (lay p : Nat) : Bool :=
  specB [] [] baseK (runAt (preK lay) [] p [.br false]) (specA lay p) [] (bK lay) keepA &&
  specB [] [] [] (runAt (preK lay) [] p [.br true]) (rejA lay p) [] [] [] &&
  (if lay = 0 then
    specB [] [] [] (runAt [] [96160] (p + stepsA lay + 1) []) (specTopCall p) [] [] keepTopCall
  else
    specB [] [] baseK (runAt (bK lay) [] (p + stepsA lay + 1) [.br false, .br false, .jmp]) (specBl lay p) []
      (postBl lay p) keepB &&
    specB [] [] [] (runAt (bK lay) [] (p + stepsA lay + 1) [.br false, .br true]) (rejCk lay) [] [] [] &&
    specB [] [] [] (runAt (bK lay) [] (p + stepsA lay + 1) [.br true]) (rejRng 62) [] [] []) &&
  specB [] [] baseK (runAt (leafK lay) [] (p + retOff lay) [.jmp]) (specLf lay) [] (postLf lay) keepLf

/-- All copies of layer `lay` from index `lo`, `n` of them. -/
def layerCheck (lay lo n : Nat) : Bool := (List.range' lo n).all fun c => copyCheck lay (trPc lay c)

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart25

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart26

/-! # V3: the Merkle shape blocks and the final compare (expected path runs)

After the leaf-pk block (V1's `LeafOut`, at the `stab_lay_0` word of the leaf's low bits), one computed jump per chunk
of the leaf index enters a **shape block** `shp_lay_ci_sh` of straight-line levels (`sh` = the chunk's bits of the leaf;
layer 0 has two chunks, levels 0..5 and 6..11, the other layers one). Level `l` of a block is

    addi a2, s6, cur(l)        -- the HASH below writes the current node into block l (R if bit l of the leaf is 1)
    ecall                      -- l = 0: the leaf-pk HASH (a0, a1 from the leaf-pk block); else block l - 1
    [li a1, 64]                -- after the leaf-pk HASH only
    addi a0, s6, blk(l); sd tp, 16(a0); sw t5, 24(a0)       -- T(3, lay, tree, 0, heap): word 0, the tree
    sw heap, 28(a0)            -- the parent's heap index: a constant register 1..7 (the top three levels),
                               -- `li gp, heap` (the other levels), `srli gp, s7, l + 1` (layer 0, chunk 0)

with `blk(l) = WIT + layerBase lay + 64 (h - 1 - l)` (V1's `s6 - 1024 - 64 (l + 1)`, top `s6 - 960 - 64 (l + 1)`),
`cur(l) = blk(l) + 48 · bit l`. After the last level: the root HASH (`li a2, 0x100 / 0x180; ecall`) followed by the next
layer's transition copy (`trPc (lay - 1) sh`) or a compare copy (`xcmp`); after level 5 of layer 0's chunk 0 the
dispatch `slli a4, gp, 2; add a4, a5; jalr -608(a4)` into `stab_0_1` (gp = s7 >> 6 from the level's heap store).

Families (each a path run checked by `specB`, kernel-checked in `MerkleCheck*`):
* `mkEntCheck lay ci sh`: the table word `j shp_lay_ci_sh` and the first `addi a2`, to the first `ecall` (2 steps);
* `mkLvlCheck lay ci sh kk`: level `mkLo lay ci + kk` from after its `ecall` to the next `ecall` (or through the chunk
  dispatch to its symbolic jump);
* `cmpCheck c`: the compare copy `c` (`ld/ld/bne` twice, HALT(0) / HALT(1)).

Layout facts (word indices, `t3m/images/verify.labels`): `stab_3_0` 209512, `stab_2_0` 209576, `stab_1_0` 209640,
`stab_0_0` 209768, `stab_0_1` 209832; `shp_3_0_sh` = 5487 + 101 sh, `shp_2_0_sh` = 11951 + 101 sh, `shp_1_0_sh` =
18416 + 134 sh, `shp_0_0_sh` = 35567 + 48 sh, `shp_0_1_sh` = 38641 + 53 sh, `xcmp` copy `c` = 38676 + 53 c (checked
against the disassembly by `checks/gen/merkle_check.py`, and by the kernel through the runs below).

BIG2 (Merkle word 0): level 0 keeps `sd tp, 16(a0); sw t5, 20(a0)` and adds `ld tp, 16(a0)`, so `tp` holds the merged
header word 0 (`mkX4`); every later level (including layer 0's chunk 1) stores it with `sd tp, 16(a0)` alone. Each
block's Merkle part is shorter by 4 / 4 / 5 / 4 / 6 words (layers 3, 2, 1, layer 0 chunks 0, 1) and ends where it
did, so its start (the table target) is that many words later (the words before it are unreached `nop`s). -/

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.CanonicalPort.Verify

/-! ## Layout -/

/-- Chunks of the leaf index: layer 0 has two (levels 0..5, 6..11), the others one. -/
def mkNch (lay : Nat) : Nat := if lay = 0 then 2 else 1
/-- The first level of chunk `ci`. -/
def mkLo (lay ci : Nat) : Nat := if lay = 0 ∧ ci = 1 then 6 else 0
/-- The levels of chunk `ci`. -/
def mkBits (lay ci : Nat) : Nat := if lay = 0 then 6 else hL lay
/-- The jump table `stab_lay_ci` (word index of its entry 0). -/
def mkTab (lay ci : Nat) : Nat := if lay = 0 ∧ ci = 1 then 209832 else stabIdx lay
/-- The shape block `shp_lay_ci_sh` (word index of its first instruction). -/
def mkShp (lay ci sh : Nat) : Nat :=
  if lay = 3 then 5487 + 101 * sh else if lay = 2 then 11951 + 101 * sh
  else if lay = 1 then 18416 + 134 * sh else if ci = 0 then 35567 + 48 * sh else 38641 + 53 * sh
/-- The parent's heap index is a constant register at the top three levels. -/
def mkReg (lay l : Nat) : Bool := decide (hL lay ≤ l + 3)
/-- Instruction words of level `l`: level 0 `addi a2; ecall; li a1; addi a0; sd tp; sw t5; ld tp; [li gp]; sd`
(BIG2: the `ld` makes `tp` the merged header word 0), later levels `addi a2; ecall; addi a0; sd tp; [li gp]; sd`. -/
def mkWords (lay l : Nat) : Nat := (if l = 0 then 8 else 5) + (if mkReg lay l then 0 else 1)
/-- Offset of level `kk` of chunk `ci` from the start of its block. -/
def mkOff (lay ci : Nat) : Nat → Nat
  | 0 => 0
  | kk + 1 => mkOff lay ci kk + mkWords lay (mkLo lay ci + kk)
/-- W's `layerBase` (the start of layer `lay`'s region, witness offset). -/
def mkBase (lay : Nat) : Nat := [11288, 15768, 18968, 22104].getD lay 0
/-- The Merkle block of level `l`: witness offset (W's `merkleBlock lay l`) and absolute address. -/
def mkBo (lay l : Nat) : Nat := mkBase lay + 64 * (hL lay - 1 - l)
def mkBlk (lay l : Nat) : Nat := 0x800 + mkBo lay l
/-- Its current-node slot when the node is a left (`b = 0`, `L`) or right (`b = 1`, `R`) child. -/
def mkCur (lay l b : Nat) : Nat := mkBlk lay l + 48 * b
/-- The root HASH's destination: the next encoding block's `M` (`0x100`) or the root slot (`0x180`). -/
def mkDst (lay leaf : Nat) : Nat := if lay = 0 then 13336 + 48 * (leaf / 2048 % 2) else 256

/-- The final top HASH retains its current output pointer. -/
def mkMove (lay level : Nat) : Nat := if lay = 0 ∧ level = 11 then 0 else 1
/-- The parent heap index stored at level `l` of block `sh` (the constant ones). -/
def mkHeap (lay ci sh l : Nat) : Nat := (2 ^ hL lay + sh * 2 ^ mkLo lay ci) / 2 ^ (l + 1)

/-! ## Registers -/

/-- The constant registers of the Merkle code (including the leaf-established dispatch window): `t0`, `s2`, `s6`, `tp = T(3)`'s word 0, the heap registers 1..7. -/
def mkK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x4, BitVec.ofNat 64 (hw 3 lay)), (.x6, 1), (.x7, 2), (.x8, 3),
    (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7), (.x15, 0xce000)]

/-- BIG2: the same without `tp` (after level 0 `tp` holds the merged header word 0, `mkX4`). -/
def mkKc (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x6, 1), (.x7, 2), (.x8, 3),
    (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7), (.x15, 0xce000)]

/-- BIG2: the merged header word 0 (`T(3)`'s word 0 in the low half, `t5` = the tree in the high half). -/
def mkX4 (lay : Nat) : E := .bin (.st .w 4) (kw (hw 3 lay)) (.reg .x30)

/-- Registers that no Merkle run writes or knows (kept for the next transition: `sp`, `s4`, `s5`, `s7`, `s8`, `s11`,
`t3`, `t5`, ...). -/
def mkKeep : List Reg := [.x1, .x2, .x16, .x17, .x19, .x20, .x21, .x23, .x24, .x25, .x27, .x28, .x29, .x30]

/-! ## The entry of a shape block -/

/-- From the table word: `j shp_lay_ci_sh; addi a2, s6, cur(lo)`, stopping at the first `ecall` (no writes). -/
def mkEntSpec (lay ci sh : Nat) : Spec := ⟨[], [], mkShp lay ci sh + 1, true, 2, [], none, 2⟩

def mkEntPost (lay ci sh : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x12, BitVec.ofNat 64 (mkCur lay (mkLo lay ci) (sh % 2)))]

def mkEntKeep : List Reg := mkKeep ++ [.x10, .x11, .x14, .x4]

def mkEntCheck (lay ci sh : Nat) : Bool :=
  specB [] [] baseK (runAt (mkKc lay) [] (mkTab lay ci + sh) []) (mkEntSpec lay ci sh) [] (mkEntPost lay ci sh) mkEntKeep

/-! ## A level -/

/-- The value of the heap store (`sw heap, 28(a0)`). -/
def mkHeapE (lay ci sh l : Nat) : E :=
  if lay = 0 ∧ ci = 0 then .bin .srl (.reg .x23) (kw (l + 1)) else kw (mkHeap lay ci sh l)

/-- The header word 0 store of level `l`: level 0 stores `T(3)`'s word 0 and the tree (`sd tp; sw t5`), later
levels store the merged `tp` (BIG2). -/
def mkHdrE (lay l : Nat) : E := if l = 0 then mkX4 lay else .reg .x4

/-- The two header writes of level `l`: word 1 `tree | heap << 32` (two `sw`), word 0 `T(3)`. -/
def mkLvlMem (lay ci sh l : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 (mkBlk lay l + 24)⟩, mkHeapE lay ci sh l),
   (⟨none, BitVec.ofNat 64 (mkBlk lay l + 16)⟩, mkHdrE lay l)]

/-- Level 0's `ld tp` leaves the merged word in `tp` (BIG2); later levels keep `tp`. -/
def mkLvlRegs (lay l : Nat) : List (Reg × E) := if l = 0 then [(.x4, mkX4 lay)] else []

/-- The registers a level keeps: `tp` after level 0. -/
def mkLvlKeep (l : Nat) : List Reg := if l = 0 then [] else [.x4]

def mkLvlAllow (lay l : Nat) : List Nat := [mkBlk lay l + 16, mkBlk lay l + 24]

/-- The chunk-1 dispatch target of layer 0 (`((s7 >> 6) << 2) + 0xce000 - 608`, even). -/
def mkDispTgt : E :=
  .bin .and (.bin .add (.bin .sll (.bin .srl (.reg .x23) (kw 6)) (kw 2)) (kw 843168)) (.c (~~~1#64))

/-- Steps of the level body (after its `ecall`, before the next `addi a2` / `li a2` / dispatch). -/
def mkBody (lay l : Nat) : Nat := (if l = 0 then 5 else 2) + (if mkReg lay l then 1 else 2)

/-- Is level `kk` of chunk `ci` the last of a chunk followed by the chunk-1 dispatch? -/
def mkIsDisp (lay ci kk : Nat) : Bool := decide (lay = 0 ∧ ci = 0 ∧ kk + 1 = mkBits lay ci)

/-- The next `a2`: the next level's current slot, or the root destination. -/
def mkNextA2 (lay ci sh kk : Nat) : Nat :=
  if kk + 1 < mkBits lay ci then mkCur lay (mkLo lay ci + kk + 1) (sh / 2 ^ (kk + 1) % 2) else if lay = 0 then 13336 + 48 * (sh / 32 % 2) else 256

/-- A level ending at the next `ecall` (the next level's HASH or the root HASH). -/
def mkLvlSpecN (lay ci sh kk : Nat) : Spec :=
  ⟨mkLvlRegs lay (mkLo lay ci + kk), mkLvlMem lay ci sh (mkLo lay ci + kk),
    mkShp lay ci sh + mkOff lay ci (kk + 1) + mkMove lay (mkLo lay ci + kk), true,
    mkBody lay (mkLo lay ci + kk) + mkMove lay (mkLo lay ci + kk), [], none,
    mkBody lay (mkLo lay ci + kk) + mkMove lay (mkLo lay ci + kk)⟩

/-- Level 5 of layer 0's chunk 0, ending with the chunk-1 dispatch (a jump to `stab_0_1`). -/
def mkLvlSpecD (lay ci sh kk : Nat) : Spec :=
  ⟨mkLvlRegs lay (mkLo lay ci + kk), mkLvlMem lay ci sh (mkLo lay ci + kk), 0, false,
    mkBody lay (mkLo lay ci + kk) + 3, [], some mkDispTgt,
    mkBody lay (mkLo lay ci + kk) + 3⟩

/-- Known at the level body's start: the constants (with `tp = T(3)`'s word 0 at level 0 only), and `a1 = 64` after
the leaf-pk HASH. -/
def mkLvlK (lay l : Nat) : List (Reg × Word) := if l = 0 then mkK lay else mkKc lay ++ [(.x11, 64)]

def mkLvlPostN (lay ci sh kk : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x11, 64), (.x10, BitVec.ofNat 64 (mkBlk lay (mkLo lay ci + kk))),
    (.x12, BitVec.ofNat 64 (mkNextA2 lay ci sh kk))]

def mkLvlPostD (lay ci kk : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x11, 64), (.x10, BitVec.ofNat 64 (mkBlk lay (mkLo lay ci + kk))), (.x15, 0xce000)]

def mkLvlKN (lay ci sh kk : Nat) : List (Reg × Word) :=
  mkLvlK lay (mkLo lay ci + kk) ++
    (if lay = 0 ∧ mkLo lay ci + kk = 11 then
      [(.x12, BitVec.ofNat 64 (13336 + 48 * (sh / 32 % 2)))] else [])

def mkLvlCheckN (lay ci sh kk : Nat) : Bool :=
  specB (mkLvlAllow lay (mkLo lay ci + kk)) [] baseK
    (runAt (mkLvlKN lay ci sh kk) [] (mkShp lay ci sh + mkOff lay ci kk + 2) [])
    (mkLvlSpecN lay ci sh kk) [] (mkLvlPostN lay ci sh kk) (mkKeep ++ (.x14 :: mkLvlKeep (mkLo lay ci + kk)))

def mkLvlCheckD (lay ci sh kk : Nat) : Bool :=
  specB (mkLvlAllow lay (mkLo lay ci + kk)) [] baseK
    (runAt (mkLvlK lay (mkLo lay ci + kk)) [] (mkShp lay ci sh + mkOff lay ci kk + 2) [.jmp])
    (mkLvlSpecD lay ci sh kk) [] (mkLvlPostD lay ci kk) (mkKeep ++ mkLvlKeep (mkLo lay ci + kk))

def mkLvlCheck (lay ci sh kk : Nat) : Bool :=
  if mkIsDisp lay ci kk then mkLvlCheckD lay ci sh kk else mkLvlCheckN lay ci sh kk

/-! ## Blocks -/

/-- The entry and every level of block `sh` of chunk `ci` of layer `lay`. -/
def mkBlockCheck (lay ci sh : Nat) : Bool :=
  mkEntCheck lay ci sh && (List.range (mkBits lay ci)).all (mkLvlCheck lay ci sh)

/-- Blocks `lo .. lo + n - 1` of chunk `ci` of layer `lay`. -/
def mkChunkCheck (lay ci lo n : Nat) : Bool := (List.range' lo n).all (mkBlockCheck lay ci)

/-! ## The compare -/

/-- The compare copy `c` (after layer 0's shape block `shp_0_1_c`). -/
def cmpPc (c : Nat) : Nat := 38675 + 53 * c
def cmpDst (c : Nat) : Nat := 13336 + 48 * (c / 32 % 2)
def cmpK (c : Nat) : List (Reg × Word) := baseK ++ [(.x12, BitVec.ofNat 64 (cmpDst c))]
def cmpBr1 (c : Nat) (d : Bool) : Br := ⟨.ne, .ld (kw (cmpDst c)), .ld (kw 160), d⟩
def cmpBr2 (c : Nat) (d : Bool) : Br := ⟨.ne, .ld (kw (cmpDst c + 8)), .ld (kw 168), d⟩

/-- The high-word difference is zero exactly when the high words agree. -/
def cmpDelta (c : Nat) : E := .bin .sub (.ld (kw (cmpDst c + 8))) (.ld (kw 168))

/-- Low words agree: high-word difference is the HALT exit code. -/
def cmpAcc (c : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, cmpDelta c)], [], cmpPc c + 7, true, 7, [cmpBr1 c false], none, 7⟩
def cmpRej1 (c : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], cmpPc c + 11, true, 5, [cmpBr1 c true], none, 5⟩
def cmpCheck (c : Nat) : Bool :=
  specB [] [] [] (runAt (cmpK c) [] (cmpPc c) [.br false]) (cmpAcc c) [] [] [] &&
  specB [] [] [] (runAt (cmpK c) [] (cmpPc c) [.br true]) (cmpRej1 c) [] [] []

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart26

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart27

/-! # The final comparison using the HALT exit code

The root stays at its route-specific x12 destination. The low-word mismatch branches to the unchanged HALT(1) arm. Otherwise a subtraction of the high
words supplies the HALT exit code, which is zero exactly when those words agree. Every accepting
path takes seven instructions followed by HALT; the fuel bound conservatively remains nine.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest)

/-- A digest is determined by its two doublewords. -/
theorem cmpDig_eq_iff (d e : Digest) :
    d = e ↔ (d.extractLsb' 0 64 = e.extractLsb' 0 64 ∧ d.extractLsb' 64 64 = e.extractLsb' 64 64) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    apply BitVec.eq_of_toNat_eq
    have e1 := congrArg BitVec.toNat h1
    have e2 := congrArg BitVec.toNat h2
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one] at e1 e2
    have hd : d.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact d.isLt
    have he : e.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact e.isLt
    rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] at e2
    rw [← Nat.mod_add_div d.toNat (2 ^ 64), ← Nat.mod_add_div e.toNat (2 ^ 64), e1, e2]

/-- The state at a compare copy. -/
structure CmpIn (pk root : Digest) (t : MachineState) : Prop where
  copy : ∃ c, c < 64 ∧ t.pc = pcOf (cmpPc c) ∧ KnownOK (cmpK c) t ∧ DigAt t (cmpDst c) root
  pk : PkOK pk t

theorem cmpBr1_holds (c : Nat) (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 (cmpDst c)) = x)
    (hy : t.getMem (BitVec.ofNat 64 160) = y) (d : Bool) : Br.holds t (cmpBr1 c d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr1, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]

theorem cmpBr2_holds (c : Nat) (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 (cmpDst c + 8)) = x)
    (hy : t.getMem (BitVec.ofNat 64 168) = y) (d : Bool) : Br.holds t (cmpBr2 c d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr2, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]

set_option maxRecDepth 100000

/-- All 64 actual comparison copies satisfy the two complete path specifications. -/
theorem cmpCheck_all : (List.range 64).all cmpCheck = true := by decide +kernel

theorem cmpCheck_at (c : Nat) (hc : c < 64) : cmpCheck c = true :=
  List.all_eq_true.mp cmpCheck_all c (List.mem_range.mpr hc)

/-- Comparing both words by the final HALT exit code takes at most eight cycles. -/
theorem cmp_good (pk root : Digest) (t : MachineState) (h : CmpIn pk root t) (Q : Prop) (hQ : Q) :
    GoodQ t 9 8 Q 8 (pure (root == pk, 0)) := by
  obtain ⟨c, hc, hpc, hknown, hroot⟩ := h.copy
  have hck := cmpCheck_at c hc
  simp only [cmpCheck, Bool.and_eq_true] at hck
  obtain ⟨hA, hR1⟩ := hck
  have hr0 : t.getMem (BitVec.ofNat 64 (cmpDst c)) = root.extractLsb' 0 64 := hroot.1
  have hr8 : t.getMem (BitVec.ofNat 64 (cmpDst c + 8)) = root.extractLsb' 64 64 := hroot.2
  have hp0 : t.getMem (BitVec.ofNat 64 160) = pk.extractLsb' 0 64 := h.pk.1
  have hp8 : t.getMem (BitVec.ofNat 64 168) = pk.extractLsb' 64 64 := h.pk.2
  have b1 := cmpBr1_holds c t _ _ hr0 hp0
  by_cases hlo : root.extractLsb' 0 64 = pk.extractLsb' 0 64
  · obtain ⟨u, hu⟩ := spec_run hA t hpc hknown (by
      intro b hb
      simp only [cmpAcc, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 false).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpAcc])
    have h10 : u.getReg .x10 = root.extractLsb' 64 64 - pk.extractLsb' 64 64 := by
      simpa only [cmpDelta, E.eval, BinOp.eval, kw, hr8, hp8] using
        hu.regs (.x10, cmpDelta c) (by simp [cmpAcc])
    have heq : u.getReg .x10 = 0 ↔ root = pk := by
      rw [h10]
      change root.extractLsb' 64 64 - pk.extractLsb' 64 64 = 0#64 ↔ root = pk
      rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add, cmpDig_eq_iff]
      simp only [hlo, true_and]
    have hg := GoodQ.halt (Q := Q) (A := 1) (hu.ecall rfl) h5 (fun _ => ⟨hQ, le_refl 1⟩)
    have hb : decide (u.getReg .x10 = 0) = (root == pk) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, heq]
    rw [hb] at hg
    exact GoodQ.steps' hu.steps hg (by simp [cmpAcc]) (by simp [cmpAcc])
      (fun q => ⟨q, by simp [cmpAcc]⟩)
  · have hne : root ≠ pk := fun e => hlo (by rw [e])
    rw [show (root == pk) = false from beq_eq_false_iff_ne.mpr hne]
    obtain ⟨u, hu⟩ := spec_run hR1 t hpc hknown (by
      intro b hb
      simp only [cmpRej1, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 true).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpRej1])
    have h10 : u.getReg .x10 = 1 := hu.regs (.x10, kw 1) (by simp [cmpRej1])
    exact GoodQ.steps' hu.steps (GoodQ.reject (Q := Q) (A := 0) (hu.ecall rfl) h5 h10)
      (by simp [cmpRej1]) (by simp [cmpRej1]) (fun q => ⟨q, by simp [cmpRej1]⟩)

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart27

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart28

/-! Kernel check of every transition copy of the four layers (`copyCheck`): the transitions, their rejections and
the leaf-pk blocks. -/

namespace SigGolfCandidate.T3M.CanonicalPort

set_option maxRecDepth 100000

theorem ld3Check_ok : ld3Check = true := by decide +kernel
theorem layerCheck_3 : layerCheck 3 0 1 = true := by decide +kernel
theorem layerCheck_2 : layerCheck 2 0 64 = true := by decide +kernel
theorem layerCheck_1 : layerCheck 1 0 64 = true := by decide +kernel
theorem layerCheck_0a : layerCheck 0 0 64 = true := by decide +kernel
theorem layerCheck_0b : layerCheck 0 64 64 = true := by decide +kernel

theorem nCopy_eq : nCopy 3 = 1 ∧ nCopy 2 = 64 ∧ nCopy 1 = 64 ∧ nCopy 0 = 128 := by decide

theorem copyCheck_at (lay c : Nat) (hlay : lay < 4) (hc : c < nCopy lay) : copyCheck lay (trPc lay c) = true := by
  obtain ⟨n3, n2, n1, n0⟩ := nCopy_eq
  have hall : ∀ lo n, layerCheck lay lo n = true → lo ≤ c → c < lo + n → copyCheck lay (trPc lay c) = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h c (List.mem_range'_1.mpr ⟨h1, h2⟩)
  interval_cases lay
  · by_cases h : c < 64
    · exact hall 0 64 layerCheck_0a (by omega) (by omega)
    · exact hall 64 64 layerCheck_0b (by omega) (by omega)
  · exact hall 0 64 layerCheck_1 (by omega) (by omega)
  · exact hall 0 64 layerCheck_2 (by omega) (by omega)
  · exact hall 0 1 layerCheck_3 (by omega) (by omega)

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart28

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart29

/-! Exact mixed-radix top-chain code layout and symbolic result specifications. -/
namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def mx (q : Nat) : Nat := if q<17 then 4 else 3
def off (i : Nat) : Word := BitVec.ofNat 64 (64*(53-i))-BitVec.ofNat 64 1664
def slot (i : Nat) : Nat := if i=0 then 512 else 528+16*i

def baseTab : List Nat := [
  82075, 82116, 82155, 82192, 82226, 82258, 82297, 82334, 82369, 82401, 82431, 82468,
  82503, 82536, 82566, 82594, 82628, 82660, 82690, 82717, 82742, 82774, 82804, 82832,
  82857, 82880, 82921, 82960, 82997, 83031, 83063, 83102, 83139, 83174, 83206, 83236,
  83273, 83308, 83341, 83371, 83399, 83433, 83465, 83495, 83522, 83547, 83579, 83609,
  83637, 83662, 83685, 83726, 83765, 83802, 83836, 83868, 83907, 83944, 83979, 84011,
  84041, 84078, 84113, 84146, 84176, 84204, 84238, 84270, 84300, 84327, 84352, 84384,
  84414, 84442, 84467, 84490, 84531, 84570, 84607, 84641, 84673, 84712, 84749, 84784,
  84816, 84846, 84883, 84918, 84951, 84981, 85009, 85043, 85075, 85105, 85132, 85157,
  85189, 85219, 85247, 85272, 85295, 85336, 85375, 85412, 85446, 85478, 85517, 85554,
  85589, 85621, 85651, 85688, 85723, 85756, 85786, 85814, 85848, 85880, 85910, 85937,
  85962, 85994, 86024, 86052, 86077, 86100, 86141, 86180, 86217, 86251, 86283, 86322,
  86359, 86394, 86426, 86456, 86493, 86528, 86561, 86591, 86619, 86653, 86685, 86715,
  86742, 86767, 86799, 86829, 86857, 86882, 86905, 86946, 86985, 87022, 87056, 87088,
  87127, 87164, 87199, 87231, 87261, 87298, 87333, 87366, 87396, 87424, 87458, 87490,
  87520, 87547, 87572, 87604, 87634, 87662, 87687, 87710, 87751, 87790, 87827, 87861,
  87893, 87932, 87969, 88004, 88036, 88066, 88103, 88138, 88171, 88201, 88229, 88263,
  88295, 88325, 88352, 88377, 88409, 88439, 88467, 88492, 88515, 88556, 88595, 88632,
  88666, 88698, 88737, 88774, 88809, 88841, 88871, 88908, 88943, 88976, 89006, 89034,
  89068, 89100, 89130, 89157, 89182, 89214, 89244, 89272, 89297, 89320, 89361, 89400,
  89437, 89471, 89503, 89542, 89579, 89614, 89646, 89676, 89713, 89748, 89781, 89811,
  89839, 89873, 89905, 89935, 89962, 89987, 90019, 90049, 90077, 90102, 90125, 90166,
  90205, 90242, 90276, 90308, 90347, 90384, 90419, 90451, 90481, 90518, 90553, 90586,
  90616, 90644, 90678, 90710, 90740, 90767, 90792, 90824, 90854, 90882, 90907, 90930,
  90971, 91010, 91047, 91081, 91113, 91152, 91189, 91224, 91256, 91286, 91323, 91358,
  91391, 91421, 91449, 91483, 91515, 91545, 91572, 91597, 91629, 91659, 91687, 91712,
  91735, 91776, 91815, 91852, 91886, 91918, 91957, 91994, 92029, 92061, 92091, 92128,
  92163, 92196, 92226, 92254, 92288, 92320, 92350, 92377, 92402, 92434, 92464, 92492,
  92517, 92540, 92581, 92620, 92657, 92691, 92723, 92762, 92799, 92834, 92866, 92896,
  92933, 92968, 93001, 93031, 93059, 93093, 93125, 93155, 93182, 93207, 93239, 93269,
  93297, 93322, 93345, 93386, 93425, 93462, 93496, 93528, 93567, 93604, 93639, 93671,
  93701, 93738, 93773, 93806, 93836, 93864, 93898, 93930, 93960, 93987, 94012, 94044,
  94074, 94102, 94127, 94150, 94191, 94230, 94267, 94301, 94333, 94372, 94409, 94444,
  94476, 94506, 94543, 94578, 94611, 94641, 94669, 94703, 94735, 94765, 94792, 94817,
  94849, 94879, 94907, 94932, 94955, 94996, 95035, 95072, 95106, 95138, 95177, 95214,
  95249, 95281, 95311, 95348, 95383, 95416, 95446, 95474, 95508, 95540, 95570, 95597,
  95622, 95654, 95684, 95712, 95737, 95760, 95792, 95822, 95849, 95874, 95904, 95932,
  95957, 95980, 96007, 96032, 96054, 96074, 96099, 96122, 96142]

def base (q dB dC : Nat) : Nat :=
  baseTab.getD (if q<17 then 25*q+5*dB+dC else 425+4*dB+dC) 0

/-- T3Z (BIG3): an inline chain's part is one word shorter than before (the head loads its header word from the
WOTS header table, so neither the running `s9` bump nor the first rung's `sb` is left; a max-digit copy has no
bump). -/
def partLen (q d : Nat) : Nat :=
  if d=mx q then 4 else if d+1=mx q then 6 else 5+2*(mx q-d)
def pcB (q dB dC : Nat) : Nat := base q dB dC+2*mx q+1
def pcC (q dB dC : Nat) : Nat := pcB q dB dC+partLen q dB
def pcX (q dB dC : Nat) : Nat := pcC q dB dC+partLen q dC
def entW (q k : Nat) : Nat := if q<17 then 176744+256*k+8*q else 209920+8*k

/-- T3Z (BIG3): a table-slot head loading the header word of chain `i` with its first digit `d` from the header
table (`addi a0; addi a2, a0, 48; ld s9, hOff i d(t3); sd s9, 16(a0); sd tp, 24(a0)`), then `j tgt` past the first
rung's `sb` (6 steps). -/
def headJD (rb : Reg) (o : Word) (tgt i d : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) o)).set .x12 (addC (addC (.reg rb) o) 48)).set .x25 (hLoad i d),
    [(kAt rb o 24,.reg .x4),(kAt rb o 16,hLoad i d)],
    [.valid (kAt rb o 24) 8,.valid (kAt rb o 16) 8,.valid (hKey i d) 8]⟩,.c (pcOf tgt),.jump,6,6⟩

/-- T3Z: the table-slot head for the penultimate digit (no `addi a2, a0, 48`: its terminal rung sets x12), the
header word with the first digit `d` read from the table, then `j tgt` (5 steps). -/
def headJDTerm (rb : Reg) (o : Word) (tgt i d : Nat) : Result :=
  ⟨⟨(RegFile.init.set .x10 (addC (.reg rb) o)).set .x25 (hLoad i d),
    [(kAt rb o 24,.reg .x4),(kAt rb o 16,hLoad i d)],
    [.valid (kAt rb o 24) 8,.valid (kAt rb o 16) 8,.valid (hKey i d) 8]⟩,.c (pcOf tgt),.jump,5,5⟩

/-- T3Z: the rest of a table-slot chain's first rung after its `sb` (`[li a2, slot]`), up to the `ecall` (0 or 1
step from `p`). -/
def tailR (slot : Option Nat) (p : Nat) : Result :=
  let n := if slot.isSome then 1 else 0
  ⟨⟨(match slot with
      | some a => RegFile.init.set .x12 (.c (BitVec.ofNat 64 a))
      | none => RegFile.init), [], []⟩, .c (pcOf (p + n)), .ecall, n, n⟩

/-- T3Z: inline terminal head (no `addi a2, a0, 48`; `li a2, slot` before the `ecall`), the header word with the
first digit `d` read from the table: up to the first `ecall` (5 steps). -/
def headRHT (rb : Reg) (o : Word) (d sl p i : Nat) : Result :=
  {headRH rb o d (some sl) p i with pc:=.c (pcOf (p+5)),steps:=5,cycles:=5}

def shift10 (w : Reg) (b : Nat) : E :=
  if b<10 then .bin .sll (.reg w) (.c (BitVec.ofNat 64 (10-b)))
  else .bin .srl (.reg w) (.c (BitVec.ofNat 64 (b-10)))
def dispatchR (q : Nat) : Result :=
  let sh := shift10 (if q<9 then .x16 else .x17) (if q<9 then 7*q else 7*(q-9))
  let a := .bin .add (.bin .and sh (.reg .x24)) (.reg .x15)
  ⟨⟨RegFile.init.set .x14 a,[],[]⟩,
    .bin .and (.bin .add a (.c (BitVec.ofNat 64 (32*q) + 18446744073709549984#64))) (.c (~~~1#64)),.jump,4,4⟩

def tailDispatchR : Result :=
  let a := .bin .add (.bin .sll (.reg .x29) (.c 5)) (.c 843776)
  ⟨⟨(RegFile.init.set .x14 a).set .x15 (.c 843776),[],[]⟩,
    .bin .and a (.c (~~~1#64)),.jump,4,4⟩

def rungsOK (q d0 sl p : Nat) : Bool :=
  (List.range' d0 (mx q-d0)).all fun m =>
    rOK (vrun (p+2*(m-d0)) 3)
      (rungR m (if m+1=mx q then some sl else none) (p+2*(m-d0)))

/-- T3Z: every table-slot rung of a shared block entered past its `sb`. -/
def tailsOK (q sl p : Nat) : Bool :=
  (List.range (mx q)).all fun m =>
    rOK (vrun (p+2*m+1) 2) (tailR (if m+1=mx q then some sl else none) (p+2*m+1))

def partOK (q i d p : Nat) : Bool :=
  if d=mx q then rOK (vrun p 4) (copyFH .x19 (off i) (slot i) p)
  else rOK (vrun p 8)
      (if d+1=mx q then headRHT .x19 (off i) d (slot i) p i
       else headRH .x19 (off i) d none p i) &&
    rungsOK q (d+1) (slot i) (p+6)

def entCheck (q k : Nat) : Bool :=
  let dA := k%(mx q+1)
  let dB := k/(mx q+1)%(mx q+1)
  let dC := k/(mx q+1)^2
  if dA=mx q then rOK (vrun (entW q k) 7)
    (copyN .x19 (off (3*q)) (slot (3*q)) (pcB q dB dC))
  else rOK (vrun (entW q k) 7)
    (if dA+1=mx q then headJDTerm .x19 (off (3*q)) (base q dB dC+2*dA+1) (3*q) dA
     else headJD .x19 (off (3*q)) (base q dB dC+2*dA+1) (3*q) dA)

def dispatchOK (q dB dC : Nat) : Bool :=
  rOK (vrun (pcX q dB dC) 5)
    (if q<16 then dispatchR (q+1) else if q=16 then tailDispatchR else retR)

def blockCheck (q dB dC : Nat) : Bool :=
  tailsOK q (slot (3*q)) (base q dB dC) &&
  rungsOK q 0 (slot (3*q)) (base q dB dC) &&
  partOK q (3*q+1) dB (pcB q dB dC) &&
  partOK q (3*q+2) dC (pcC q dB dC) && dispatchOK q dB dC

def tripleCheck (q : Nat) : Bool :=
  ((List.range ((mx q+1)^3)).all fun k => entCheck q k) &&
  ((List.range ((mx q+1)^2)).all fun x => blockCheck q (x/(mx q+1)) (x%(mx q+1)))

theorem piece_steps45 {p f : Nat} {r : Result} (h : vrun p f=some r)
    (hp : p<210432) (s : MachineState) (hpc : s.pc=pcOf p)
    (ho : ∀o∈r.st.obl,o.holds s) :
    Steps CanonicalNative.fixture s r.steps r.cycles (r.toState s) :=
  symRun_sound h (lcodeAt p (by omega)) s hpc ((Oblig.all_iff _ _).mpr ho)

theorem piece_ecall45 {p f : Nat} {r : Result} (h : vrun p f=some r)
    (hp : p<210432) (s : MachineState) (ho : ∀o∈r.st.obl,o.holds s)
    (hst : r.stop=.ecall) :
    fetch CanonicalNative.fixture (r.toState s)=some (.base .ECALL) :=
  symRun_ecall h (lcodeAt p (by omega)) s ((Oblig.all_iff _ _).mpr ho) hst

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart29

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart30

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 100000
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

theorem land_mask10 (n k : Nat) (hk : k≤7) :
    n &&& (1024*(2^k-1))=1024*(n/1024%2^k) := by
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_and,show (1024 : Nat)=2^10 by norm_num,Nat.testBit_two_pow_mul,Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
  by_cases h : 10≤j
  · simp only [h,decide_true,Bool.true_and,show j-10+10=j by omega]
    by_cases hj : j-10<k <;> simp [hj]
  · simp [h]

theorem field_shl10 (W s k : Nat) (hs : s≤10) (hk : k≤7) :
    W*2^s%2^64/1024%2^k=W/2^(10-s)%2^k := by
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_mod_two_pow,Nat.testBit_mod_two_pow,show (1024 : Nat)=2^10 by norm_num,
    Nat.testBit_div_two_pow,Nat.testBit_div_two_pow,Nat.testBit_mod_two_pow,Nat.testBit_mul_two_pow]
  by_cases hj : j<k
  · simp only [hj,decide_true,Bool.true_and,show j+10<64 by omega,show s≤j+10 by omega]
    rw [show j+10-s=j+(10-s) by omega]
  · simp [hj]

def shiftWord10 (W : Word) (b : Nat) : Word := if b<10 then W<<<(10-b) else W>>>(b-10)

theorem word_mask10 (W : Word) (b : Nat) (hb : b<64) :
    shiftWord10 W b &&& 130048#64=BitVec.ofNat 64 (1024*(W.toNat/2^b%128)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,show (130048#64).toNat=1024*(2^7-1) by rfl,land_mask10 _ _ (by decide)]
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 1024*(W.toNat/2^b%128)<2^64 by omega)]
  apply congrArg (fun x => 1024*x)
  unfold shiftWord10
  split_ifs with h
  · simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
    rw [field_shl10 _ _ _ (by omega) (by decide),show 10-(10-b)=b by omega]
    rfl
  · simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    rw [Nat.div_div_eq_div_mul,
      show 2^(b-10)*1024=2^b by rw [show (1024 : Nat)=2^10 by rfl,←pow_add];congr 1;omega]
    rfl

theorem shift10_eval (s : MachineState) (w : Reg) (W : Word) (hw : s.getReg w=W)
    (b : Nat) (hb : b<64) : (shift10 w b).eval s=shiftWord10 W b := by
  unfold shift10 shiftWord10
  split_ifs with h <;> simp only [E.eval,BinOp.eval,hw,BitVec.toNat_ofNat]
  · rw [Nat.mod_eq_of_lt (show 10-b<2^64 by omega),Nat.mod_eq_of_lt (show 10-b<64 by omega)]
  · rw [Nat.mod_eq_of_lt (show b-10<2^64 by omega),Nat.mod_eq_of_lt (show b-10<64 by omega)]

theorem dispatch_window (X : Word) (q : Nat) :
    X + 712704#64 + (BitVec.ofNat 64 (32*q) + 18446744073709549984#64) =
      X + pcOf 176744 + BitVec.ofNat 64 (32*q) := by
  calc X + 712704#64 + (BitVec.ofNat 64 (32*q) + 18446744073709549984#64) =
      X + (712704#64 + 18446744073709549984#64) + BitVec.ofNat 64 (32*q) := by ac_rfl
    _ = _ := by rfl

theorem dispatch_target (W : Word) (b q : Nat) (hb : b<64) (hq : q<17) :
    ((shiftWord10 W b &&& 130048#64)+pcOf 176744+BitVec.ofNat 64 (32*q)) &&& ~~~1#64 =
      pcOf (entW q (W.toNat/2^b%128)) := by
  rw [word_mask10 W b hb,ofNat_add_ofNat,ofNat_add_ofNat,
    even_andNot1' _ (by omega)]
  unfold pcOf entW
  rw [if_pos hq]
  apply congrArg (BitVec.ofNat 64)
  omega

theorem prologue_target (v : Digest) :
    (((v.extractLsb' 0 64 <<< 10) &&& 130048#64)+pcOf 176744) &&& ~~~1#64 =
      pcOf (176744+256*(v.toNat%128)) := by
  have h := dispatch_target (v.extractLsb' 0 64) 0 0 (by decide) (by decide)
  simpa [shiftWord10,entW,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,
    Nat.mod_mod_of_dvd _ (show 128∣2^64 by decide)] using h

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart30

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart31

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def sourceWord (v : Digest) (q : Nat) : Word := if q<9 then v.extractLsb' 0 64 else v.extractLsb' 63 64
def sourceBit (q : Nat) : Nat := if q<9 then 7*q else 7*(q-9)

theorem extract_field (v : Digest) (a b : Nat) (h : b+7≤64) :
    (v.extractLsb' a 64).toNat/2^b%128=v.toNat/2^(a+b)%128 := by
  have hr := Search.ext_shr_mask v a b 7 h
  have hl : (v.extractLsb' a 64 >>> b) &&& 127#64=
      BitVec.ofNat 64 ((v.extractLsb' a 64).toNat/2^b%128) := by
    have he : v.extractLsb' a 64=BitVec.ofNat 64 (v.extractLsb' a 64).toNat := by
      apply BitVec.eq_of_toNat_eq; simp
    conv_lhs => rw [he]
    rw [ofNat_shr _ _ (v.extractLsb' a 64).isLt,Search.ofNat_and127]
  have hh := hl.symm.trans hr
  exact (ofNat_inj (by omega) (by omega)).mp hh

theorem source_field (v : Digest) (q : Nat) (hq : q<17) :
    (sourceWord v q).toNat/2^(sourceBit q)%128=Search.topRank v q := by
  unfold sourceWord sourceBit Search.topRank
  split_ifs with h
  · simpa using extract_field v 0 (7*q) (by omega)
  · rw [extract_field v 63 (7*(q-9)) (by omega),show 63+7*(q-9)=7*q by omega]

theorem dispatch_step {p q : Nat} (hq : q<17) (hp : p<210432)
    (hrun : vrun p 5=some (dispatchR q)) (s : MachineState) (v : Digest)
    (hpc : s.pc=pcOf p) (h16 : s.getReg .x16=v.extractLsb' 0 64)
    (h17 : s.getReg .x17=v.extractLsb' 63 64)
    (h24 : s.getReg .x24=130048#64) (h15 : s.getReg .x15=712704#64) :
    ∃t, Steps CanonicalNative.fixture s 4 4 t ∧ t.pc=pcOf (entW q (Search.topRank v q)) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hW : s.getReg (if q<9 then .x16 else .x17)=sourceWord v q := by
    unfold sourceWord
    split_ifs <;> assumption
  have hb : sourceBit q<64 := by unfold sourceBit;split_ifs <;> omega
  refine ⟨(dispatchR q).toState s,piece_steps45 hrun hp s hpc (by simp [dispatchR]),?_,?_,?_⟩
  · change (((shift10 (if q<9 then .x16 else .x17) (sourceBit q)).eval s &&& s.getReg .x24)+
      s.getReg .x15+(BitVec.ofNat 64 (32*q)+18446744073709549984#64)) &&& ~~~1#64=pcOf (entW q (Search.topRank v q))
    rw [h24,h15,dispatch_window,shift10_eval s _ _ hW _ hb,dispatch_target _ _ q hb hq,source_field v q hq]
  · intro r hr
    rw [Result.toState_getReg]
    simp only [dispatchR]
    rw [RegFile.get_set_ne _ _ (show r≠.x14 by simpa using hr),RegFile.init_get_eval]
  · intro A _ _
    simp [dispatchR,rv_simp]

theorem tail_dispatch_step {p : Nat} (hp : p<210432)
    (hrun : vrun p 5=some tailDispatchR) (s : MachineState) (k : Nat) (hk : k<64)
    (hpc : s.pc=pcOf p) (h29 : s.getReg .x29=BitVec.ofNat 64 k) :
    ∃t, Steps CanonicalNative.fixture s 4 4 t ∧ t.pc=pcOf (entW 17 k) ∧
      RegsExcept s t [.x14,.x15] ∧ Frame s t (fun _ => False) := by
  refine ⟨tailDispatchR.toState s,piece_steps45 hrun hp s hpc (by simp [tailDispatchR]),?_,?_,?_⟩
  · simp only [Result.toState_pc,tailDispatchR,E.eval,BinOp.eval,h29]
    change ((BitVec.ofNat 64 k <<< 5)+BitVec.ofNat 64 843776) &&& ~~~1#64=pcOf (entW 17 k)
    rw [ofNat_shl,ofNat_add_ofNat,even_andNot1' _ (by omega)]
    unfold entW pcOf
    norm_num
    congr 1 <;> omega
  · intro r hr
    rw [Result.toState_getReg]
    simp only [tailDispatchR]
    rw [RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp)),
      RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp)),RegFile.init_get_eval]
  · intro A _ _
    simp [tailDispatchR,rv_simp]

#print axioms dispatch_step
#print axioms tail_dispatch_step
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart31

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart32

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_0 : tripleCheck 0=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart32

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart33

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_1 : tripleCheck 1=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart33

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart34

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_2 : tripleCheck 2=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart34

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart35

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_3 : tripleCheck 3=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart35

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart36

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_4 : tripleCheck 4=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart36

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart37

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_5 : tripleCheck 5=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart37

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart38

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_6 : tripleCheck 6=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart38

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart39

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_7 : tripleCheck 7=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart39

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart40

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_8 : tripleCheck 8=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart40

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart41

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_9 : tripleCheck 9=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart41

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart42

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_10 : tripleCheck 10=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart42

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart43

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_11 : tripleCheck 11=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart43

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart44

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_12 : tripleCheck 12=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart44

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart45

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_13 : tripleCheck 13=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart45

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart46

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_14 : tripleCheck 14=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart46

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart47

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_15 : tripleCheck 15=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart47

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart48

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_16 : tripleCheck 16=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart48

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart49

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem tripleCheck_17 : tripleCheck 17=true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart49

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart50

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem tripleCheck_at (q : Nat) (hq : q<18) : tripleCheck q=true := by
  interval_cases q
  exacts [tripleCheck_0, tripleCheck_1, tripleCheck_2, tripleCheck_3, tripleCheck_4, tripleCheck_5, tripleCheck_6, tripleCheck_7, tripleCheck_8, tripleCheck_9, tripleCheck_10, tripleCheck_11, tripleCheck_12, tripleCheck_13, tripleCheck_14, tripleCheck_15, tripleCheck_16, tripleCheck_17]

theorem entCheck_at (q k : Nat) (hq : q<18) (hk : k<(mx q+1)^3) : entCheck q k=true := by
  have h := tripleCheck_at q hq
  simp only [tripleCheck,Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1 k (List.mem_range.mpr hk)

theorem blockCheck_at (q dB dC : Nat) (hq : q<18) (hB : dB ≤ mx q) (hC : dC ≤ mx q) :
    blockCheck q dB dC=true := by
  have h := tripleCheck_at q hq
  simp only [tripleCheck,Bool.and_eq_true] at h
  have hh : (mx q+1)*dB+dC<(mx q+1)^2 := by
    unfold mx at *
    split_ifs at * <;> omega
  have e1 : ((mx q+1)*dB+dC)/(mx q+1)=dB := by
    unfold mx at *
    split_ifs at * <;> omega
  have e2 : ((mx q+1)*dB+dC)%(mx q+1)=dC := by
    unfold mx at *
    split_ifs at * <;> omega
  have hb := List.all_eq_true.mp h.2 ((mx q+1)*dB+dC) (List.mem_range.mpr hh)
  rwa [e1,e2] at hb

#print axioms tripleCheck_at
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart50

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart51

/-! Machine semantics of one mixed-radix top chain, with exact immutable image checks supplied separately. -/
namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false

structure NCtx where
  w : WBytes
  tree : Nat
  leaf : Nat
  S3 : Nat
  digits : Nat → Nat
  ret : Nat

namespace NCtx

def blk (c : NCtx) (i : Nat) : Nat := c.S3 - 1664 + 64 * (53 - i)
def dig (c : NCtx) (i : Nat) : Nat := c.digits i
def topMax (i : Nat) : Nat := mx (i / 3)
def last (i : Nat) : Nat := topMax i - 1

def w0 (i : Nat) : Nat := 0x101 + 2 ^ 40 * i
def w1 (c : NCtx) : Nat := hdr1 c.tree c.leaf
def pad0 (c : NCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800)
def pad1 (c : NCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800 + 32)
def val (c : NCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800 + 48)
def ok (c : NCtx) : Prop :=
  c.tree < 2 ^ 32 ∧ c.leaf < 2 ^ 32 ∧ c.S3 % 8 = 0 ∧ 0x800 + 11288 + 1664 ≤ c.S3 ∧ c.S3 + 2064 ≤ 0x7000 ∧
    c.ret < 209920

/-- T3Z (BIG3): `x28` is the midpoint of the WOTS header table's bank 0 (set by the lower layers' leaf-pk restore
`lui t3, 0xff4`); every head reads its header word from the table. -/
def known (c : NCtx) : List (Reg × Word) :=
  [(.x5, 0), (.x11, 64), (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6),
   (.x28, BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank 0 0)), (.x19, BitVec.ofNat 64 c.S3),
   (.x4, BitVec.ofNat 64 c.w1), (.x27, BitVec.ofNat 64 0x101), (.x1, pcOf c.ret)]

def kOf (c : NCtx) (q : Nat) : Nat :=
  c.dig (3*q) + (mx q+1)*c.dig (3*q+1) + (mx q+1)^2*c.dig (3*q+2)
def qb (c : NCtx) (i : Nat) : Nat := base (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
def qB (c : NCtx) (i : Nat) : Nat := pcB (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
def qC (c : NCtx) (i : Nat) : Nat := pcC (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
def qX (c : NCtx) (i : Nat) : Nat := pcX (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
def startPc (c : NCtx) (i : Nat) : Nat :=
  if i%3=0 then entW (i/3) (c.kOf (i/3)) else if i%3=1 then c.qB i else c.qC i

def rungPc (c : NCtx) (i m : Nat) : Nat :=
  if i%3=0 then c.qb i+2*m
  else c.startPc i + (if c.dig i = last i then 3 else 4) + 2*(m-c.dig i)
def endPc (c : NCtx) (i : Nat) : Nat :=
  if i%3=0 then c.qB i else if i%3=1 then c.qC i else c.qX i

/-- The memory written by the chains `0 .. i - 1`. -/
def Wr (c : NCtx) (i : Nat) (A : Nat) : Prop :=
  (0x200 ≤ A ∧ A < 0x5D0) ∨ (c.S3 - 1664 + 64 * (54 - i) ≤ A ∧ A < c.blk 0 + 80)
def WrIn (c : NCtx) (i : Nat) (A : Nat) : Prop :=
  c.Wr i A ∨ (c.blk i + 16 ≤ A ∧ A < c.blk i + 32) ∨ (c.blk i + 48 ≤ A ∧ A < c.blk i + 80)

/-- The chain blocks hold the witness at the start `s0`, and (T3Z) the image data (the WOTS header table) is in
place. -/
def Orig0 (c : NCtx) (s0 : MachineState) : Prop :=
  (∀ i, i < 54 → ∀ k < 8, OrigW c.w s0 (c.blk i + 8 * k)) ∧ SigGolfCandidate.T3M.CanonicalPort.Verify.DataOK s0

def Base (c : NCtx) (s0 : MachineState) (W : Nat → Prop) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → s.getReg x = s0.getReg x) ∧ Frame s0 s W ∧
    (∀ j < acc.length, DigAt s (slot j) (acc.getD j 0))

/-- Before chain `i`'s code (T3Z: no running `x25`; the heads read the header table). -/
def ChainIn (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr i) acc s ∧ acc.length = i ∧ s.pc = pcOf (c.startPc i)

def HdrOk (c : NCtx) (i : Nat) (s : MachineState) : Prop :=
  (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat % 2 ^ 32 = 0x101 ∧
    (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat / 2 ^ 40 = i ∧
    s.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1

def StepInv (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (s : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc s ∧ acc.length = i ∧
    c.HdrOk i s ∧ DigAt s (c.blk i + 48) v ∧ s.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    (m < last i → s.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48)) ∧ s.pc = pcOf (c.rungPc i m)

def PreHash (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (t : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc t ∧ acc.length = i ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (w0 i + 2 ^ 32 * m) ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1 ∧ DigAt t (c.blk i + 48) v ∧
    t.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    t.getReg .x12 = BitVec.ofNat 64 (if m = last i then slot i else c.blk i + 48) ∧
    t.pc = pcOf (c.rungPc i m + (if m = last i then 2 else 1)) ∧ fetch vimage t = some (.base .ECALL)

def EndInv (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (i + 1)) acc s ∧ acc.length = i + 1 ∧ s.pc = pcOf (c.endPc i)

/-! ## Geometry -/

theorem blk_props (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) :
    c.blk i % 8 = 0 ∧ 0x800 + 11288 ≤ c.blk i ∧ c.blk i + 80 ≤ 0x7000 := by
  obtain ⟨-, -, h64, hlo, hhi, -⟩ := hc
  unfold blk; refine ⟨?_, ?_, ?_⟩ <;> omega

theorem blk_le (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) : c.blk i + 64 * i = c.blk 0 := by
  obtain ⟨-, -, -, hlo, -⟩ := hc
  unfold blk; omega

theorem slot_props (i : Nat) (hi : i < 54) : slot i % 16 = 0 ∧ 512 ≤ slot i ∧ slot i + 32 ≤ 0x580 := by
  unfold slot; split <;> omega

theorem base_off (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) (k : Nat) (hk : k ≤ 80) :
    BitVec.ofNat 64 c.S3 + (off i + BitVec.ofNat 64 k) = BitVec.ofNat 64 (c.blk i + k) := by
  obtain ⟨-, -, -, hlo, hhi, -⟩ := hc
  unfold off blk
  rw [ofNat_add_off _ _ _ _ (by omega) (by omega), show c.S3 + 64 * (53 - i) - 1664 = c.S3 - 1664 + 64 * (53 - i) by
    omega]

theorem base_off0 (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) :
    BitVec.ofNat 64 c.S3 + off i = BitVec.ofNat 64 (c.blk i) := by
  obtain ⟨-, -, -, hlo, hhi, -⟩ := hc
  unfold off blk
  rw [ofNat_add_off0 _ _ _ (by omega) (by omega), show c.S3 + 64 * (53 - i) - 1664 = c.S3 - 1664 + 64 * (53 - i) by
    omega]

theorem w0_hdr0 (c : NCtx) (i m : Nat) (hi : i < 54) (hm : m < 256) (ht : c.tree < 2 ^ 32) :
    w0 i + 2 ^ 32 * m = hdr0 1 (0 : Layer).val c.tree (m + 256 * i) := by
  rw [hdr0_eq _ _ _ _ (by norm_num) (by norm_num) ht (by omega)]
  unfold w0; simp; ring

theorem w0_lt (i m : Nat) (hi : i < 54) (hm : m < 256) : w0 i + 2 ^ 32 * m < 2 ^ 64 := by
  unfold w0; omega

/-- The machine's hash input at a step of chain `i`. -/
theorem chain_hashInput (c : NCtx) (hc : c.ok) (i m : Nat) (hi : i < 54) (hm : m < 256) (v : Digest)
    (t : MachineState) (h10 : t.getReg .x10 = BitVec.ofNat 64 (c.blk i))
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)))
    (hp0 : DigAt t (c.blk i) (c.pad0 i)) (hp1 : DigAt t (c.blk i + 32) (c.pad1 i))
    (h16 : t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (w0 i + 2 ^ 32 * m))
    (h24 : t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1)
    (hv : DigAt t (c.blk i + 48) v) :
    hashInput t = toQ (chainInputP 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) v) := by
  obtain ⟨h64, hlo, hhi⟩ := c.blk_props hc i hi
  apply hashInput_toQ t _ 0 (c.blk i) (chainInputP_length _ _ _ _ _ _ _ _) h10 (by omega) (by omega) h11
    (by norm_num)
  rw [wordsOf_chainInputP, show 8 * (0 + 1) = 2 + (2 + (2 + 2)) from rfl, readWords_add, readWords_add,
    readWords_add, readWords_two, readWords_two, readWords_two, readWords_two, hp0.1, hp0.2,
    show c.blk i + 8 * 2 = c.blk i + 16 by ring, h16,
    show c.blk i + 16 + 8 = c.blk i + 24 by ring, h24,
    show c.blk i + 16 + 8 * 2 = c.blk i + 32 by ring, hp1.1, hp1.2,
    show c.blk i + 32 + 8 * 2 = c.blk i + 48 by ring, hv.1, hv.2, w0_hdr0 c i m hi hm hc.1]
  rfl

theorem orig_frame {c : NCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i k : Nat} (hi : i < 54) (hk : k < 8) (hW : ¬ W (c.blk i + 8 * k)) :
    OrigW c.w t (c.blk i + 8 * k) := by
  have := c.blk_props hc i hi
  unfold OrigW
  rw [hF _ (by omega) hW]
  exact h0.1 i hi k hk

theorem pads_at {c : NCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat}
    (hi : i < 54) (hF : Frame s0 t (c.WrIn i)) :
    DigAt t (c.blk i) (c.pad0 i) ∧ DigAt t (c.blk i + 32) (c.pad1 i) := by
  have hb := c.blk_props hc i hi
  have nW : ∀ k, k = 0 ∨ k = 1 ∨ k = 4 ∨ k = 5 → ¬ c.WrIn i (c.blk i + 8 * k) := by
    intro k hk hw
    have := c.blk_le hc i hi
    have hlo := hc.2.2.2.1
    unfold WrIn Wr blk at *
    omega
  have o0 := orig_frame hF h0 hc hi (k := 0) (by omega) (nW 0 (by omega))
  have o1 := orig_frame hF h0 hc hi (k := 1) (by omega) (nW 1 (by omega))
  have o4 := orig_frame hF h0 hc hi (k := 4) (by omega) (nW 4 (by omega))
  have o5 := orig_frame hF h0 hc hi (k := 5) (by omega) (nW 5 (by omega))
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at o0 o1
  rw [show 8 * 4 = 32 by rfl] at o4
  rw [show c.blk i + 8 * 5 = c.blk i + 32 + 8 by ring] at o5
  refine ⟨DigAt_origW o0 o1 (by omega), ?_⟩
  have := DigAt_origW o4 o5 (by omega)
  rwa [show c.blk i + 32 - 0x800 = c.blk i - 0x800 + 32 by omega] at this

theorem val_at {c : NCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat} (hi : i < 54)
    (hF : Frame s0 t (c.Wr i)) : DigAt t (c.blk i + 48) (c.val i) := by
  have hb := c.blk_props hc i hi
  have nW : ∀ k, k = 6 ∨ k = 7 → ¬ c.Wr i (c.blk i + 8 * k) := by
    intro k hk hw
    have := c.blk_le hc i hi
    have hlo := hc.2.2.2.1
    unfold Wr blk at *
    omega
  have o6 := orig_frame hF h0 hc hi (k := 6) (by omega) (nW 6 (by omega))
  have o7 := orig_frame hF h0 hc hi (k := 7) (by omega) (nW 7 (by omega))
  rw [show c.blk i + 8 * 6 = c.blk i + 48 by ring] at o6
  rw [show c.blk i + 8 * 7 = c.blk i + 48 + 8 by ring] at o7
  have := DigAt_origW o6 o7 (by omega)
  rwa [show c.blk i + 48 - 0x800 = c.blk i - 0x800 + 48 by omega] at this

theorem topMax_bounds (i : Nat) : 3 ≤ topMax i ∧ topMax i ≤ 4 := by
  unfold topMax mx; split <;> omega

theorem last_bounds (i : Nat) : 2 ≤ last i ∧ last i ≤ 3 := by
  have := topMax_bounds i; unfold last; omega

theorem rungPc_succ (c : NCtx) (i m : Nat) (hd : c.dig i ≤ m) :
    c.rungPc i (m+1) = c.rungPc i m+2 := by
  unfold rungPc; split_ifs <;> omega

theorem rungPc_end (c : NCtx) (i : Nat) (hi : i < 54) (hd : c.dig i < topMax i) :
    c.rungPc i (last i) + 3 = c.endPc i := by
  have hm := topMax_bounds i
  have e1 : i%3=1 → c.dig (3*(i/3)+1)=c.dig i := fun h => by rw [show 3*(i/3)+1=i by omega]
  have e2 : i%3=2 → c.dig (3*(i/3)+2)=c.dig i := fun h => by rw [show 3*(i/3)+2=i by omega]
  unfold rungPc endPc startPc qb qB qC qX pcX pcC pcB partLen
  unfold last topMax at *
  split_ifs <;> omega

/-- The step registers hold the steps. -/
theorem posE_eval (c : NCtx) {s0 s : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x) (i m : Nat) (hm : m ≤ last i) :
    (posE m).eval s = BitVec.ofNat 64 m := by
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hm3 : m ≤ 3 := by have := last_bounds i; omega
  interval_cases m
  · rfl
  · exact kr .x6 1 (by simp [known]) (by decide)
  · exact kr .x7 2 (by simp [known]) (by decide)
  · exact kr .x8 3 (by simp [known]) (by decide)

theorem w0_low (i m : Nat) (hi : i < 54) (hm : m < 256) :
    (BitVec.ofNat 64 (w0 i + 2 ^ 32 * m)).toNat % 2 ^ 32 = 0x101 ∧
      (BitVec.ofNat 64 (w0 i + 2 ^ 32 * m)).toNat / 2 ^ 40 = i := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w0_lt i m hi hm)]
  unfold w0; constructor <;> omega

theorem w0_low0 (i : Nat) (hi : i < 54) :
    (BitVec.ofNat 64 (w0 i)).toNat % 2 ^ 32 = 0x101 ∧ (BitVec.ofNat 64 (w0 i)).toNat / 2 ^ 40 = i := by
  have := w0_low i 0 hi (by omega)
  rwa [Nat.mul_zero, Nat.add_zero] at this

end NCtx
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart51

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart52

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.CanonicalPort.Nonbinary
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def DigitsOk (c : NCtx) : Prop := ∀i,i<54 → c.dig i ≤ topMax i

theorem dig_group_le (c : NCtx) (hd : c.DigitsOk) (q k : Nat) (hq : q<18) (hk : k<3) :
    c.dig (3*q+k) ≤ mx q := by
  have h := hd (3*q+k) (by omega)
  simpa only [topMax,show (3*q+k)/3=q by omega] using h

theorem kOf_lt (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) :
    c.kOf q < (mx q+1)^3 := by
  have h0 := c.dig_group_le hd q 0 hq (by decide)
  have h1 := c.dig_group_le hd q 1 hq (by decide)
  have h2 := c.dig_group_le hd q 2 hq (by decide)
  simp only [Nat.add_zero] at h0
  unfold kOf mx at *
  split_ifs at * <;> omega

theorem kOf_digits (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) :
    c.kOf q%(mx q+1)=c.dig (3*q) ∧
    c.kOf q/(mx q+1)%(mx q+1)=c.dig (3*q+1) ∧
    c.kOf q/(mx q+1)^2=c.dig (3*q+2) := by
  have h0 := c.dig_group_le hd q 0 hq (by decide)
  have h1 := c.dig_group_le hd q 1 hq (by decide)
  have h2 := c.dig_group_le hd q 2 hq (by decide)
  simp only [Nat.add_zero] at h0
  unfold kOf mx at *
  split_ifs at * <;> exact ⟨by omega,by omega,by omega⟩

theorem blk_at (c : NCtx) (hd : c.DigitsOk) (i : Nat) (hi : i<54) :
    blockCheck (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))=true :=
  blockCheck_at _ _ _ (by omega) (c.dig_group_le hd _ 1 (by omega) (by decide))
    (c.dig_group_le hd _ 2 (by omega) (by decide))

theorem chk_headJ (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (hd : c.dig i< last i) :
    vrun (c.startPc i) 7=some (headJD .x19 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  have he := entCheck_at q (c.kOf q) (by omega) (c.kOf_lt hds q (by omega))
  obtain ⟨k1,k2,k3⟩ := c.kOf_digits hds q (by omega)
  have hd' : c.dig (3*q)< mx q-1 := by simpa only [last,topMax,eq] using hd
  unfold entCheck at he
  rw [k1,k2,k3,if_neg (by omega),if_neg (by omega)] at he
  have hs : c.startPc (3*q)=entW q (c.kOf q) := by simp [startPc,h0,eq]
  have hr : c.rungPc (3*q) (c.dig (3*q))=base q (c.dig (3*q+1)) (c.dig (3*q+2))+2*c.dig (3*q) := by
    simp [rungPc,qb,h0,eq]
  rw [hs,hr]
  exact rOK_eq he

theorem chk_headJTerm (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (hd : c.dig i=last i) :
    vrun (c.startPc i) 7=some (headJDTerm .x19 (off i) (c.rungPc i (c.dig i)+1) i (c.dig i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  have he := entCheck_at q (c.kOf q) (by omega) (c.kOf_lt hds q (by omega))
  obtain ⟨k1,k2,k3⟩ := c.kOf_digits hds q (by omega)
  have hm := topMax_bounds (3*q)
  have hd' : c.dig (3*q)=mx q-1 := by simpa only [last,topMax,eq] using hd
  simp only [topMax,eq] at hm
  unfold entCheck at he
  rw [k1,k2,k3,if_neg (by omega),if_pos (by omega)] at he
  have hs : c.startPc (3*q)=entW q (c.kOf q) := by simp [startPc,h0,eq]
  have hr : c.rungPc (3*q) (c.dig (3*q))=base q (c.dig (3*q+1)) (c.dig (3*q+2))+2*c.dig (3*q) := by
    simp [rungPc,qb,h0,eq]
  rw [hs,hr]
  exact rOK_eq he

theorem chk_copyJ (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3=0) (hd : c.dig i=topMax i) :
    vrun (c.startPc i) 7=some (copyN .x19 (off i) (slot i) (c.endPc i)) := by
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  have he := entCheck_at q (c.kOf q) (by omega) (c.kOf_lt hds q (by omega))
  obtain ⟨k1,k2,k3⟩ := c.kOf_digits hds q (by omega)
  have hd' : c.dig (3*q)=mx q := by simpa only [topMax,eq] using hd
  unfold entCheck at he
  rw [k1,k2,k3,if_pos hd'] at he
  have hs : c.startPc (3*q)=entW q (c.kOf q) := by simp [startPc,h0,eq]
  have he' : c.endPc (3*q)=pcB q (c.dig (3*q+1)) (c.dig (3*q+2)) := by simp [endPc,qB,h0,eq]
  rw [hs,he']
  exact rOK_eq he

theorem part_at (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54) (h0 : i%3≠0) :
    partOK (i/3) i (c.dig i) (c.startPc i)=true := by
  obtain ⟨q,r,rfl,hr⟩ : ∃q r,i=3*q+r ∧ r<3 := ⟨i/3,i%3,by omega,by omega⟩
  have eq : (3*q+r)/3=q := by omega
  have hb := c.blk_at hds (3*q+r) hi
  rw [eq] at hb
  unfold blockCheck at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨-,hB⟩,hC⟩,-⟩ := hb
  unfold startPc qB qC
  rw [if_neg h0,eq]
  rcases (show r=1 ∨ r=2 by omega) with rfl|rfl
  · rw [if_pos (by omega)];exact hB
  · rw [if_neg (by omega)];exact hC

theorem chk_headR (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3≠0) (hd : c.dig i< last i) :
    vrun (c.startPc i) 8=some (headRH .x19 (off i) (c.dig i) none (c.startPc i) i) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  have hd' : c.dig i< mx (i/3)-1 := hd
  rw [if_neg (by omega),Bool.and_eq_true] at hp
  rw [if_neg (by omega)] at hp
  exact rOK_eq hp.1

theorem chk_headRTerm (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3≠0) (hd : c.dig i=last i) :
    vrun (c.startPc i) 8=some (headRHT .x19 (off i) (c.dig i) (slot i) (c.startPc i) i) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  have hd' : c.dig i=mx (i/3)-1 := hd
  have hm : 3≤ mx (i/3) := (topMax_bounds i).1
  rw [if_neg (by omega),Bool.and_eq_true] at hp
  rw [if_pos (by omega)] at hp
  exact rOK_eq hp.1

theorem chk_copyF (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54)
    (h0 : i%3≠0) (hd : c.dig i=topMax i) :
    vrun (c.startPc i) 4=some (copyFH .x19 (off i) (slot i) (c.startPc i)) := by
  have hp := c.part_at hds i hi h0
  unfold partOK at hp
  change c.dig i=mx (i/3) at hd
  rw [if_pos hd] at hp
  exact rOK_eq hp

theorem chk_rung (c : NCtx) (hds : c.DigitsOk) (i m : Nat) (hi : i<54)
    (hm : c.dig i ≤ m) (hm2 : m ≤ last i) (hfirst : i%3≠0 → c.dig i< m) :
    vrun (c.rungPc i m) 3=some (rungR m (if m=last i then some (slot i) else none) (c.rungPc i m)) := by
  have hmx := topMax_bounds i
  by_cases h0 : i%3=0
  · obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
    have eq : 3*q/3=q := by omega
    have hb := c.blk_at hds (3*q) hi
    rw [eq] at hb
    unfold blockCheck at hb
    simp only [Bool.and_eq_true] at hb
    have hn : m< mx q := by simpa only [last,topMax,eq] using (show m< topMax (3*q) by unfold last at hm2;omega)
    have hh := List.all_eq_true.mp hb.1.1.1.2 m (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
    have hr : c.rungPc (3*q) m=base q (c.dig (3*q+1)) (c.dig (3*q+2))+2*m := by simp [rungPc,qb,h0,eq]
    have ht : (m+1=mx q) ↔ m=last (3*q) := by unfold last topMax;rw [eq];omega
    simpa only [rungsOK,Nat.sub_zero,Nat.add_zero,hr,ht] using rOK_eq hh
  · have hp := c.part_at hds i hi h0
    have hd := hfirst h0
    have hn : c.dig i< mx (i/3) := by change c.dig i< topMax i;unfold last at hm2;omega
    unfold partOK at hp
    rw [if_neg (by omega),Bool.and_eq_true] at hp
    have hmmax : m< mx (i/3) := by change m<topMax i;unfold last at hm2;omega
    have hh := List.all_eq_true.mp hp.2 m (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
    have hr : c.rungPc i m=c.startPc i+6+2*(m-(c.dig i+1)) := by
      unfold rungPc
      rw [if_neg h0,if_neg (by omega)]
      omega
    have ht : (m+1=mx (i/3)) ↔ m=last i := by unfold last topMax;omega
    simpa only [hr,ht] using rOK_eq hh

/-- T3Z: a table-slot chain's first rung entered past its `sb` (the head's `j` target). -/
theorem chk_tail (c : NCtx) (hds : c.DigitsOk) (i m : Nat) (hi : i<54) (h0 : i%3=0) (hm2 : m ≤ last i) :
    vrun (c.rungPc i m+1) 2=some (tailR (if m=last i then some (slot i) else none) (c.rungPc i m+1)) := by
  have hmx := topMax_bounds i
  obtain ⟨q,rfl⟩ : ∃q,i=3*q := ⟨i/3,by omega⟩
  have eq : 3*q/3=q := by omega
  have hb := c.blk_at hds (3*q) hi
  rw [eq] at hb
  unfold blockCheck at hb
  simp only [Bool.and_eq_true] at hb
  have hn : m< mx q := by simpa only [last,topMax,eq] using (show m< topMax (3*q) by unfold last at hm2;omega)
  have hh := List.all_eq_true.mp hb.1.1.1.1 m (List.mem_range.mpr hn)
  have hr : c.rungPc (3*q) m=base q (c.dig (3*q+1)) (c.dig (3*q+2))+2*m := by simp [rungPc,qb,h0,eq]
  have ht : (m+1=mx q) ↔ m=last (3*q) := by unfold last topMax;rw [eq];omega
  simpa only [hr,ht] using rOK_eq hh

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx

end CanonicalPortPart52

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart53

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

theorem baseTab_all : (baseTab.all fun x => decide (x<96160))=true := by decide +kernel

theorem base_lt (q dB dC : Nat) : base q dB dC<96160 := by
  unfold base
  rw [List.getD_eq_getElem?_getD]
  split
  · cases hn : baseTab[25*q+5*dB+dC]? with
    | none => simp
    | some x => simpa using List.all_eq_true.mp baseTab_all x (List.mem_of_getElem? hn)
  · cases hn : baseTab[425+4*dB+dC]? with
    | none => simp
    | some x => simpa using List.all_eq_true.mp baseTab_all x (List.mem_of_getElem? hn)

theorem mx_bounds (q : Nat) : 3≤ mx q ∧ mx q≤4 := by unfold mx;split <;> omega

theorem partLen_le (q d : Nat) : partLen q d≤14 := by
  have hm := mx_bounds q
  unfold partLen
  split_ifs <;> omega

namespace NCtx

theorem qX_lt (c : NCtx) (i : Nat) : c.qX i<97000 := by
  have hb := base_lt (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
  have h1 := partLen_le (i/3) (c.dig (3*(i/3)+1))
  have h2 := partLen_le (i/3) (c.dig (3*(i/3)+2))
  have hm := mx_bounds (i/3)
  unfold qX pcX pcC pcB
  omega

theorem startPc_lt (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<54) : c.startPc i<210432 := by
  have hb := base_lt (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
  have h1 := partLen_le (i/3) (c.dig (3*(i/3)+1))
  have hm := mx_bounds (i/3)
  have hk := c.kOf_lt hds (i/3) (by omega)
  unfold startPc entW qB qC pcC pcB mx at *
  split_ifs at * <;> omega

theorem rungPc_lt (c : NCtx) (i m : Nat) (hm : m≤ last i) : c.rungPc i m<210432 := by
  have hb := base_lt (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
  have h1 := partLen_le (i/3) (c.dig (3*(i/3)+1))
  have hmx := mx_bounds (i/3)
  have hl := last_bounds i
  unfold rungPc qb startPc qB qC pcC pcB
  split_ifs <;> omega

theorem inline_rungPc (c : NCtx) (i : Nat) (h0 : i%3≠0) :
    c.rungPc i (c.dig i)=c.startPc i+(if c.dig i=last i then 3 else 4) := by
  simp [rungPc,h0]

theorem inline_copy_end (c : NCtx) (i : Nat) (h0 : i%3≠0) (hd : c.dig i=topMax i) :
    c.startPc i+4=c.endPc i := by
  have e1 : i%3=1 → c.dig (3*(i/3)+1)=c.dig i := fun h => by rw [show 3*(i/3)+1=i by omega]
  have e2 : i%3=2 → c.dig (3*(i/3)+2)=c.dig i := fun h => by rw [show 3*(i/3)+2=i by omega]
  unfold startPc endPc qB qC qX pcX pcC partLen
  unfold topMax at hd
  split_ifs <;> omega

end NCtx
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart53

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart54

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false

theorem tailR_keeps (slot : Option Nat) (p : Nat) : Keeps (tailR slot p) [.x12] := by
  intro x hx
  simp only [tailR]
  split
  · rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
  · rfl

namespace NCtx

/-- **The HASH of step `m` of chain `i`.** -/
theorem prehash_step (c : NCtx) (hc : c.ok) (s0 : MachineState) (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i m : Nat) (hi : i < 54) (hm : m ≤ last i) (hd : c.dig i ≤ m)
    (acc : List Digest) (v : Digest) (t : MachineState) (ht : c.PreHash s0 i acc m v t) :
    t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = toQ (chainInputP 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) v) ∧
      ∀ a : BitVec 256,
        (m < last i → c.StepInv s0 i acc (m + 1) (a.extractLsb' 0 128) (writeHash t a)) ∧
        (m = last i → c.EndInv s0 i (acc ++ [a.extractLsb' 0 128]) (writeHash t a)) := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h16, h24, hv, h10, h12, hpc, -⟩ := ht
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → t.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have t5 : t.getReg .x5 = 0 := kr _ _ (by simp [known]) (by decide)
  have t11 : t.getReg .x11 = BitVec.ofNat 64 64 := kr _ _ (by simp [known]) (by decide)
  obtain ⟨p0, p1⟩ := pads_at hc h0 hi hF
  refine ⟨t5, ?_, ?_, ?_⟩
  · apply hashArgs_const t (c.blk i) 64 (if m = last i then slot i else c.blk i + 48) h10 t11 h12 (by omega)
      (by omega) (by omega)
    · split <;> omega
    · split <;> omega
  · exact c.chain_hashInput hc i m hi (by omega) v t h10 t11 p0 p1 h16 h24 hv
  · intro a
    have hdst : ∀ (B : Nat), t.getReg .x12 = BitVec.ofNat 64 B → B + 32 < 2 ^ 64 →
        Frame t (writeHash t a) (fun A => B ≤ A ∧ A < B + 32) := fun B hB hB' => Frame.writeHash t a B hB hB'
    refine ⟨fun hm2 => ?_, fun hm2 => ?_⟩
    · have d12 : t.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48) := by rw [h12, if_neg (by omega)]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.WrIn i) := (hF.trans fr).mono (by
        intro A _ h; rcases h with h | h
        · exact h
        · right; right; omega)
      have fget : ∀ A, A < 2 ^ 64 → ¬ (c.blk i + 48 ≤ A ∧ A < c.blk i + 48 + 32) →
          (writeHash t a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A hA hn => fr A hA hn
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, hlen,
        ⟨?_, ?_, ?_⟩, DigAt.writeHash_lo t a _ d12 (by omega),
        by rw [getReg_writeHash]; exact h10, fun _ => by rw [getReg_writeHash]; exact d12, ?_⟩
      · have hj' := hS j hj
        have hsj := slot_props j (by omega)
        exact hj'.frame fr (by omega) (by omega) (by omega)
      · rw [fget _ (by omega) (by omega), h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w0_lt i m hi (by omega))]
        unfold w0; omega
      · rw [fget _ (by omega) (by omega), h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w0_lt i m hi (by omega))]
        unfold w0; omega
      · rw [fget _ (by omega) (by omega)]; exact h24
      · rw [pc_writeHash, hpc, if_neg (by omega), c.rungPc_succ i m hd, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1
    · subst hm2
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (slot i) := by rw [h12, if_pos rfl]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.Wr (i + 1)) := (hF.trans fr).mono (by
        intro A _ h
        have := c.blk_le hc i hi
        have hlo := hc.2.2.2.1
        unfold WrIn Wr blk at *
        omega)
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, by simp [hlen], ?_⟩
      · rw [List.length_append, List.length_singleton] at hj
        by_cases hjl : j < acc.length
        · have hj' := hS j hjl
          have hsj := slot_props j (by omega)
          have hmono : slot j + 16 ≤ slot i := by unfold slot; split_ifs <;> omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
          exact hj'.frame fr (by omega) (by omega) (by omega)
        · have hj2 : j = acc.length := by omega
          subst hj2
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, hlen]
          exact DigAt.writeHash_lo t a _ d12 (by omega)
      · have hd3 : c.dig i < topMax i := by omega
        rw [pc_writeHash, hpc, if_pos rfl, ← c.rungPc_end i hi hd3, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1

/-- **One rung**: `sb POS_m, 20(a0)` (and `li a2, slot` for the last step), up to the `ecall`. -/
theorem rung_piece (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m p : Nat) (hi : i < 54) (hm : m ≤ last i) (hp : p < 210432)
    (hrun : vrun p 3 = some (rungR m (if m = last i then some (slot i) else none) p)) (s : MachineState)
    (hpc : s.pc = pcOf p) (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (c.blk i)) (hH : c.HdrOk i s) :
    ∃ t, Steps vimage s (if m = last i then 2 else 1) (if m = last i then 2 else 1) t ∧ fetch vimage t = some (.base .ECALL) ∧
      (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = last i → t.getReg .x12 = BitVec.ofNat 64 (slot i)) ∧ (m < last i → t.getReg .x12 = s.getReg .x12) ∧
      t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (w0 i + 2 ^ 32 * m) ∧
      Frame s t (fun A => A = c.blk i + 16) ∧ t.pc = pcOf (p + (if m = last i then 2 else 1)) := by
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  set r := rungR m (if m = last i then some (slot i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, rungR, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show ((E.reg .x10).eval s).toNat % 8 = 0
      simp only [E.eval, h10, BitVec.toNat_ofNat]; omega
    · show accessValid (Addr.eval s ⟨some (.reg .x10), 20⟩) 1 = true
      simp only [Addr.eval, E.eval, h10]
      rw [show (20 : Word) = BitVec.ofNat 64 20 from rfl, ofNat_add_ofNat]
      exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps45 hrun hp s hpc hobl
  have hec := piece_ecall45 hrun hp s hobl (by simp [hr, rungR])
  have hn : r.steps = (if m = last i then 2 else 1) ∧ r.cycles = (if m = last i then 2 else 1) := by
    simp only [hr, rungR]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := rungR_keeps m (if m = last i then some (slot i) else none) p
  have key : (⟨some (.reg .x10), 16⟩ : Addr).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
    simp only [Addr.eval, E.eval, h10]
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then
        StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (c.blk i + 16))) 4 (BitVec.ofNat 64 m)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, rungR]
    rw [memEval_one s _ _ (c.blk i + 16) A key (by omega) hA]
    split
    · have e1 : (addC (E.reg .x10) 16).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
        rw [addC_eval]; simp only [E.eval, h10]
        rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
      simp only [E.eval, BinOp.eval]
      rw [e1, c.posE_eval hk hR i m hm]
    · rfl
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h2 => ?_, fun h2 => ?_, ?_,
    fun A hA hn => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_pos h2]
    rw [RegFile.get_set_self _ _ (by decide)]; rfl
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_neg (show m ≠ last i by omega)]
    rw [RegFile.init_get_eval]
  · rw [tmem _ (by omega), if_pos rfl]
    obtain ⟨hl, hj, -⟩ := hH
    rw [stepByte _ _ _ _ (by omega) (by omega) (by omega) hl hj]
    congr 1; unfold w0; ring
  · rw [tmem _ hA, if_neg hn]
  · rw [Result.toState_pc]; simp only [hr, rungR]
    by_cases h2 : m = last i <;> simp [h2, E.eval]

/-- T3Z: **the rest of a table-slot chain's first rung** after its `sb` (the head's jump target): `[li a2, slot]`,
up to the `ecall`. -/
theorem tail_piece (i m p : Nat) (hp : p < 210432)
    (hrun : vrun p 2 = some (tailR (if m = last i then some (slot i) else none) p)) (s : MachineState)
    (hpc : s.pc = pcOf p) :
    ∃ t, Steps vimage s (if m = last i then 1 else 0) (if m = last i then 1 else 0) t ∧
      fetch vimage t = some (.base .ECALL) ∧ (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = last i → t.getReg .x12 = BitVec.ofNat 64 (slot i)) ∧ (m ≠ last i → t.getReg .x12 = s.getReg .x12) ∧
      Frame s t (fun _ => False) ∧ t.pc = pcOf (p + (if m = last i then 1 else 0)) := by
  set r := tailR (if m = last i then some (slot i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by simp [hr, tailR]
  have hst := piece_steps45 hrun hp s hpc hobl
  have hec := piece_ecall45 hrun hp s hobl (by simp [hr, tailR])
  have hn : r.steps = (if m = last i then 1 else 0) ∧ r.cycles = (if m = last i then 1 else 0) := by
    simp only [hr, tailR]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := tailR_keeps (if m = last i then some (slot i) else none) p
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h2 => ?_, fun h2 => ?_,
    fun A hA _ => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, tailR, if_pos h2]
    rw [RegFile.get_set_self _ _ (by decide)]; rfl
  · rw [Result.toState_getReg]
    simp only [hr, tailR, if_neg h2]
    rw [RegFile.init_get_eval]
  · rw [Result.toState_getMem]; simp [hr, tailR, memEval]
  · rw [Result.toState_pc]; simp only [hr, tailR]
    by_cases h2 : m = last i <;> simp [h2, E.eval]

/-- **A rung after a step's hash.** -/
theorem rung_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m : Nat) (hi : i < 54) (hm : m ≤ last i) (hp : c.rungPc i m < 210432)
    (hrun : vrun (c.rungPc i m) 3 = some (rungR m (if m = last i then some (slot i) else none) (c.rungPc i m)))
    (acc : List Digest) (v : Digest) (s : MachineState) (hs : c.StepInv s0 i acc m v s) :
    ∃ t, Steps vimage s (if m = last i then 2 else 1) (if m = last i then 2 else 1) t ∧ c.PreHash s0 i acc m v t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hH, hv, h10, h12, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  obtain ⟨t, hst, hec, hreg, h12a, h12b, h16, hfr, hpc'⟩ :=
    c.rung_piece hc hk i m (c.rungPc i m) hi hm hp hrun s hpc hR h10 hH
  refine ⟨t, hst, ⟨⟨fun x hx => ?_, (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, h16, ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR x hx
  · intro A _ h; rcases h with h | h
    · exact h
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [hfr _ (by omega) (by omega)]; exact hH.2.2
  · exact hv.frame hfr (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide)]; exact h10
  · by_cases h2 : m = last i
    · rw [h12a h2, if_pos h2]
    · rw [h12b (by omega), h12 (by omega), if_neg h2]
  · rw [hpc']

end NCtx
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart54

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart55
namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
namespace NCtx

theorem kAt_eval (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i < 54) (k : Nat) (hk : k ≤ 80) : (kAt .x19 (off i) k).eval s = BitVec.ofNat 64 (c.blk i + k) := by
  simp only [kAt, Addr.eval, E.eval, h19]
  exact c.base_off hc i hi k hk

theorem lAt_eval (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i < 54) (k : Nat) (hk : k ≤ 80) :
    (lAt .x19 (off i) k).eval s = s.getMem (BitVec.ofNat 64 (c.blk i + k)) := by
  simp only [lAt, E.eval, addC_eval, h19]
  rw [c.base_off hc i hi k hk]

/-- T3Z (BIG3, the table-load proof of erickeigen's 59cbf8ec / our T3X `LCtx.header_load` on the top layer): a
head's header load `ld s9, hOff i d(t3)` reads word `8 i + d` of the header table's bank 0, which the chain phase
never writes (its frame lies below `0x7000`). -/
theorem header_load (c : NCtx) (hc : c.ok) {s0 s : MachineState} (h0 : c.Orig0 s0) (i d : Nat)
    (hi : i < 54) (hd : d < 8) (hF : Frame s0 s (c.Wr i))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank 0 0)) :
    (Oblig.valid (hKey i d) 8).holds s ∧
      (hLoad i d).eval s = BitVec.ofNat 64 (w0 i + 2 ^ 32 * d) := by
  have hb := c.blk_props hc 0 (by omega)
  have hA : 2 ^ 23 + 4096 ≤ SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * 0 + 64 * i + 8 * d ∧
      SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * 0 + 64 * i + 8 * d + 8 ≤ 2 ^ 24 := by
    unfold SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA; omega
  have key : (hKey i d).eval s = BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * 0 + 64 * i + 8 * d) := by
    simp only [hKey, Addr.eval, E.eval, h28, hOff]
    change BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank 0 0) +
      (BitVec.ofNat 64 (64 * i + 8 * d) - BitVec.ofNat 64 2048) =
        BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * 0 + 64 * i + 8 * d)
    rw [ofNat_add_off0 (SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank 0 0) (64 * i + 8 * d) 2048
      (by unfold SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA; omega)
      (by unfold SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA; omega)]
    apply congrArg (BitVec.ofNat 64)
    unfold SigGolfCandidate.T3M.CanonicalPort.Verify.headerBank SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA
    omega
  have fr : s.getMem (BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * 0 + 64 * i + 8 * d)) =
      s0.getMem (BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * 0 + 64 * i + 8 * d)) := by
    apply hF (SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * 0 + 64 * i + 8 * d) (by omega)
    unfold Wr
    intro h
    rcases h with h | h <;> omega
  refine ⟨?_, ?_⟩
  · show accessValid ((hKey i d).eval s) 8 = true
    rw [key]
    exact valid_ofNat _ 8 hA.2 (by unfold SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA; omega)
  · have he : (addC (.reg .x28) (hOff i d)).eval s =
        BitVec.ofNat 64 (SigGolfCandidate.T3M.CanonicalPort.Verify.HDATA + 4096 * 0 + 64 * i + 8 * d) := by
      simpa only [hKey, Addr.eval, addC_eval, E.eval] using key
    change s.getMem ((addC (.reg .x28) (hOff i d)).eval s) = _
    rw [he, fr, h0.2.header 0 i d (by norm_num) (by omega) hd]
    all_goals (congr 1 <;> unfold w0 <;> omega)

theorem copy_mem (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i < 54) (A : Nat) (hA : A < 2 ^ 64) :
    memEval s (copyMem .x19 (off i) (slot i)) (BitVec.ofNat 64 A) =
      if A = slot i + 8 then s.getMem (BitVec.ofNat 64 (c.blk i + 56))
      else if A = slot i then s.getMem (BitVec.ofNat 64 (c.blk i + 48)) else s.getMem (BitVec.ofNat 64 A) := by
  have hs := slot_props i hi
  unfold copyMem
  rw [memEval_two s _ _ _ _ (slot i + 8) (slot i) A rfl rfl (by omega) (by omega) hA,
    c.lAt_eval hc h19 i hi 56 (by omega), c.lAt_eval hc h19 i hi 48 (by omega)]

theorem copy_obl (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i < 54) : ∀ o ∈ copyObl .x19 (off i), o.holds s := by
  have hb := c.blk_props hc i hi
  simp only [copyObl, List.mem_cons, List.not_mem_nil, or_false]
  rintro o (rfl | rfl)
  · show accessValid ((kAt .x19 (off i) 56).eval s) 8 = true
    rw [c.kAt_eval hc h19 i hi 56 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid ((kAt .x19 (off i) 48).eval s) 8 = true
    rw [c.kAt_eval hc h19 i hi 48 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)

theorem copy_post (c : NCtx) (hc : c.ok) {s0 s t : MachineState} (h0 : c.Orig0 s0) (i : Nat)
    (hi : i < 54) (acc : List Digest) (hlen : acc.length = i) (hF : Frame s0 s (c.Wr i))
    (hS : ∀ j < acc.length, DigAt s (slot j) (acc.getD j 0))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3)
    (htm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) = memEval s (copyMem .x19 (off i) (slot i)) (BitVec.ofNat 64 A)) :
    Frame s0 t (c.Wr (i + 1)) ∧ ∀ j < (acc ++ [c.val i]).length,
      DigAt t (slot j) ((acc ++ [c.val i]).getD j 0) := by
  have hb := c.blk_props hc i hi
  have hs := slot_props i hi
  have tm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = slot i + 8 then s.getMem (BitVec.ofNat 64 (c.blk i + 56))
      else if A = slot i then s.getMem (BitVec.ofNat 64 (c.blk i + 48)) else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (htm A hA).trans (c.copy_mem hc h19 i hi A hA)
  have hfr : Frame s t (fun A => A = slot i + 8 ∨ A = slot i) := by
    intro A hA hn
    rw [tm A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  refine ⟨(hF.trans hfr).mono ?_, fun j hj => ?_⟩
  · intro A _ h
    have := c.blk_le hc i hi
    have hlo := hc.2.2.2.1
    rcases h with h | h
    · unfold Wr at h ⊢; unfold blk at h this ⊢; omega
    · left; omega
  · rw [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < acc.length
    · have hsj := slot_props j (by omega)
      have hmono : slot j + 16 ≤ slot i := by unfold slot; split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
      exact (hS j hjl).frame hfr (by omega) (by omega) (by omega)
    · have hj2 : j = acc.length := by omega
      subst hj2
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, hlen]
      have hv := val_at hc h0 hi hF
      refine ⟨?_, ?_⟩
      · rw [tm _ (by omega), if_neg (by omega), if_pos rfl]; exact hv.1
      · rw [tm _ (by omega), if_pos rfl]; exact hv.2

/-- **The max-digit copy of a table-slot chain** (`A = 3q`; T3Z: no `s9` update), then `j` past the shared
block's `A` rungs (5 steps). -/
theorem copyN_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54)
    (hp0 : c.startPc i < 210432)
    (hrun : vrun (c.startPc i) 7 = some (copyN .x19 (off i) (slot i) (c.endPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  set r := copyN .x19 (off i) (slot i) (c.endPc i) with hr
  have hst := piece_steps45 hrun hp0 s hpc (by simpa [hr, copyN] using c.copy_obl hc h19 i hi)
  have hkeep := copyN_keeps .x19 (off i) (slot i) (c.endPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i hi acc hlen hF hS h19
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen], ?_⟩⟩
  rw [Result.toState_pc]; rfl

/-- **The max-digit copy of an inline chain** (`B`, `C`; T3Z: no bump, 4 instructions). -/
theorem copyFH_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hp0 : c.startPc i < 210432)
    (hend : c.startPc i + 4 = c.endPc i)
    (hrun : vrun (c.startPc i) 4 = some (copyFH .x19 (off i) (slot i) (c.startPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 4 4 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  set r := copyFH .x19 (off i) (slot i) (c.startPc i) with hr
  have hst := piece_steps45 hrun hp0 s hpc (by simpa [hr, copyFH] using c.copy_obl hc h19 i hi)
  have hkeep := copyFH_keeps .x19 (off i) (slot i) (c.startPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i hi acc hlen hF hS h19
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen], ?_⟩⟩
  rw [Result.toState_pc]; simp only [hr, copyFH, E.eval]; rw [hend]


end NCtx
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart55

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart56
namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false

theorem headJD_keeps (rb : Reg) (o : Word) (tgt i d : Nat) :
    Keeps (headJD rb o tgt i d) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headJD]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem headJDTerm_keeps (rb : Reg) (o : Word) (tgt i d : Nat) :
    Keeps (headJDTerm rb o tgt i d) [.x10, .x25] := by
  intro x hx
  simp only [headJDTerm]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

namespace NCtx
/-- **The head of a table-slot chain** (`A = 3q`; T3Z: the header word of chain `i` with its first digit read from
the header table, then `j` past the first rung's `sb`) up to the first `ecall` (6 steps). -/
theorem headJ_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hd : c.dig i < last i)
    (hp0 : c.startPc i < 210432) (hp1 : c.rungPc i (c.dig i) + 1 < 210432)
    (hrun1 : vrun (c.startPc i) 7 = some (headJD .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)))
    (hrun2 : vrun (c.rungPc i (c.dig i) + 1) 2 =
      some (tailR (if c.dig i = last i then some (slot i) else none) (c.rungPc i (c.dig i) + 1)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 6 6 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load hc h0 i (c.dig i) hi (by omega) hF (kr _ _ (by simp [known]) (by decide))
  set r := headJD .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJD, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl)
    · show accessValid ((kAt .x19 (off i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (off i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · exact htable.1
  have hst1 := piece_steps45 hrun1 hp0 s hpc hobl
  set t1 := r.toState s with ht1
  have hkeep := headJD_keeps .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)
  have a0e : (addC (E.reg .x19) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have t10 : t1.getReg .x10 = BitVec.ofNat 64 (c.blk i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJD]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  have t12 : t1.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJD]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide), addC_eval, a0e,
      show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  have tmem : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 24 then BitVec.ofNat 64 c.w1
      else if A = c.blk i + 16 then BitVec.ofNat 64 (w0 i + 2 ^ 32 * c.dig i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [ht1, Result.toState_getMem]
    simp only [hr, headJD]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    change (if A = c.blk i + 24 then s.getReg .x4 else if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), htable.2]
  have hfr1 : Frame s t1 (fun A => A = c.blk i + 24 ∨ A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hR1 : ∀ x ∉ chainRegs, t1.getReg x = s0.getReg x := fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx)
  have hpc1 : t1.pc = pcOf (c.rungPc i (c.dig i) + 1) := by rw [ht1, Result.toState_pc]; rfl
  obtain ⟨t, hst2, hec, hreg, -, h12b, hfr2, hpc2⟩ :=
    tail_piece i (c.dig i) (c.rungPc i (c.dig i) + 1) hp1 hrun2 t1 hpc1
  have hsteps : r.steps = 6 ∧ r.cycles = 6 := ⟨rfl, rfl⟩
  rw [hsteps.1, hsteps.2] at hst1
  have hn : c.dig i ≠ last i := by omega
  rw [if_neg hn] at hst2
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨t, (hst1.trans hst2).of_eq (by norm_num) (by norm_num),
    ⟨⟨fun x hx => ?_, ((hF.trans hfr1).trans hfr2).mono ?_, fun j hj => ?_⟩, hlen, ?_,
    ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR1 x hx
  · intro A _ h
    rcases h with (h | h) | h
    · exact Or.inl h
    · right; left; omega
    · exact False.elim h
  · have hsj := slot_props j (by omega)
    exact ((hS j hj).frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_pos rfl]
  · exact (hv0.frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hreg _ (by decide)]; exact t10
  · rw [h12b hn, t12, if_neg hn]
  · rw [hpc2]; all_goals (congr 1 <;> split_ifs <;> omega)

/-- **The head of a table-slot chain at the penultimate digit** (`A = 3q`; no `addi a2, a0, 48`; T3Z: the header
word with the first digit read from the header table, then `j` to the rung's `li a2, slot`) up to the `ecall`
(6 steps). -/
theorem headJTerm_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hd : c.dig i = last i)
    (hp0 : c.startPc i < 210432) (hp1 : c.rungPc i (c.dig i) + 1 < 210432)
    (hrun1 : vrun (c.startPc i) 7 = some (headJDTerm .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)))
    (hrun2 : vrun (c.rungPc i (c.dig i) + 1) 2 =
      some (tailR (if c.dig i = last i then some (slot i) else none) (c.rungPc i (c.dig i) + 1)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 6 6 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load hc h0 i (c.dig i) hi (by omega) hF (kr _ _ (by simp [known]) (by decide))
  set r := headJDTerm .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJDTerm, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl)
    · show accessValid ((kAt .x19 (off i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (off i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · exact htable.1
  have hst1 := piece_steps45 hrun1 hp0 s hpc hobl
  set t1 := r.toState s with ht1
  have hkeep := headJDTerm_keeps .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)
  have a0e : (addC (E.reg .x19) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have t10 : t1.getReg .x10 = BitVec.ofNat 64 (c.blk i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJDTerm]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide), a0e]
  have tmem : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 24 then BitVec.ofNat 64 c.w1
      else if A = c.blk i + 16 then BitVec.ofNat 64 (w0 i + 2 ^ 32 * c.dig i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [ht1, Result.toState_getMem]
    simp only [hr, headJDTerm]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    change (if A = c.blk i + 24 then s.getReg .x4 else if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), htable.2]
  have hfr1 : Frame s t1 (fun A => A = c.blk i + 24 ∨ A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hR1 : ∀ x ∉ chainRegs, t1.getReg x = s0.getReg x := fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx)
  have hpc1 : t1.pc = pcOf (c.rungPc i (c.dig i) + 1) := by rw [ht1, Result.toState_pc]; rfl
  obtain ⟨t, hst2, hec, hreg, h12a, -, hfr2, hpc2⟩ :=
    tail_piece i (c.dig i) (c.rungPc i (c.dig i) + 1) hp1 hrun2 t1 hpc1
  have hsteps : r.steps = 5 ∧ r.cycles = 5 := ⟨rfl, rfl⟩
  rw [hsteps.1, hsteps.2] at hst1
  rw [if_pos hd] at hst2
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨t, (hst1.trans hst2).of_eq (by norm_num) (by norm_num),
    ⟨⟨fun x hx => ?_, ((hF.trans hfr1).trans hfr2).mono ?_, fun j hj => ?_⟩, hlen, ?_,
    ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR1 x hx
  · intro A _ h
    rcases h with (h | h) | h
    · exact Or.inl h
    · right; left; omega
    · exact False.elim h
  · have hsj := slot_props j (by omega)
    exact ((hS j hj).frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_pos rfl]
  · exact (hv0.frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hreg _ (by decide)]; exact t10
  · rw [h12a hd, if_pos hd]
  · rw [hpc2]; all_goals (congr 1 <;> split_ifs <;> omega)


end NCtx
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart56

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart57
namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false

theorem headRHT_keeps (rb : Reg) (o : Word) (d sl p i : Nat) :
    Keeps (headRHT rb o d sl p i) [.x10, .x12, .x25] :=
  headRH_keeps rb o d (some sl) p i

namespace NCtx
/-- **The head of an inline chain** (`B`, `C`; T3Z: the header word with the first digit read from the header
table, no first-rung `sb`), up to the first `ecall` (5 steps). -/
theorem headR_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hd : c.dig i < last i)
    (hp0 : c.startPc i < 210432) (hrp : c.rungPc i (c.dig i) = c.startPc i + 4)
    (hrun : vrun (c.startPc i) 8 = some (headRH .x19 (off i) (c.dig i) none (c.startPc i) i))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load hc h0 i (c.dig i) hi (by omega) hF (kr _ _ (by simp [known]) (by decide))
  set r := headRH .x19 (off i) (c.dig i) none (c.startPc i) i with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headRH, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl)
    · show accessValid ((kAt .x19 (off i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (off i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · exact htable.1
  have hst := piece_steps45 hrun hp0 s hpc hobl
  have hec := piece_ecall45 hrun hp0 s hobl (by simp [hr, headRH])
  have hn : r.steps = 5 ∧ r.cycles = 5 := ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headRH_keeps .x19 (off i) (c.dig i) none (c.startPc i) i
  have a0e : (addC (E.reg .x19) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (w0 i + 2 ^ 32 * c.dig i)
      else if A = c.blk i + 24 then BitVec.ofNat 64 c.w1 else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headRH]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    change (if A = c.blk i + 24 then s.getReg .x4 else if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), htable.2]
    split_ifs <;> simp_all
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16 ∨ A = c.blk i + 24) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [Result.toState_getReg]; simp only [hr, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  · have h2 : ¬ c.dig i = last i := by omega
    rw [Result.toState_getReg]; simp only [hr, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    simp only [h2, if_false]
    rw [addC_eval, a0e, show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  · have h2 : ¬ c.dig i = last i := by omega
    rw [Result.toState_pc]; simp only [hr, headRH, hrp]
    simp [h2, E.eval]

/-- **The head of an inline chain at the penultimate digit** (`B`, `C`; no `addi a2, a0, 48`, `li a2, slot`
before the `ecall`; T3Z: the header word read from the header table), up to the `ecall` (5 steps). -/
theorem headRTerm_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hd : c.dig i = last i)
    (hp0 : c.startPc i < 210432) (hrp : c.rungPc i (c.dig i) = c.startPc i + 3)
    (hrun : vrun (c.startPc i) 8 =
      some (headRHT .x19 (off i) (c.dig i) (slot i) (c.startPc i) i))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧
      c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load hc h0 i (c.dig i) hi (by omega) hF (kr _ _ (by simp [known]) (by decide))
  set r := headRHT .x19 (off i) (c.dig i) (slot i) (c.startPc i) i with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headRHT, headRH, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl)
    · show accessValid ((kAt .x19 (off i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (off i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · exact htable.1
  have hst := piece_steps45 hrun hp0 s hpc hobl
  have hec := piece_ecall45 hrun hp0 s hobl (by simp [hr, headRHT, headRH])
  have hn : r.steps = 5 ∧ r.cycles = 5 := ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headRHT_keeps .x19 (off i) (c.dig i) (slot i) (c.startPc i) i
  have a0e : (addC (E.reg .x19) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (w0 i + 2 ^ 32 * c.dig i)
      else if A = c.blk i + 24 then BitVec.ofNat 64 c.w1 else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headRHT, headRH]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    change (if A = c.blk i + 24 then s.getReg .x4 else if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), htable.2]
    split_ifs <;> simp_all
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16 ∨ A = c.blk i + 24) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [Result.toState_getReg]; simp only [hr, headRHT, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headRHT, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    simp only [hd, if_true, E.eval]
  · rw [Result.toState_pc]; simp only [hr, headRHT, headRH, hrp]
    simp [hd, E.eval]


end NCtx
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary

end CanonicalPortPart57

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart58

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.CanonicalPort.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem chainInputP_pad (lay : Layer) (tree leaf i step : Nat) (p0 p1 v : Digest) :
    pad64 (chainInputP lay tree leaf i step p0 p1 v)=chainInputP lay tree leaf i step p0 p1 v :=
  pad64_of_aligned _ (by rw [chainInputP_length])

theorem chainInputP_blocks (lay : Layer) (tree leaf i step : Nat) (p0 p1 v : Digest) :
    (toQ (chainInputP lay tree leaf i step p0 p1 v)).blocks=1 := by
  rw [blocks_toQ ⟨by rw [chainInputP_length];omega,by rw [chainInputP_length]⟩,chainInputP_length]

def rest (c : NCtx) (i m : Nat) (v : Digest) : M Digest :=
  (List.range' m (topMax i-m)).foldlM
    (fun v step => shortHash (chainInputP 0 c.tree c.leaf i step (c.pad0 i) (c.pad1 i) v)) v

theorem rest_succ (c : NCtx) (i m : Nat) (h : m ≤ last i) (v : Digest) :
    c.rest i m v=shortHash (chainInputP 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) v) >>= c.rest i (m+1) := by
  have hm := topMax_bounds i
  unfold last at h
  unfold rest
  rw [show topMax i-m=(topMax i-(m+1))+1 by omega,List.range'_succ,List.foldlM_cons]

theorem rest_max (c : NCtx) (i : Nat) (v : Digest) : c.rest i (topMax i) v=pure v := by
  simp [rest]

theorem chainP_rest (c : NCtx) (i d : Nat) (v : Digest) :
    chainP 0 c.tree c.leaf i d (topMax i-d) (c.pad0 i) (c.pad1 i) v=c.rest i d v := rfl

def preCost (i m : Nat) : Nat := 8+9*(last i-m)+(if m< last i then 1 else 0)

theorem steps_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<54)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀v t,c.EndInv s0 i (acc++[v]) t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K (acc++[v]))) :
    ∀k m,m+k=last i → c.dig i ≤ m → ∀v s,c.PreHash s0 i acc m v s →
      SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N+3*(topMax i-m)+5) (C+preCost i m) Q (A+preCost i m)
        (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM (c.rest i m v) (fun v => K (acc++[v]))) := by
  have hmax := topMax_bounds i
  have hlast := last_bounds i
  have hlastEq : last i+1=topMax i := by unfold last;omega
  intro k
  induction k with
  | zero =>
      intro m hm hd v s hs
      obtain rfl : m=last i := by omega
      obtain ⟨h5,hv,hin,hpost⟩ := c.prehash_step hc s0 hk h0 i (last i) hi (le_refl _) hd acc v s hs
      rw [rest_succ c i (last i) (le_refl _)]
      have hf := hs.2.2.2.2.2.2.2.2
      have H : ∀a : BitVec 256,SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ (writeHash s a) N C Q A
          (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM (c.rest i (last i+1) (a.extractLsb' 0 128)) (fun v => K (acc++[v]))) := by
        intro a
        rw [hlastEq,rest_max,SigGolfCandidate.T3M.CanonicalPort.Verify.ccM_pure]
        exact hK _ _ ((hpost a).2 rfl)
      have h3 := SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.shortHash_bind (f:=c.rest i (last i+1)) (K:=fun v => K (acc++[v])) hf h5 hv
        (by rw [chainInputP_pad];exact hin) H
      rw [chainInputP_pad,chainInputP_blocks] at h3
      exact h3.mono (by omega) (by simp [preCost]) (fun hq => ⟨hq,by simp [preCost]⟩)
  | succ k ih =>
      intro m hm hd v s hs
      obtain ⟨h5,hv,hin,hpost⟩ := c.prehash_step hc s0 hk h0 i m hi (by omega) hd acc v s hs
      rw [rest_succ c i m (by omega)]
      have hf := hs.2.2.2.2.2.2.2.2
      have H : ∀a : BitVec 256,SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ (writeHash s a) (N+3*(topMax i-(m+1))+5+2)
          (C+preCost i (m+1)+(if m+1=last i then 2 else 1)) Q
          (A+preCost i (m+1)+(if m+1=last i then 2 else 1))
          (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM (c.rest i (m+1) (a.extractLsb' 0 128)) (fun v => K (acc++[v]))) := by
        intro a
        have hrun := c.chk_rung hds i (m+1) hi (by omega) (by omega) (fun _ => by omega)
        obtain ⟨u,hu,hp⟩ := c.rung_step hc hk i (m+1) hi (by omega) (c.rungPc_lt i _ (by omega)) hrun acc _ _
          ((hpost a).1 (by omega))
        have ht := ih (m+1) (by omega) (by omega) _ _ hp
        exact SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hu ht (by split <;> omega) (by omega) (fun hq => ⟨hq,by omega⟩)
      have h3 := SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.shortHash_bind (f:=c.rest i (m+1)) (K:=fun v => K (acc++[v])) hf h5 hv
        (by rw [chainInputP_pad];exact hin) H
      rw [chainInputP_pad,chainInputP_blocks] at h3
      refine h3.mono (by omega) ?_ (fun hq => ⟨hq,?_⟩)
      · unfold preCost
        by_cases he : m+1=last i
        · rw [if_pos he,if_neg (by omega),if_pos (by omega)];omega
        · rw [if_neg he,if_pos (by omega),if_pos (by omega)];omega
      · unfold preCost
        by_cases he : m+1=last i
        · rw [if_pos he,if_neg (by omega),if_pos (by omega)];omega
        · rw [if_neg he,if_pos (by omega),if_pos (by omega)];omega

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx

end CanonicalPortPart58

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart59

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.CanonicalPort.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def tableJump (i : Nat) : Nat := if i%3=0 then 1 else 0

/-- T3Z (BIG3): a head is `5` (inline: the table load with the first digit, no first-rung `sb`) or `6` (table slot:
the same load and the jump past the first rung's `sb`); a max-digit copy is `4` (inline, no bump) or `5` (table slot,
no `s9` update). -/
def chainCost (i d : Nat) : Nat :=
  if d=topMax i then 4+tableJump i
  else 5+tableJump i+9*(topMax i-d)-(if d+1=topMax i then 1 else 0)

theorem chainCost_positive (i d : Nat) (hd : d< topMax i) :
    chainCost i d=5+tableJump i+preCost i d := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  unfold chainCost preCost
  rw [if_neg (by omega)]
  split_ifs <;> omega

theorem positive_head (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<54)
    (hd : c.dig i< topMax i) (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃t,Steps vimage s (5+tableJump i) (5+tableJump i) t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  have hl : last i+1=topMax i := by have := topMax_bounds i;unfold last;omega
  have hsp := c.startPc_lt hds i hi
  by_cases htab : i%3=0
  · have hrun2 := c.chk_tail hds i (c.dig i) hi htab (by omega)
    have hrp : c.rungPc i (c.dig i)+1<210432 := by
      have hb := base_lt (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
      have hl2 := last_bounds i
      unfold rungPc qb
      rw [if_pos htab]
      omega
    by_cases ht : c.dig i=last i
    · have hrun1 := c.chk_headJTerm hds i hi htab ht
      obtain ⟨t,hst,htp⟩ := c.headJTerm_step hc hk h0 i hi ht hsp hrp hrun1 hrun2 acc s hs
      exact ⟨t,hst.of_eq (by simp [tableJump,htab]) (by simp [tableJump,htab]),htp⟩
    · have hrun1 := c.chk_headJ hds i hi htab (by omega)
      obtain ⟨t,hst,htp⟩ := c.headJ_step hc hk h0 i hi (by omega) hsp hrp hrun1 hrun2 acc s hs
      exact ⟨t,hst.of_eq (by simp [tableJump,htab]) (by simp [tableJump,htab]),htp⟩
  · by_cases ht : c.dig i=last i
    · have hrun := c.chk_headRTerm hds i hi htab ht
      have hr : c.rungPc i (c.dig i)=c.startPc i+3 := by rw [inline_rungPc c i htab,if_pos ht]
      obtain ⟨t,hst,htp⟩ := c.headRTerm_step hc hk h0 i hi ht hsp hr hrun acc s hs
      exact ⟨t,hst.of_eq (by simp [tableJump,htab]) (by simp [tableJump,htab]),htp⟩
    · have hrun := c.chk_headR hds i hi htab (by omega)
      have hr : c.rungPc i (c.dig i)=c.startPc i+4 := by rw [inline_rungPc c i htab,if_neg ht]
      obtain ⟨t,hst,htp⟩ := c.headR_step hc hk h0 i hi (by omega) hsp hr hrun acc s hs
      exact ⟨t,hst.of_eq (by simp [tableJump,htab]) (by simp [tableJump,htab]),htp⟩

/-- One exact mixed-radix chain, ending before the next dispatch. -/
theorem chain_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<54)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀v t,c.EndInv s0 i (acc++[v]) t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K (acc++[v])))
    (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N+40) (C+chainCost i (c.dig i)) Q (A+chainCost i (c.dig i))
      (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM (chainP 0 c.tree c.leaf i (c.dig i) (topMax i-c.dig i) (c.pad0 i) (c.pad1 i) (c.val i))
        (fun v => K (acc++[v]))) := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  have hd := hds i hi
  have hsp := c.startPc_lt hds i hi
  by_cases hmax : c.dig i=topMax i
  · rw [hmax,Nat.sub_self]
    have hp : chainP 0 c.tree c.leaf i (topMax i) 0 (c.pad0 i) (c.pad1 i) (c.val i)=pure (c.val i) := rfl
    rw [hp,SigGolfCandidate.T3M.CanonicalPort.Verify.ccM_pure]
    by_cases htab : i%3=0
    · obtain ⟨t,hst,ht⟩ := c.copyN_step hc hk h0 i hi hsp
        (c.chk_copyJ hds i hi htab hmax) acc s hs
      exact SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hst (hK _ _ ht) (by omega) (by simp [chainCost,tableJump,htab])
        (fun hq => ⟨hq,by simp [chainCost,tableJump,htab]⟩)
    · obtain ⟨t,hst,ht⟩ := c.copyFH_step hc hk h0 i hi hsp
        (c.inline_copy_end i htab hmax) (c.chk_copyF hds i hi htab hmax) acc s hs
      exact SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hst (hK _ _ ht) (by omega) (by simp [chainCost,tableJump,htab])
        (fun hq => ⟨hq,by simp [chainCost,tableJump,htab]⟩)
  · have hd' : c.dig i< topMax i := by omega
    rw [chainP_rest]
    have H := c.steps_good hc hds hk h0 i hi acc K N C A Q hK (last i-c.dig i) (c.dig i) (by omega) (le_refl _)
    obtain ⟨t,hst,ht⟩ := c.positive_head hc hds hk h0 i hi hd' acc s hs
    have hj : tableJump i≤1 := by unfold tableJump;split <;> omega
    have he := chainCost_positive i (c.dig i) hd'
    exact SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps' hst (H _ _ ht) (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)

#print axioms chain_good
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx

end CanonicalPortPart59

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart60

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.CanonicalPort.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

/-- The first two chains of each triple fall through to the following inline chain. -/
theorem next_inline (c : NCtx) (s0 : MachineState) (i : Nat) (hi : i<54) (h2 : i%3≠2)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) :
    c.ChainIn s0 (i+1) acc s := by
  obtain ⟨hB,hlen,hpc⟩ := hs
  refine ⟨hB,hlen,?_⟩
  rw [hpc]
  unfold endPc startPc
  have e : (i+1)/3=i/3 := by omega
  by_cases h0 : i%3=0
  · rw [if_pos h0,if_neg (show (i+1)%3≠0 by omega),if_pos (show (i+1)%3=1 by omega)]
    unfold qB;rw [e]
  · rw [if_neg h0,if_pos (show i%3=1 by omega),if_neg (show (i+1)%3≠0 by omega),
      if_neg (show (i+1)%3≠1 by omega)]
    unfold qC;rw [e]

def chainF (c : NCtx) (ends : List Digest) (i : Nat) : M (List Digest) := do
  let v ← chainP 0 c.tree c.leaf i (c.dig i) (topMax i-c.dig i) (c.pad0 i) (c.pad1 i) (c.val i)
  pure (ends++[v])

def chainsCost (c : NCtx) (i k : Nat) : Nat :=
  ((List.range' i k).map fun j => chainCost j (c.dig j)).sum

/-- Finish a nonempty suffix of one triple, before its four-instruction dispatch. -/
theorem group_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (q : Nat) (hq : q<18) (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t,c.EndInv s0 (3*q+2) ends t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K ends)) :
    ∀ k i, 3*q ≤ i → i+k = 3*q+3 → 0 < k → ∀ acc s, c.ChainIn s0 i acc s →
      SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N+40*k) (C+c.chainsCost i k) Q (A+c.chainsCost i k)
        (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM ((List.range' i k).foldlM c.chainF acc) K) := by
  intro k
  induction k with
  | zero => intro i _ _ h;omega
  | succ k ih =>
    intro i hi hik _ acc s hs
    rw [List.range'_succ,List.foldlM_cons]
    simp only [chainF,bind_assoc,pure_bind,SigGolfCandidate.T3M.CanonicalPort.Verify.ccM_bind]
    have H := c.chain_good hc hds hk h0 i (by omega) acc
      (fun ends => SigGolfCandidate.T3M.CanonicalPort.Verify.ccM ((List.range' (i+1) k).foldlM c.chainF ends) K)
      (N+40*k) (C+c.chainsCost (i+1) k) (A+c.chainsCost (i+1) k) Q
      (fun v t ht => by
        by_cases hk0 : k=0
        · subst hk0
          have he : i=3*q+2 := by omega
          rw [he] at ht
          simpa [chainsCost] using hK _ t ht
        · have ht' : c.ChainIn s0 (i+1) (acc++[v]) t := c.next_inline s0 i (by omega) (by omega) (acc++[v]) t ht
          exact ih (i+1) (by omega) (by omega) (by omega) (acc++[v]) t ht') s hs
    refine H.mono (by omega) ?_ (fun hq => ⟨hq,?_⟩)
    · simp only [chainsCost,List.range'_succ,List.map_cons,List.sum_cons];omega
    · simp only [chainsCost,List.range'_succ,List.map_cons,List.sum_cons];omega

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx

end CanonicalPortPart60

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart61

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.CanonicalPort.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def Fit (c : NCtx) (v : Digest) : Prop := ∀i,i<54 → c.dig i=coreDigit 0 v i

theorem fit_digits (c : NCtx) {v : Digest} (hf : c.Fit v) : c.DigitsOk := by
  intro i hi
  rw [hf i hi]
  have h := T3.Nonbinary.coreDigit_le 0 v i
  simpa [maxDigit,topMax,mx,show (i/3<17)↔i<51 by omega] using h

theorem fit_rank (c : NCtx) {v : Digest} (hf : c.Fit v) (hv : topRanksValid v=true)
    (q : Nat) (hq : q<17) : c.kOf q=Search.topRank v q := by
  have hr := T3.Nonbinary.top_rank_lt v hv q hq
  unfold kOf
  rw [hf (3*q) (by omega),hf (3*q+1) (by omega),hf (3*q+2) (by omega)]
  have h0 := T3.Nonbinary.top_core_triple v q 0 hq (by decide)
  have h1 := T3.Nonbinary.top_core_triple v q 1 hq (by decide)
  have h2 := T3.Nonbinary.top_core_triple v q 2 hq (by decide)
  simp only [Nat.add_zero] at h0
  rw [h0,h1,h2]
  simp only [mx,if_pos hq,Nat.reduceAdd,Nat.reducePow,Nat.div_one]
  unfold Search.topRank
  omega

theorem fit_tail (c : NCtx) {v : Digest} (hf : c.Fit v) (hv : v.toNat<2^125) :
    c.kOf 17=v.toNat/2^119 := by
  unfold kOf
  rw [hf 51 (by decide),hf 52 (by decide),hf 53 (by decide)]
  norm_num [mx,coreDigit]
  omega


theorem decode_facts {v : Digest} {ds : List Nat} (h : decode 0 v=some ds) :
    v.toNat<2^125 ∧ topRanksValid v=true ∧ (Search.topDigits v).sum=126 := by
  rw [Search.decode_top] at h
  split_ifs at h with hgood
  · exact hgood

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx

end CanonicalPortPart61

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart62

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.CanonicalPort.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

structure Encoded (v : Digest) (s : MachineState) : Prop where
  lo : s.getReg .x16=v.extractLsb' 0 64
  hi : s.getReg .x17=v.extractLsb' 63 64
  tail : s.getReg .x29=BitVec.ofNat 64 (v.toNat/2^119)
  mask : s.getReg .x24=130048#64
  table : s.getReg .x15=712704#64

theorem dispatch_at (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<18) :
    vrun (c.endPc (3*q+2)) 5=some (if q<16 then dispatchR (q+1) else if q=16 then tailDispatchR else retR) := by
  have hh := c.blk_at hds (3*q+2) (by omega)
  unfold blockCheck at hh
  simp only [Bool.and_eq_true] at hh
  have h := rOK_eq hh.2
  have eq : (3*q+2)/3=q := by omega
  simpa only [dispatchOK,endPc,qX,eq,show (3*q+2)%3=2 by omega,if_false,Nat.reduceEqDiff] using h

/-- Between the first seventeen triples, only x14 changes. -/
theorem end_dispatch (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {v : Digest}
    (he : Encoded v s0) (hf : c.Fit v) (hv : topRanksValid v=true)
    (q : Nat) (hq : q<16) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 (3*q+2) acc s) :
    ∃t,Steps vimage s 4 4 t ∧ c.ChainIn s0 (3*(q+1)) acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hr := c.dispatch_at hds q (by omega)
  rw [if_pos hq] at hr
  have hbound : c.endPc (3*q+2)<210432 := by
    have := c.qX_lt (3*q+2)
    simpa only [endPc,show (3*q+2)%3=2 by omega,if_false,Nat.reduceEqDiff] using (show c.qX (3*q+2)<210432 by omega)
  obtain ⟨t,st,pt,rt,ft⟩ := dispatch_step (by omega) hbound hr s v hpc
    ((hR _ (by decide)).trans he.lo) ((hR _ (by decide)).trans he.hi)
    ((hR _ (by decide)).trans he.mask) ((hR _ (by decide)).trans he.table)
  refine ⟨t,st,⟨⟨fun x hx => ?_,(hF.trans ft).mono (by intro A hA h;rcases h with h|h;simpa only [show 3*q+2+1=3*(q+1) by omega] using h;contradiction),fun j hj => ?_⟩,by omega,?_⟩⟩
  · rw [rt.get (by intro h;simp only [List.mem_singleton] at h;subst x;exact hx (by decide))]
    exact hR x hx
  · exact (hS j hj).frame ft (by have := slot_props j (by omega);omega) (by simp) (by simp)
  · rw [pt]
    unfold startPc
    rw [if_pos (show 3*(q+1)%3=0 by omega),show 3*(q+1)/3=q+1 by omega,c.fit_rank hf hv (q+1) (by omega)]

/-- Changing this unused initial register preserves the original witness. -/
def tailInitial (s0 t : MachineState) : MachineState := s0.setReg .x15 (t.getReg .x15)

theorem tailInitial_mem (s0 t : MachineState) (a : Word) :
    (tailInitial s0 t).getMem a=s0.getMem a := rfl

theorem tailInitial_regs (s0 t : MachineState) (r : Reg) (hr : r≠.x15) :
    (tailInitial s0 t).getReg r=s0.getReg r := by
  unfold tailInitial
  rw [setReg_of_ne s0 _ (by decide)]
  cases r <;> simp_all [MachineState.getReg]

theorem tailInitial_15 (s0 t : MachineState) :
    (tailInitial s0 t).getReg .x15=t.getReg .x15 := by
  unfold tailInitial
  rw [setReg_of_ne s0 _ (by decide)]
  rfl

theorem tailInitial_known (c : NCtx) {s0 t : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) :
    ∀p∈c.known,(tailInitial s0 t).getReg p.1=p.2 := by
  intro p hp
  rw [tailInitial_regs _ _ _ (by rcases p with ⟨r,w⟩;simp only [known,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp;rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl,_⟩ := h <;> simp)]
  exact hk p hp

theorem tailInitial_orig (c : NCtx) {s0 t : MachineState} (h0 : c.Orig0 s0) :
    c.Orig0 (tailInitial s0 t) := by
  refine ⟨fun i hi k hk => h0.1 i hi k hk, h0.2.congr (fun A _ _ => tailInitial_mem s0 t _)⟩

/-- The final radix-four table changes x15; the baseline rebase preserves memory exactly. -/
theorem end_tail (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {v : Digest}
    (he : Encoded v s0) (hf : c.Fit v) (hv : v.toNat<2^125)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 50 acc s) :
    ∃t,Steps vimage s 4 4 t ∧ c.ChainIn (tailInitial s0 t) 51 acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hr := c.dispatch_at hds 16 (by decide)
  norm_num at hr
  have hbound : c.endPc 50<210432 := by
    have := c.qX_lt 50
    simpa only [endPc,Nat.reduceMod,if_false,Nat.reduceEqDiff] using (show c.qX 50<210432 by omega)
  obtain ⟨t,st,pt,rt,ft⟩ := tail_dispatch_step hbound hr s (v.toNat/2^119) (by omega) hpc
    ((hR _ (by decide)).trans he.tail)
  refine ⟨t,st,⟨⟨fun x hx => ?_,?_,fun j hj => ?_⟩,by omega,?_⟩⟩
  · by_cases hx15 : x=.x15
    · subst x;rw [tailInitial_15]
    · rw [tailInitial_regs _ _ _ hx15,rt.get (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or];exact ⟨fun h => hx (by rw [h];decide),hx15⟩)]
      exact hR x hx
  · intro A hA hn
    rw [tailInitial_mem]
    exact ft.get hA (by simp) |>.trans (hF.get hA hn)
  · exact (hS j hj).frame ft (by have := slot_props j (by omega);omega) (by simp) (by simp)
  · rw [pt]
    change pcOf (entW 17 (v.toNat/2^119))=pcOf (entW 17 (c.kOf 17))
    rw [c.fit_tail hf hv]

end SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx

end CanonicalPortPart62

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart63

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfResearch.NonbinaryTop
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def digitCredit (i d : Nat) : Nat := if last i≤d then 1 else 0
def digitSum (f : Nat → Nat) : Nat := ((List.range 54).map f).sum
def creditSum (f : Nat → Nat) : Nat := ((List.range 54).map fun i => digitCredit i (f i)).sum
def totalCost (f : Nat → Nat) : Nat := ((List.range 54).map fun i => chainCost i (f i)).sum

theorem chainCost_balance (i d : Nat) (hd : d≤topMax i) :
    chainCost i d+9*d+digitCredit i d=5+tableJump i+9*topMax i := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  unfold chainCost digitCredit
  split_ifs <;> omega

theorem total_balance (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i) :
    totalCost f+9*digitSum f+creditSum f=2205 := by
  have H : ∀ l : List Nat,(∀i∈l,f i≤topMax i) →
      (l.map fun i => chainCost i (f i)).sum+9*(l.map f).sum+
        (l.map fun i => digitCredit i (f i)).sum=
        (l.map fun i => 5+tableJump i+9*topMax i).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro h
      have hi := chainCost_balance i (f i) (h i (by simp))
      have ht := ih (fun j hj => h j (by simp [hj]))
      simp only [List.map_cons,List.sum_cons]
      omega
  have hs := H (List.range 54) (fun i hi => hd i (List.mem_range.mp hi))
  have he : ((List.range 54).map fun i => 5+tableJump i+9*topMax i).sum=2205 := by decide +kernel
  exact hs.trans he

/-- Exact cost of all chains, seventeen four-instruction dispatches, and the final jump. -/
theorem total_cost_credit (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i)
    (hs : digitSum f=126) : totalCost f+17*4+1+creditSum f=1140 := by
  have h := total_balance f hd
  omega

theorem range_map_ofFn (f : Nat → Nat) :
    (List.range 54).map f=List.ofFn (fun i : Fin 54 => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj;simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]

theorem source_credit_parse {v : Digest} {w : Codec.Word}
    (hp : Decoder.parse 17 v.toNat=some w) : creditSum (coreDigit 0 v)=Cost.credit w := by
  unfold creditSum
  rw [range_map_ofFn,List.ofFn_add (n:=51) (m:=3),List.sum_append]
  change (List.ofFn fun i : Fin (17*3) => digitCredit i.val (coreDigit 0 v i.val)).sum+
      (List.ofFn fun k : Fin 3 => digitCredit (51+k.val) (coreDigit 0 v (51+k.val))).sum=Cost.credit w
  rw [List.ofFn_mul]
  simp only [List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  unfold Cost.credit Cost.credit5 Cost.credit4
  apply congrArg₂ Nat.add
  · apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    have he := T3.Nonbinary.coreDigit_parse5 hp j k
    have hl : last (j.val*3+k.val)=3 := by
      unfold last topMax mx
      rw [if_pos (by have := j.isLt;have := k.isLt;omega)]
    simpa only [digitCredit,hl,Nat.mul_comm] using congrArg (fun d => if 3≤d then (1:Nat) else 0) he
  · apply Finset.sum_congr rfl
    intro k hk
    have he := T3.Nonbinary.coreDigit_parse4 hp k
    have hl : last (51+k.val)=2 := by
      unfold last topMax mx
      rw [if_neg (by have := k.isLt;omega)]
    simpa only [digitCredit,hl] using congrArg (fun d => if 2≤d then (1:Nat) else 0) he

theorem source_accepted_credit {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : 11≤creditSum (coreDigit 0 v) := by
  obtain ⟨w,hw,_,_,hc⟩ := T3.Nonbinary.decode_top_credit h
  have hp : Decoder.parse 17 v.toNat=some w := by
    change ((Decoder.parse 17 v.toNat).filter fun w => decide (Counting.weight w=126))=some w at hw
    exact (Option.filter_eq_some_iff.mp hw).1
  rw [source_credit_parse hp]
  exact hc

theorem source_accepted_sum {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : digitSum (coreDigit 0 v)=126 := by
  obtain ⟨w,hw,_,hs,_⟩ := T3.Nonbinary.decode_top_credit h
  have hp : Decoder.parse 17 v.toNat=some w := by
    change ((Decoder.parse 17 v.toNat).filter fun w => decide (Counting.weight w=126))=some w at hw
    exact (Option.filter_eq_some_iff.mp hw).1
  change (dataDigits 0 v).sum=126
  rw [T3.Nonbinary.dataDigits_parse hp,T3.Nonbinary.wordDigits_sum,hs]

theorem source_accepted_total {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : totalCost (coreDigit 0 v)+17*4+1≤1129 := by
  have hd : ∀i,i<54 → coreDigit 0 v i≤topMax i := by
    intro i hi
    have hc := T3.Nonbinary.coreDigit_le (0:Layer) v i
    have he : maxDigit 0 i=topMax i := by
      unfold maxDigit topMax mx
      simp only [ite_true]
      split_ifs <;> omega
    rw [he] at hc
    exact hc
  have hb := total_cost_credit (coreDigit 0 v) hd (source_accepted_sum h)
  have hc := source_accepted_credit h
  omega

#print axioms total_cost_credit
#print axioms source_accepted_total
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx

end CanonicalPortPart63

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart64

namespace SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.CanonicalPort.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def TopOut (c : NCtx) (s0 : MachineState) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → x ≠ .x15 → s.getReg x=s0.getReg x) ∧
  Frame s0 s (c.Wr 54) ∧ acc.length=54 ∧
  (∀ j < acc.length, DigAt s (slot j) (acc.getD j 0)) ∧ s.pc=pcOf c.ret

theorem end_return (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 b : MachineState}
    (hk : ∀ p ∈ c.known, s0.getReg p.1=p.2)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv (tailInitial s0 b) 53 acc s) :
    ∃ t, Steps vimage s 1 1 t ∧ c.TopOut s0 acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hr := c.dispatch_at hds 17 (by decide)
  norm_num at hr
  have hp : c.endPc 53 < 210432 := by
    have := c.qX_lt 53
    simpa only [endPc,Nat.reduceMod,if_false,Nat.reduceEqDiff] using (show c.qX 53<210432 by omega)
  have st := piece_steps45 hr hp s hpc (by simp [retR])
  have h1 : s.getReg .x1=pcOf c.ret :=
    (hR .x1 (by decide)).trans ((tailInitial_regs _ _ _ (by decide)).trans (hk (.x1,pcOf c.ret) (by simp [known])))
  refine ⟨retR.toState s,st,⟨fun x hx hx15 => ?_,?_,hlen,?_,?_⟩⟩
  · exact (retR_keeps.reg s (by simp)).trans ((hR x hx).trans (tailInitial_regs _ _ _ hx15))
  · intro A hA hn
    exact hF A hA hn
  · intro j hj;exact hS j hj
  · rw [Result.toState_pc]
    simp only [retR,E.eval,BinOp.eval,h1]
    exact even_andNot1' _ (by have := hc.2.2.2.2.2;omega)

theorem chainsCost_add (c : NCtx) (i n k : Nat) :
    c.chainsCost i (n+k)=c.chainsCost i n+c.chainsCost (i+n) k := by
  unfold chainsCost
  rw [← List.range'_append_1,List.map_append,List.sum_append]

/-- The seventeen radix-five triples, with only the sixteen intervening dispatches. -/
theorem prefix_good (c : NCtx) (hc : c.ok) {s0 : MachineState} {v : Digest}
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : Encoded v s0) (hf : c.Fit v) (hv : topRanksValid v=true)
    (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.EndInv s0 50 acc t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K acc)) :
    ∀ n q, n+q=17 → 0<n → ∀ acc s,c.ChainIn s0 (3*q) acc s →
      SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N+124*n) (C+c.chainsCost (3*q) (3*n)+4*(n-1)) Q
        (A+c.chainsCost (3*q) (3*n)+4*(n-1))
        (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM ((List.range' (3*q) (3*n)).foldlM c.chainF acc) K) := by
  intro n
  induction n with
  | zero => intro q _ h;omega
  | succ n ih =>
    intro q hn _ acc s hs
    have hd := c.fit_digits hf
    by_cases hz : n=0
    · subst n
      have hq : q=16 := by omega
      subst q
      have H := c.group_good hc hd hk h0 16 (by decide) K N C A Q hK 3 48 (by decide) (by decide) (by decide) acc s hs
      exact H.mono (by omega) (by simp) (fun h => ⟨h,by simp⟩)
    · rw [show 3*(n+1)=3+3*n by omega,← List.range'_append_1,List.foldlM_append,SigGolfCandidate.T3M.CanonicalPort.Verify.ccM_bind]
      have H := c.group_good hc hd hk h0 q (by omega)
        (fun ends => SigGolfCandidate.T3M.CanonicalPort.Verify.ccM ((List.range' (3*q+3) (3*n)).foldlM c.chainF ends) K)
        (N+124*n+4) (C+c.chainsCost (3*(q+1)) (3*n)+4*(n-1)+4)
        (A+c.chainsCost (3*(q+1)) (3*n)+4*(n-1)+4) Q
        (fun ends t ht => by
          obtain ⟨u,st,hu⟩ := c.end_dispatch hc hd he hf hv q (by omega) ends t ht
          have H := ih (q+1) (by omega) (by omega) ends u hu
          rw [show 3*(q+1)=3*q+3 by omega] at H
          exact SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps st H)
        3 (3*q) (le_refl _) (by omega) (by decide) acc s hs
      have ec := c.chainsCost_add (3*q) 3 (3*n)
      rw [show 3*q+3=3*(q+1) by omega] at ec
      exact H.mono (by omega) (by omega) (fun h => ⟨h,by omega⟩)

def topP (c : NCtx) : M (List Digest) := (List.range' 0 54).foldlM c.chainF []

/-- All 54 mixed-radix chains, seventeen dispatches and the return instruction. -/
theorem top_good_exact (c : NCtx) (hc : c.ok) {s0 : MachineState} {v : Digest}
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : Encoded v s0) (hf : c.Fit v) (hv : v.toNat<2^125) (hr : topRanksValid v=true)
    (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.TopOut s0 acc t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K acc))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N+2321) (C+c.chainsCost 0 54+69) Q (A+c.chainsCost 0 54+69)
      (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM c.topP K) := by
  have hd := c.fit_digits hf
  unfold topP
  rw [show (54:Nat)=51+3 from rfl,← List.range'_append_1,List.foldlM_append,SigGolfCandidate.T3M.CanonicalPort.Verify.ccM_bind]
  have H := c.prefix_good hc hk h0 he hf hr
    (fun ends => SigGolfCandidate.T3M.CanonicalPort.Verify.ccM ((List.range' 51 3).foldlM c.chainF ends) K)
    (N+125) (C+c.chainsCost 51 3+5) (A+c.chainsCost 51 3+5) Q
    (fun ends t ht => by
      obtain ⟨u,st,hu⟩ := c.end_tail hc hd he hf hv ends t ht
      have H := c.group_good hc hd (c.tailInitial_known hk) (c.tailInitial_orig h0) 17 (by decide)
        K (N+1) (C+1) (A+1) Q
        (fun acc t ht => by
          obtain ⟨u,st,hu⟩ := c.end_return hc hd hk acc t ht
          exact SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps st (hK acc u hu))
        3 51 (by decide) (by decide) (by decide) ends u hu
      have H := SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ.steps st H
      exact H.mono (by omega) (by omega) (fun h => ⟨h,by omega⟩))
    17 0 (by decide) (by decide) [] s hs
  have ec := c.chainsCost_add 0 51 3
  norm_num only [Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] at ec H ⊢
  exact H.mono (by omega) (by omega) (fun h => ⟨h,by omega⟩)

theorem top_good (c : NCtx) (hc : c.ok) {s0 : MachineState} {v : Digest} {ds : List Nat}
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : Encoded v s0) (hf : c.Fit v) (hv : decode 0 v=some ds)
    (K : List Digest → OracleComp Legacy.HashSpec SigGolfCandidate.T3M.CanonicalPort.Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ acc t,c.TopOut s0 acc t → SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ t N C Q A (K acc))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    SigGolfCandidate.T3M.CanonicalPort.Verify.GoodQ s (N+2321) (C+1129) Q (A+1129) (SigGolfCandidate.T3M.CanonicalPort.Verify.ccM c.topP K) := by
  have hd := decode_facts hv
  have H := c.top_good_exact hc hk h0 he hf hd.1 hd.2.1 K N C A Q hK s hs
  have e : c.chainsCost 0 54=totalCost (coreDigit 0 v) := by
    unfold chainsCost totalCost
    rw [← List.range_eq_range']
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [hf i (List.mem_range.mp hi)]
  have hb := source_accepted_total hv
  rw [e] at H
  exact H.mono (le_refl _) (by omega) (fun h => ⟨h,by omega⟩)

#print axioms top_good
end SigGolfCandidate.T3M.CanonicalPort.Nonbinary.NCtx

end CanonicalPortPart64

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart65

/-! Seven-instruction lane sum, adapted from accepted i34-9 PR283.
The T3 top two-bit variant and relaxed first-word bound are proved here. -/
namespace SigGolfCandidate.T3M.CanonicalPort.Verify

/-- Splitting a word by a mask and its complement: the parts have disjoint bits, so they add up to the word. -/
theorem swar7_split (x m : BitVec 64) : (x &&& m) + (x &&& ~~~m) = x := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i hi; simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]; cases x[i] <;> cases m[i] <;> rfl
  · ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]; cases x[i] <;> cases m[i] <;> rfl

/-- `M1` has period 6 with three set bits: bit `i` is set exactly when bit `i + 3` is clear. -/
theorem swar7_period : ∀ i : Fin 61,
    (0x71c71c71c71c71c7#64).getLsbD i.val = !(0x71c71c71c71c71c7#64).getLsbD (i.val + 3) := by
  decide

/-- `(x >>> 3) & M1` is the odd-digit part `x & ~M1` shifted down by three. -/
theorem swar7_shift (x : BitVec 64) :
    (x >>> 3) &&& 0x71c71c71c71c71c7#64 = (x &&& ~~~0x71c71c71c71c71c7#64) >>> 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not]
  by_cases h : i < 61
  · have hp := swar7_period ⟨i, h⟩
    simp only at hp
    rw [hp, show 3 + i = i + 3 by omega]
    simp [show i + 3 < 64 by omega]
  · have hx : x.getLsbD (3 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [hx]

/-- The odd-digit part `x & ~M1` is a multiple of 8 (bits 0..2 belong to `M1`). -/
theorem swar7_low (x : BitVec 64) : (x &&& ~~~0x71c71c71c71c71c7#64).toNat % 8 = 0 := by
  have h7 : (x &&& ~~~0x71c71c71c71c71c7#64) &&& 7#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
    by_cases h : i < 3
    · have : (0x71c71c71c71c71c7#64).getLsbD i = true := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide
      simp [this]
    · have : (7#64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [Bool.and_eq_false_iff]; right
        exact Nat.testBit_lt_two_pow (by
          calc 7 < 2 ^ 3 := by decide
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [this]
  have := congrArg BitVec.toNat h7
  rw [BitVec.toNat_and] at this
  have e : (7#64).toNat = 2 ^ 3 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this

/-- The 7-step lane word equals the reference one when only the second word is below `2^63`: the odd-digit parts
`A - (A & M1)`, `B - (B & M1)` are multiples of 8 and their sum does not wrap. -/
theorem swar7_eq (a b : BitVec 64) (hb : b.toNat < 2 ^ 63) :
    ((a &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64)) +
      (((a + b) - ((a &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64))) >>> 3) =
    ((a >>> 3) &&& 0x71c71c71c71c71c7#64) + (a &&& 0x71c71c71c71c71c7#64) +
      ((b >>> 3) &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64) := by
  rw [swar7_shift a, swar7_shift b]
  set M : BitVec 64 := 0x71c71c71c71c71c7#64 with hM
  have la := swar7_low a
  have lb := swar7_low b
  rw [← hM] at la lb
  have loa : (a &&& ~~~M).toNat ≤ 0x8e38e38e38e38e38 := by
    rw [BitVec.toNat_and]; simpa [hM] using (Nat.and_le_right : a.toNat &&& (~~~M).toNat ≤ (~~~M).toNat)
  have lob : (b &&& ~~~M).toNat ≤ 0x0e38e38e38e38e38 := by
    have hb' : b.toNat % 2 ^ 63 = b.toNat := Nat.mod_eq_of_lt hb
    have he := Nat.and_mod_two_pow (a := b.toNat) (b := (~~~M).toNat) (n := 63)
    rw [hb', Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left hb)] at he
    rw [BitVec.toNat_and, he]
    simpa [hM] using (Nat.and_le_right : b.toNat &&& ((~~~M).toNat % 2 ^ 63) ≤ (~~~M).toNat % 2 ^ 63)
  have h1 : (a + b) - ((a &&& M) + (b &&& M)) = (a &&& ~~~M) + (b &&& ~~~M) := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc a + b = ((a &&& M) + (a &&& ~~~M)) + ((b &&& M) + (b &&& ~~~M)) := by
           rw [swar7_split a M, swar7_split b M]
         _ = ((a &&& ~~~M) + (b &&& ~~~M)) + ((a &&& M) + (b &&& M)) := by ac_rfl
  have h2 : ((a &&& ~~~M) + (b &&& ~~~M)) >>> 3 = ((a &&& ~~~M) >>> 3) + ((b &&& ~~~M) >>> 3) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (show (a &&& ~~~M).toNat + (b &&& ~~~M).toNat < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  ac_rfl


/-- `M4` has period 4 with two set bits: bit `i` is set exactly when bit `i + 2` is clear. -/
theorem swar2_period : ∀ i : Fin 62,
    (0x3333333333333333#64).getLsbD i.val = !(0x3333333333333333#64).getLsbD (i.val + 2) := by
  decide

/-- `(x >>> 2) & M4` is the odd-digit part `x & ~M4` shifted down by two. -/
theorem swar2_shift (x : BitVec 64) :
    (x >>> 2) &&& 0x3333333333333333#64 = (x &&& ~~~0x3333333333333333#64) >>> 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not]
  by_cases h : i < 62
  · have hp := swar2_period ⟨i, h⟩
    simp only at hp
    rw [hp, show 2 + i = i + 2 by omega]
    simp [show i + 2 < 64 by omega]
  · have hx : x.getLsbD (2 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [hx]

/-- The odd-digit part `x & ~M4` is a multiple of 4 (bits 0..1 belong to `M4`). -/
theorem swar2_low (x : BitVec 64) : (x &&& ~~~0x3333333333333333#64).toNat % 4 = 0 := by
  have h7 : (x &&& ~~~0x3333333333333333#64) &&& 3#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
    by_cases h : i < 2
    · have : (0x3333333333333333#64).getLsbD i = true := by
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide
      simp [this]
    · have : (3#64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [Bool.and_eq_false_iff]; right
        exact Nat.testBit_lt_two_pow (by
          calc 3 < 2 ^ 2 := by decide
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [this]
  have := congrArg BitVec.toNat h7
  rw [BitVec.toNat_and] at this
  have e : (3#64).toNat = 2 ^ 2 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this

/-- The 7-step lane word equals the reference one when only the second word is below `2^34`: the odd-digit parts
`A - (A & M4)`, `B - (B & M4)` are multiples of 4 and their sum does not wrap. -/
theorem swar2_eq (a b : BitVec 64) (hb : b.toNat < 2 ^ 34) :
    ((a &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64)) +
      (((a + b) - ((a &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64))) >>> 2) =
    ((a >>> 2) &&& 0x3333333333333333#64) + (a &&& 0x3333333333333333#64) +
      ((b >>> 2) &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64) := by
  rw [swar2_shift a, swar2_shift b]
  set M : BitVec 64 := 0x3333333333333333#64 with hM
  have la := swar2_low a
  have lb := swar2_low b
  rw [← hM] at la lb
  have loa : (a &&& ~~~M).toNat ≤ 0xcccccccccccccccc := by
    rw [BitVec.toNat_and]; simpa [hM] using (Nat.and_le_right : a.toNat &&& (~~~M).toNat ≤ (~~~M).toNat)
  have lob : (b &&& ~~~M).toNat < 2 ^ 34 := by
    rw [BitVec.toNat_and]; exact lt_of_le_of_lt Nat.and_le_left hb
  have h1 : (a + b) - ((a &&& M) + (b &&& M)) = (a &&& ~~~M) + (b &&& ~~~M) := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc a + b = ((a &&& M) + (a &&& ~~~M)) + ((b &&& M) + (b &&& ~~~M)) := by
           rw [swar7_split a M, swar7_split b M]
         _ = ((a &&& ~~~M) + (b &&& ~~~M)) + ((a &&& M) + (b &&& M)) := by ac_rfl
  have h2 : ((a &&& ~~~M) + (b &&& ~~~M)) >>> 2 = ((a &&& ~~~M) >>> 2) + ((b &&& ~~~M) >>> 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (show (a &&& ~~~M).toNat + (b &&& ~~~M).toNat < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  ac_rfl


end SigGolfCandidate.T3M.CanonicalPort.Verify

end CanonicalPortPart65

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart66

/-! # V1 layers: the transition (`LayerIn` → counter, encoding hash, decode → the chain code)

**`LayerIn w pk index lay M s`** (the interface with V2's `FtsOut` for layer 3 and V3's Merkle root for layers 2, 1, 0):
at a transition copy of layer `lay`, V2's `Glob (preK lay) w pk s` (the layer's constant registers, the witness header,
`pk`, the zero words of the encoding block), the remaining index bits `index / 2^below` in `rReg lay` (`s6` for
layer 3, `t5` below), the previous root `M` at `0x100`, and the witness regions of the layers `≤ lay` original (V2's
`Orig` on the offsets `[11288, layerEnd lay)`).

* `encA_step` : from `LayerIn`, either the counter rejection (HALT(1)) or the encoding `ecall` with the input
  `encodingInput lay tree leaf M (wctr w lay)` (`EncPre`);
* `encB_step` (lower layers) : after the answer `a`, either a decode rejection (HALT(1)) when Core's `decode` fails,
  or the chain code's `ChainIn 0` with the context `lctx` built from `a` (digits = Core's). -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)

/-! ## Layer facts -/

/-- The index bits below layer `lay` (Core's `route`). -/
def below (lay : Nat) : Nat := [19, 12, 6, 0].getD lay 0
/-- The end (witness offset) of layer `lay`'s region (memory order 0, 1, 2, 3). -/
def layerEnd (lay : Nat) : Nat := [15768, 18968, 22104, 25240].getD lay 0

theorem hL_eq (lay : Layer) : hL lay.val = height lay := by fin_cases lay <;> rfl
theorem below_eq (lay : Layer) : below lay.val = (![19, 12, 6, 0] : Layer → Nat) lay := by fin_cases lay <;> rfl
theorem tgtL_eq (lay : Layer) : tgtL lay.val = target lay := by fin_cases lay <;> rfl

/-- The state at a transition copy of layer `lay`. -/
structure LayerIn (w : WBytes) (pk : Digest) (index lay : Nat) (M : Digest) (s : MachineState) : Prop where
  lay4 : lay < 4
  idx : index < 2 ^ 31
  copy : ∃ c, c < nCopy lay ∧ s.pc = pcOf (trPc lay c)
  glob : Glob (preK lay) w pk s
  route : s.getReg (rReg lay) = BitVec.ofNat 64 (index / 2 ^ below lay)
  msg : DigAt s 0x100 M
  orig : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd lay) s

/-! ## Route -/

theorem route_fst (index : Nat) (lay : Layer) : (route index lay).1 = index / 2 ^ below lay.val % 2 ^ hL lay.val := by
  simp only [route, below_eq, hL_eq]

theorem route_snd (index : Nat) (lay : Layer) : (route index lay).2 = index / 2 ^ (below lay.val + hL lay.val) := by
  simp only [route, below_eq, hL_eq]

theorem leaf_lt (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ hL lay.val := by
  rw [route_fst]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem hL_le (lay : Layer) : 6 ≤ hL lay.val ∧ hL lay.val ≤ 12 := by fin_cases lay <;> decide

theorem tree_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) : (route index lay).2 < 2 ^ 32 := by
  rw [route_snd]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)

theorem leaf_lt32 (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ 32 := by
  have h1 := leaf_lt index lay
  have h2 := (hL_le lay).2
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega : hL lay.val ≤ 32))

/-- The route registers' values (`leafE`, `treeE`, `tpE`, `s7E`). -/
theorem route_evals (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31) (s : MachineState)
    (h : s.getReg (rReg lay.val) = BitVec.ofNat 64 (index / 2 ^ below lay.val)) :
    (leafE lay.val).eval s = BitVec.ofNat 64 (route index lay).1 ∧
      (treeE lay.val).eval s = BitVec.ofNat 64 (route index lay).2 ∧
      (tpE lay.val).eval s = BitVec.ofNat 64 (hdr1 (route index lay).2 (route index lay).1) ∧
      (s7E lay.val).eval s = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1) := by
  have hl := leaf_lt index lay
  have ht := tree_lt index lay hidx
  have hl32 := leaf_lt32 index lay
  have hU : index / 2 ^ below lay.val < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hlE : (leafE lay.val).eval s = BitVec.ofNat 64 (route index lay).1 := by
    rw [route_fst]
    unfold leafE
    split
    · rename_i h0
      have hl0 : lay = 0 := Fin.ext h0
      subst hl0
      simp only [E.eval]
      rw [show rReg (0 : Layer).val = .x30 from rfl] at h
      rw [h]; congr 1
      simp only [show below (0 : Layer).val = 19 from rfl, show hL (0 : Layer).val = 12 from rfl]
      rw [Nat.mod_eq_of_lt (by omega)]
    · simp only [E.eval, BinOp.eval, h, kw]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hU, Nat.mod_eq_of_lt (show 2 ^ hL lay.val - 1 < 2 ^ 64 by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) (hL_le lay).2; omega),
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.pow_le_pow_right (by norm_num) (by have := (hL_le lay).2; omega)))]
  have htE : (treeE lay.val).eval s = BitVec.ofNat 64 (route index lay).2 := by
    rw [route_snd]
    simp only [treeE, E.eval, BinOp.eval, h, kw]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hU,
      Nat.mod_eq_of_lt (show hL lay.val < 2 ^ 64 by have := (hL_le lay).2; omega),
      Nat.mod_eq_of_lt (show hL lay.val < 64 by have := (hL_le lay).2; omega), Nat.shiftRight_eq_div_pow,
      Nat.div_div_eq_div_mul, ← Nat.pow_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]
  refine ⟨hlE, htE, ?_, ?_⟩
  · simp only [tpE, E.eval, BinOp.eval, hlE, htE, kw]
    rw [hdr1_eq _ _ ht hl32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show (route index lay).1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (32 : Nat) < 2 ^ 64 by norm_num),
      show 32 % 64 = 32 from rfl, Nat.mod_eq_of_lt (show (route index lay).2 < 2 ^ 64 by omega), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show (route index lay).1 * 2 ^ 32 < 2 ^ 64 by
        have : (route index lay).1 * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hl32 (by norm_num)
        omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show (route index lay).2 + 2 ^ 32 * (route index lay).1 < 2 ^ 64 by omega)]
    rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt ht]
    ring
  · simp only [s7E, E.eval, BinOp.eval, hlE, kw]
    apply BitVec.eq_of_toNat_eq
    have hp : 2 ^ hL lay.val < 2 ^ 64 := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (hL_le lay).2; omega
    rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show (route index lay).1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt hp,
      Nat.mod_eq_of_lt (show 2 ^ hL lay.val + (route index lay).1 < 2 ^ 64 by
        have : 2 * 2 ^ hL lay.val ≤ 2 ^ 13 := by
          rw [← Nat.pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by have := (hL_le lay).2; omega)
        omega)]
    rw [Nat.lor_comm, show 2 ^ hL lay.val = 2 ^ hL lay.val * 1 by ring, ← Nat.two_pow_add_eq_or_of_lt hl]

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)

/-! ## The counter -/

theorem ctrE_eval (w : WBytes) (lay : Layer) (s : MachineState) (hH : WitHdr w s) :
    (ctrE lay.val).eval s = BitVec.ofNat 64 (wctr w lay).toNat := by
  have hj : 2 + (lay.val + 1) / 2 < 8 := by have := lay.isLt; omega
  have hw := hH (2 + (lay.val + 1) / 2) hj
  rw [show WIT + 8 * (2 + (lay.val + 1) / 2) = 0x810 + 8 * ((lay.val + 1) / 2) by unfold WIT; ring] at hw
  apply BitVec.eq_of_toNat_eq
  show (LoadKind.wu.fromWord (s.getMem (BitVec.ofNat 64 (0x810 + 8 * ((lay.val + 1) / 2))))
    (4 * ((lay.val + 1) % 2))).toNat = _
  rw [hw]
  simp only [LoadKind.fromWord, extractWord32, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, wword_toNat, wctr, wle32, counterOff,
    BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
  have e1 : 4 * ((lay.val + 1) % 2) / 4 * 32 = 32 * ((lay.val + 1) % 2) := by omega
  rw [e1]
  have e2 : w.toNat / 2 ^ (64 * (2 + (lay.val + 1) / 2)) % 2 ^ 64 / 2 ^ (32 * ((lay.val + 1) % 2)) % 2 ^ 32 =
      w.toNat / 2 ^ (8 * (20 + 4 * lay.val)) % 2 ^ 32 := by
    have hk : 8 * (20 + 4 * lay.val) = 64 * (2 + (lay.val + 1) / 2) + 32 * ((lay.val + 1) % 2) := by omega
    rw [hk, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    generalize w.toNat / 2 ^ (64 * (2 + (lay.val + 1) / 2)) = X
    have : (lay.val + 1) % 2 = 0 ∨ (lay.val + 1) % 2 = 1 := by omega
    rcases this with h | h <;> rw [h] <;> norm_num <;> omega
  rw [e2]

theorem ctr_lt (w : WBytes) (lay : Layer) : (wctr w lay).toNat < 2 ^ 32 := (wctr w lay).isLt

theorem ctrBr_iff (w : WBytes) (lay : Layer) (s : MachineState) (hH : WitHdr w s) (d : Bool) :
    Br.holds s (ctrBr lay.val d) ↔ d = decide ((wctr w lay).toNat ≥ counterLimit) := by
  have hd := ctr_lt w lay
  simp only [ctrBr, Br.holds, CmpOp.eval, E.eval, BinOp.eval, ctrE_eval w lay s hH, kw]
  have e : (BitVec.ofNat 64 (wctr w lay).toNat >>> ((BitVec.ofNat 64 22).toNat % 64)) =
      BitVec.ofNat 64 ((wctr w lay).toNat / 2 ^ 22) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show (wctr w lay).toNat < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (wctr w lay).toNat / 2 ^ 22 < 2 ^ 64 by omega)]
  rw [e]
  by_cases h : (wctr w lay).toNat ≥ counterLimit
  · have hne : BitVec.ofNat 64 ((wctr w lay).toNat / 2 ^ 22) ≠ 0 := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [toNat_ofNat_lt (by omega)] at this
      unfold counterLimit at h
      simp at this; omega
    rw [show (BitVec.ofNat 64 ((wctr w lay).toNat / 2 ^ 22) != (BitVec.ofNat 64 0 : Word)) = true from
      bne_iff_ne.mpr hne, decide_eq_true h]
    exact eq_comm
  · have h0 : (wctr w lay).toNat / 2 ^ 22 = 0 := by unfold counterLimit at h; omega
    rw [h0, decide_eq_false h, show (BitVec.ofNat 64 0 != (BitVec.ofNat 64 0 : Word)) = false by decide]
    exact eq_comm

/-! ## The checks of a copy, unpacked -/

theorem copy_parts (lay p : Nat) (h : copyCheck lay p = true) :
    specB [] [] baseK (runAt (preK lay) [] p [.br false]) (specA lay p) [] (bK lay) keepA = true ∧
    specB [] [] [] (runAt (preK lay) [] p [.br true]) (rejA lay p) [] [] [] = true ∧
    (lay = 0 →
      specB [] [] [] (runAt [] [96160] (p + stepsA lay + 1) []) (specTopCall p) [] [] keepTopCall = true) ∧
    (lay ≠ 0 →
      specB [] [] baseK (runAt (bK lay) [] (p + stepsA lay + 1) [.br false, .br false, .jmp]) (specBl lay p) []
        (postBl lay p) keepB = true ∧
      specB [] [] [] (runAt (bK lay) [] (p + stepsA lay + 1) [.br false, .br true]) (rejCk lay) [] [] [] = true ∧
      specB [] [] [] (runAt (bK lay) [] (p + stepsA lay + 1) [.br true]) (rejRng 62) [] [] [] = true) ∧
    specB [] [] baseK (runAt (leafK lay) [] (p + retOff lay) [.jmp]) (specLf lay) [] (postLf lay) keepLf = true := by
  unfold copyCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun h0 => ?_, fun h0 => ?_, h4⟩
  · rw [if_pos h0] at h3; exact h3
  · rw [if_neg h0] at h3; simp only [Bool.and_eq_true] at h3; exact ⟨h3.1.1, h3.1.2, h3.2⟩

/-! ## A: up to the encoding `ecall` -/

/-- Before the encoding `ecall` (copy `c`; the route in `tp`, `s7`, `t5`). -/
structure EncPre (w : WBytes) (pk : Digest) (index lay c : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (trPc lay c + stepsA lay)
  glob : Glob (bK lay) w pk t
  tp : ∀ (L : Layer), L.val = lay → t.getReg .x4 = BitVec.ofNat 64 (hdr1 (route index L).2 (route index L).1)
  s7 : ∀ (L : Layer), L.val = lay → t.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay + (route index L).1)
  t5 : ∀ (L : Layer), L.val = lay → t.getReg .x30 = BitVec.ofNat 64 (route index L).2
  orig : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd lay) t

theorem hw4_hdr0 (lay : Layer) (tree : Nat) (ht : tree < 2 ^ 32) : hw 4 lay.val = hdr0 4 lay.val tree 0 := by
  rw [hdr0_eq _ _ _ _ (by norm_num) (by have := lay.isLt; omega) ht (by norm_num)]
  unfold hw; ring

/-- **A**: the counter rejection, or the encoding `ecall` with Core's `encodingInput`. -/
theorem encA_step (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (M : Digest) (s : MachineState)
    (hs : LayerIn w pk index lay.val M s) :
    ((wctr w lay).toNat ≥ counterLimit → ∃ u, Steps image s (stepsA lay.val) (stepsA lay.val) u ∧
        fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    ((wctr w lay).toNat < counterLimit → ∃ t, Steps image s (stepsA lay.val) (stepsA lay.val) t ∧
        fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
        hashInput t = toQ (pad64 (encodingInput lay (route index lay).2 (route index lay).1 M (wctr w lay))) ∧
        ∃ c, c < nCopy lay.val ∧ EncPre w pk index lay.val c t) := by
  obtain ⟨c, hc, hpc⟩ := hs.copy
  have hcc := copy_parts lay.val (trPc lay.val c) (copyCheck_at lay.val c lay.isLt hc)
  have hk : KnownOK (preK lay.val) s := hs.glob.1
  have hH : WitHdr w s := hs.glob.2.1
  constructor
  · intro hge
    obtain ⟨u, hu⟩ := spec_run hcc.2.1 s hpc hk (by
      intro b hb; simp only [rejA, List.mem_singleton] at hb; subst hb
      exact (ctrBr_iff w lay s hH true).mpr (by simp [hge])) (by simp)
    exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, kw 1) (by simp [rejA]), hu.regs (.x10, kw 1) (by simp [rejA])⟩
  · intro hlt
    obtain ⟨t, ht⟩ := spec_run hcc.1 s hpc hk (by
      intro b hb; simp only [specA, List.mem_singleton] at hb; subst hb
      exact (ctrBr_iff w lay s hH false).mpr (by simp; omega)) (by simp)
    obtain ⟨hlE, htE, htpE, hs7E⟩ := route_evals index lay hs.idx s hs.route
    have hkt : KnownOK (bK lay.val) t := ht.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 256 := hkt (.x10, 256) (by simp [bK])
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := hkt (.x11, 64) (by simp [bK, layK])
    have h12 : t.getReg .x12 = BitVec.ofNat 64 320 := hkt (.x12, 320) (by simp [bK])
    have hG : Glob (bK lay.val) w pk t := by
      have := ht.glob _ w pk hs.glob (RelOK.nil s)
      exact ⟨hkt, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩
    have hm : ∀ A, t.getMem A = memEval s (specA lay.val (trPc lay.val c)).mem A := ht.mem
    have frame : ∀ A, A < 2 ^ 64 → A ≠ 288 → A ≠ 280 → A ≠ 272 →
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3
      rw [hm]
      apply memEval_frame_ofNat s _ A hA
      intro p hp
      simp only [specA, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp <;> omega
    have tree_lt' := tree_lt index lay hs.idx
    refine ⟨t, ht.steps, ht.ecall rfl, hkt (.x5, 0) (by simp [bK, layK, baseK]),
      hashArgs_of t 256 64 320 h10 h11 h12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      ?_, c, hc, ⟨?_, hG, fun L hL => ?_, fun L hL => ?_, fun L hL => ?_, ?_⟩⟩
    · -- the encoding block
      apply hashInput_words8 t _ 256 (by rw [pad64_encodingInput]; simp [encodingInput, SphincsSecurity.bytesLE_length])
        h10 (by norm_num) (by norm_num) h11
      rw [wordsOf_encodingInput]
      have m0 := hs.msg
      have hPZ : PZero s := hs.glob.2.2.2.1
      have hPH : PHalf s := hs.glob.2.2.2.2.1
      simp only [List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [frame 256 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact m0.1
      · rw [show (256 : Nat) + 8 = 264 by rfl, frame 264 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        exact m0.2
      · rw [show (256 : Nat) + 16 = 272 by rfl, hm]
        simp only [specA]
        rw [memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
          memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
          memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
        simp only [E.eval, kw]
        rw [hw4_hdr0 lay _ tree_lt']
      · rw [show (256 : Nat) + 24 = 280 by rfl, hm]
        simp only [specA]
        rw [memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
          memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl, htpE]
      · rw [show (256 : Nat) + 32 = 288 by rfl, hm]
        simp only [specA]
        rw [memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
        simp only [E.eval, BinOp.eval, kw]
        rw [ctrE_eval w lay s hH]
        apply BitVec.eq_of_toNat_eq
        rw [merge_w0_toNat]
        have hph : (s.getMem (BitVec.ofNat 64 288)).toNat / 2 ^ 32 = 0 := hPH
        have := ctr_lt w lay
        simp only [BitVec.toNat_ofNat] at hph ⊢
        rw [hph]; omega
      · rw [show (256 : Nat) + 40 = 296 by rfl, frame 296 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        exact hPZ 0x128 (by simp [pSlots])
      · rw [show (256 : Nat) + 48 = 304 by rfl, frame 304 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        exact hPZ 0x130 (by simp [pSlots])
      · rw [show (256 : Nat) + 56 = 312 by rfl, frame 312 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        exact hPZ 0x138 (by simp [pSlots])
    · exact ht.pc rfl
    · obtain rfl : L = lay := Fin.ext hL
      rw [ht.regs (.x4, tpE L.val) (by simp [specA]), htpE]
    · obtain rfl : L = lay := Fin.ext hL
      rw [ht.regs (.x23, s7E L.val) (by simp [specA]), hs7E]
    · obtain rfl : L = lay := Fin.ext hL
      rw [ht.regs (.x30, treeE L.val) (by simp [specA]), htE]
    · exact hs.orig.frame (fun j hj hp => by
        rw [hm]
        apply memEval_frame_ofNat s _ _ (by unfold WIT WX at *; omega)
        intro p hp'
        simp only [specA, List.mem_cons, List.not_mem_nil, or_false] at hp'
        unfold WIT at *
        rcases hp' with rfl | rfl | rfl <;> simp <;> omega)

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)

/-! ## The decode expressions (Word level) -/

theorem toNat_srl (x : Word) (k : Nat) (hk : k < 64) : (x >>> ((BitVec.ofNat 64 k).toNat % 64)).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.shiftRight_eq_div_pow]

theorem toNat_sll (x : Word) (k : Nat) (hk : k < 64) :
    (x <<< ((BitVec.ofNat 64 k).toNat % 64)).toNat = x.toNat * 2 ^ k % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.shiftLeft_eq]

theorem toNat_andc (x : Word) (k : Nat) (hk : k < 2 ^ 64) : (x &&& BitVec.ofNat 64 k).toNat = x.toNat &&& k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

theorem toNat_remuc (x : Word) (k : Nat) (hk : 0 < k) (hk' : k < 2 ^ 64) :
    (rv64_remu x (BitVec.ofNat 64 k)).toNat = x.toNat % k := by
  unfold rv64_remu
  have hne : (BitVec.ofNat 64 k == 0#64) = false := by
    apply beq_false_of_ne
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk'] at this
    simp at this; omega
  rw [hne]
  simp only [Bool.false_eq_true, if_false, BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk']

/-- The two doublewords of the encoding answer at `0x140`. -/
structure AnsAt (u : MachineState) (a : BitVec 256) : Prop where
  lo : u.getMem (BitVec.ofNat 64 320) = a.extractLsb' 0 64
  hi : u.getMem (BitVec.ofNat 64 328) = a.extractLsb' 64 64

/-- The value of the answer's digest (Core's `shortHash`). -/
abbrev ansV (a : BitVec 256) : Nat := (a.extractLsb' 0 128).toNat

theorem ansV_split (a : BitVec 256) :
    ansV a = (a.extractLsb' 0 64).toNat + 2 ^ 64 * (a.extractLsb' 64 64).toNat := by
  simp only [ansV, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  generalize a.toNat = X
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul]

theorem ansV_lo (a : BitVec 256) : ansV a % 2 ^ 64 = (a.extractLsb' 0 64).toNat := by
  rw [ansV_split]; have := (a.extractLsb' 0 64).isLt; omega

theorem ansV_hi (a : BitVec 256) : ansV a / 2 ^ 64 = (a.extractLsb' 64 64).toNat := by
  rw [ansV_split]; have := (a.extractLsb' 0 64).isLt; omega

theorem a6E_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) : a6E.eval u = a.extractLsb' 0 64 := h.lo
theorem a7E_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) : a7E.eval u = a.extractLsb' 64 64 := h.hi

/-- `sumE` is the lower decode's SWAR sum of the answer (`Decode.lowSum`) when `v1 < 2^62`. -/
theorem sumE_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (hr : ansV a / 2 ^ 64 < 2 ^ 62) :
    (sumE.eval u).toNat = lowSum (ansV a) := by
  have hb : (b1E.eval u).toNat = 2 * (ansV a / 2 ^ 64) := by
    simp only [b1E, E.eval, BinOp.eval, a7E_eval h, kw]
    rw [toNat_sll _ 1 (by norm_num), ← ansV_hi]
    rw [Nat.mod_eq_of_lt (by omega)]; ring
  have hsw : sw1E.eval u = sw1RefE.eval u := by
    have he : (BitVec.ofNat 64 3).toNat % 64 = 3 := by decide
    simp only [sw1E, swLowE, sw1RefE, E.eval, BinOp.eval, kw, M1c, he]
    exact swar7_eq _ _ (by rw [hb]; omega)
  have hs1 : (sw1E.eval u).toNat = sw1 (ansV a % 2 ^ 64) (2 * (ansV a / 2 ^ 64)) := by
    rw [hsw]
    simp only [sw1RefE, E.eval, BinOp.eval, kw]
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, toNat_andc _ _ (by norm_num [M1c]),
      toNat_andc _ _ (by norm_num [M1c]), toNat_andc _ _ (by norm_num [M1c]), toNat_andc _ _ (by norm_num [M1c]),
      toNat_srl _ 3 (by norm_num), toNat_srl _ 3 (by norm_num)]
    have e1 := a6E_eval h
    simp only [a6E, E.eval] at e1
    simp only [a6E, E.eval]
    rw [e1, ← ansV_lo]
    have e2 : (E.eval u b1E) = BitVec.ofNat 64 (2 * (ansV a / 2 ^ 64)) := by
      apply BitVec.eq_of_toNat_eq; rw [hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [e2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2 * (ansV a / 2 ^ 64) < 2 ^ 64 by omega)]
    unfold sw1; rfl
  unfold lowSum lowSwar
  simp only [sumE, E.eval, BinOp.eval, kw]
  rw [toNat_remuc _ _ (by norm_num) (by norm_num), toNat_andc _ _ (by norm_num [M2c]), BitVec.toNat_add,
    toNat_srl _ 6 (by norm_num), hs1]
  rfl

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)

/-! ## B (lower layers): decode and the chain prologue -/

theorem rngBr_iff {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (k : Nat) (hk : k < 64) (d : Bool) :
    Br.holds u (rngBr k d) ↔ d = decide ((a.extractLsb' 64 64).toNat / 2 ^ k ≠ 0) := by
  simp only [rngBr, Br.holds, CmpOp.eval, E.eval, BinOp.eval, a7E_eval h, kw]
  have e : ((a.extractLsb' 64 64) >>> ((BitVec.ofNat 64 k).toNat % 64) != BitVec.ofNat 64 0) =
      decide ((a.extractLsb' 64 64).toNat / 2 ^ k ≠ 0) := by
    by_cases h0 : (a.extractLsb' 64 64).toNat / 2 ^ k = 0
    · have : (a.extractLsb' 64 64) >>> ((BitVec.ofNat 64 k).toNat % 64) = BitVec.ofNat 64 0 := by
        apply BitVec.eq_of_toNat_eq; rw [toNat_srl _ _ hk, h0]; rfl
      rw [this, decide_eq_false (by omega)]; rfl
    · have : (a.extractLsb' 64 64) >>> ((BitVec.ofNat 64 k).toNat % 64) ≠ BitVec.ofNat 64 0 := by
        intro he; have := congrArg BitVec.toNat he
        rw [toNat_srl _ _ hk, BitVec.toNat_ofNat, Nat.zero_mod] at this; exact h0 this
      rw [decide_eq_true h0]; exact bne_iff_ne.mpr this
  rw [e]; exact eq_comm

theorem ckBr_iff {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (hr : ansV a / 2 ^ 64 < 2 ^ 62) (lay : Layer)
    (d : Bool) :
    Br.holds u (ckBr lay.val d) ↔ d = decide (¬ (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8) := by
  have hS := lowSum_lt (ansV a)
  have hT : tgtL lay.val ≤ 195 := by fin_cases lay <;> decide
  have hT7 : 7 ≤ tgtL lay.val := by fin_cases lay <;> decide
  have ht4 : ((t4E lay.val).eval u).toNat = (lowSum (ansV a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 := by
    simp only [t4E, E.eval, BinOp.eval, kw]
    rw [BitVec.toNat_add, sumE_eval h hr, BitVec.toNat_ofNat]
    omega
  have hiff : (lowSum (ansV a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 < 8 ↔
      (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8 := by omega
  have key : (BinOp.sltu.eval ((t4E lay.val).eval u) (BitVec.ofNat 64 8) == BitVec.ofNat 64 0) =
      decide (¬ (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8) := by
    simp only [BinOp.eval, BitVec.ult, ht4, BitVec.toNat_ofNat]
    by_cases hc : (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8
    · have h1 : decide ((lowSum (ansV a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 < 8 % 2 ^ 64) = true := by
        rw [decide_eq_true_eq, show (8 : Nat) % 2 ^ 64 = 8 by norm_num]; exact hiff.mpr hc
      rw [h1, decide_eq_false (fun h => h hc)]; decide
    · have h1 : decide ((lowSum (ansV a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 < 8 % 2 ^ 64) = false := by
        rw [decide_eq_false_iff_not, show (8 : Nat) % 2 ^ 64 = 8 by norm_num]; exact fun h' => hc (hiff.mp h')
      rw [h1, decide_eq_true hc]; decide
  simp only [ckBr, Br.holds, CmpOp.eval]
  show (BinOp.sltu.eval ((t4E lay.val).eval u) (BitVec.ofNat 64 8) == BitVec.ofNat 64 0) = d ↔ _
  rw [key]; exact eq_comm

/-- The checksum digit of the lower decode. -/
def ckOf (lay : Layer) (a : BitVec 256) : Nat := (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64

/-- `a7` of the lower chain code: `(v1 << 1) | v0 >> 63`. -/
def a7lW (a : BitVec 256) : Word := ((a.extractLsb' 64 64) <<< 1) ||| ((a.extractLsb' 0 64) >>> 63)

/-- The chain context of the lower layer `lay` from the answer `a` (transition copy at `p`). -/
def lctxOf (w : WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) (p : Nat) : LCtx :=
  ⟨w, lay, 0, 0, (route index lay).2, (route index lay).1, s6v lay.val, a.extractLsb' 0 64, a7lW a, ckOf lay a,
    p + retOff lay.val⟩

theorem a7lW_toNat (a : BitVec 256) (hr : ansV a / 2 ^ 64 < 2 ^ 62) : (a7lW a).toNat = ansV a / 2 ^ 63 := by
  have hv := ansV_split a
  have h0 := (a.extractLsb' 0 64).isLt
  have h1 : (a.extractLsb' 64 64).toNat < 2 ^ 62 := by rw [← ansV_hi]; exact hr
  unfold a7lW
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show (a.extractLsb' 64 64).toNat * 2 ^ 1 < 2 ^ 64 by omega)]
  have hc : (a.extractLsb' 0 64).toNat / 2 ^ 63 < 2 ^ 1 := by omega
  rw [show (a.extractLsb' 64 64).toNat * 2 ^ 1 = 2 ^ 1 * (a.extractLsb' 64 64).toNat by ring,
    ← Nat.two_pow_add_eq_or_of_lt hc, hv]
  omega

/-- The machine's digits of the lower chain code are Core's decoded digits. -/
theorem lctx_digits (w : WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) (p : Nat) (hlay : lay ≠ 0)
    (ds : List Nat) (hds : decode lay (a.extractLsb' 0 128) = some ds) :
    ∀ i < 43, (lctxOf w index lay a p).dig i = ds.getD i 0 := by
  rw [decode_lower lay hlay] at hds
  have hr : ansV a / 2 ^ 64 / 2 ^ 62 = 0 := by
    by_contra hne; rw [if_pos hne] at hds; cases hds
  rw [if_neg (by simpa using hr)] at hds
  split at hds
  · rename_i hck
    simp only [Option.some.injEq] at hds
    subst hds
    intro i hi
    unfold LCtx.dig lctxOf
    simp only []
    by_cases h21 : i < 21
    · rw [if_pos h21, List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.getD_some]
      show (a.extractLsb' 0 64).toNat / 8 ^ i % 8 = ansV a / 2 ^ (3 * i) % 2 ^ 3
      rw [← ansV_lo, show (8 : Nat) ^ i = 2 ^ (3 * i) by rw [Nat.pow_mul]]
      have hV : ansV a = ansV a % 2 ^ 64 + 2 ^ 64 * (ansV a / 2 ^ 64) := (Nat.mod_add_div _ _).symm
      conv_rhs => rw [hV]
      exact (div_mod_add_pow (ansV a % 2 ^ 64) (ansV a / 2 ^ 64) (3 * i) 64 3 (by omega)).symm
    · by_cases h42 : i < 42
      · rw [if_neg h21, if_pos h42, List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
          List.getElem?_map, List.getElem?_range (by omega)]
        simp only [Option.map_some, Option.getD_some]
        show (a7lW a).toNat / 8 ^ (i - 21) % 8 = ansV a / 2 ^ (3 * i) % 2 ^ 3
        rw [a7lW_toNat a (by omega), Nat.div_div_eq_div_mul, show (2 : Nat) ^ 63 * 8 ^ (i - 21) = 2 ^ (3 * i) by
          rw [show (8 : Nat) = 2 ^ 3 by rfl, ← Nat.pow_mul, ← Nat.pow_add]; congr 1; omega]
        rfl
      · have hi42 : i = 42 := by omega
        subst hi42
        rw [if_neg h21, if_neg h42, List.getD_append_right _ _ _ _ (by simp)]
        rw [List.length_map, List.length_range, Nat.sub_self, List.getD_cons_zero]
        show ckOf lay a = _
        unfold ckOf
        rw [tgtL_eq]
  · cases hds

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)

theorem xtrTab_bound : (xtrTab.all fun r => r.all fun x => decide (x < 40000)) = true := by decide

theorem getD_lt_of_all : ∀ (l : List Nat) (B c : Nat), 0 < B → (l.all fun x => decide (x < B)) = true →
    l.getD c 0 < B
  | [], B, c, hB, _ => by simpa using hB
  | x :: l, B, 0, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa using h.1
  | x :: l, B, c + 1, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_lt_of_all l B c hB h.2

theorem getD_getD_lt : ∀ (L : List (List Nat)) (i j B : Nat), 0 < B →
    (L.all fun r => r.all fun x => decide (x < B)) = true → (L.getD i []).getD j 0 < B
  | [], i, j, B, hB, _ => by simpa using hB
  | r :: L, 0, j, B, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_lt_of_all r B j hB h.1
  | r :: L, i + 1, j, B, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_getD_lt L i j B hB h.2

theorem trPc_lt (lay c : Nat) : trPc lay c < 40000 :=
  getD_getD_lt xtrTab lay c 40000 (by norm_num) xtrTab_bound

/-- Witness words (V2's `Orig`) as the chain code's `OrigW`. -/
theorem origW_of {w : WBytes} {s : MachineState} {P : Nat → Prop} (hO : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w P s) (A : Nat)
    (hA : WIT ≤ A) (h8 : (A - WIT) % 8 = 0) (hx : A - WIT < WX) (hP : P (A - WIT)) : OrigW w s A := by
  have := hO.word (A - WIT) h8 hx hP
  rw [show WIT + (A - WIT) = A by omega] at this
  unfold OrigW
  rw [this, wword, show 64 * ((A - WIT) / 8) = 8 * (A - 0x800) by unfold WIT at *; omega]

/-- **B (lower layers)**: after the encoding answer `a`, a decode rejection (HALT(1)) or the chain code's `ChainIn 0`
for `lctxOf`. -/
theorem encB_step (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (c : Nat) (hc : c < nCopy lay.val)
    (hidx : index < 2 ^ 31) (t : MachineState) (ht : EncPre w pk index lay.val c t) (a : BitVec 256) :
    (decode lay (a.extractLsb' 0 128) = none → ∃ v k cy, Steps image (writeHash t a) k cy v ∧
        fetch image v = some (.base .ECALL) ∧ v.getReg .x5 = 1 ∧ v.getReg .x10 = 1 ∧ k ≤ 23 ∧ cy ≤ 26) ∧
    (decode lay (a.extractLsb' 0 128) ≠ none → ∃ s0, Steps image (writeHash t a) 29 32 s0 ∧
        (lctxOf w index lay a (trPc lay.val c)).ok ∧
        (∀ p ∈ (lctxOf w index lay a (trPc lay.val c)).known, s0.getReg p.1 = p.2) ∧
        (lctxOf w index lay a (trPc lay.val c)).Orig0 s0 ∧
        (lctxOf w index lay a (trPc lay.val c)).ChainIn s0 0 [] s0 ∧ Glob (lowerLayK lay.val) w pk s0 ∧
        SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd lay.val) s0 ∧
        s0.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1) ∧
        s0.getReg .x30 = BitVec.ofNat 64 (route index lay).2) := by
  set u := writeHash t a with hu
  have hcc := copy_parts lay.val (trPc lay.val c) (copyCheck_at lay.val c lay.isLt hc)
  have hB := (hcc.2.2.2.1 (fun h => hlay (Fin.ext h)))
  have hkt : KnownOK (bK lay.val) t := ht.glob.1
  have h12 : t.getReg .x12 = BitVec.ofNat 64 320 := hkt (.x12, 320) (by simp [bK])
  have hku : KnownOK (bK lay.val) u := fun p hp => by rw [hu, writeHash_getReg]; exact hkt p hp
  have hpcu : u.pc = pcOf (trPc lay.val c + stepsA lay.val + 1) := by
    rw [hu, writeHash_pc, ht.pc, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ofNat_add_ofNat]
    congr 1
  have hans : AnsAt u a := ⟨writeHash_at0 t a 320 h12 (by norm_num), writeHash_at8 t a 320 h12 (by norm_num)⟩
  have hdec := decode_lower lay hlay (a.extractLsb' 0 128)
  have hS := lowSum_lt (ansV a)
  constructor
  · intro hnone
    by_cases hr : (a.extractLsb' 64 64).toNat / 2 ^ 62 ≠ 0
    · obtain ⟨v, hv⟩ := spec_run hB.2.2 u hpcu hku (by
        intro b hb; simp only [rejRng, List.mem_singleton] at hb; subst hb
        exact (rngBr_iff hans 62 (by norm_num) true).mpr (by rw [decide_eq_true hr])) (by simp)
      exact ⟨v, 7, 7, hv.steps, hv.ecall rfl, hv.regs (.x5, kw 1) (by simp [rejRng]),
        hv.regs (.x10, kw 1) (by simp [rejRng]), by norm_num, by norm_num⟩
    · have hr' : ansV a / 2 ^ 64 < 2 ^ 62 := by rw [ansV_hi]; omega
      have hck : ¬ (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8 := by
        intro hck
        rw [hdec, if_neg (by rw [ansV_hi]; simpa using hr)] at hnone
        rw [if_pos (by rw [← tgtL_eq]; exact hck)] at hnone
        cases hnone
      obtain ⟨v, hv⟩ := spec_run hB.2.1 u hpcu hku (by
        intro b hb; simp only [rejCk, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact (ckBr_iff hans hr' lay true).mpr (by rw [decide_eq_true hck])
        · exact (rngBr_iff hans 62 (by norm_num) false).mpr (by rw [decide_eq_false hr])) (by simp)
      exact ⟨v, 22, 25, hv.steps, hv.ecall rfl, hv.regs (.x5, kw 1) (by simp [rejCk]),
        hv.regs (.x10, kw 1) (by simp [rejCk]), by norm_num, by norm_num⟩
  · intro hsome
    have hr0 : (a.extractLsb' 64 64).toNat / 2 ^ 62 = 0 := by
      by_contra hne
      apply hsome; rw [hdec, if_pos (by rw [ansV_hi]; exact hne)]
    have hr' : ansV a / 2 ^ 64 < 2 ^ 62 := by rw [ansV_hi]; omega
    have hck : (tgtL lay.val + 2 ^ 64 - lowSum (ansV a)) % 2 ^ 64 < 8 := by
      by_contra hck
      apply hsome
      rw [hdec, if_neg (by rw [ansV_hi]; simpa using hr0), if_neg (by rw [← tgtL_eq]; exact hck)]
    obtain ⟨s0, hs0⟩ := spec_run hB.1 u hpcu hku (by
      intro b hb; simp only [specBl, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact (ckBr_iff hans hr' lay false).mpr (by rw [decide_eq_false (not_not_intro hck)])
      · exact (rngBr_iff hans 62 (by norm_num) false).mpr (by rw [decide_eq_false (fun h => h hr0)])) (by simp)
    set L := lctxOf w index lay a (trPc lay.val c) with hL
    have htp := trPc_lt lay.val c
    have hko : KnownOK (postBl lay.val (trPc lay.val c)) s0 := hs0.known
    have hkeep := hs0.keep
    have e17 : (a7lE.eval u) = a7lW a := by
      simp only [a7lE, b1E, E.eval, BinOp.eval, a7E_eval hans, a6E_eval hans, kw, a7lW]
      rfl
    have e29 : ((t4E lay.val).eval u) = 7#64 - BitVec.ofNat 64 (ckOf lay a) := by
      have hT : tgtL lay.val ≤ 195 := by fin_cases lay <;> decide
      have hT7 : 7 ≤ tgtL lay.val := by fin_cases lay <;> decide
      have hS' : lowSum (ansV a) < 4095 := lowSum_lt (ansV a)
      have hle : lowSum (ansV a) ≤ tgtL lay.val ∧ tgtL lay.val - lowSum (ansV a) < 8 := by omega
      have hcv : ckOf lay a = tgtL lay.val - lowSum (ansV a) := by unfold ckOf; omega
      rw [hcv]
      apply BitVec.eq_of_toNat_eq
      simp only [t4E, E.eval, BinOp.eval, kw]
      rw [BitVec.toNat_add, sumE_eval hans hr', BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      omega
    have hLok : L.ok := by
      refine ⟨tree_lt index lay hidx, leaf_lt32 index lay, by simp [hL, lctxOf], ?_, ?_, ?_, ?_, ?_, by simp [hL, lctxOf]⟩
      · simp only [hL, lctxOf]; fin_cases lay <;> decide
      · simp only [hL, lctxOf]; fin_cases lay <;> simp [s6v]
      · simp only [hL, lctxOf]; fin_cases lay <;> decide
      · simp only [hL, lctxOf]; unfold ckOf at hck ⊢; omega
      · simp only [hL, lctxOf]; unfold retOff; split_ifs <;> omega
    have hGu : Glob (bK lay.val) w pk u := by
      have := Glob_writeHash ht.glob a 320 h12 (by decide)
      exact this
    have hGs0 := hs0.glob _ w pk hGu (RelOK.nil u)
    have hOu : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd lay.val) u := by
      have := Orig_writeHash ht.orig a 320 h12 (by norm_num)
      exact this.mono (fun o ho => ⟨ho, Or.inr (by unfold WIT; omega)⟩)
    have hOs0 : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd lay.val) s0 := by
      have := hs0.orig_const hOu
      exact this.mono (fun o ho => ⟨ho, by simp⟩)
    have hpc0 : s0.pc = pcOf (L.startPc 0) := by
      rw [hs0.spc tgtl rfl]
      simp only [tgtl, E.eval, BinOp.eval, a6E_eval hans, kw]
      have hk0 : L.kOf 0 = (a.extractLsb' 0 64).toNat % 512 := by
        rw [L.kOf_eq 0 (by norm_num), if_pos (by norm_num)]
        show (a.extractLsb' 0 64).toNat / 2 ^ (9 * (0 % 7)) % 512 = _
        rw [show 9 * (0 % 7) = 0 from rfl, pow_zero, Nat.div_one]
      have hm : ((a.extractLsb' 0 64) <<< ((BitVec.ofNat 64 9).toNat % 64) &&& BitVec.ofNat 64 0x3fe00) =
          BitVec.ofNat 64 (512 * L.kOf 0) := by
        apply BitVec.eq_of_toNat_eq
        rw [toNat_andc _ _ (by norm_num), toNat_sll _ 9 (by norm_num), show (0x3fe00 : Nat) = 512 * (2 ^ 9 - 1) by norm_num,
          land_mask _ _ (le_refl _), field_shl _ _ _ (le_refl _) (le_refl _), hk0, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show 512 * ((a.extractLsb' 0 64).toNat % 512) < 2 ^ 64 by omega)]
        rw [Nat.sub_self, pow_zero, Nat.div_one]
        rfl
      rw [hm]
      have e2 : BitVec.ofNat 64 (512 * L.kOf 0) + BitVec.ofNat 64 448800 =
          BitVec.ofNat 64 (0x1000 + 4 * entW 0 (L.kOf 0)) := by
        rw [ofNat_add_ofNat]; congr 1; unfold entW ttabIdx; omega
      rw [e2, even_andNot1' _ (by omega)]
      unfold LCtx.startPc; simp
    have hkL : ∀ q ∈ lowerLayK lay.val, s0.getReg q.1 = q.2 := fun q hq => hko q (by simp [postBl, hq])
    refine ⟨s0, hs0.steps, hLok, ?_, ?_, ⟨⟨fun _ _ => rfl, Frame.refl _ _, fun j hj => by simp at hj⟩, rfl,
      hGs0.2.2.2.2.2, hpc0⟩, ⟨hkL, hGs0.2.1, hGs0.2.2.1, hGs0.2.2.2.1, hGs0.2.2.2.2⟩, hOs0, ?_, ?_⟩
    · -- the chain code's known registers
      intro p hp
      simp only [LCtx.known, hL, lctxOf, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals dsimp only
      · exact hkL (.x5, 0) (by simp [lowerLayK, baseK])
      · exact hkL (.x11, 64) (by simp [lowerLayK])
      · exact hkL (.x6, 1) (by simp [lowerLayK])
      · exact hkL (.x7, 2) (by simp [lowerLayK])
      · exact hkL (.x8, 3) (by simp [lowerLayK])
      · exact hkL (.x9, 4) (by simp [lowerLayK])
      · exact hkL (.x13, 5) (by simp [lowerLayK])
      · exact hkL (.x26, 6) (by simp [lowerLayK])
      · exact hkL (.x28, BitVec.ofNat 64 (headerBank lay.val 0)) (by simp [lowerLayK])
      · exact hkL (.x2, 0x3fe00) (by simp [lowerLayK])
      · exact hko (.x15, 0x6e000) (by simp [postBl])
      · exact hko (.x22, BitVec.ofNat 64 (s6v lay.val)) (by simp [postBl])
      · rw [hkeep .x4 (by simp [keepB]), hu, writeHash_getReg, ht.tp lay rfl]; rfl
      · rw [hkL (.x27, BitVec.ofNat 64 (hw 1 lay.val)) (by simp [lowerLayK])]; unfold hw; congr 1
      · rw [hs0.regs (.x16, a6E) (by simp [specBl]), a6E_eval hans]
      · rw [hs0.regs (.x17, a7lE) (by simp [specBl]), e17]
      · rw [hs0.regs (.x29, t4E lay.val) (by simp [specBl]), e29]
      · exact hko (.x1, pcOf (trPc lay.val c + retOff lay.val)) (by simp [postBl])
    · -- the chain blocks are original
      intro i hi hi' k hk
      have hb := L.blk_props hLok i hi'
      have hS6 : L.S6 = s6v lay.val := rfl
      have hlb : 0x800 + (layerEnd lay.val) = L.S6 + 64 + 64 * 0 + 0 ∨ True := Or.inr trivial
      apply origW_of hOs0 _ (by unfold WIT; omega) (by
          unfold WIT; simp only [LCtx.blk, hS6]; fin_cases lay <;> simp [s6v] <;> omega)
        (by unfold WIT WX; omega)
      simp only [LCtx.blk, hS6]
      unfold WIT
      fin_cases lay <;> simp [s6v, layerEnd] <;> omega
    · rw [hkeep .x23 (by simp [keepB]), hu, writeHash_getReg, ht.s7 lay rfl]
    · rw [hkeep .x30 (by simp [keepB]), hu, writeHash_getReg, ht.t5 lay rfl]

end SigGolfCandidate.T3M.CanonicalPort

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart66

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart67

/-! # V1 layers: the leaf-pk block (`xlpk*`) and `LeafOut` (the state at the Merkle dispatch)

At the chain code's return pc `trPc lay c + retOff lay` the leaf-pk block writes the leaf header word
`T(2) = s11 + 0x100` and the route word `tp` at `base + 16`, `base + 24` (`base = 0x300` lower, `0x200` top; the
top also zeroes `0x570`, `0x578`, the padding of its 944-byte input), sets `tp = s11 + 0x200` (word 0 of the node
headers of the Merkle levels), `a0 = base`, `a1 = 704` / `960` (the leaf-pk HASH arguments), `a5` = the window of
`stab_lay_0`, and jumps (`jalr`) to the table word of the leaf's chunk-0 bits. The leaf-pk HASH itself is the first
`ecall` of the Merkle shape block (V3); `LeafOut.hashInput` states its input.

`leafCheck` is `copyCheck`'s leaf-pk part with every register the block does not write kept (`keepLfAll`), checked
for every copy by the kernel (`leafCheck_at`).

**`LeafOut w pk index lay ends u`** (V3's input): `u` is at the `stab_lay_0` word of the leaf's chunk-0 bits; V2's
`Glob (lfK lay)` (the next transition's constants `s11 = T(1, lay)`, `s8`, `sp`, `s4`, `s5`, `t3`, the step registers
`1 .. 7`, `tp = T(3, lay)`, `a0`, `a1`, `a5`, `s6`); `s7 = 2^h + leaf`, `t5 = tree`; the chain ends in the leaf-pk
slots, the leaf header words (and the top's zero words); the witness of the layers below and of this layer's Merkle
blocks original. `leafL_step` (from the lower chain phase's `ChainOut 43`) and `leafT_step` (from the top's `TopOut`)
reach it in 11 resp. 13 steps (= cycles). -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)

/-! ## The leaf-pk block with all untouched registers kept -/

/-- The registers the leaf-pk block neither writes nor knows at its start. -/
def keepLfAll (lay : Nat) : List Reg := [.x1, .x2, .x7, .x8, .x9, .x12, .x13, .x16, .x17, .x19, .x20, .x21, .x22, .x23,
  .x24, .x25, .x26, .x29, .x30, .x31] ++ (if lay = 0 then [.x6, .x28] else [])

/-- `copyCheck`'s leaf-pk part, keeping `keepLfAll`. -/
def leafCheck (lay p : Nat) : Bool :=
  specB [] [] baseK (runAt (leafK lay) [] (p + retOff lay) [.jmp]) (specLf lay) [] (postLf lay) (keepLfAll lay)

/-- The leaf-pk blocks of the copies `lo .. lo + n - 1` of layer `lay`. -/
def leafChecks (lay lo n : Nat) : Bool := (List.range' lo n).all fun c => leafCheck lay (trPc lay c)

set_option maxRecDepth 100000 in
theorem leafChecks_3 : leafChecks 3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem leafChecks_2 : leafChecks 2 0 64 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem leafChecks_1 : leafChecks 1 0 64 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem leafChecks_0 : leafChecks 0 0 128 = true := by decide +kernel

theorem leafCheck_at (lay c : Nat) (hlay : lay < 4) (hc : c < nCopy lay) : leafCheck lay (trPc lay c) = true := by
  obtain ⟨n3, n2, n1, n0⟩ := nCopy_eq
  have hall : ∀ n, leafChecks lay 0 n = true → c < n → leafCheck lay (trPc lay c) = true :=
    fun n h h2 => List.all_eq_true.mp h c (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
  interval_cases lay
  · exact hall 128 leafChecks_0 (by omega)
  · exact hall 64 leafChecks_1 (by omega)
  · exact hall 64 leafChecks_2 (by omega)
  · exact hall 1 leafChecks_3 (by omega)

/-! ## `LeafOut` -/

/-- The leaf-pk input block: `0x200` (top, 58 ends, 960 bytes) or `0x300` (lower, 43 ends, 704 bytes). -/
def lfBase (lay : Nat) : Nat := if lay = 0 then 512 else 768
def lfBytes (lay : Nat) : Nat := if lay = 0 then 896 else 704
/-- Its 64-byte blocks. -/
def lfBlocks (lay : Nat) : Nat := if lay = 0 then 14 else 11
/-- The leaf-pk slot of chain `j`. -/
def lfSlot (lay j : Nat) : Nat := if lay = 0 then slotT j else slotL j
/-- The leaf bits of the first `stab` dispatch (the Merkle levels' chunk 0: 7 on layer 1, else 6). -/
def stabBits (lay : Nat) : Nat := if lay = 1 then 7 else 6
/-- Steps (= cycles) of the leaf-pk block. -/
def lfSteps (lay : Nat) : Nat := if lay = 0 then 13 else 11

/-- The registers the block keeps that the Merkle code and the next transition read: `sp`, `t3`, the step
registers `1 .. 7`, `s6`; below the top also the 3-bit masks `s4`, `s5` and `s8 = 0x10000`. -/
def lfKeepK (lay : Nat) : List (Reg × Word) :=
  [(.x2, 0x3fe00), (.x28, BitVec.ofNat 64 (headerBank 0 0)), (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6),
   (.x31, 7), (.x22, BitVec.ofNat 64 (s6v lay))] ++
  (if lay = 0 then [] else [(.x20, BitVec.ofNat 64 M1c), (.x21, BitVec.ofNat 64 M2c), (.x24, 0x10000)])

/-- The known registers at the Merkle dispatch: `postLf` (`t0`, `s2`, `s11 = T(1)`, `gp = T(2)`, `tp = T(3)`, `a0`,
`a1`, `a5`) and `lfKeepK`. -/
def lfK (lay : Nat) : List (Reg × Word) := postLf lay ++ lfKeepK lay

/-- **The state at the Merkle dispatch** (V3's input): the `stab_lay_0` word of the leaf's chunk-0 bits, the
registers `lfK`, `s7 = 2^h + leaf`, `t5 = tree`, the `chainCount lay` ends in the leaf-pk slots, the leaf header
words `T(2, lay, tree, 0, leaf)` at `base + 16`, `base + 24` (and on the top the zero words at `0x570`, `0x578`), and
the witness offsets `[11288, layerBase lay + 64 h)` (the layers below and this layer's Merkle blocks) original. -/
structure LeafOut (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (ends : List Digest) (u : MachineState) :
    Prop where
  pc : u.pc = pcOf (stabIdx lay.val + (route index lay).1 % 2 ^ stabBits lay.val)
  glob : Glob (lfK lay.val) w pk u
  s7 : u.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1)
  t5 : u.getReg .x30 = BitVec.ofNat 64 (route index lay).2
  len : ends.length = chainCount lay
  ends : ∀ j < chainCount lay, DigAt u (lfSlot lay.val j) (ends.getD j 0)
  T0 : u.getMem (BitVec.ofNat 64 (lfBase lay.val + 16)) = BitVec.ofNat 64 (hdr0 2 lay.val (route index lay).2 0)
  T1 : u.getMem (BitVec.ofNat 64 (lfBase lay.val + 24)) =
    BitVec.ofNat 64 (hdr1 (route index lay).2 (route index lay).1)
  zero : lay = 0 → u.getMem (BitVec.ofNat 64 0x570) = 0 ∧ u.getMem (BitVec.ofNat 64 0x578) = 0
  orig : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerBase lay + 64 * height lay) u

/-- **The leaf-pk HASH input at `LeafOut`** (`a0`, `a1` and the block as left by the leaf-pk block): Core's
`leafHash` input, `lfBlocks lay` blocks. -/
theorem LeafOut.hashInput {w : WBytes} {pk : Digest} {index : Nat} {lay : Layer} {ends : List Digest}
    {u : MachineState} (h : LeafOut w pk index lay ends u) :
    hashInput u = toQ (pad64 (leafInput lay (route index lay).2 (route index lay).1 ends)) ∧
      (toQ (pad64 (leafInput lay (route index lay).2 (route index lay).1 ends))).blocks = lfBlocks lay.val := by
  have h10 := h.glob.1 (.x10, BitVec.ofNat 64 (lfBase lay.val)) (by simp [lfK, postLf, lfBase])
  have h11 := h.glob.1 (.x11, BitVec.ofNat 64 (lfBytes lay.val)) (by simp [lfK, postLf, lfBytes])
  have hT0 := h.T0
  have hT1 := h.T1
  have hS := h.ends
  have hn := h.len
  by_cases h0 : lay = 0
  · subst h0
    have r := topLeaf_hashInput u _ _ ends hn h10 h11 hS hT0 hT1 (h.zero rfl).1 (h.zero rfl).2
    exact ⟨r.1, r.2⟩
  · have hc := LCtx.chainCount_lower lay h0
    have hv : lay.val ≠ 0 := fun hv => h0 (Fin.ext hv)
    simp only [lfBase, lfBytes, lfSlot, lfBlocks, if_neg hv] at h10 h11 hT0 hT1 hS ⊢
    rw [hc] at hn hS
    exact lowLeaf_hashInput u lay _ _ ends hn h10 h11 hS hT0 hT1

/-! ## Helpers -/

/-- V2's `Glob` through a frame that avoids the protected low words (`< 0x140`) and the witness header. -/
theorem glob_frame {gk gk' : List (Reg × Word)} {w : WBytes} {pk : Digest} {s t : MachineState}
    {W : Nat → Prop} (hG : Glob gk w pk s) (hf : Frame s t W)
    (hW : ∀ A, W A → 0x140 ≤ A ∧ (A < 0x800 ∨ 0x840 ≤ A) ∧ A < 2 ^ 23) (hk : ∀ p ∈ gk', t.getReg p.1 = p.2) :
    Glob gk' w pk t := by
  obtain ⟨-, hH, hP, hZ, hh, hD⟩ := hG
  have hn : ∀ A, A < 0x140 → ¬ W A := fun A hA h => by have := hW A h; omega
  refine ⟨hk, fun j hj => ?_, ⟨?_, ?_⟩, fun a ha => ?_, ?_, ?_⟩
  · rw [hf.get (by unfold WIT; omega) (fun h => by have := hW _ h; unfold WIT at this; omega)]; exact hH j hj
  · exact (hf.get (A := 0xA0) (by norm_num) (hn _ (by norm_num))).trans hP.1
  · exact (hf.get (A := 0xA8) (by norm_num) (hn _ (by norm_num))).trans hP.2
  · have ha' : a < 0x140 := by simp only [pSlots, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
    rw [hf.get (by omega) (hn _ ha')]; exact hZ a ha
  · unfold PHalf CTRW at *; rw [hf.get (by norm_num) (hn _ (by norm_num))]; exact hh
  · exact hD.congr (fun A hA hB => hf.get (by omega) (fun hw => by
      have := hW A hw
      unfold SigGolfCandidate.T3M.CanonicalPort.Verify.TAB at hA
      omega))

theorem land4 (n k : Nat) : n &&& (4 * (2 ^ k - 1)) = 4 * (n / 4 % 2 ^ k) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, show (4 : Nat) = 2 ^ 2 by norm_num, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h2 : 2 ≤ j
  · simp only [h2, decide_true, Bool.true_and, show j - 2 + 2 = j by omega]
    by_cases hj : j - 2 < k
    · simp [hj]
    · simp [hj]
  · simp [h2]

theorem stabMask_eq (lay : Nat) : stabMask lay = 4 * (2 ^ stabBits lay - 1) := by
  unfold stabMask stabBits; split <;> rfl

/-- The dispatch target: the `stab_lay_0` word of the low `stabBits` bits of the leaf (`s7 = 2^h + leaf`). -/
theorem tgtLfOld_eval (lay : Nat) (t : MachineState) (h leaf : Nat) (hn : stabBits lay ≤ h) (hh : h ≤ 12)
    (hl : leaf < 2 ^ h) (hs : stabIdx lay < 2 ^ 32)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 (2 ^ h + leaf)) :
    (tgtLfOld lay).eval t = pcOf (stabIdx lay + leaf % 2 ^ stabBits lay) := by
  have hpow : 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
  have hb : stabBits lay ≤ 7 := by unfold stabBits; split <;> omega
  have hpb : 2 ^ stabBits lay ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hb
  have hX : 2 ^ h + leaf < 2 ^ 13 := by omega
  have hmod : (2 ^ h + leaf) % 2 ^ stabBits lay = leaf % 2 ^ stabBits lay := by
    rw [show 2 ^ h = 2 ^ stabBits lay * 2 ^ (h - stabBits lay) by rw [← Nat.pow_add]; congr 1; omega,
      Nat.mul_add_mod]
  have hm : ((t.getReg .x23) <<< ((BitVec.ofNat 64 2).toNat % 64) &&& BitVec.ofNat 64 (stabMask lay)) =
      BitVec.ofNat 64 (4 * (leaf % 2 ^ stabBits lay)) := by
    apply BitVec.eq_of_toNat_eq
    have hmk : stabMask lay < 2 ^ 64 := by unfold stabMask; split <;> norm_num
    rw [toNat_andc _ _ hmk, toNat_sll _ 2 (by norm_num), stabMask_eq, land4, h23, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 2 ^ h + leaf < 2 ^ 64 by omega),
      show (2 ^ h + leaf) * 2 ^ 2 % 2 ^ 64 / 4 = 2 ^ h + leaf by omega, hmod, BitVec.toNat_ofNat]
    have := Nat.mod_lt leaf (show 0 < 2 ^ stabBits lay by positivity)
    omega
  simp only [tgtLfOld, E.eval, BinOp.eval, kw]
  rw [hm, ofNat_add_ofNat, even_andNot1' _ (by omega)]
  congr 1
  omega

theorem stabBits_le (lay : Layer) : stabBits lay.val ≤ hL lay.val := by fin_cases lay <;> decide

theorem stabIdx_lt (lay : Nat) : stabIdx lay < 2 ^ 32 := by
  unfold stabIdx
  rcases lay with _ | _ | _ | _ | n <;> simp

/-- A lower route has exactly the sentinel absorbed by the relocated dispatch. -/
theorem tgtLf_lower_eval (lay : Layer) (hlay : lay ≠ 0) (t : MachineState) (leaf : Nat)
    (hl : leaf < 2 ^ hL lay.val)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + leaf)) :
    (tgtLf lay.val).eval t = pcOf (stabIdx lay.val + leaf % 2 ^ stabBits lay.val) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have he : stabBits lay.val = hL lay.val := by fin_cases lay <;> simp_all [stabBits, hL]
  have hb : 2 ^ hL lay.val ≤ 128 := by fin_cases lay <;> simp_all [hL]
  have hi := stabIdx_lt lay.val
  have hbase : 4 * 2 ^ hL lay.val ≤ 0x1000 + 4 * stabIdx lay.val := by omega
  have hshift : t.getReg .x23 <<< ((BitVec.ofNat 64 2).toNat % 64) =
      BitVec.ofNat 64 (4 * (2 ^ hL lay.val + leaf)) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sll _ 2 (by norm_num), h23]
    simp only [BitVec.toNat_ofNat]
    omega
  simp only [tgtLf, if_neg h0, E.eval, BinOp.eval, kw]
  rw [hshift, ofNat_add_ofNat]
  have hn : 4 * (2 ^ hL lay.val + leaf) + (0x1000 + 4 * stabIdx lay.val - 4 * 2 ^ hL lay.val) =
      0x1000 + 4 * (stabIdx lay.val + leaf) := by omega
  rw [hn, even_andNot1' _ (by omega), he, Nat.mod_eq_of_lt hl]

theorem hw2_hdr0 (lay : Layer) (tree : Nat) (ht : tree < 2 ^ 32) : hw 2 lay.val = hdr0 2 lay.val tree 0 := by
  rw [hdr0_eq _ _ _ _ (by norm_num) (by have := lay.isLt; omega) ht (by norm_num)]
  unfold hw; ring

/-- The lower layers' geometry: `s6 - 1024` is the machine address of the chain blocks, right above the Merkle
blocks. -/
theorem geomL (lay : Layer) (h : lay ≠ 0) :
    s6v lay.val = 2048 + layerBase lay + 64 * height lay + 1024 ∧ layerBase lay + 64 * height lay ≤ layerEnd lay.val ∧
      11288 ≤ layerBase lay ∧ layerEnd lay.val < 25241 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide

theorem geomT : s6v 0 = 15064 ∧ layerBase 0 = 11288 ∧ height 0 = 12 ∧ layerEnd 0 = 15768 := by
  decide

/-! ## The leaf-pk block -/

/-- **The lower leaf-pk block**: from the lower chain phase's `ChainOut 43` (base `s0` = `encB_step`'s state) to
`LeafOut` in 11 steps. -/
theorem leafL_step (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (c : Nat)
    (hc : c < nCopy lay.val) (hidx : index < 2 ^ 31) (a : BitVec 256) (s0 : MachineState)
    (hk : ∀ p ∈ (lctxOf w index lay a (trPc lay.val c)).known, s0.getReg p.1 = p.2)
    (hG : Glob (lowerLayK lay.val) w pk s0) (hO : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd lay.val) s0)
    (h23 : s0.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1))
    (h30 : s0.getReg .x30 = BitVec.ofNat 64 (route index lay).2)
    (ends : List Digest) (t : MachineState)
    (ht : (lctxOf w index lay a (trPc lay.val c)).ChainOut s0 43 ends t) :
    ∃ u, Steps image t 11 11 u ∧ LeafOut w pk index lay ends u := by
  set L := lctxOf w index lay a (trPc lay.val c) with hLd
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := ht
  have hkL : ∀ q ∈ lowerLayK lay.val, s0.getReg q.1 = q.2 := hG.1
  have hknown : KnownOK (leafK lay.val) t := by
    intro p hp
    simp only [leafK, if_neg h0, baseK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ((rfl | rfl) | rfl) | rfl
    · rw [hR .x5 (by simp [chainRegs])]; exact hkL (_, _) (by simp [lowerLayK, baseK])
    · rw [hR .x18 (by simp [chainRegs])]; exact hkL (_, _) (by simp [lowerLayK, baseK])
    · rw [hR .x27 (by simp [chainRegs])]; exact hkL (_, _) (by simp [lowerLayK])
    · rw [hR .x6 (by simp [chainRegs])]; exact hkL (_, _) (by simp [lowerLayK])
  obtain ⟨u, hu⟩ := spec_run (leafCheck_at lay.val c lay.isLt hc) t (by rw [hpc]; rfl) hknown
    (by intro b hb; simp [specLf, h0] at hb) (by simp)
  have hst := hu.steps
  rw [show (specLf lay.val).steps = 11 by simp [specLf, h0], show (specLf lay.val).cycles = 11 by simp [specLf, h0]]
    at hst
  refine ⟨u, hst, ?_⟩
  have hku : KnownOK (postLf lay.val) u := hu.known
  have hkeep := hu.keep
  have hmem : ∀ A, u.getMem A = memEval t [(⟨none, BitVec.ofNat 64 792⟩, .reg .x4),
      (⟨none, BitVec.ofNat 64 784⟩, kw (hw 2 lay.val))] A := by
    intro A; rw [hu.mem]; simp [specLf, h0]
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ 792 → A ≠ 784 → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2
    rw [hmem]
    apply memEval_frame_ofNat t _ A hA
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp <;> omega
  have htr := tree_lt index lay hidx
  have hlf := leaf_lt index lay
  obtain ⟨hg1, hg2, hg3, hg4⟩ := geomL lay hlay
  have hS6 : L.S6 = s6v lay.val := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd h hlay, ?_⟩
  · -- the dispatch
    rw [hu.spc (tgtLf lay.val) (by simp [specLf, h0])]
    have := hL_le lay
    exact tgtLf_lower_eval lay hlay t _ hlf
      (by rw [hR .x23 (by simp [chainRegs]), h23])
  · -- the registers and the protected memory
    have hGt : Glob baseK w pk t := glob_frame hG hF (fun A hA => by
        unfold LCtx.Wr LCtx.blk at hA; rw [hS6] at hA
        have : slotL L.i0 = 768 := rfl
        rw [this] at hA
        rcases hA with hA | hA <;> omega)
      (fun p hp => hknown p (by simp [leafK, hp]))
    have hGu := hu.glob _ w pk hGt (RelOK.nil t)
    refine ⟨fun p hp => ?_, hGu.2.1, hGu.2.2.1, hGu.2.2.2.1, hGu.2.2.2.2⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hku p hp
    · have h22 : s0.getReg .x22 = BitVec.ofNat 64 (s6v lay.val) :=
        hk (.x22, BitVec.ofNat 64 L.S6) (by simp [LCtx.known])
      simp only [lfKeepK, if_neg h0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)
      all_goals first
        | exact hku (.x28, BitVec.ofNat 64 (headerBank 0 0)) (by simp [postLf, h0])
        | exact hku (.x6, 1) (by simp [postLf, leafK, h0])
        | rw [hkeep _ (by simp [keepLfAll, h0]), hR _ (by simp [chainRegs])]
      all_goals first
        | exact h22
        | exact hkL (_, _) (by simp [lowerLayK])
  · rw [hkeep .x23 (by simp [keepLfAll, h0]), hR .x23 (by simp [chainRegs]), h23]
  · rw [hkeep .x30 (by simp [keepLfAll, h0]), hR .x30 (by simp [chainRegs]), h30]
  · rw [hlen, LCtx.chainCount_lower lay hlay]; rfl
  · intro j hj
    rw [LCtx.chainCount_lower lay hlay] at hj
    have e := hS j (by rw [hlen]; exact hj)
    have hj0 : slotL (L.i0 + j) = slotL j := by rw [show L.i0 = 0 from rfl, Nat.zero_add]
    rw [hj0] at e
    simp only [lfSlot, if_neg h0]
    have hsl : slotL j = 768 ∨ 800 ≤ slotL j := by unfold slotL; split <;> omega
    have hsl' : slotL j < 2 ^ 32 := by unfold slotL; split <;> omega
    exact ⟨(hfr (slotL j) (by omega) (by omega) (by omega)).trans e.1,
      (hfr (slotL j + 8) (by omega) (by omega) (by omega)).trans e.2⟩
  · rw [show lfBase lay.val + 16 = 784 by simp [lfBase, h0], hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    simp only [E.eval, kw]
    rw [hw2_hdr0 lay _ htr]
  · rw [show lfBase lay.val + 24 = 792 by simp [lfBase, h0], hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    simp only [E.eval]
    rw [hR .x4 (by simp [chainRegs]), hk (.x4, BitVec.ofNat 64 L.w1) (by simp [LCtx.known])]
    rfl
  · -- the witness below the chain blocks
    have hOt : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerBase lay + 64 * height lay) t :=
      (hO.mono (fun o ho => ⟨ho.1, by omega⟩)).frame (fun j hj hp => hF.get (by unfold WIT WX at *; omega)
        (fun hw => by
          unfold LCtx.Wr at hw; rw [hS6] at hw
          unfold WIT at hw
          rcases hw with hw | hw <;> omega))
    exact (hu.orig_const hOt).mono (fun o ho => ⟨ho, by simp⟩)

/-- Exact chain-end interface before the shared top leaf aggregation block. -/
structure TopLeafReady (w : WBytes) (pk : Digest) (index c : Nat) (ends : List Digest)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf (trPc 0 c + 69)
  glob : Glob (leafK 0) w pk t
  keep : KnownOK (lfKeepK 0) t
  s7 : t.getReg .x23 = BitVec.ofNat 64 (2 ^ hL 0 + (route index 0).1)
  t5 : t.getReg .x30 = BitVec.ofNat 64 (route index 0).2
  tp : t.getReg .x4 = BitVec.ofNat 64 (hdr1 (route index 0).2 (route index 0).1)
  len : ends.length = 54
  ends : ∀ j < 54, DigAt t (slotT j) (ends.getD j 0)
  orig : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerBase 0 + 64 * height 0) t

/-- The exact 13-instruction top leaf block, independent of the chain decoder representation. -/
theorem leafT_step (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0) (hidx : index < 2 ^ 31)
    (ends : List Digest) (t : MachineState) (ht : TopLeafReady w pk index c ends t) :
    ∃ u, Steps image t 13 13 u ∧ LeafOut w pk index 0 ends u := by
  obtain ⟨u, hu⟩ := spec_run (leafCheck_at 0 c (by norm_num) hc) t ht.pc ht.glob.1
    (by intro b hb; simp [specLf] at hb) (by simp)
  have hst := hu.steps
  rw [show (specLf 0).steps = 13 by simp [specLf], show (specLf 0).cycles = 13 by simp [specLf]] at hst
  refine ⟨u, hst, ?_⟩
  have hku : KnownOK (postLf 0) u := hu.known
  have hkeep := hu.keep
  have hmem : ∀ A, u.getMem A = memEval t [(⟨none, BitVec.ofNat 64 1400⟩, kw 0), (⟨none, BitVec.ofNat 64 1392⟩, kw 0),
      (⟨none, BitVec.ofNat 64 536⟩, .reg .x4), (⟨none, BitVec.ofNat 64 528⟩, kw (hw 2 0))] A := by
    intro A; rw [hu.mem]; simp [specLf]
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ 1400 → A ≠ 1392 → A ≠ 536 → A ≠ 528 →
      u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    rw [hmem]
    apply memEval_frame_ofNat t _ A hA
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp <;> omega
  have htr := tree_lt index 0 hidx
  have hlf := leaf_lt index 0
  refine ⟨?_, ?_, ?_, ?_, ht.len, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩, ?_⟩
  · rw [hu.spc (tgtLf 0) (by simp [specLf])]
    change (tgtLfOld 0).eval t = _
    exact tgtLfOld_eval 0 t (hL 0) _ (stabBits_le 0) (by decide) hlf (stabIdx_lt _) ht.s7
  · have hGu := hu.glob _ w pk ht.glob (RelOK.nil t)
    refine ⟨fun p hp => ?_, hGu.2.1, hGu.2.2.1, hGu.2.2.2.1, hGu.2.2.2.2⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hku p hp
    · have hkp : p.1 ∈ keepLfAll 0 := by
        change p ∈ lfKeepK 0 at hp
        simp [lfKeepK] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [keepLfAll]
      rw [hkeep _ hkp]
      exact ht.keep p hp
  · rw [hkeep .x23 (by simp [keepLfAll]), ht.s7]
    rfl
  · rw [hkeep .x30 (by simp [keepLfAll]), ht.t5]
  · intro j hj
    have hj' : j < 54 := hj
    have e := ht.ends j hj'
    simp only [lfSlot, if_pos rfl]
    have hsl : slotT j = 512 ∨ (544 ≤ slotT j ∧ slotT j ≤ 1376) := by unfold slotT; split <;> omega
    exact ⟨(hfr (slotT j) (by omega) (by omega) (by omega) (by omega) (by omega)).trans e.1,
      (hfr (slotT j + 8) (by omega) (by omega) (by omega) (by omega) (by omega)).trans e.2⟩
  · rw [show lfBase (0 : Layer).val + 16 = 528 from rfl, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    simp only [E.eval, kw]
    exact hw2_hdr0 0 _ htr |>.symm ▸ rfl
  · rw [show lfBase (0 : Layer).val + 24 = 536 from rfl, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    exact ht.tp
  · rw [show (0x570 : Nat) = 1392 by norm_num, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    rfl
  · rw [show (0x578 : Nat) = 1400 by norm_num, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    rfl
  · exact (hu.orig_const ht.orig).mono (fun o ho => ⟨ho, by simp⟩)

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart67

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart68

namespace SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 600000
set_option Elab.async false

def pairRank (v : Digest) (q : Nat) : Nat := v.toNat / 2 ^ (7 * q) % 16384

theorem pairRank_lt (v : Digest) (q : Nat) : pairRank v q < 16384 := by unfold pairRank; omega

theorem pairRank_components (v : Digest) (q : Nat) :
    pairRank v q = topRank v q + 128 * topRank v (q+1) := by
  unfold pairRank topRank
  rw [show 7 * (q + 1) = 7 * q + 7 by omega, Nat.pow_add]
  norm_num
  rw [← Nat.div_div_eq_div_mul, show 16384 = 128 * 128 by rfl, Nat.mod_mul]

theorem pairWindow_rank (v : Digest) (q : Nat) (hq : q < 8 ∨ (9 ≤ q ∧ q < 16)) :
    topWindow v q &&& 16383#64 = BitVec.ofNat 64 (pairRank v q) := by
  unfold topWindow pairRank
  split_ifs with h
  · simpa using ext_shr_mask v 0 (7 * q) 14 (by omega)
  · have he := ext_shr_mask v 63 (7 * (q - 9)) 14 (by omega)
    rw [show 63 + 7 * (q - 9) = 7 * q by omega] at he
    exact he

theorem pairWindow_shift (v : Digest) (q : Nat) (hq : q < 7 ∨ 9 ≤ q) :
    topWindow v q >>> 14 = topWindow v (q + 2) := by
  unfold topWindow
  by_cases h : q < 7
  · rw [if_pos (by omega),if_pos (by omega),← BitVec.shiftRight_add]
    congr 1 <;> omega
  · rw [if_neg (by omega),if_neg (by omega),← BitVec.shiftRight_add]
    congr 1 <;> omega

theorem pairLookup_pairRank (v : Digest) (q : Nat) :
    pairLookup (pairRank v q) = pairWeight (topRank v q) (topRank v (q+1)) := by
  rw [pairRank_components,pairLookup_components _ _ (topRank_lt v q)]

end SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary

end CanonicalPortPart68

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart69

namespace SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 100000
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

def pairInitCode : List (BitVec 32) := [0x00ff89b7, 0x00004c37, 0xfffc0c13]
sym_block pairInitBase := symRun { noAlias := true } pairInitCode 0#64 200
theorem pairInit_run (pc : Word) : symRun { noAlias := true } pairInitCode pc 200 =
    some ⟨pairInitBase.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by rfl

def pairPtr0Code : List (BitVec 32) := [0x01887733, 0x01370733]
sym_block pairPtr0Base := symRun { noAlias := true } pairPtr0Code 0#64 200
theorem pairPtr0_run (pc : Word) : symRun { noAlias := true } pairPtr0Code pc 200 =
    some ⟨pairPtr0Base.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

def pairPtrCode : List (BitVec 32) := [0x018ef733, 0x01370733]
sym_block pairPtrBase := symRun { noAlias := true } pairPtrCode 0#64 200
theorem pairPtr_run (pc : Word) : symRun { noAlias := true } pairPtrCode pc 200 =
    some ⟨pairPtrBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

def pairShift0Code : List (BitVec 32) := [0x00e85e93]
sym_block pairShift0Base := symRun { noAlias := true } pairShift0Code 0#64 200
theorem pairShift0_run (pc : Word) : symRun { noAlias := true } pairShift0Code pc 200 =
    some ⟨pairShift0Base.res.st, .c (pc + 4), .endOfCode, 1, 1⟩ := by rfl

def pairTailCode : List (BitVec 32) := [0x00ec8cb3, 0x00eede93]
sym_block pairTailBase := symRun { noAlias := true } pairTailCode 0#64 200
theorem pairTail_run (pc : Word) : symRun { noAlias := true } pairTailCode pc 200 =
    some ⟨pairTailBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

def singlePtrCode : List (BitVec 32) := [0x07fef713, 0x01370733]
sym_block singlePtrBase := symRun { noAlias := true } singlePtrCode 0#64 200
theorem singlePtr_run (pc : Word) : symRun { noAlias := true } singlePtrCode pc 200 =
    some ⟨singlePtrBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

def singleTailCode : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
sym_block singleTailBase := symRun { noAlias := true } singleTailCode 0#64 200
theorem singleTail_run (pc : Word) : symRun { noAlias := true } singleTailCode pc 200 =
    some ⟨singleTailBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

def pairCrossCode : List (BitVec 32) := [0x00189893, 0x01d8e8b3, 0x00088e93]
sym_block pairCrossBase := symRun { noAlias := true } pairCrossCode 0#64 200
theorem pairCross_run (pc : Word) : symRun { noAlias := true } pairCrossCode pc 200 =
    some ⟨pairCrossBase.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by rfl

def tailInitCode : List (BitVec 32) := [0x00ffc9b7]
sym_block tailInitBase := symRun { noAlias := true } tailInitCode 0#64 200
theorem tailInit_run (pc : Word) : symRun { noAlias := true } tailInitCode pc 200 =
    some ⟨tailInitBase.res.st, .c (pc + 4), .endOfCode, 1, 1⟩ := by rfl

theorem pairInit_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc pairInitCode) (hpc : s.pc = pc) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧
      t.getReg .x19 = BitVec.ofNat 64 PAIR_DATA ∧ t.getReg .x24 = 16383#64 ∧
      RegsExcept s t [.x19,.x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (pairInit_run pc) hc s hpc (by simp [pairInitBase.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · rfl
  · rfl
  · rfl
  · intro q hq; cases q <;> simp at hq <;> simp [pairInitBase.res,rv_simp] <;> rfl
  · intro A _ _; simp [pairInitBase.res,rv_simp]

theorem pairPtr0_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc pairPtr0Code) (hpc : s.pc = pc) (v : Digest) (q : Nat)
    (hq : q < 8 ∨ (9 ≤ q ∧ q < 16))
    (hw : s.getReg .x16 = topWindow v q) (hb : s.getReg .x19 = BitVec.ofNat 64 PAIR_DATA)
    (hm : s.getReg .x24 = 16383#64) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧
      t.getReg .x14 = BitVec.ofNat 64 (PAIR_DATA + pairRank v q) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (pairPtr0_run pc) hc s hpc (by simp [pairPtr0Base.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,pairPtr0Base.res,rv_simp,hw,hb,hm,pairWindow_rank v q hq,ofNat_add_ofNat]
    congr 1; omega
  · intro q hq; cases q <;> simp at hq <;> simp [pairPtr0Base.res,rv_simp] <;> rfl
  · intro A _ _; simp [pairPtr0Base.res,rv_simp]

theorem pairPtr_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc pairPtrCode) (hpc : s.pc = pc) (v : Digest) (q : Nat)
    (hq : q < 8 ∨ (9 ≤ q ∧ q < 16))
    (hw : s.getReg .x29 = topWindow v q) (hb : s.getReg .x19 = BitVec.ofNat 64 PAIR_DATA)
    (hm : s.getReg .x24 = 16383#64) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧
      t.getReg .x14 = BitVec.ofNat 64 (PAIR_DATA + pairRank v q) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (pairPtr_run pc) hc s hpc (by simp [pairPtrBase.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,pairPtrBase.res,rv_simp,hw,hb,hm,pairWindow_rank v q hq,ofNat_add_ofNat]
    congr 1; omega
  · intro q hq; cases q <;> simp at hq <;> simp [pairPtrBase.res,rv_simp] <;> rfl
  · intro A _ _; simp [pairPtrBase.res,rv_simp]

theorem pairShift0_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc pairShift0Code) (hpc : s.pc = pc) (v : Digest)
    (hw : s.getReg .x16 = v.extractLsb' 0 64) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧ t.getReg .x29 = topWindow v 2 ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (pairShift0_run pc) hc s hpc (by simp [pairShift0Base.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp [pairShift0Base.res,rv_simp,hw,topWindow]
  · intro q hq; cases q <;> simp at hq <;> simp [pairShift0Base.res,rv_simp] <;> rfl
  · intro A _ _; simp [pairShift0Base.res,rv_simp]

theorem pairTail_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc pairTailCode) (hpc : s.pc = pc) (W : Word) (sum value : Nat)
    (hw : s.getReg .x29 = W) (hs : s.getReg .x25 = BitVec.ofNat 64 sum)
    (hv : s.getReg .x14 = BitVec.ofNat 64 value) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧
      t.getReg .x29 = W >>> 14 ∧ t.getReg .x25 = BitVec.ofNat 64 (sum + value) ∧
      RegsExcept s t [.x25,.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (pairTail_run pc) hc s hpc (by simp [pairTailBase.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · rfl
  · simp [pairTailBase.res,rv_simp,hw]
  · simp [pairTailBase.res,rv_simp,hs,hv,ofNat_add_ofNat]
  · intro q hq; cases q <;> simp at hq <;> simp [pairTailBase.res,rv_simp] <;> rfl
  · intro A _ _; simp [pairTailBase.res,rv_simp]

theorem singleTail_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc singleTailCode) (hpc : s.pc = pc) (W : Word) (sum value : Nat)
    (hw : s.getReg .x29 = W) (hs : s.getReg .x25 = BitVec.ofNat 64 sum)
    (hv : s.getReg .x14 = BitVec.ofNat 64 value) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧
      t.getReg .x29 = W >>> 7 ∧ t.getReg .x25 = BitVec.ofNat 64 (sum + value) ∧
      RegsExcept s t [.x25,.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (singleTail_run pc) hc s hpc (by simp [singleTailBase.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · rfl
  · simp [singleTailBase.res,rv_simp,hw]
  · simp [singleTailBase.res,rv_simp,hs,hv,ofNat_add_ofNat]
  · intro q hq; cases q <;> simp at hq <;> simp [singleTailBase.res,rv_simp] <;> rfl
  · intro A _ _; simp [singleTailBase.res,rv_simp]

theorem singlePtr_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc singlePtrCode) (hpc : s.pc = pc) (v : Digest)
    (hw : s.getReg .x29 = topWindow v 8) (hb : s.getReg .x19 = BitVec.ofNat 64 PAIR_DATA) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧
      t.getReg .x14 = BitVec.ofNat 64 (PAIR_DATA + topRank v 8) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (singlePtr_run pc) hc s hpc (by simp [singlePtrBase.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,singlePtrBase.res,rv_simp,hw,hb,topWindow_rank v 8 (by decide),ofNat_add_ofNat]
    congr 1; omega
  · intro q hq; cases q <;> simp at hq <;> simp [singlePtrBase.res,rv_simp] <;> rfl
  · intro A _ _; simp [singlePtrBase.res,rv_simp]

theorem pairCross_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc pairCrossCode) (hpc : s.pc = pc) (v : Digest)
    (hw : s.getReg .x29 = v.extractLsb' 0 64 >>> 63) (hh : s.getReg .x17 = v.extractLsb' 64 64) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧
      t.getReg .x17 = v.extractLsb' 63 64 ∧ t.getReg .x29 = topWindow v 9 ∧
      RegsExcept s t [.x17,.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (pairCross_run pc) hc s hpc (by simp [pairCrossBase.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · rfl
  · simpa [pairCrossBase.res,rv_simp,hw,hh] using topWindow_cross v
  · simpa [pairCrossBase.res,rv_simp,hw,hh,topWindow] using topWindow_cross v
  · intro q hq; cases q <;> simp at hq <;> simp [pairCrossBase.res,rv_simp] <;> rfl
  · intro A _ _; simp [pairCrossBase.res,rv_simp]

theorem tailInit_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc tailInitCode) (hpc : s.pc = pc) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧ t.getReg .x19 = BitVec.ofNat 64 TAIL_DATA ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (tailInit_run pc) hc s hpc (by simp [tailInitBase.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro q hq; cases q <;> simp at hq <;> simp [tailInitBase.res,rv_simp] <;> rfl
  · intro A _ _; simp [tailInitBase.res,rv_simp]

/-- The read is stepped directly: byte-table addresses need not be word aligned. -/
theorem pair_lbu_spec {image : Image} (s : MachineState) (pc : Word) (inst : BitVec 32) (rd : Reg)
    (hc : CodeAt image pc [inst]) (hpc : s.pc = pc)
    (hd : decodeInstruction inst = some (.base (.LBU rd .x14 0))) (hrd : rd ≠ .x0)
    (r : Nat) (hr : r < 16384) (ha : s.getReg .x14 = BitVec.ofNat 64 (PAIR_DATA + r))
    (ht : PairTableOK s) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧ t.getReg rd = BitVec.ofNat 64 (pairLookup r) ∧
      RegsExcept s t [rd] ∧ Frame s t (fun _ => False) := by
  have hz : signExtend12 (0 : BitVec 12) = (0 : Word) := rfl
  have hlt : PAIR_DATA + r < 2 ^ 64 := by unfold PAIR_DATA; omega
  have hv : accessValid (s.getReg .x14 + signExtend12 0) 1 = true := by
    rw [ha,hz]
    simp only [add_zero,accessValid_iff,MEMORY_BYTES,toNat_ofNat_lt hlt,Nat.mod_one,and_true,true_and]
    unfold PAIR_DATA; omega
  have hs := steps_lbu hc hpc hd hv
  simp only [ha,hz,add_zero,PairTableOK.rank s ht r hr] at hs
  refine ⟨_,hs,?_,?_,?_,?_⟩
  · exact congrArg (fun p => p + 4) hpc
  · exact MachineState.getReg_setReg_eq hrd
  · intro q hq; simp only [List.mem_singleton] at hq
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hq)
  · intro A _ _; simp [MachineState.setReg,MachineState.setPC,MachineState.getMem]

end SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary

end CanonicalPortPart69

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart70

namespace SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

abbrev packedFoldRegs : List Reg := [.x19,.x24,.x25,.x29,.x14,.x17]

private theorem pairLookup_single (r : Nat) (hr : r < 128) : pairLookup r = rankLookup r := by
  simp only [pairLookup, Nat.mod_eq_of_lt hr, Nat.div_eq_of_lt hr,pairWeight,rankLookup]
  have hz : rankWeight 0 = 0 := rfl
  simp only [show 0 < 125 by decide,and_true,hz,Nat.add_zero]

private theorem pf_96164 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96164) pairInitCode := by
  have h := codeAt_from 96164 (by decide)
  have hp : pairInitCode <+: codeFrom 96164 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96167 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96167) pairPtr0Code := by
  have h := codeAt_from 96167 (by decide)
  have hp : pairPtr0Code <+: codeFrom 96167 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96169 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96169) [0x00074c83] := by
  have h := codeAt_from 96169 (by decide)
  have hp : [0x00074c83] <+: codeFrom 96169 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96170 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96170) pairShift0Code := by
  have h := codeAt_from 96170 (by decide)
  have hp : pairShift0Code <+: codeFrom 96170 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96171 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96171) pairPtrCode := by
  have h := codeAt_from 96171 (by decide)
  have hp : pairPtrCode <+: codeFrom 96171 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96173 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96173) [0x00074703] := by
  have h := codeAt_from 96173 (by decide)
  have hp : [0x00074703] <+: codeFrom 96173 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96174 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96174) pairTailCode := by
  have h := codeAt_from 96174 (by decide)
  have hp : pairTailCode <+: codeFrom 96174 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96176 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96176) pairPtrCode := by
  have h := codeAt_from 96176 (by decide)
  have hp : pairPtrCode <+: codeFrom 96176 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96178 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96178) [0x00074703] := by
  have h := codeAt_from 96178 (by decide)
  have hp : [0x00074703] <+: codeFrom 96178 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96179 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96179) pairTailCode := by
  have h := codeAt_from 96179 (by decide)
  have hp : pairTailCode <+: codeFrom 96179 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96181 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96181) pairPtrCode := by
  have h := codeAt_from 96181 (by decide)
  have hp : pairPtrCode <+: codeFrom 96181 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96183 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96183) [0x00074703] := by
  have h := codeAt_from 96183 (by decide)
  have hp : [0x00074703] <+: codeFrom 96183 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96184 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96184) pairTailCode := by
  have h := codeAt_from 96184 (by decide)
  have hp : pairTailCode <+: codeFrom 96184 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96186 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96186) singlePtrCode := by
  have h := codeAt_from 96186 (by decide)
  have hp : singlePtrCode <+: codeFrom 96186 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96188 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96188) [0x00074703] := by
  have h := codeAt_from 96188 (by decide)
  have hp : [0x00074703] <+: codeFrom 96188 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96189 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96189) singleTailCode := by
  have h := codeAt_from 96189 (by decide)
  have hp : singleTailCode <+: codeFrom 96189 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96191 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96191) pairCrossCode := by
  have h := codeAt_from 96191 (by decide)
  have hp : pairCrossCode <+: codeFrom 96191 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96194 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96194) pairPtrCode := by
  have h := codeAt_from 96194 (by decide)
  have hp : pairPtrCode <+: codeFrom 96194 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96196 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96196) [0x00074703] := by
  have h := codeAt_from 96196 (by decide)
  have hp : [0x00074703] <+: codeFrom 96196 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96197 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96197) pairTailCode := by
  have h := codeAt_from 96197 (by decide)
  have hp : pairTailCode <+: codeFrom 96197 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96199 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96199) pairPtrCode := by
  have h := codeAt_from 96199 (by decide)
  have hp : pairPtrCode <+: codeFrom 96199 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96201 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96201) [0x00074703] := by
  have h := codeAt_from 96201 (by decide)
  have hp : [0x00074703] <+: codeFrom 96201 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96202 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96202) pairTailCode := by
  have h := codeAt_from 96202 (by decide)
  have hp : pairTailCode <+: codeFrom 96202 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96204 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96204) pairPtrCode := by
  have h := codeAt_from 96204 (by decide)
  have hp : pairPtrCode <+: codeFrom 96204 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96206 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96206) [0x00074703] := by
  have h := codeAt_from 96206 (by decide)
  have hp : [0x00074703] <+: codeFrom 96206 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96207 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96207) pairTailCode := by
  have h := codeAt_from 96207 (by decide)
  have hp : pairTailCode <+: codeFrom 96207 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96209 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96209) pairPtrCode := by
  have h := codeAt_from 96209 (by decide)
  have hp : pairPtrCode <+: codeFrom 96209 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96211 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96211) [0x00074703] := by
  have h := codeAt_from 96211 (by decide)
  have hp : [0x00074703] <+: codeFrom 96211 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96212 : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96212) pairTailCode := by
  have h := codeAt_from 96212 (by decide)
  have hp : pairTailCode <+: codeFrom 96212 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

theorem pairStep_spec {image : Image} (s : MachineState) (pc : Word) (v : Digest) (q sum : Nat)
    (hc1 : CodeAt image pc pairPtrCode) (hc2 : CodeAt image (pc+4+4) [0x00074703])
    (hc3 : CodeAt image (pc+4+4+4) pairTailCode) (hpc : s.pc = pc)
    (hq : q < 7 ∨ (9 ≤ q ∧ q < 16))
    (hw : s.getReg .x29 = topWindow v q) (hs : s.getReg .x25 = BitVec.ofNat 64 sum)
    (hb : s.getReg .x19 = BitVec.ofNat 64 PAIR_DATA) (hm : s.getReg .x24 = 16383#64)
    (ht : PackedTables s) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pc+4+4+4+4+4 ∧
      t.getReg .x29 = topWindow v (q+2) ∧
      t.getReg .x25 = BitVec.ofNat 64 (sum + pairLookup (pairRank v q)) ∧
      RegsExcept s t [.x25,.x29,.x14] ∧ Frame s t (fun _ => False) := by
  obtain ⟨s1,e1,p1,a1,r1,f1⟩ := pairPtr_spec s pc hc1 hpc v q (by omega) hw hb hm
  obtain ⟨s2,e2,p2,a2,r2,f2⟩ := pair_lbu_spec s1 _ 0x00074703 .x14 hc2 p1 (by rfl) (by decide)
    _ (pairRank_lt v q) a1 (ht.frame f1).pair
  obtain ⟨s3,e3,p3,w3,a3,r3,f3⟩ := pairTail_spec s2 _ hc3 p2 _ sum _
    (by rw [r2.get (by decide),r1.get (by decide),hw])
    (by rw [r2.get (by decide),r1.get (by decide),hs]) a2
  exact ⟨s3,(e1.trans e2).trans e3,p3,w3.trans (pairWindow_shift v q (by omega)),a3,
    ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩

theorem singleStep_spec (s : MachineState) (v : Digest) (sum : Nat)
    (hpc : s.pc = pcOf 96186) (hw : s.getReg .x29 = topWindow v 8)
    (hs : s.getReg .x25 = BitVec.ofNat 64 sum)
    (hb : s.getReg .x19 = BitVec.ofNat 64 PAIR_DATA) (ht : PackedTables s) :
    ∃ t, Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s 5 5 t ∧ t.pc = pcOf 96191 ∧
      t.getReg .x29 = v.extractLsb' 0 64 >>> 63 ∧
      t.getReg .x25 = BitVec.ofNat 64 (sum + rankLookup (topRank v 8)) ∧
      RegsExcept s t [.x25,.x29,.x14] ∧ Frame s t (fun _ => False) := by
  obtain ⟨s1,e1,p1,a1,r1,f1⟩ := singlePtr_spec s _ pf_96186 hpc v hw hb
  obtain ⟨s2,e2,p2,a2,r2,f2⟩ := pair_lbu_spec s1 _ 0x00074703 .x14 pf_96188 p1 (by rfl) (by decide)
    _ (by have := topRank_lt v 8; omega) a1 (ht.frame f1).pair
  obtain ⟨s3,e3,p3,w3,a3,r3,f3⟩ := singleTail_spec s2 _ pf_96189 p2 _ sum _
    (by rw [r2.get (by decide),r1.get (by decide),hw])
    (by rw [r2.get (by decide),r1.get (by decide),hs]) a2
  rw [pairLookup_single _ (topRank_lt v 8)] at a3
  refine ⟨s3,(e1.trans e2).trans e3,p3,?_,a3,
    ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
  simpa [topWindow,← BitVec.shiftRight_add] using w3

/-- All nine actual checksum reads, including the preserved cross-word dispatch window. -/
theorem pairedFold_spec (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96164) (h16 : s.getReg .x16 = v.extractLsb' 0 64)
    (h17 : s.getReg .x17 = v.extractLsb' 64 64) (ht : PackedTables s) :
    ∃ t, Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s 50 50 t ∧ t.pc = pcOf 96214 ∧
      t.getReg .x29 = topWindow v 17 ∧ t.getReg .x25 = BitVec.ofNat 64 (compressedSum (topRank v)) ∧
      t.getReg .x17 = v.extractLsb' 63 64 ∧
      t.getReg .x19 = BitVec.ofNat 64 PAIR_DATA ∧ t.getReg .x24 = 16383#64 ∧
      RegsExcept s t packedFoldRegs ∧ Frame s t (fun _ => False) := by
  obtain ⟨u0,e0,p0,b0,m0,r0,f0⟩ := pairInit_spec s _ pf_96164 hpc
  obtain ⟨u1,e1,p1,a1,r1,f1⟩ := pairPtr0_spec u0 _ pf_96167 p0 v 0 (by decide)
    (by rw [r0.get (by decide),h16]; simp [topWindow]) b0 m0
  obtain ⟨u2,e2,p2,a2,r2,f2⟩ := pair_lbu_spec u1 _ 0x00074c83 .x25 pf_96169 p1
    (by rfl) (by decide) _ (pairRank_lt v 0) a1 ((ht.frame f0).frame f1).pair
  obtain ⟨t0,e3,p3,w0,r3,f3⟩ := pairShift0_spec u2 _ pf_96170 p2 v
    (by rw [r2.get (by decide),r1.get (by decide),r0.get (by decide),h16])
  have E0 : Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s 7 7 t0 := ((e0.trans e1).trans e2).trans e3
  have R0 : RegsExcept s t0 packedFoldRegs := (((r0.trans r1).trans r2).trans r3).mono (by decide)
  have F0 : Frame s t0 (fun _ => False) := (((f0.trans f1).trans f2).trans f3).mono (by simp)
  have S0 : t0.getReg .x25 = BitVec.ofNat 64 (pairLookup (pairRank v 0)) := by rw [r3.get (by decide),a2]
  have B0 : t0.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),b0]
  have M0 : t0.getReg .x24 = 16383#64 := by rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),m0]
  have H0 : t0.getReg .x17 = v.extractLsb' 64 64 := by rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),r0.get (by decide),h17]
  obtain ⟨t1,e1p,p1p,w1,a1,r1p,f1p⟩ := pairStep_spec t0 (pcOf 96171) v 2 _
    pf_96171 pf_96173 pf_96174 p3 (by decide) w0 S0 B0 M0 (ht.frame F0)
  have E1 : Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s 12 12 t1 := E0.trans e1p
  have R1 : RegsExcept s t1 packedFoldRegs := (R0.trans r1p).mono (by decide)
  have F1 : Frame s t1 (fun _ => False) := (F0.trans f1p).mono (by simp)
  have S1 : t1.getReg .x25 = BitVec.ofNat 64 (pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) := a1
  have B1 : t1.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r1p.get (by decide),B0]
  have M1 : t1.getReg .x24 = 16383#64 := by rw [r1p.get (by decide),M0]
  have H1 : t1.getReg .x17 = v.extractLsb' 64 64 := by rw [r1p.get (by decide),H0]
  obtain ⟨t2,e2p,p2p,w2,a2,r2p,f2p⟩ := pairStep_spec t1 (pcOf 96176) v 4 _
    pf_96176 pf_96178 pf_96179 p1p (by decide) w1 S1 B1 M1 (ht.frame F1)
  have E2 : Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s 17 17 t2 := E1.trans e2p
  have R2 : RegsExcept s t2 packedFoldRegs := (R1.trans r2p).mono (by decide)
  have F2 : Frame s t2 (fun _ => False) := (F1.trans f2p).mono (by simp)
  have S2 : t2.getReg .x25 = BitVec.ofNat 64 ((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) := a2
  have B2 : t2.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r2p.get (by decide),B1]
  have M2 : t2.getReg .x24 = 16383#64 := by rw [r2p.get (by decide),M1]
  have H2 : t2.getReg .x17 = v.extractLsb' 64 64 := by rw [r2p.get (by decide),H1]
  obtain ⟨t3,e3p,p3p,w3,a3,r3p,f3p⟩ := pairStep_spec t2 (pcOf 96181) v 6 _
    pf_96181 pf_96183 pf_96184 p2p (by decide) w2 S2 B2 M2 (ht.frame F2)
  have E3 : Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s 22 22 t3 := E2.trans e3p
  have R3 : RegsExcept s t3 packedFoldRegs := (R2.trans r3p).mono (by decide)
  have F3 : Frame s t3 (fun _ => False) := (F2.trans f3p).mono (by simp)
  have S3 : t3.getReg .x25 = BitVec.ofNat 64 (((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) := a3
  have B3 : t3.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r3p.get (by decide),B2]
  have M3 : t3.getReg .x24 = 16383#64 := by rw [r3p.get (by decide),M2]
  have H3 : t3.getReg .x17 = v.extractLsb' 64 64 := by rw [r3p.get (by decide),H2]
  obtain ⟨us,es,ps,ws,ass,rs,fs⟩ := singleStep_spec t3 v _ p3p w3 S3 B3 (ht.frame F3)
  obtain ⟨t4,ec,pc,wc,wwc,rc,fc⟩ := pairCross_spec us _ pf_96191 ps v ws
    (by rw [rs.get (by decide),H3])
  have E4 : Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s 30 30 t4 := (E3.trans es).trans ec
  have R4 : RegsExcept s t4 packedFoldRegs := ((R3.trans rs).trans rc).mono (by decide)
  have F4 : Frame s t4 (fun _ => False) := ((F3.trans fs).trans fc).mono (by simp)
  have S4 : t4.getReg .x25 = BitVec.ofNat 64 ((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) := by rw [rc.get (by decide),ass]
  have B4 : t4.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [rc.get (by decide),rs.get (by decide),B3]
  have M4 : t4.getReg .x24 = 16383#64 := by rw [rc.get (by decide),rs.get (by decide),M3]
  have H4 : t4.getReg .x17 = v.extractLsb' 63 64 := wc
  obtain ⟨t5,e5p,p5p,w5,a5,r5p,f5p⟩ := pairStep_spec t4 (pcOf 96194) v 9 _
    pf_96194 pf_96196 pf_96197 pc (by decide) wwc S4 B4 M4 (ht.frame F4)
  have E5 : Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s 35 35 t5 := E4.trans e5p
  have R5 : RegsExcept s t5 packedFoldRegs := (R4.trans r5p).mono (by decide)
  have F5 : Frame s t5 (fun _ => False) := (F4.trans f5p).mono (by simp)
  have S5 : t5.getReg .x25 = BitVec.ofNat 64 (((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) + pairLookup (pairRank v 9)) := a5
  have B5 : t5.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r5p.get (by decide),B4]
  have M5 : t5.getReg .x24 = 16383#64 := by rw [r5p.get (by decide),M4]
  have H5 : t5.getReg .x17 = v.extractLsb' 63 64 := by rw [r5p.get (by decide),H4]
  obtain ⟨t6,e6p,p6p,w6,a6,r6p,f6p⟩ := pairStep_spec t5 (pcOf 96199) v 11 _
    pf_96199 pf_96201 pf_96202 p5p (by decide) w5 S5 B5 M5 (ht.frame F5)
  have E6 : Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s 40 40 t6 := E5.trans e6p
  have R6 : RegsExcept s t6 packedFoldRegs := (R5.trans r6p).mono (by decide)
  have F6 : Frame s t6 (fun _ => False) := (F5.trans f6p).mono (by simp)
  have S6 : t6.getReg .x25 = BitVec.ofNat 64 ((((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) + pairLookup (pairRank v 9)) + pairLookup (pairRank v 11)) := a6
  have B6 : t6.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r6p.get (by decide),B5]
  have M6 : t6.getReg .x24 = 16383#64 := by rw [r6p.get (by decide),M5]
  have H6 : t6.getReg .x17 = v.extractLsb' 63 64 := by rw [r6p.get (by decide),H5]
  obtain ⟨t7,e7p,p7p,w7,a7,r7p,f7p⟩ := pairStep_spec t6 (pcOf 96204) v 13 _
    pf_96204 pf_96206 pf_96207 p6p (by decide) w6 S6 B6 M6 (ht.frame F6)
  have E7 : Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s 45 45 t7 := E6.trans e7p
  have R7 : RegsExcept s t7 packedFoldRegs := (R6.trans r7p).mono (by decide)
  have F7 : Frame s t7 (fun _ => False) := (F6.trans f7p).mono (by simp)
  have S7 : t7.getReg .x25 = BitVec.ofNat 64 (((((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) + pairLookup (pairRank v 9)) + pairLookup (pairRank v 11)) + pairLookup (pairRank v 13)) := a7
  have B7 : t7.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r7p.get (by decide),B6]
  have M7 : t7.getReg .x24 = 16383#64 := by rw [r7p.get (by decide),M6]
  have H7 : t7.getReg .x17 = v.extractLsb' 63 64 := by rw [r7p.get (by decide),H6]
  obtain ⟨t8,e8p,p8p,w8,a8,r8p,f8p⟩ := pairStep_spec t7 (pcOf 96209) v 15 _
    pf_96209 pf_96211 pf_96212 p7p (by decide) w7 S7 B7 M7 (ht.frame F7)
  have E8 : Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s 50 50 t8 := E7.trans e8p
  have R8 : RegsExcept s t8 packedFoldRegs := (R7.trans r8p).mono (by decide)
  have F8 : Frame s t8 (fun _ => False) := (F7.trans f8p).mono (by simp)
  have S8 : t8.getReg .x25 = BitVec.ofNat 64 ((((((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) + pairLookup (pairRank v 9)) + pairLookup (pairRank v 11)) + pairLookup (pairRank v 13)) + pairLookup (pairRank v 15)) := a8
  have B8 : t8.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r8p.get (by decide),B7]
  have M8 : t8.getReg .x24 = 16383#64 := by rw [r8p.get (by decide),M7]
  have H8 : t8.getReg .x17 = v.extractLsb' 63 64 := by rw [r8p.get (by decide),H7]
  refine ⟨t8,E8,p8p,w8,?_,H8,B8,M8,R8,F8⟩
  simpa only [pairLookup_pairRank,Nat.reduceAdd,compressedSum] using S8

end SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary

end CanonicalPortPart70

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart71

namespace SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 100000
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
def ptrCode : List (BitVec 32) := [0x013e8733]
sym_block ptrBase := symRun { noAlias := true } ptrCode (pcOf 96215) 200

theorem ptr_spec {image : Image} (s : MachineState)
    (hc : CodeAt image (pcOf 96215) ptrCode) (hpc : s.pc = pcOf 96215)
    (r : Nat) (h29 : s.getReg .x29 = BitVec.ofNat 64 r)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 TAIL_DATA) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 96216 ∧
      t.getReg .x14 = BitVec.ofNat 64 (TAIL_DATA + r) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound ptrBase hc s hpc (by simp [ptrBase.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [ptrBase.res, rv_simp, h29, h19, ofNat_add_ofNat, Nat.add_comm]
  · intro q hq; cases q <;> simp at hq <;> simp [ptrBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [ptrBase.res, rv_simp]

theorem tail_lbu {image : Image} (s : MachineState)
    (hc : CodeAt image (pcOf 96216) [0x00074703]) (hpc : s.pc = pcOf 96216)
    (r : Nat) (hr : r < 64) (h14 : s.getReg .x14 = BitVec.ofNat 64 (TAIL_DATA + r))
    (ht : TailTableOK s) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 96217 ∧
      t.getReg .x14 = BitVec.ofNat 64 (126 - tailSum r) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hz : signExtend12 (0 : BitVec 12) = (0 : Word) := rfl
  have hlt : TAIL_DATA + r < 2 ^ 64 := by unfold TAIL_DATA; omega
  have hv : accessValid (s.getReg .x14 + signExtend12 0) 1 = true := by
    rw [h14, hz]
    simp only [add_zero,accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt hlt, Nat.mod_one, and_true, true_and]
    unfold TAIL_DATA; omega
  have hd : decodeInstruction (0x00074703 : BitVec 32) = some (.base (.LBU .x14 .x14 0)) := rfl
  have hs := steps_lbu hc hpc hd hv
  simp only [h14,hz,add_zero,TailTableOK.rank s ht r hr] at hs
  refine ⟨_, hs, ?_, ?_, ?_, ?_⟩
  · exact congrArg (fun p => p + 4) hpc
  · rfl
  · intro q hq; simp only [List.mem_singleton] at hq
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hq)
  · intro A _ _; simp [MachineState.setReg, MachineState.setPC, MachineState.getMem]

/-- Complementing the tail table permits a direct comparison and skips two additions on acceptance. -/
def sumCode : List (BitVec 32) := [0x00ec8663]
sym_block sumBase := symRun { noAlias := true } sumCode (pcOf 96217) 200

def tailRejectJumpCode : List (BitVec 32) := [0x0300006f]
sym_block tailRejectJumpBase := symRun { noAlias := true } tailRejectJumpCode (pcOf 96218) 200

theorem sum_spec {image : Image} (s : MachineState)
    (hc : CodeAt image (pcOf 96217) sumCode) (hpc : s.pc = pcOf 96217)
    (sum value : Nat) (hsum : sum ≤ 4335) (hvalue : value ≤ 9)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 sum)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 (126 - value)) :
    ∃ t, Steps image s 1 1 t ∧
      t.pc = (if sum + value = 126 then pcOf 96220 else pcOf 96218) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound sumBase hc s hpc (by simp [sumBase.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, sumBase.res, E.eval, CmpOp.eval, BinOp.eval,
      h25, h14, BitVec.toNat_ofNat, Nat.reduceMod, beq_iff_eq]
    have he : (BitVec.ofNat 64 sum = BitVec.ofNat 64 (126-value)) ↔ sum + value = 126 := by
      rw [ofNat_inj (by omega) (by omega)]
      omega
    simp only [he]
  · intro q hq; cases q <;> simp [sumBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [sumBase.res, rv_simp]

theorem tailRejectJump_spec {image : Image} (s : MachineState)
    (hc : CodeAt image (pcOf 96218) tailRejectJumpCode) (hpc : s.pc = pcOf 96218) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 96230 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound tailRejectJumpBase hc s hpc (by simp [tailRejectJumpBase.res, rv_simp]), ?_, ?_, ?_⟩
  · rfl
  · intro q hq; cases q <;> simp [tailRejectJumpBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [tailRejectJumpBase.res, rv_simp]

/-- The tail comparison takes three instructions on acceptance and four on rejection. -/
theorem tail_compare_spec {image : Image} (s : MachineState) (v : Digest) (sum : Nat)
    (hptr : CodeAt image (pcOf 96215) ptrCode)
    (hload : CodeAt image (pcOf 96216) [0x00074703])
    (hsumcode : CodeAt image (pcOf 96217) sumCode)
    (hreject : CodeAt image (pcOf 96218) tailRejectJumpCode)
    (hsum : sum ≤ 4335) (hv : v.toNat < 2 ^ 125)
    (hpc : s.pc = pcOf 96215) (h29 : s.getReg .x29 = topWindow v 17)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 sum)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 TAIL_DATA) (ht : PackedTables s) :
    ∃ t, Steps image s (if sum + tailWeight v = 126 then 3 else 4)
      (if sum + tailWeight v = 126 then 3 else 4) t ∧
      t.pc = (if sum + tailWeight v = 126 then pcOf 96220 else pcOf 96230) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hr : v.toNat / 2 ^ 119 < 64 := by omega
  rw [topWindow_tail v hv] at h29
  obtain ⟨s1,e1,p1,a1,r1,f1⟩ := ptr_spec s hptr hpc _ h29 h19
  obtain ⟨s2,e2,p2,a2,r2,f2⟩ := tail_lbu s1 hload p1 _ hr a1 (ht.frame f1).tail
  obtain ⟨s3,e3,p3,r3,f3⟩ := sum_spec s2 hsumcode p2 sum _ hsum (tailSum_le _ hr)
    (by rw [r2.get (by decide), r1.get (by decide), h25]) a2
  rw [tailSum_eq v hv] at p3
  by_cases ha : sum + tailWeight v = 126
  · simp only [if_pos ha] at p3 ⊢
    exact ⟨s3,(e1.trans e2).trans e3,p3,
      ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
  · simp only [if_neg ha] at p3 ⊢
    obtain ⟨s4,e4,p4,r4,f4⟩ := tailRejectJump_spec s3 hreject p3
    exact ⟨s4,((e1.trans e2).trans e3).trans e4,p4,
      (((r1.trans r2).trans r3).trans r4).mono (by decide),
      (((f1.trans f2).trans f3).trans f4).mono (by simp)⟩

private theorem tail_init_at : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96214) tailInitCode := by
  have h := codeAt_from 96214 (by decide)
  have hp : tailInitCode <+: codeFrom 96214 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem tail_ptr_at : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96215) ptrCode := by
  have h := codeAt_from 96215 (by decide)
  have hp : ptrCode <+: codeFrom 96215 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem tail_load_at : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96216) [0x00074703] := by
  have h := codeAt_from 96216 (by decide)
  have hp : [0x00074703] <+: codeFrom 96216 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem tail_sum_at : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96217) sumCode := by
  have h := codeAt_from 96217 (by decide)
  have hp : sumCode <+: codeFrom 96217 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem tail_reject_at : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96218) tailRejectJumpCode := by
  have h := codeAt_from 96218 (by decide)
  have hp : tailRejectJumpCode <+: codeFrom 96218 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

/-- The complete tail takes four instructions on acceptance, five on rejection. -/
theorem tail_spec (s : MachineState) (v : Digest) (sum : Nat) (hsum : sum ≤ 4335)
    (hv : v.toNat < 2 ^ 125) (hpc : s.pc = pcOf 96214)
    (h29 : s.getReg .x29 = topWindow v 17) (h25 : s.getReg .x25 = BitVec.ofNat 64 sum)
    (ht : PackedTables s) :
    ∃ t, Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s (if sum + tailWeight v = 126 then 4 else 5)
      (if sum + tailWeight v = 126 then 4 else 5) t ∧
      t.pc = (if sum + tailWeight v = 126 then pcOf 96220 else pcOf 96230) ∧
      RegsExcept s t [.x14,.x19] ∧ Frame s t (fun _ => False) := by
  obtain ⟨s1,e1,p1,b1,r1,f1⟩ := tailInit_spec s _ tail_init_at hpc
  obtain ⟨s2,e2,p2,r2,f2⟩ := tail_compare_spec s1 v sum tail_ptr_at tail_load_at tail_sum_at tail_reject_at hsum hv p1
    (by rw [r1.get (by decide),h29]) (by rw [r1.get (by decide),h25]) b1 (ht.frame f1)
  refine ⟨s2,?_,p2,(r1.trans r2).mono (by decide),(f1.trans f2).mono (by simp)⟩
  by_cases ha : sum + tailWeight v = 126
  · simpa only [if_pos ha] using e1.trans e2
  · simpa only [if_neg ha] using e1.trans e2
end SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary

end CanonicalPortPart71

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart72

namespace SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 100000
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
def headCode : List (BitVec 32) := [0x14003803, 0x14803883, 0x03d8d713, 0x10071663]
sym_block headBase := symRun { noAlias := true } headCode (pcOf 96160) 200

theorem head_at : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96160) headCode := by
  have h := codeAt_from 96160 (by decide)
  have hp : headCode <+: codeFrom 96160 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩

theorem head_spec (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96160) (hv : DigAt s 320 v) :
    ∃ t, Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s 4 4 t ∧
      t.pc = (if v.toNat < 2 ^ 125 then pcOf 96164 else pcOf 96230) ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧ t.getReg .x17 = v.extractLsb' 64 64 ∧
      RegsExcept s t [.x16,.x17,.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound headBase head_at s hpc (by simp [headBase.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, headBase.res, E.eval, CmpOp.eval, BinOp.eval,
      show BitVec.ofNat 64 (320 + 8) = 328#64 from rfl, hv.2,
      BitVec.toNat_ofNat, Nat.reduceMod, bne_iff_ne, ne_eq,
      ext64_shr_eq_zero v 61 (by decide), show (64 + 61 : Nat) = 125 from rfl]
    split_ifs <;> first | rfl | omega
  · simpa only [Result.toState_getReg, headBase.res, rv_simp] using hv.1
  · simpa only [Result.toState_getReg, headBase.res, rv_simp] using hv.2
  · intro r hr; cases r <;> simp at hr <;> simp [headBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [headBase.res, rv_simp]

theorem compressedSum_le (v : Digest) : compressedSum (topRank v) ≤ 4335 := by
  have h0 := pairWeight_le (topRank v 0) (topRank v 1)
  have h1 := pairWeight_le (topRank v 2) (topRank v 3)
  have h2 := pairWeight_le (topRank v 4) (topRank v 5)
  have h3 := pairWeight_le (topRank v 6) (topRank v 7)
  have h4 := rankLookup_le (topRank v 8)
  have h5 := pairWeight_le (topRank v 9) (topRank v 10)
  have h6 := pairWeight_le (topRank v 11) (topRank v 12)
  have h7 := pairWeight_le (topRank v 13) (topRank v 14)
  have h8 := pairWeight_le (topRank v 15) (topRank v 16)
  unfold compressedSum; omega

/-- The actual verifier validates exactly the original decoder in fifty-eight steps. -/
theorem decode_ok (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96160) (hv : DigAt s 320 v) (ht : PackedTables s)
    (hvalid : T3.decode 0 v = some (topDigits v)) :
    ∃ t, Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s 58 58 t ∧ t.pc = pcOf 96220 ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧ t.getReg .x17 = v.extractLsb' 63 64 ∧
      t.getReg .x29 = topWindow v 17 ∧
      RegsExcept s t [.x16,.x17,.x14,.x25,.x29,.x19,.x24] ∧ Frame s t (fun _ => False) := by
  have hh : v.toNat < 2 ^ 125 ∧ pairedLookupSum v = 126 := by
    rw [decode_top_paired] at hvalid
    split_ifs at hvalid with hh
    exact hh
  obtain ⟨t1,e1,p1,a1,b1,r1,f1⟩ := head_spec s v hpc hv
  rw [if_pos hh.1] at p1
  obtain ⟨t2,e2,p2,w2,a2,h172,b192,b242,r2,f2⟩ := pairedFold_spec t1 v p1 a1 b1 (ht.frame f1)
  have hb : compressedSum (topRank v) + tailWeight v = 126 := hh.2
  obtain ⟨t3,e3,p3,r3,f3⟩ := tail_spec t2 v _ (compressedSum_le v) hh.1 p2 w2 a2 ((ht.frame f1).frame f2)
  rw [if_pos hb] at p3 e3
  refine ⟨t3,(e1.trans e2).trans e3,p3,?_,?_,?_,
    ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
  · rw [r3.get (by decide),r2.get (by decide),a1]
  · rw [r3.get (by decide),h172]
  · rw [r3.get (by decide),w2]

end SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary

end CanonicalPortPart72

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart73

namespace SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

/-- Every rejected source encoding takes the actual verifier to its rejection jump. -/
theorem decode_reject (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96160) (hv : DigAt s 320 v) (ht : PackedTables s)
    (hbad : T3.decode 0 v = none) :
    ∃ k t, Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s k k t ∧ k ≤ 60 ∧ t.pc = pcOf 96230 ∧
      RegsExcept s t [.x16,.x17,.x14,.x25,.x29,.x19,.x24] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, e1, p1, a1, b1, r1, f1⟩ := head_spec s v hpc hv
  by_cases hr : v.toNat < 2 ^ 125
  · rw [if_pos hr] at p1
    obtain ⟨t2,e2,p2,w2,a2,h172,b192,b242,r2,f2⟩ := pairedFold_spec t1 v p1 a1 b1 (ht.frame f1)
    have hn : pairedLookupSum v ≠ 126 := by
      intro he
      rw [decode_top_paired,if_pos ⟨hr,he⟩] at hbad
      contradiction
    have hb : compressedSum (topRank v) + tailWeight v ≠ 126 := hn
    obtain ⟨t3,e3,p3,r3,f3⟩ := tail_spec t2 v _ (compressedSum_le v) hr p2 w2 a2 ((ht.frame f1).frame f2)
    rw [if_neg hb] at p3 e3
    exact ⟨59,t3,(e1.trans e2).trans e3,by decide,p3,
      ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
  · rw [if_neg hr] at p1
    exact ⟨4, t1, e1, by decide, p1, r1.mono (by decide), f1⟩

end SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary

end CanonicalPortPart73

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart74
namespace SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 600000
def rejectJumpCode : List (BitVec 32) := [0xbfda206f]
sym_block rejectJumpBase := symRun { noAlias := true } rejectJumpCode (pcOf 96230) 20

theorem rejectJump_at : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96230) rejectJumpCode := by
  have h := codeAt_from 96230 (by decide)
  have hp : rejectJumpCode <+: codeFrom 96230 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
def rejectExitCode : List (BitVec 32) := [0x00100293, 0x00100513]
sym_block rejectExitBase := symRun { noAlias := true } rejectExitCode (pcOf 741) 20

theorem rejectExit_at : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 741) rejectExitCode := by
  have h := codeAt_from 741 (by decide)
  have hp : rejectExitCode <+: codeFrom 741 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩

theorem reject_halt (s : MachineState) (hpc : s.pc = pcOf 96230) :
    ∃ t, Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s 3 3 t ∧ fetch SigGolfCandidate.T3M.CanonicalPort.Verify.image t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧ t.getReg .x10 = 1 := by
  have e1 := symRun_sound rejectJumpBase rejectJump_at s hpc (by simp [rejectJumpBase.res, rv_simp])
  have p1 : (rejectJumpBase.res.toState s).pc = pcOf 741 := by simp [rejectJumpBase.res, rv_simp, pcOf]
  have e2 := symRun_sound rejectExitBase rejectExit_at (rejectJumpBase.res.toState s) p1
    (by simp [rejectExitBase.res, rv_simp])
  refine ⟨_, e1.trans e2, ?_, ?_, ?_⟩
  · have h : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 743) [0x00000073] := by
      have h := codeAt_from 743 (by decide)
      have hp : [0x00000073] <+: codeFrom 743 := by decide +kernel
      exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
    exact h.fetch _ (by simp [rejectExitBase.res, rv_simp, pcOf])
  · simp [rejectExitBase.res, rv_simp]
  · simp [rejectExitBase.res, rv_simp]
end SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary

end CanonicalPortPart74

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart75

namespace SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 100000
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
def prologueCode : List (BitVec 32) := [0x000049b7, 0xd9898993, 0xd4098b13, 0x00020c37, 0xc00c0c13, 0x000ae7b7, 0x00a81713, 0x01877733, 0x00f70733, 0x9a070067]
sym_block prologueBase := symRun { noAlias := true } prologueCode (pcOf 96220) 200

theorem prologue_at : CodeAt SigGolfCandidate.T3M.CanonicalPort.Verify.image (pcOf 96220) prologueCode := by
  have h := codeAt_from 96220 (by decide)
  have hp : prologueCode <+: codeFrom 96220 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩

def prologueTarget (v : Digest) : Word :=
  (((v.extractLsb' 0 64 <<< (10 : Word)) &&& 130048#64) + pcOf 176744) &&& ~~~1#64

theorem prologue_spec (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96220)
    (h16 : s.getReg .x16 = v.extractLsb' 0 64) (h17 : s.getReg .x17 = v.extractLsb' 63 64) :
    ∃ t, Steps SigGolfCandidate.T3M.CanonicalPort.Verify.image s 10 10 t ∧ t.pc = prologueTarget v ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧
      t.getReg .x17 = v.extractLsb' 63 64 ∧
      t.getReg .x22 = 15064#64 ∧ t.getReg .x19 = 15768#64 ∧ t.getReg .x24 = 130048#64 ∧
      t.getReg .x15 = 712704#64 ∧
      RegsExcept s t [.x3,.x17,.x22,.x19,.x24,.x15,.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound prologueBase prologue_at s hpc (by simp [prologueBase.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, prologueBase.res, rv_simp, h16, prologueTarget, pcOf]
    rfl
  · simpa [prologueBase.res, rv_simp] using h16
  · simp [prologueBase.res, rv_simp, h16, h17]
  · simp [prologueBase.res, rv_simp]
  · simp [prologueBase.res, rv_simp]
  · simp [prologueBase.res, rv_simp]
  · simp [prologueBase.res, rv_simp, pcOf]
  · intro r hr; cases r <;> simp at hr <;> simp [prologueBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [prologueBase.res, rv_simp]

end SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary

end CanonicalPortPart75

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart76

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

/-- Registers changed by the two jumps, strong decoder, and top-chain dispatch prologue. -/
def topEntryRegs : List Reg := [.x1,.x3,.x16,.x17,.x14,.x25,.x29,.x19,.x22,.x24,.x15]

/-- Exact transition interface. `u` is the state immediately after the encoding HASH. -/
structure TopEntry (u : MachineState) (v : Digest) (p : Nat) (s : MachineState) : Prop where
  pc : s.pc = pcOf (176744 + 256 * (v.toNat % 128))
  ra : s.getReg .x1 = pcOf (p + 69)
  lo : s.getReg .x16 = v.extractLsb' 0 64
  hi : s.getReg .x17 = (v.extractLsb' 64 64 <<< (1 : Word)) ||| (v.extractLsb' 0 64 >>> (63 : Word))
  tail : s.getReg .x29 = Search.topWindow v 17
  s6 : s.getReg .x22 = 15064#64
  s3 : s.getReg .x19 = 15768#64
  mask : s.getReg .x24 = 130048#64
  table : s.getReg .x15 = 712704#64
  regs : RegsExcept u s topEntryRegs
  frame : Frame u s (fun _ => False)

/-- Both direct jumps from a top transition copy to the shared decoder. -/
theorem topCall_step (c : Nat) (hc : c < nCopy 0) (u : MachineState)
    (hpc : u.pc = pcOf (trPc 0 c + 17)) (hk : KnownOK (bK 0) u) :
    ∃ s, Steps image u 2 2 s ∧ s.pc = pcOf 96160 ∧ s.getReg .x1 = pcOf (trPc 0 c + 69) ∧
      RegsExcept u s [.x1] ∧ Frame u s (fun _ => False) := by
  have hcc := (copy_parts 0 (trPc 0 c) (copyCheck_at 0 c (by decide) hc)).2.2.1 rfl
  obtain ⟨s, hs⟩ := spec_run hcc u hpc (by simp [KnownOK]) (by simp [specTopCall]) (by simp)
  refine ⟨s, hs.steps, hs.pc rfl, ?_, ?_, ?_⟩
  · exact hs.regs (.x1, kw (0x1000 + 4 * (trPc 0 c + 69))) (by simp [specTopCall])
  · intro r hr
    cases r
    case x0 => simp [MachineState.getReg]
    case x1 => simp at hr
    all_goals exact hs.keep _ (by simp [keepTopCall])
  · intro A hA _
    rw [hs.mem]
    rfl

/-- Every failed mixed-radix decode reaches HALT(1), with at most 65 instructions. -/
theorem topTransition_reject (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : EncPre w pk index 0 c t) (a : BitVec 256)
    (hbad : T3.decode 0 (a.extractLsb' 0 128) = none) :
    ∃ k s, Steps image (writeHash t a) k k s ∧ k ≤ 65 ∧
      fetch image s = some (.base .ECALL) ∧ s.getReg .x5 = 1 ∧ s.getReg .x10 = 1 := by
  have h12 : t.getReg .x12 = 320#64 := ht.glob.1 (_, _) (by simp [bK])
  have hk : KnownOK (bK 0) (writeHash t a) := fun p hp => by rw [writeHash_getReg]; exact ht.glob.1 p hp
  have hpc : (writeHash t a).pc = pcOf (trPc 0 c + 17) := by
    rw [writeHash_pc, ht.pc]
    change pcOf (trPc 0 c + 16) + 4 = pcOf (trPc 0 c + 17)
    simpa only [Nat.add_assoc] using pcOf_add4 (trPc 0 c + 16)
  obtain ⟨s, e, ps, ra, rs, fs⟩ := topCall_step c hc _ hpc hk
  have hglob := Glob_writeHash ht.glob a 320 h12 (by decide)
  have hv := (DigAt.writeHash_lo t a 320 h12 (by decide)).frame fs (by decide) (by simp) (by simp)
  have hd := hglob.2.2.2.2.2.packed.frame fs
  obtain ⟨k, r, er, hk, pr, rr, fr⟩ := SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary.decode_reject s _ ps hv hd hbad
  obtain ⟨z, ez, hz, h5, h10⟩ := SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary.reject_halt r pr
  refine ⟨2 + k + 3, z, (e.trans er).trans ez, by omega, hz, h5, h10⟩

/-- Exact 70-instruction top transition from the HASH answer to the first mixed-radix chain entry. -/
theorem topTransition_ok (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : EncPre w pk index 0 c t) (a : BitVec 256)
    (hgood : T3.decode 0 (a.extractLsb' 0 128) = some (Search.topDigits (a.extractLsb' 0 128))) :
    ∃ s, Steps image (writeHash t a) 70 70 s ∧
      TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s := by
  have h12 : t.getReg .x12 = 320#64 := ht.glob.1 (_, _) (by simp [bK])
  have hk : KnownOK (bK 0) (writeHash t a) := fun p hp => by rw [writeHash_getReg]; exact ht.glob.1 p hp
  have hpc : (writeHash t a).pc = pcOf (trPc 0 c + 17) := by
    rw [writeHash_pc, ht.pc]
    change pcOf (trPc 0 c + 16) + 4 = pcOf (trPc 0 c + 17)
    simpa only [Nat.add_assoc] using pcOf_add4 (trPc 0 c + 16)
  obtain ⟨s, e, ps, ra, rs, fs⟩ := topCall_step c hc _ hpc hk
  have hglob := Glob_writeHash ht.glob a 320 h12 (by decide)
  have hv := (DigAt.writeHash_lo t a 320 h12 (by decide)).frame fs (by decide) (by simp) (by simp)
  have hd := hglob.2.2.2.2.2.packed.frame fs
  obtain ⟨r, er, pr, h16, h17, h29, rr, fr⟩ := SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary.decode_ok s _ ps hv hd hgood
  obtain ⟨z, ez, pz, lo, hi, s6, s3, mask, tab, rz, fz⟩ := SigGolfCandidate.T3M.CanonicalPort.Verify.Nonbinary.prologue_spec r _ pr h16 h17
  refine ⟨z, (e.trans er).trans ez, ⟨?_, ?_, lo, ?_, ?_, s6, s3, mask, tab, ?_, ?_⟩⟩
  · rw [pz]
    exact Nonbinary.prologue_target _
  · rw [rz.get (by decide), rr.get (by decide), ra]
  · rw [hi]; exact (Search.topWindow_cross _).symm
  · rw [rz.get (by decide), h29]
  · exact ((rs.trans rr).trans rz).mono (by decide)
  · exact ((fs.trans fr).trans fz).mono (by simp)

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart76

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart77

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest route coreDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

/-- The actual mixed-radix top chain context after an encoding answer. -/
def nctxOf (w : WBytes) (index : Nat) (v : Digest) (p : Nat) : NCtx :=
  ⟨w, (route index 0).2, (route index 0).1, 15768, coreDigit 0 v, p + 69⟩

theorem nctx_ok (w : WBytes) (index : Nat) (v : Digest) (c : Nat) (hidx : index < 2 ^ 31) :
    (nctxOf w index v (trPc 0 c)).ok := by
  have hp := trPc_lt 0 c
  exact ⟨tree_lt index 0 hidx, leaf_lt32 index 0, by norm_num [nctxOf], by norm_num [nctxOf], by norm_num [nctxOf], by dsimp [nctxOf]; omega⟩

theorem nctx_known (w : WBytes) (pk : Digest) (index c : Nat) (t s : MachineState) (a : BitVec 256)
    (ht : EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s) :
    KnownOK (nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)).known s := by
  intro p hp
  simp only [NCtx.known, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact he.s3
  all_goals try exact he.ra
  all_goals rw [he.regs.get (by simp [topEntryRegs]), writeHash_getReg]
  all_goals try exact ht.tp 0 rfl
  all_goals exact ht.glob.1 _ (by simp [bK, layK, baseK, nctxOf, NCtx.w1, hw])

theorem topEntry_orig (w : WBytes) (pk : Digest) (index c : Nat) (t s : MachineState) (a : BitVec 256)
    (ht : EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s) :
    SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd 0) s := by
  have h12 : t.getReg .x12 = 320#64 := ht.glob.1 (_, _) (by simp [bK])
  have ho := Orig_writeHash ht.orig a 320 h12 (by norm_num)
  have hu : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd 0) (writeHash t a) :=
    ho.mono (fun o h => ⟨h, Or.inr (by unfold WIT; omega)⟩)
  exact hu.frame (fun j hj hp => he.frame.get (by unfold WIT WX at *; omega) (by simp))

theorem nctx_orig (w : WBytes) (index : Nat) (v : Digest) (p : Nat) (s : MachineState)
    (ho : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd 0) s) (hD : DataOK s) :
    (nctxOf w index v p).Orig0 s := by
  refine ⟨fun i hi k hk => ?_, hD⟩
  clear hD
  apply origW_of ho _
  all_goals simp only [NCtx.blk, nctxOf]
  all_goals norm_num [WIT, WX, layerEnd] at *
  all_goals omega

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart77

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart78

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest route)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def topChainRegs : List Reg := [.x10,.x12,.x25,.x3,.x14,.x15]
def topChainWrites (A : Nat) : Prop := (512 ≤ A ∧ A < 1488) ∨ (14104 ≤ A ∧ A < 17576)

/-- The global chain fold's final register/memory interface is exactly the top leaf block's input. -/
theorem topLeafReady_of (w : WBytes) (pk : Digest) (index c : Nat) (t s0 s : MachineState)
    (a : BitVec 256) (ends : List Digest) (ht : EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s0)
    (hp : s.pc = pcOf (trPc 0 c + 69))
    (hr : RegsExcept s0 s topChainRegs) (hf : Frame s0 s topChainWrites)
    (hlen : ends.length = 54) (hend : ∀j<54, DigAt s (slotT j) (ends.getD j 0)) :
    TopLeafReady w pk index c ends s := by
  have hk : KnownOK (leafK 0) s := by
    intro p hp
    simp [leafK,baseK] at hp
    rcases hp with rfl | rfl | rfl
    all_goals rw [hr.get (by simp [topChainRegs]), he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    all_goals exact ht.glob.1 _ (by simp [bK,layK,baseK,hw])
  have h12 : t.getReg .x12 = 320#64 := ht.glob.1 (_,_) (by simp [bK])
  have hg := Glob_writeHash ht.glob a 320 h12 (by decide)
  have hfr : Frame (writeHash t a) s topChainWrites :=
    (he.frame.trans hf).mono (by intro A h; simpa using h)
  have hglob : Glob (leafK 0) w pk s := glob_frame hg hfr (by
    intro A h
    unfold topChainWrites at h
    rcases h with h | h <;> omega) hk
  refine ⟨hp,hglob,?_,?_,?_,?_,hlen,hend,?_⟩
  · intro p hp
    simp [lfKeepK] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [hr.get (by simp [topChainRegs])]
    all_goals try exact he.s6
    all_goals rw [he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    all_goals exact ht.glob.1 _ (by simp [bK,layK,baseK])
  · rw [hr.get (by simp [topChainRegs]),he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    exact ht.s7 0 rfl
  · rw [hr.get (by simp [topChainRegs]),he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    exact ht.t5 0 rfl
  · rw [hr.get (by simp [topChainRegs]),he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    exact ht.tp 0 rfl
  · have ho := topEntry_orig w pk index c t s0 a ht he
    apply (ho.mono (fun o h => ⟨h.1, by norm_num [layerBase,T3.height,layerEnd] at *;omega⟩)).frame
    intro j hj hp
    exact hf.get (by unfold WIT WX at *;omega) (by
      norm_num [layerBase,T3.height] at hp
      unfold topChainWrites WIT
      omega)

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart78

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart79

/-! Shared layer interfaces and costs, together with correctness of the unchanged lower layers.
The mixed-radix top transition and chain composition are assembled in `LayerGood`. -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 width maxDigit shortHash leafHash)

/-! ## The layer as a program -/

/-- Core's chains of layer `lay` with the witness pads and values (`layerP`'s `mapM`). -/
def chainsP (w : WBytes) (lay : Layer) (tree leaf : Nat) (digits : List Nat) : T3.M (List Digest) :=
  (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wvalue w lay i.val)

/-- `layerP`'s Merkle path from the leaf value (V3's part). -/
def merkleP (w : WBytes) (index : Nat) (lay : Layer) (value : Digest) : T3.M Digest :=
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := wpath w lay (route index lay).1 j.val
    let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 3 lay.val (route index lay).2 (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1))
      pair.1 (wmerklePad w lay j.val) pair.2) value

theorem layerP_eq (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerP w index lay digits = chainsP w lay (route index lay).2 (route index lay).1 digits >>= fun ends =>
      leafHash lay (route index lay).2 (route index lay).1 ends >>= merkleP w index lay := by
  unfold layerP chainsP merkleP
  generalize route index lay = p
  obtain ⟨leaf, tree⟩ := p
  rfl

/-- **One layer of `layersP` up to the chain ends**, continued by `R`. -/
def layerHead {β : Type} (w : WBytes) (index : Nat) (lay : Layer) (M : Digest)
    (R : List Digest → T3.M (Option β)) : T3.M (Option β) :=
  if (wctr w lay).toNat ≥ counterLimit then pure none else
  shortHash (encodingInput lay (route index lay).2 (route index lay).1 M (wctr w lay)) >>= fun answer =>
    match decode lay answer with
    | none => pure none
    | some digits => chainsP w lay (route index lay).2 (route index lay).1 digits >>= R

/-- **W's layer loop, one step**: layer `n` is `layerHead` continued by the leaf pk, the Merkle path and the
layers below. -/
theorem layersP_succ (w : WBytes) (index n : Nat) (M : Digest) :
    layersP w index (n + 1) M = layerHead w index (Fin.ofNat 4 n) M (fun ends =>
      leafHash (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 ends >>=
        merkleP w index (Fin.ofNat 4 n) >>= layersP w index n) := by
  rw [layersP]
  unfold layerHead
  split_ifs with h
  · rfl
  · simp only [layerP_eq, bind_assoc]
    generalize hr : route index (Fin.ofNat 4 n) = p
    obtain ⟨leaf, tree⟩ := p
    simp only
    congr 1; funext answer
    cases decode (Fin.ofNat 4 n) answer <;> rfl

/-! ## Costs -/

/-- Steps / cycles of decode and entry dispatch (lower30 /32, top118-step conservative fuel /70 cycles). -/
def stB (lay : Nat) : Nat := if lay = 0 then 118 else 29
def cyB (lay : Nat) : Nat := if lay = 0 then 70 else 32
/-- The chain phase's accepting cycles without maximal digits: lower `2993 − 9 target`, top `1129` after the mandatory eleven-cycle terminal-store credit. -/
def chainCost0 (lay : Nat) : Nat := if lay = 0 then 1129 else 2993 - 9 * tgtL lay
/-- The chain phase's steps on every path. -/
def chainFuel (lay : Nat) : Nat := if lay = 0 then 2321 else 1720

/-- **The cycles of one layer from `LayerIn` to `LeafOut`** with the max-digit savings `Z`: A (`stepsA`), the
encoding HASH (8), B, the leaf-pk block, the chains `chainCost0 lay − Z`. -/
def layerCost (lay Z : Nat) : Nat := stepsA lay + 8 + cyB lay + lfSteps lay + chainCost0 lay - Z

/-- The steps of one layer on every path. -/
def layerFuel (lay : Nat) : Nat := stepsA lay + 1 + stB lay + chainFuel lay + lfSteps lay

theorem layerCost_vals :
    layerCost 3 0 = 1317 ∧ layerCost 2 0 = 1304 ∧ layerCost 1 0 = 1304 ∧ layerCost 0 0 = 1236 := by decide

theorem layerFuel_vals :
    layerFuel 3 = 1780 ∧ layerFuel 2 = 1776 ∧ layerFuel 1 = 1776 ∧ layerFuel 0 = 2469 := by decide

/-! ## Decode facts -/

theorem ckOf_lt (lay : Layer) (hlay : lay ≠ 0) (a : BitVec 256) (ds : List Nat)
    (hds : decode lay (a.extractLsb' 0 128) = some ds) : ckOf lay a < 8 := by
  rw [decode_lower lay hlay] at hds
  split_ifs at hds with h1 h2
  unfold ckOf; rw [tgtL_eq]; exact h2

theorem decode_top_sum (value : Digest) (ds : List Nat) (h : decode 0 value = some ds) :
    ds = dataDigits 0 value ∧ (dataDigits 0 value).sum = 126 := by
  rw [Search.decode_top] at h
  split_ifs at h with hp
  · exact ⟨(Option.some.inj h).symm, hp.2.2⟩

theorem s6v_chainBlock (lay : Layer) (h : lay ≠ 0) : s6v lay.val = 0x800 + chainBlock lay 42 + 1024 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide

theorem chainCount_top : chainCount (0 : Layer) = 54 := by decide

/-! ## The exact accepting cost -/

/-- **The accepting cost of a lower layer is `layerCost lay Z`**: on an accepted encoding (`decode = some ds`) the
run from `LayerIn` to `LeafOut` — A (`stepsA`), the encoding HASH (8), B (32), the chain phase (`lowCost`), the
leaf-pk block (11) — costs `layerCost lay Z` cycles with `Z = zSum 0 43` (the max-digit savings). -/
theorem layerCost_low (w : WBytes) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (a : BitVec 256) (p : Nat)
    (ds : List Nat) (hds : decode lay (a.extractLsb' 0 128) = some ds) :
    stepsA lay.val + 8 + 32 + (lctxOf w index lay a p).lowCost + 11 =
      layerCost lay.val ((lctxOf w index lay a p).zSum 0 43) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hD := lctx_digits w index lay a p hlay ds hds
  have hsum := LCtx.decode_lower_sum lay hlay _ ds hds
  have hck : (lctxOf w index lay a p).ck < 8 := ckOf_lt lay hlay a ds hds
  have hacc := (lctxOf w index lay a p).lowCost_accept hck ds hD hsum.1 (target lay) hsum.2
  rw [← tgtL_eq] at hacc
  simp only [layerCost, cyB, lfSteps, chainCost0, if_neg h0]
  omega

/-! ## One layer -/

/-- **A lower layer** (`lay ≠ 0`): `layerHead` from `LayerIn` to `LeafOut`. -/
theorem layer_good_low (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (M : Digest)
    (s : MachineState) (hs : LayerIn w pk index lay.val M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index lay ends u → GoodQ u N C Q A (ccM (R ends) K)) :
    GoodQ s (N + layerFuel lay.val) (C + layerCost lay.val 0) Q (A + layerCost lay.val 0)
      (ccM (layerHead w index lay M R) K) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hidx := hs.idx
  have hA := encA_step w pk index lay M s hs
  have hT : 9 * tgtL lay.val ≤ 2993 := by fin_cases lay <;> decide
  have hfuel : layerFuel lay.val = stepsA lay.val + 1 + 29 + 1720 + 11 := by simp [layerFuel, stB, chainFuel, lfSteps, h0]
  have hcost : layerCost lay.val 0 = stepsA lay.val + 8 + 32 + 11 + (2993 - 9 * tgtL lay.val) := by
    simp only [layerCost, cyB, lfSteps, chainCost0, if_neg h0]; omega
  unfold layerHead
  by_cases hctr : (wctr w lay).toNat ≥ counterLimit
  · rw [if_pos hctr, ccM_pure, hK0]
    obtain ⟨u, hst, hf, h5, h10⟩ := hA.1 hctr
    exact GoodQ.steps' hst (GoodQ.reject (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  · rw [if_neg hctr]
    obtain ⟨t, hst, hf, h5, hv, hin, c, hc, hpre⟩ := hA.2 (by omega)
    have hblk := blocks_encodingInput lay (route index lay).2 (route index lay).1 M (wctr w lay)
    have H : ∀ a : BitVec 256, GoodQ (writeHash t a) (N + 11 + 1720 + 29) (C + 11 + (2993 - 9 * tgtL lay.val) + 32)
        Q (A + 11 + (2993 - 9 * tgtL lay.val) + 32)
        (ccM (match decode lay (a.extractLsb' 0 128) with
          | none => pure none
          | some digits => chainsP w lay (route index lay).2 (route index lay).1 digits >>= R) K) := by
      intro a
      have hB := encB_step w pk index lay hlay c hc hidx t hpre a
      cases hds : decode lay (a.extractLsb' 0 128) with
      | none =>
        dsimp only
        rw [ccM_pure, hK0]
        obtain ⟨v, k, cy, hst', hf', h5', h10', hk, hcy⟩ := hB.1 hds
        exact GoodQ.steps' hst' (GoodQ.reject (Q := Q) (A := 0) hf' h5' h10') (by omega) (by omega)
          (fun hq => ⟨hq, by omega⟩)
      | some ds =>
        dsimp only
        obtain ⟨s0, hst0, hLok, hkn, hO0, hIn, hG0, hOr0, h23, h30⟩ := hB.2 (by rw [hds]; simp)
        set L := lctxOf w index lay a (trPc lay.val c) with hLd
        have hD := lctx_digits w index lay a (trPc lay.val c) hlay ds hds
        have hsum := LCtx.decode_lower_sum lay hlay _ ds hds
        have hck : L.ck < 8 := ckOf_lt lay hlay a ds hds
        have hacc := L.lowCost_accept hck ds hD hsum.1 (target lay) hsum.2
        rw [← tgtL_eq] at hacc
        have hP := L.lowP_eq hlay rfl ds hD (s6v_chainBlock lay hlay)
        have hG := L.lower_good hLok rfl rfl hck hkn hO0 (fun ends => ccM (R ends) K) (N + 11) (C + 11) (A + 11) Q
          (fun ends t ht => by
            obtain ⟨u, hstu, hu⟩ := leafL_step w pk index lay hlay c hc hidx a s0 hkn hG0 hOr0 h23 h30 ends t ht
            exact GoodQ.steps' hstu (hR ends u hu) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩))
          s0 hIn
        have e : chainsP w lay (route index lay).2 (route index lay).1 ds = L.lowP := by
          rw [hP]; unfold chainsP; rw [LCtx.chainCount_lower lay hlay]; rfl
        rw [ccM_bind, e]
        exact GoodQ.steps' hst0 hG (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
    have := GoodQ.shortHash_bind (f := fun answer => match decode lay answer with
      | none => pure none
      | some digits => chainsP w lay (route index lay).2 (route index lay).1 digits >>= R) hf h5 hv hin H
    rw [hblk] at this
    exact GoodQ.steps' hst this (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)

/-! ## Interfaces: V2's `FtsOut` → layer 3's `LayerIn`; V3's Merkle end → the next `LayerIn` -/

/-- **V2's `FtsOut` reaches layer 3's `LayerIn`** (stated on `FtsOut`'s fields `glob`, `idx`, `pc` (`layerPc = 656`),
`root`, `wit`, with `F.idx = a.toNat % 2^31 < 2^31`): the load block (words 656 .. 660, `ld3Spec`, 5 cycles) reads
five layer constants from the embedded data (`DataOK`, part of `Glob`); the copy `xtr3_1` starts at 661. The four carried constants remain known. -/
theorem layerIn_of_fts (w : WBytes) (pk : Digest) (idx : Nat) (root : Digest) (u : MachineState)
    (hidx : idx < 2 ^ 31) (hglob : Glob carryK w pk u) (hreg : u.getReg .x22 = BitVec.ofNat 64 idx)
    (hpc : u.pc = pcOf 656) (hroot : DigAt u 0x100 root)
    (hwit : SigGolfCandidate.T3M.CanonicalPort.Verify.Orig w (fun o => o < 64 ∨ 11288 ≤ o) u) :
    ∃ t, Steps image u 5 5 t ∧ LayerIn w pk idx 3 root t := by
  obtain ⟨t, ht⟩ := spec_run ld3Check_ok u hpc hglob.1 (by simp [ld3Spec]) (by simp)
  have hm : ∀ A, t.getMem A = u.getMem A := fun A => by rw [ht.mem]; rfl
  have hD : DataOK u := hglob.2.2.2.2.2
  have r28 : t.getReg .x28 = (E.ld (kw DATA)).eval u := ht.regs (.x28, .ld (kw DATA)) (by simp [ld3Spec])
  have r21 : t.getReg .x21 = (E.ld (kw (DATA + 8))).eval u := ht.regs (.x21, .ld (kw (DATA + 8))) (by simp [ld3Spec])
  have r20 : t.getReg .x20 = (E.ld (kw (DATA + 16))).eval u :=
    ht.regs (.x20, .ld (kw (DATA + 16))) (by simp [ld3Spec])
  have r27 : t.getReg .x27 = (E.ld (kw (DATA + 24))).eval u :=
    ht.regs (.x27, .ld (kw (DATA + 24))) (by simp [ld3Spec])
  have r2 : t.getReg .x2 = (E.ld (kw (DATA + 32))).eval u := ht.regs (.x2, .ld (kw (DATA + 32))) (by simp [ld3Spec])
  have e28 : t.getReg .x28 = BitVec.ofNat 64 (2 ^ 40) :=
    r28.trans (hD.word 0 (by omega) (2 ^ 40) (by decide) DATA (by omega))
  have e21 : t.getReg .x21 = BitVec.ofNat 64 M2c :=
    r21.trans (hD.word 1 (by omega) M2c (by decide) (DATA + 8) (by omega))
  have e20 : t.getReg .x20 = BitVec.ofNat 64 M1c :=
    r20.trans (hD.word 2 (by omega) M1c (by decide) (DATA + 16) (by omega))
  have e27 : t.getReg .x27 = BitVec.ofNat 64 (hw 1 3) :=
    r27.trans (hD.word 3 (by omega) (hw 1 3) (by decide) (DATA + 24) (by omega))
  have e2 : t.getReg .x2 = BitVec.ofNat 64 0x3fe00 :=
    r2.trans (hD.word 4 (by omega) 0x3fe00 (by decide) (DATA + 32) (by omega))
  have hG0 : Glob afterLoadK w pk t := ht.glob _ _ _ hglob (RelOK.nil u)
  have hpk : preK 3 = afterLoadK ++ [(.x28, BitVec.ofNat 64 (2 ^ 40)), (.x21, BitVec.ofNat 64 M2c),
      (.x20, BitVec.ofNat 64 M1c), (.x27, BitVec.ofNat 64 (hw 1 3)), (.x2, BitVec.ofNat 64 0x3fe00)] := rfl
  have hk : ∀ p ∈ preK 3, t.getReg p.1 = p.2 := by
    intro p hp
    rw [hpk] at hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | rfl | rfl | rfl | rfl | rfl
    · exact ht.known p hp
    · exact e28
    · exact e21
    · exact e20
    · exact e27
    · exact e2
  refine ⟨t, ht.steps, ⟨by norm_num, hidx, ⟨0, by rw [nCopy_eq.1]; norm_num, by rw [ht.pc rfl]; rfl⟩, ⟨hk, hG0.2⟩,
    ?_, ?_, ?_⟩⟩
  · rw [show rReg 3 = .x22 from rfl, ht.keep .x22 (by simp), hreg, show below 3 = 0 from rfl, pow_zero, Nat.div_one]
  · exact ⟨(hm _).trans hroot.1, (hm _).trans hroot.2⟩
  · exact (hwit.mono (fun o ho => Or.inr ho.1)).frame (fun j _ _ => hm _)

/-- The tree index of layer `L > 0` is the next layer's remaining index (`t5` at the next transition). -/
theorem tree_next (index : Nat) (L : Layer) (h : L ≠ 0) : (route index L).2 = index / 2 ^ below (L.val - 1) := by
  rw [route_snd]
  fin_cases L
  · exact absurd rfl h
  all_goals rfl

/-- The next layer's region ends where layer `L`'s Merkle blocks begin. -/
theorem layerEnd_prev (L : Layer) (h : L ≠ 0) : layerEnd (L.val - 1) = layerBase L := by
  fin_cases L
  · exact absurd rfl h
  all_goals decide

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart79

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart80

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest route coreDigit dataDigits maxDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

theorem nctx_block (w : WBytes) (index : Nat) (v : Digest) (p i : Nat) :
    (nctxOf w index v p).blk i - 0x800 = chainBlock 0 i := by
  change 15768 - 1664 + 64 * (53 - i) - 2048 = 11288 + 64 * 12 + 64 * (54 - 1 - i)
  omega

theorem nctx_chain_eq (w : WBytes) (index : Nat) (v : Digest) (p i : Nat) (hi : i < 54) :
    let c := nctxOf w index v p
    chainP 0 c.tree c.leaf i (c.dig i) (NCtx.topMax i - c.dig i) (c.pad0 i) (c.pad1 i) (c.val i) =
      chainP 0 (route index 0).2 (route index 0).1 i ((dataDigits 0 v).getD i 0)
        (maxDigit 0 i - (dataDigits 0 v).getD i 0) (wchainPads w 0 i).1 (wchainPads w 0 i).2 (wvalue w 0 i) := by
  have hm : NCtx.topMax i = maxDigit 0 i := by
    simp [NCtx.topMax, Nonbinary.mx, maxDigit, show (i / 3 < 17) ↔ i < 51 by omega]
  dsimp only
  rw [T3.dataDigits_getD 0 v i hi, hm]
  unfold NCtx.pad0 NCtx.pad1 NCtx.val
  rw [nctx_block]
  rfl

/-- The checked chain context hashes exactly Core's padded source chains. -/
theorem nctx_mapM_eq (w : WBytes) (index : Nat) (v : Digest) (p : Nat) :
    let c := nctxOf w index v p
    (List.finRange 54).mapM (fun i => chainP 0 c.tree c.leaf i.val (c.dig i.val)
      (NCtx.topMax i.val - c.dig i.val) (c.pad0 i.val) (c.pad1 i.val) (c.val i.val)) =
    chainsP w 0 (route index 0).2 (route index 0).1 (dataDigits 0 v) := by
  unfold chainsP
  apply congrArg (fun f => (List.finRange 54).mapM f)
  funext i
  exact nctx_chain_eq w index v p i.val i.isLt

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart80

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart81

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 shortHash leafHash)
open Nonbinary (NCtx)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem nctx_topP_eq (w : WBytes) (index : Nat) (v : Digest) (p : Nat) :
    (nctxOf w index v p).topP = chainsP w 0 (route index 0).2 (route index 0).1 (dataDigits 0 v) := by
  unfold NCtx.topP NCtx.chainF
  rw [foldlM_app_mapM]
  simp only [List.nil_append, id_map']
  rw [← List.range_eq_range', ← finRange_mapM]
  exact nctx_mapM_eq w index v p

theorem nctx_initial (w : WBytes) (index : Nat) (v : Digest) (p : Nat) (u s : MachineState)
    (he : TopEntry u v p s) (hvalid : T3.topRanksValid v = true) :
    (nctxOf w index v p).ChainIn s 0 [] s := by
  let c := nctxOf w index v p
  have hf : c.Fit v := fun i hi => rfl
  refine ⟨⟨fun r hr => rfl, Frame.refl s _, by simp⟩,rfl,?_⟩
  rw [he.pc]
  change pcOf (176744 + 256 * (v.toNat % 128)) = pcOf (c.startPc 0)
  rw [NCtx.startPc, if_pos (by decide), c.fit_rank hf hvalid 0 (by decide)]
  simp [Nonbinary.entW,Search.topRank]

theorem nctx_encoded (u s : MachineState) (v : Digest) (p : Nat) (he : TopEntry u v p s)
    (hv : v.toNat < 2 ^ 125) : NCtx.Encoded v s := by
  refine ⟨he.lo,?_,?_,he.mask,he.table⟩
  · rw [he.hi]
    exact Search.topWindow_cross v
  · rw [he.tail,Search.topWindow_tail v hv]

/-- The mixed-radix top layer, including all rejected encodings and the eleven-cycle mandatory credit. -/
theorem layer_good_top (w : WBytes) (pk : Digest) (index : Nat) (M : Digest)
    (s : MachineState) (hs : LayerIn w pk index 0 M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index 0 ends u → GoodQ u N C Q A (ccM (R ends) K)) :
    GoodQ s (N + layerFuel 0) (C + layerCost 0 0) Q (A + layerCost 0 0) (ccM (layerHead w index 0 M R) K) := by
  have hidx := hs.idx
  have hA := encA_step w pk index 0 M s hs
  have hfuel : layerFuel 0 = 16 + 1 + 118 + 2321 + 13 := by decide
  have hcost : layerCost 0 0 = 16 + 8 + 70 + 13 + 1129 := by decide
  have hsA : stepsA (0 : Layer).val = 16 := rfl
  unfold layerHead
  by_cases hctr : (wctr w 0).toNat ≥ counterLimit
  · rw [if_pos hctr, ccM_pure, hK0]
    obtain ⟨u, hst, hf, h5, h10⟩ := hA.1 hctr
    rw [hsA] at hst
    exact GoodQ.steps' hst (GoodQ.reject (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  · rw [if_neg hctr]
    obtain ⟨t, hst, hf, h5, hv, hin, c, hc, hpre⟩ := hA.2 (by omega)
    rw [hsA] at hst
    have hblk := blocks_encodingInput 0 (route index 0).2 (route index 0).1 M (wctr w 0)
    have H : ∀ a : BitVec 256, GoodQ (writeHash t a) (N + 13 + 2321 + 118) (C + 13 + 1129 + 70) Q (A + 13 + 1129 + 70)
        (ccM (match decode 0 (a.extractLsb' 0 128) with
          | none => pure none
          | some digits => chainsP w 0 (route index 0).2 (route index 0).1 digits >>= R) K) := by
      intro a
      cases hds : decode 0 (a.extractLsb' 0 128) with
      | none =>
        dsimp only
        rw [ccM_pure,hK0]
        obtain ⟨k,z,st,hk,hz,h5z,h10z⟩ := topTransition_reject w pk index c hc t hpre a hds
        exact GoodQ.steps' st (GoodQ.reject (Q := Q) (A := 0) hz h5z h10z) (by omega) (by omega)
          (fun hq => ⟨hq,by omega⟩)
      | some ds =>
        dsimp only
        have hcan : decode 0 (a.extractLsb' 0 128) = some (Search.topDigits (a.extractLsb' 0 128)) := by
          rw [hds,(decode_top_sum _ _ hds).1]
          rfl
        obtain ⟨s0,st0,he⟩ := topTransition_ok w pk index c hc t hpre a hcan
        let L := nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)
        have hLok : L.ok := nctx_ok w index _ c hidx
        have hkn : KnownOK L.known s0 := nctx_known w pk index c t s0 a hpre he
        have h12 : t.getReg .x12 = 320#64 := hpre.glob.1 (_, _) (by simp [bK])
        have hDs0 : DataOK s0 := (Glob_writeHash hpre.glob a 320 h12 (by decide)).2.2.2.2.2.congr
          (fun A _ hA => he.frame.get (by omega) (by simp))
        have hO := nctx_orig w index (a.extractLsb' 0 128) (trPc 0 c) s0
          (topEntry_orig w pk index c t s0 a hpre he) hDs0
        have hfit : L.Fit (a.extractLsb' 0 128) := fun i hi => rfl
        have hdec := NCtx.decode_facts hds
        have hIn := nctx_initial w index _ (trPc 0 c) _ s0 he hdec.2.1
        have hEnc := nctx_encoded _ s0 _ (trPc 0 c) he hdec.1
        have hG := L.top_good hLok hkn hO hEnc hfit hds (fun ends => ccM (R ends) K)
          (N+13) (C+13) (A+13) Q (fun ends z hz => by
            obtain ⟨hr,hf,hlen,hend,hpc⟩ := hz
            have hregs : RegsExcept s0 z topChainRegs := by
              intro r hrn
              apply hr r
              · intro hh;exact hrn ((by decide : chainRegs ⊆ topChainRegs) hh)
              · intro hh;subst r;exact hrn (by decide)
            have hframe : Frame s0 z topChainWrites := by
              exact hf
            have hready := topLeafReady_of w pk index c t s0 z a ends hpre he hpc hregs hframe hlen
              (fun j hj => by have h := hend j (by omega);exact h)
            obtain ⟨u,st,hu⟩ := leafT_step w pk index c hc hidx ends z hready
            exact GoodQ.steps' st (hR ends u hu) (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)) s0 hIn
        have e : chainsP w 0 (route index 0).2 (route index 0).1 ds = L.topP := by
          rw [(decode_top_sum _ _ hds).1]
          exact (nctx_topP_eq w index _ (trPc 0 c)).symm
        rw [ccM_bind,e]
        exact GoodQ.steps' st0 hG (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)
    have := GoodQ.shortHash_bind (f := fun answer => match decode 0 answer with
      | none => pure none
      | some digits => chainsP w 0 (route index 0).2 (route index 0).1 digits >>= R) hf h5 hv hin H
    rw [hblk] at this
    exact GoodQ.steps' hst this (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart81

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart82

/-! All four layers compose the checked lower and mixed-radix top verifiers. -/
namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 shortHash leafHash)

/-- **One layer** (`layer_good`): `layerHead` from `LayerIn` to `LeafOut`, fuel `layerFuel lay`, at most
`layerCost lay 0` cycles on every path. -/
theorem layer_good (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (M : Digest)
    (s : MachineState) (hs : LayerIn w pk index lay.val M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index lay ends u → GoodQ u N C Q A (ccM (R ends) K)) :
    GoodQ s (N + layerFuel lay.val) (C + layerCost lay.val 0) Q (A + layerCost lay.val 0)
      (ccM (layerHead w index lay M R) K) := by
  by_cases h0 : lay = 0
  · subst h0
    exact layer_good_top w pk index M s hs R K hK0 N C A Q hR
  · exact layer_good_low w pk index lay h0 M s hs R K hK0 N C A Q hR

/-- **W's layer loop, one layer** (`layersP w index (n + 1) M`, layer `n < 4`): the form V3 composes, with the
continuation from `LeafOut` = the leaf pk, `merkleP` and the layers below. -/
theorem layersP_good (w : WBytes) (pk : Digest) (index n : Nat) (hn : n < 4) (M : Digest) (s : MachineState)
    (hs : LayerIn w pk index n M s) (K : Option Digest → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0))
    (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index (Fin.ofNat 4 n) ends u →
      GoodQ u N C Q A (ccM (leafHash (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1
        ends >>= merkleP w index (Fin.ofNat 4 n) >>= layersP w index n) K)) :
    GoodQ s (N + layerFuel n) (C + layerCost n 0) Q (A + layerCost n 0) (ccM (layersP w index (n + 1) M) K) := by
  have hv : (Fin.ofNat 4 n : Layer).val = n := by simp [Fin.val_ofNat, Nat.mod_eq_of_lt hn]
  rw [layersP_succ]
  have := layer_good w pk index (Fin.ofNat 4 n) M s (by rw [hv]; exact hs) _ K hK0 N C A Q hR
  rwa [hv] at this


end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart82

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart83

/-! Kernel checks of the Merkle shape blocks of layers 3 and 2 (64 blocks each: the table-word entry and the six
levels, ending at the root HASH into the next encoding block). -/

namespace SigGolfCandidate.T3M.CanonicalPort

set_option maxRecDepth 100000

theorem mkChunk_3 : mkChunkCheck 3 0 0 64 = true := by decide +kernel
theorem mkChunk_2 : mkChunkCheck 2 0 0 64 = true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart83

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart84

/-! Kernel checks of the Merkle shape blocks of layer 1 (128 blocks: the table-word entry and the seven levels, ending
at the root HASH into the next encoding block). -/

namespace SigGolfCandidate.T3M.CanonicalPort

set_option maxRecDepth 100000

theorem mkChunk_1a : mkChunkCheck 1 0 0 64 = true := by decide +kernel
theorem mkChunk_1b : mkChunkCheck 1 0 64 64 = true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart84

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart85

/-! Kernel checks of the Merkle shape blocks of layer 0 (chunk 0: 64 blocks of levels 0..5 ending with the chunk-1
dispatch; chunk 1: 64 blocks of levels 6..11 ending at the root HASH into `0x180`) and of the 64 compare copies. -/

namespace SigGolfCandidate.T3M.CanonicalPort

set_option maxRecDepth 100000

theorem mkChunk_00 : mkChunkCheck 0 0 0 64 = true := by decide +kernel
theorem mkChunk_01 : mkChunkCheck 0 1 0 64 = true := by decide +kernel

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart85

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart86

/-! # V3: every Merkle shape block and every compare copy, kernel-checked

`mkBlockCheck_at`: for every layer, chunk and chunk value, the table-word entry and all levels of the shape block
(`MerkleCheckA`: layers 3, 2; `MerkleCheckB`: layer 1; `MerkleCheckC`: layer 0 and the compare copies);
`mkEnt_of`, `mkLvl_of`: its parts; `cmpCheck_at`: the 64 compare copies. -/

namespace SigGolfCandidate.T3M.CanonicalPort

theorem mkBlockCheck_at (lay ci sh : Nat) (hlay : lay < 4) (hci : ci < mkNch lay) (hsh : sh < 2 ^ mkBits lay ci) :
    mkBlockCheck lay ci sh = true := by
  have hall : ∀ lo n, mkChunkCheck lay ci lo n = true → lo ≤ sh → sh < lo + n → mkBlockCheck lay ci sh = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h sh (List.mem_range'_1.mpr ⟨h1, h2⟩)
  interval_cases lay
  · have hci' : ci < 2 := by simpa [mkNch] using hci
    interval_cases ci
    · exact hall 0 64 mkChunk_00 (by omega) (by simpa [mkBits] using hsh)
    · exact hall 0 64 mkChunk_01 (by omega) (by simpa [mkBits] using hsh)
  all_goals (have hci0 : ci = 0 := by simp [mkNch] at hci; omega); subst hci0
  · have : sh < 128 := by simpa [mkBits, hL] using hsh
    by_cases h64 : sh < 64
    · exact hall 0 64 mkChunk_1a (by omega) (by omega)
    · exact hall 64 64 mkChunk_1b (by omega) (by omega)
  · exact hall 0 64 mkChunk_2 (by omega) (by simpa [mkBits, hL] using hsh)
  · exact hall 0 64 mkChunk_3 (by omega) (by simpa [mkBits, hL] using hsh)

theorem mkEnt_of {lay ci sh : Nat} (h : mkBlockCheck lay ci sh = true) : mkEntCheck lay ci sh = true := by
  simp only [mkBlockCheck, Bool.and_eq_true] at h; exact h.1

theorem mkLvl_of {lay ci sh : Nat} (h : mkBlockCheck lay ci sh = true) (kk : Nat) (hkk : kk < mkBits lay ci) :
    mkLvlCheck lay ci sh kk = true := by
  simp only [mkBlockCheck, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.2 kk (List.mem_range.mpr hkk)


end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart86

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart87

/-! # V3: the Merkle shape blocks refine `leafHash >>= merkleP` (from V1's `LeafOut` to `MkEnd`)

From V1's `LeafOut w pk index lay ends u` (the `stab_lay_0` word of the leaf's low bits) the machine runs the shape
block(s) of the leaf: the leaf-pk HASH (input `LeafOut.hashInput`), then for each level `k < h` the block's header
`T(3, lay, tree, 0, heap)` and the HASH of block `k` into the next level's current slot (`k + 1 < h`) or into the root
destination `0x100` / the retained top-node slot (`k + 1 = h`). This is exactly `leafHash lay tree leaf ends >>= merkleP w index lay`
(V1's `merkleP`, level by level `mkStep`), query for query, on every oracle (the code is straight-line).

* `MAfter … k v s`: after HASH `k` (`k < h`) — the node `v` of level `k` in its current slot, the witness up to block
  `k` original except that slot, the Merkle constants known, the registers of `mkKeep` as at the entry `u`;
* `MkEnd … root t`: after the root HASH, at the next transition copy / compare copy (`mkFin lay leaf + 1`), `root` at
  `mkDst lay leaf`, the witness below the layer's Merkle blocks original;
* `lvl_step`: one level (with layer 0's chunk dispatch at level 5); `merkle_rest`: the levels by induction;
* **`merkle_good`**: from `LeafOut`, `GoodQ u (N + mkFuel lay) (C + mkCyc lay) Q (A + mkCyc lay)
  (ccM (leafHash … ends >>= merkleP w index lay) K)` given `K`'s judgment at every `MkEnd`; `mkCyc` = 273 / 181 /
  168 / 168 cycles (layers 0..3), `mkFuel` = 78 / 45 / 39 / 39 steps (BIG2: one header word-0 store per level after
  level 0, whose `ld tp` merges the word; `MAfter.x4`). -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount pad64 shortHash leafHash header)

/-! ## Core's Merkle path, level by level -/

/-- Level `j` of V1's `merkleP` from the node `value`. -/
def mkStep (w : WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) : T3.M Digest :=
  let other := wpath w lay (route index lay).1 j
  let pair := if (route index lay).1 / 2 ^ j % 2 = 0 then (value, other) else (other, value)
  nodeHashP 3 lay.val (route index lay).2 (2 ^ (height lay - j - 1) + (route index lay).1 / 2 ^ (j + 1))
    pair.1 (wmerklePad w lay j) pair.2

theorem mkFinRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem merkleP_eq (w : WBytes) (index : Nat) (lay : Layer) (value : Digest) :
    merkleP w index lay value = (List.range (height lay)).foldlM (mkStep w index lay) value := by
  rw [← mkFinRange_map_val, List.foldlM_map]
  rfl

/-- The block hashed after level `j`: `[L | T(3, lay, tree, 0, heap) | pad | R]`, the node on the leaf's side. -/
def mkIn (w : WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) : List UInt8 :=
  let other := wpath w lay (route index lay).1 j
  let pair := if (route index lay).1 / 2 ^ j % 2 = 0 then (value, other) else (other, value)
  blk4 pair.1 (header 3 lay.val (route index lay).2 0 (2 ^ (height lay - j - 1) + (route index lay).1 / 2 ^ (j + 1)))
    (wmerklePad w lay j) pair.2

theorem mkStep_eq (w : WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) :
    mkStep w index lay value j = shortHash (mkIn w index lay value j) := rfl

theorem mkIn_length (w : WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) :
    (mkIn w index lay value j).length = 64 := blk4_length _ _ _ _

theorem mkIn_blocks (w : WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) :
    (toQ (pad64 (mkIn w index lay value j))).blocks = 1 := blocks_blk4 _ _ _ _

/-! ## Chunks, levels and pcs -/

/-- The chunk of level `k`. -/
def mkCi (lay k : Nat) : Nat := if lay = 0 ∧ 6 ≤ k then 1 else 0
/-- The chunk bits of the leaf: the index of its shape block. -/
def mkSh (lay ci leaf : Nat) : Nat := leaf / 2 ^ mkLo lay ci % 2 ^ mkBits lay ci
/-- The `ecall` of HASH `k` (level `k`'s; HASH 0 hashes the leaf pk). -/
def mkEc (lay leaf k : Nat) : Nat :=
  mkShp lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) + mkOff lay (mkCi lay k) (k - mkLo lay (mkCi lay k)) + 1
/-- The root HASH's `ecall`; the next transition copy / compare copy follows it. -/
def mkFin (lay leaf : Nat) : Nat :=
  mkShp lay (mkNch lay - 1) (mkSh lay (mkNch lay - 1) leaf) + mkOff lay (mkNch lay - 1) (mkBits lay (mkNch lay - 1)) + (if lay = 0 then 0 else 1)
/-- Instruction steps from after HASH `k` to the next HASH (layer 0, level 5: the chunk dispatch and the table word). -/
def mkLvlSt (lay k : Nat) : Nat := mkBody lay k + mkMove lay k + (if lay = 0 ∧ k = 5 then 4 else 0)

theorem mk_facts (lay k : Nat) (hlay : lay < 4) (hk : k < hL lay) :
    mkCi lay k < mkNch lay ∧ mkLo lay (mkCi lay k) ≤ k ∧ k - mkLo lay (mkCi lay k) < mkBits lay (mkCi lay k) ∧
    mkIsDisp lay (mkCi lay k) (k - mkLo lay (mkCi lay k)) = decide (lay = 0 ∧ k = 5) ∧
    (k + 1 < hL lay → ¬ (lay = 0 ∧ k = 5) → mkCi lay (k + 1) = mkCi lay k ∧
      k + 1 - mkLo lay (mkCi lay k) = k - mkLo lay (mkCi lay k) + 1 ∧
      k - mkLo lay (mkCi lay k) + 1 < mkBits lay (mkCi lay k)) ∧
    (k + 1 = hL lay → mkCi lay k = mkNch lay - 1 ∧ ¬ (k - mkLo lay (mkCi lay k) + 1 < mkBits lay (mkCi lay k)) ∧
      k - mkLo lay (mkCi lay k) + 1 = mkBits lay (mkCi lay k)) := by
  interval_cases lay
  · change k < 12 at hk; interval_cases k <;> decide
  · change k < 7 at hk; interval_cases k <;> decide
  · change k < 6 at hk; interval_cases k <;> decide
  · change k < 6 at hk; interval_cases k <;> decide

theorem mk_disp_facts : mkCi 0 5 = 0 ∧ mkLo 0 0 = 0 ∧ mkCi 0 6 = 1 ∧ mkLo 0 1 = 6 ∧ mkBits 0 0 = 6 ∧ mkBits 0 1 = 6 ∧
    mkNch 0 = 2 := by decide

theorem mkLvlSt_ne (lay k : Nat) (h : ¬ (lay = 0 ∧ k = 5)) : mkLvlSt lay k = mkBody lay k + mkMove lay k := by
  simp [mkLvlSt, h]

/-- Bit `k` of a chunk value is bit `lo + k` of the leaf. -/
theorem mkBlk_bit (E b n k : Nat) (hk : k < n) : E / 2 ^ b % 2 ^ n / 2 ^ k % 2 = E / 2 ^ (b + k) % 2 := by
  have h1 : 2 ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h1, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega)), Nat.div_div_eq_div_mul,
    ← Nat.pow_add]

theorem mkSh_bit (lay ci leaf kk : Nat) (hkk : kk < mkBits lay ci) :
    mkSh lay ci leaf / 2 ^ kk % 2 = leaf / 2 ^ (mkLo lay ci + kk) % 2 := mkBlk_bit _ _ _ _ hkk

theorem mkSh_lt (lay ci leaf : Nat) : mkSh lay ci leaf < 2 ^ mkBits lay ci := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem mkBit_lt (x k : Nat) : x / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)

/-! ## Addresses -/

theorem mkBase_eq (lay : Layer) : mkBase lay.val = layerBase lay := by fin_cases lay <;> rfl

theorem mkBo_eq (lay : Layer) (k : Nat) : mkBo lay.val k = merkleBlock lay k := by
  unfold mkBo merkleBlock; rw [mkBase_eq, hL_eq]

theorem mkBo_facts (lay k : Nat) (hlay : lay < 4) (hk : k < hL lay) :
    mkBo lay k % 8 = 0 ∧ 11288 ≤ mkBo lay k ∧ mkBo lay k + 80 ≤ 25256 ∧ mkBase lay ≤ mkBo lay k ∧
    (k + 1 < hL lay → mkBo lay (k + 1) + 64 = mkBo lay k) ∧ (k + 1 = hL lay → mkBo lay k = mkBase lay) ∧
    mkBo lay k + 64 ≤ mkBase lay + 64 * hL lay := by
  interval_cases lay <;> simp only [hL, List.getD_cons_succ, List.getD_cons_zero] at hk ⊢ <;>
    simp only [mkBo, mkBase, hL, List.getD_cons_succ, List.getD_cons_zero] <;> omega

theorem mkBase_ge (lay : Nat) (hlay : lay < 4) : 11288 ≤ mkBase lay ∧ mkBase lay % 8 = 0 := by
  interval_cases lay <;> decide

theorem layerBase_add (lay : Layer) : layerBase lay + 64 * height lay = mkBase lay.val + 64 * hL lay.val := by
  rw [mkBase_eq, hL_eq]

/-! ## Heap indices -/

theorem mkPow_add_div (h k x : Nat) (hk : k < h) :
    (2 ^ h + x) / 2 ^ (k + 1) = 2 ^ (h - k - 1) + x / 2 ^ (k + 1) := by
  have : 2 ^ h = 2 ^ (k + 1) * 2 ^ (h - k - 1) := by rw [← Nat.pow_add]; congr 1; omega
  rw [this, Nat.mul_add_div (Nat.two_pow_pos _)]

theorem mkDiv64_mul_div (leaf k : Nat) (hk : 6 ≤ k) : leaf / 64 * 64 / 2 ^ (k + 1) = leaf / 2 ^ (k + 1) := by
  have e : 2 ^ (k + 1) = 64 * 2 ^ (k - 5) := by
    rw [show (64 : Nat) = 2 ^ 6 by rfl, ← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_comm 64 (2 ^ (k - 5)), Nat.mul_div_mul_right _ _ (by decide : 0 < 64), Nat.div_div_eq_div_mul,
    Nat.mul_comm 64]

theorem mkHeap_eq (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay)
    (hci : ¬ (lay = 0 ∧ mkCi lay k = 0)) :
    mkHeap lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) k = 2 ^ (hL lay - k - 1) + leaf / 2 ^ (k + 1) := by
  unfold mkHeap
  by_cases h0 : lay = 0
  · subst h0
    have hk6 : 6 ≤ k := by
      by_contra hk6; exact hci ⟨rfl, by simp [mkCi]; omega⟩
    have hci1 : mkCi 0 k = 1 := by simp [mkCi]; omega
    rw [hci1]
    have hl : leaf < 4096 := by simpa [hL] using hleaf
    have hsh : mkSh 0 1 leaf = leaf / 64 := by
      simp only [mkSh, mkLo, mkBits]; norm_num; omega
    rw [hsh, show mkLo 0 1 = 6 by rfl, show hL 0 = 12 by rfl, show (2 : Nat) ^ 6 = 64 by rfl,
      mkPow_add_div 12 k _ (by simpa [hL] using hk), mkDiv64_mul_div leaf k hk6]
  · have hci0 : mkCi lay k = 0 := by simp [mkCi, h0]
    rw [hci0]
    have hsh : mkSh lay 0 leaf = leaf := by
      simp only [mkSh, mkLo, mkBits, h0, false_and, if_false, Nat.pow_zero, Nat.div_one]
      exact Nat.mod_eq_of_lt hleaf
    rw [hsh, show mkLo lay 0 = 0 by simp [mkLo], Nat.pow_zero, Nat.mul_one, mkPow_add_div _ k _ hk]

theorem mkHeapE_eval (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay)
    (s : MachineState) (h23 : s.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay + leaf)) :
    (mkHeapE lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) k).eval s =
      BitVec.ofNat 64 (2 ^ (hL lay - k - 1) + leaf / 2 ^ (k + 1)) := by
  have hh : hL lay ≤ 12 := by interval_cases lay <;> decide
  have hpow : 2 ^ hL lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) hh
  unfold mkHeapE
  split_ifs with hc
  · apply BitVec.eq_of_toNat_eq
    simp only [E.eval, BinOp.eval, kw, h23]
    have h1 : 2 ^ (hL lay - k - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : leaf / 2 ^ (k + 1) ≤ leaf := Nat.div_le_self _ _
    rw [toNat_srl _ _ (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 2 ^ hL lay + leaf < 2 ^ 64 by omega), mkPow_add_div _ k _ hk]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · simp only [E.eval, kw]
    rw [mkHeap_eq lay leaf k hlay hleaf hk hc]

/-! ## Invariants -/

/-- The witness words still original after HASH `k` (the node at `cur = mkCur lay k b`): the region up to the end of
block `k`, minus the 32 bytes the HASH wrote at `cur`. -/
def mkP (lay k b : Nat) (o : Nat) : Prop :=
  11288 ≤ o ∧ o < mkBo lay k + 64 ∧ (0x800 + o + 8 ≤ mkCur lay k b ∨ mkCur lay k b + 32 ≤ 0x800 + o)

/-- After HASH `k < h`: at the next instruction, the node `v` in level `k`'s current slot. -/
structure MAfter (w : WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (k : Nat) (v : Digest)
    (s : MachineState) : Prop where
  pc : s.pc = pcOf (mkEc lay leaf k + 1)
  glob : Glob baseK w pk s
  known : KnownOK (mkLvlK lay k) s
  keep : ∀ r ∈ mkKeep, s.getReg r = u.getReg r
  node : DigAt s (mkCur lay k (leaf / 2 ^ k % 2)) v
  orig : Orig w (mkP lay k (leaf / 2 ^ k % 2)) s
  dstReg : s.getReg .x12 = BitVec.ofNat 64 (mkCur lay k (leaf / 2 ^ k % 2))
  /-- BIG2: after level 0, `tp` is the merged header word 0. -/
  x4 : k ≠ 0 → s.getReg .x4 = StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay)) 4 (u.getReg .x30)

/-- After the root HASH: at the next transition copy (layers 3, 2, 1) or compare copy (layer 0). -/
structure MkEnd (w : WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (root : Digest) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf (mkFin lay leaf + 1)
  glob : Glob baseK w pk t
  known : KnownOK (mkKc lay ++ [(.x11, 64)]) t
  keep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r
  root : DigAt t (mkDst lay leaf) root
  orig : Orig w (fun o => 11288 ≤ o ∧ o < mkBase lay) t
  dstReg : t.getReg .x12 = BitVec.ofNat 64 (mkDst lay leaf)

/-! ## Helpers -/

/-- `hashInput` as a function of `a0`, `a1` and the byte reader. -/
def mkHashInputOf (a b : Word) (f : Word → BitVec 8) : Query :=
  ⟨b.toNat / 64 - 1, BitVec.ofNat (8 * (64 * (b.toNat / 64 - 1 + 1))) ((List.range (64 * (b.toNat / 64 - 1 + 1))).foldl
    (fun acc i => acc + (f (a + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i)) 0)⟩

theorem mkHashInput_eq_of (s : MachineState) : hashInput s = mkHashInputOf (s.getReg .x10) (s.getReg .x11) s.getByte := rfl

theorem mkHashInput_congr {s t : MachineState} (h10 : t.getReg .x10 = s.getReg .x10)
    (h11 : t.getReg .x11 = s.getReg .x11) (hm : ∀ A, t.getMem A = s.getMem A) : hashInput t = hashInput s := by
  have hb : t.getByte = s.getByte := funext fun a => by simp only [MachineState.getByte, hm]
  rw [mkHashInput_eq_of, mkHashInput_eq_of, h10, h11, hb]

theorem mkK_sub (lay : Nat) (l : List (Reg × Word)) : ∀ p ∈ mkK lay, p ∈ mkK lay ++ l :=
  fun p hp => List.mem_append_left _ hp

theorem mkKeep_sub (l : List Reg) : ∀ r ∈ mkKeep, r ∈ mkKeep ++ l := fun r hr => List.mem_append_left _ hr

theorem mkKc_mkK (lay : Nat) : ∀ p ∈ mkKc lay, p ∈ mkK lay := by
  intro p hp
  simp only [mkKc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp <;> simp [mkK, hp]

theorem mkK_cases (lay : Nat) (p : Reg × Word) (hp : p ∈ mkK lay) :
    p ∈ mkKc lay ∨ p = (.x4, BitVec.ofNat 64 (hw 3 lay)) := by
  simp only [mkK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp <;> simp [mkKc, hp]

/-- The merged header word 0 (`mkX4`) evaluated. -/
theorem mkX4_eval (lay : Nat) (s : MachineState) :
    (mkX4 lay).eval s = StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay)) 4 (s.getReg .x30) := rfl

/-- The level's two header writes, read back at constant addresses (after level 0, given the merged `tp`). -/
theorem lvlMem_read (lay ci sh l : Nat) (s : MachineState) (A : Nat) (hA : A < 2 ^ 64) (hB : mkBlk lay l + 24 < 2 ^ 64)
    (h4 : l ≠ 0 → s.getReg .x4 = StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay)) 4 (s.getReg .x30)) :
    memEval s (mkLvlMem lay ci sh l) (BitVec.ofNat 64 A) =
      if A = mkBlk lay l + 24 then
        (mkHeapE lay ci sh l).eval s
      else if A = mkBlk lay l + 16 then StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay)) 4 (s.getReg .x30) else s.getMem (BitVec.ofNat 64 A) := by
  have hH : (mkHdrE lay l).eval s = StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay)) 4 (s.getReg .x30) := by
    unfold mkHdrE
    split_ifs with hl
    · exact mkX4_eval lay s
    · exact h4 hl
  unfold mkLvlMem
  rw [memEval_cons_ofNat _ _ _ _ _ hA hB, memEval_cons_ofNat _ _ _ _ _ hA (by omega), memEval_nil, hH]

/-! ## The HASH after a level -/

/-- At a state `t` whose memory is `s`'s with level `k`'s two header writes, `a0 = blk(k)`, `a1 = 64`: the HASH input
is `mkIn … v k`, and the witness below block `k` is still original. -/
theorem lvl_input (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState) (hidx : index < 2 ^ 31)
    (hs7 : u.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1))
    (ht5 : u.getReg .x30 = BitVec.ofNat 64 (route index lay).2)
    (k : Nat) (hk : k < hL lay.val) (v : Digest) (s t : MachineState)
    (hs : MAfter w pk lay.val (route index lay).1 u k v s)
    (hmem : ∀ A, t.getMem A =
      memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k) A)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay.val k)) (h11 : t.getReg .x11 = BitVec.ofNat 64 64) :
    hashInput t = toQ (pad64 (mkIn w index lay v k)) ∧ Orig w (fun o => 11288 ≤ o ∧ o < mkBo lay.val k) t := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  have htree : (route index lay).2 < 2 ^ 32 := tree_lt index lay hidx
  obtain ⟨hB8, hBlo, hBhi, -, -, -, -⟩ := mkBo_facts lay.val k hlay hk
  have h4s : k ≠ 0 → s.getReg .x4 = StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay.val)) 4 (s.getReg .x30) :=
    fun hk0 => (hs.x4 hk0).trans (by rw [hs.keep .x30 (by simp [mkKeep])])
  have hrd : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = mkBlk lay.val k + 24 then
        (mkHeapE lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k).eval s
      else if A = mkBlk lay.val k + 16 then StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay.val)) 4 (s.getReg .x30) else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (hmem _).trans (lvlMem_read _ _ _ _ s A hA (by unfold mkBlk; omega) h4s)
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ mkBlk lay.val k + 24 → A ≠ mkBlk lay.val k + 16 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2; rw [hrd A hA, if_neg h1, if_neg h2]
  have h30 : s.getReg .x30 = BitVec.ofNat 64 (route index lay).2 := (hs.keep .x30 (by simp [mkKeep])).trans ht5
  have h23 : s.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1) :=
    (hs.keep .x23 (by simp [mkKeep])).trans hs7
  have hheap : 2 ^ (height lay - k - 1) + (route index lay).1 / 2 ^ (k + 1) < 2^32 := by
    have hp : (2 : Nat) ^ (height lay - k - 1) ≤ 2^12 :=
      Nat.pow_le_pow_right (by decide) (by
        have hh : height lay ≤ 12 := by fin_cases lay <;> decide
        omega)
    have hph : (2 : Nat)^hL lay.val ≤ 2^12 :=
      Nat.pow_le_pow_right (by decide) (by rw [hL_eq]; fin_cases lay <;> decide)
    have hd := Nat.div_le_self (route index lay).1 (2^(k+1))
    omega
  have hT1 : t.getMem (BitVec.ofNat 64 (mkBlk lay.val k + 24)) = BitVec.ofNat 64
      (hdr1 (2 ^ (height lay - k - 1) + (route index lay).1 / 2 ^ (k + 1)) 0) := by
    rw [hrd _ (by unfold mkBlk; omega), if_pos rfl,
      mkHeapE_eval lay.val (route index lay).1 k hlay hleaf hk s h23, hL_eq]
    congr 1
    unfold hdr1
    simp only [Nat.mod_eq_of_lt hheap, Nat.div_eq_of_lt hheap, Nat.zero_mod, Nat.zero_add, Nat.add_zero, Nat.zero_mul]
  have hT0 : t.getMem (BitVec.ofNat 64 (mkBlk lay.val k + 16)) =
      BitVec.ofNat 64 (hdr0 3 lay.val (route index lay).2 (route index lay).2) := by
    rw [hrd _ (by unfold mkBlk; omega), if_neg (by omega), if_pos rfl, h30, merge_hi,
      hdr0_eq 3 lay.val _ _ (by decide) (by omega) htree htree]
    congr 1
    unfold hdr1 hw
    omega
  have hO := hs.orig
  have hlen := mkIn_length w index lay v k
  refine ⟨?_, ?_⟩
  · rw [pad64_of_aligned _ (by rw [hlen])]
    apply hashInput_words8 t _ (mkBlk lay.val k) hlen h10 (by unfold mkBlk; omega) (by unfold mkBlk; omega) h11
    have hpad := hO.dig (mkBo lay.val k + 32) (by omega) (by unfold WX; omega)
      ⟨by omega, by omega, by unfold mkCur mkBlk; have := mkBit_lt (route index lay).1 k; interval_cases (route index lay).1 / 2 ^ k % 2 <;> omega⟩
      ⟨by omega, by omega, by unfold mkCur mkBlk; have := mkBit_lt (route index lay).1 k; interval_cases (route index lay).1 / 2 ^ k % 2 <;> omega⟩
    have e32 : WIT + (mkBo lay.val k + 32) = mkBlk lay.val k + 32 := by unfold WIT mkBlk; omega
    rw [e32, show mkBlk lay.val k + 32 + 8 = mkBlk lay.val k + 40 by omega] at hpad
    have f32 := hfr (mkBlk lay.val k + 32) (by unfold mkBlk; omega) (by omega) (by omega)
    have f40 := hfr (mkBlk lay.val k + 40) (by unfold mkBlk; omega) (by omega) (by omega)
    have f0 := hfr (mkBlk lay.val k) (by unfold mkBlk; omega) (by omega) (by omega)
    have f8 := hfr (mkBlk lay.val k + 8) (by unfold mkBlk; omega) (by omega) (by omega)
    have f48 := hfr (mkBlk lay.val k + 48) (by unfold mkBlk; omega) (by omega) (by omega)
    have f56 := hfr (mkBlk lay.val k + 56) (by unfold mkBlk; omega) (by omega) (by omega)
    have hnode := hs.node
    unfold mkIn wpath wmerklePad
    rw [← mkBo_eq lay k]
    rcases (show (route index lay).1 / 2 ^ k % 2 = 0 ∨ (route index lay).1 / 2 ^ k % 2 = 1 by omega) with hb | hb
    · rw [hb] at hnode hO
      simp only [hb, if_true, sibOff, show (0 : Nat) ≠ 1 by decide, if_false]
      have hsib := hO.dig (mkBo lay.val k + 48) (by omega) (by unfold WX; omega)
        ⟨by omega, by omega, Or.inr (by unfold mkCur mkBlk; omega)⟩ ⟨by omega, by omega, Or.inr (by unfold mkCur mkBlk; omega)⟩
      have e48 : WIT + (mkBo lay.val k + 48) = mkBlk lay.val k + 48 := by unfold WIT mkBlk; omega
      rw [e48, show mkBlk lay.val k + 48 + 8 = mkBlk lay.val k + 56 by omega] at hsib
      have hn0 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val k)) = v.extractLsb' 0 64 := by
        have := hnode.1; simpa [mkCur] using this
      have hn8 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val k + 8)) = v.extractLsb' 64 64 := by
        have := hnode.2; simpa [mkCur] using this
      rw [wordsOf_blk4, f0, f8, hT0, hT1, f32, f40, f48, f56, hn0, hn8, hpad.1, hpad.2, hsib.1, hsib.2]
      simp only [dlo, dhi, header_packed_lo_3, header_packed_hi_3, header_packed_lo_9, header_packed_hi_9, header_packed_lo_10, header_packed_hi_10]
    · rw [hb] at hnode hO
      simp only [hb, show (1 : Nat) ≠ 0 by decide, if_false, sibOff, if_true, Nat.add_zero]
      have hsib := hO.dig (mkBo lay.val k) (by omega) (by unfold WX; omega)
        ⟨by omega, by omega, Or.inl (by unfold mkCur mkBlk; omega)⟩ ⟨by omega, by omega, Or.inl (by unfold mkCur mkBlk; omega)⟩
      have e0 : WIT + mkBo lay.val k = mkBlk lay.val k := by unfold WIT mkBlk; omega
      rw [e0] at hsib
      have hn48 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val k + 48)) = v.extractLsb' 0 64 := by
        have := hnode.1; simpa [mkCur] using this
      have hn56 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val k + 56)) = v.extractLsb' 64 64 := by
        have := hnode.2; simpa [mkCur, Nat.add_assoc] using this
      rw [wordsOf_blk4, f0, f8, hT0, hT1, f32, f40, f48, f56, hn48, hn56, hpad.1, hpad.2, hsib.1, hsib.2]
      simp only [dlo, dhi, header_packed_lo_3, header_packed_hi_3, header_packed_lo_9, header_packed_hi_9, header_packed_lo_10, header_packed_hi_10]
  · intro j hj ⟨h1, h2⟩
    rw [hfr _ (by unfold WIT WX at *; omega) (by unfold WIT mkBlk; omega) (by unfold WIT mkBlk; omega)]
    exact hO j hj ⟨h1, by omega, Or.inl (by unfold mkCur mkBlk; have := mkBit_lt (route index lay).1 k; omega)⟩

theorem mkDst_bound (lay leaf : Nat) :
    mkDst lay leaf % 8 = 0 ∧ mkDst lay leaf + 32 ≤ 2^23 := by
  have hm : leaf / 2048 % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold mkDst
  split <;> omega

theorem safeDest_dst (lay leaf : Nat) (hlay : lay < 4) : safeDest (mkDst lay leaf) = true := by
  by_cases h : lay = 0
  · apply safeDest_hi _ _ (mkDst_bound lay leaf).1 (mkDst_bound lay leaf).2
    simp [mkDst,h,WLO,WIT]; omega
  · simp [mkDst,h,safeDest,pSlots,CTRW,WIT,MEMORY_BYTES]
    intro x hx; right; omega

theorem mkDst_chunk (leaf : Nat) :
    13336 + 48 * (mkSh 0 1 leaf / 32 % 2) = mkDst 0 leaf := by
  have h := mkSh_bit 0 1 leaf 5 (by decide)
  change 13336 + 48 * (mkSh 0 1 leaf / 2^5 % 2) =
    13336 + 48 * (leaf / 2^(mkLo 0 1+5) % 2)
  exact congrArg (fun x => 13336 + 48*x) h

theorem mkMove_next (lay k : Nat) (hk : k+1 < hL lay) : mkMove lay k = 1 := by
  by_cases h : lay = 0
  · subst lay
    have : k < 11 := by change k+1<12 at hk; omega
    simp [mkMove]; omega
  · simp [mkMove,h]

theorem mkMove_last (lay k : Nat) (hk : k+1 = hL lay) :
    mkMove lay k = if lay = 0 then 0 else 1 := by
  by_cases h : lay = 0
  · subst lay
    have : k = 11 := by change k+1=12 at hk; omega
    simp [mkMove,this]
  · simp [mkMove,h]

/-- After the HASH that follows level `k`: the next `MAfter` (`k + 1 < h`) or `MkEnd` (`k + 1 = h`). -/
theorem lvl_after (w : WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (hlay : lay < 4)
    (k : Nat) (hk : k < hL lay) (t : MachineState)
    (hglob : Glob baseK w pk t) (hknown : KnownOK (mkKc lay ++ [(.x11, 64)]) t)
    (hkeep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r)
    (h4 : t.getReg .x4 = StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay)) 4 (u.getReg .x30))
    (horig : Orig w (fun o => 11288 ≤ o ∧ o < mkBo lay k) t) (a : BitVec 256) :
    (k + 1 < hL lay → t.pc = pcOf (mkEc lay leaf (k + 1)) →
      t.getReg .x12 = BitVec.ofNat 64 (mkCur lay (k + 1) (leaf / 2 ^ (k + 1) % 2)) →
      MAfter w pk lay leaf u (k + 1) (a.extractLsb' 0 128) (writeHash t a)) ∧
    (k + 1 = hL lay → t.pc = pcOf (mkFin lay leaf) → t.getReg .x12 = BitVec.ofNat 64 (mkDst lay leaf) →
      MkEnd w pk lay leaf u (a.extractLsb' 0 128) (writeHash t a)) := by
  obtain ⟨hB8, hBlo, hBhi, hBase, hBnext, hBlast, -⟩ := mkBo_facts lay k hlay hk
  refine ⟨fun hk1 hpc h12 => ?_, fun hk1 hpc h12 => ?_⟩
  · obtain ⟨hB8', hBlo', hBhi', -, -, -, -⟩ := mkBo_facts lay (k + 1) hlay hk1
    have hnx := hBnext hk1
    have hb := mkBit_lt leaf (k + 1)
    have hd : mkCur lay (k + 1) (leaf / 2 ^ (k + 1) % 2) + 32 < 2 ^ 64 := by unfold mkCur mkBlk; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [writeHash_pc, hpc, pcOf_add4]
    · exact Glob_writeHash hglob a _ h12 (safeDest_hi _ (by unfold mkCur mkBlk WLO WIT; omega)
        (by unfold mkCur mkBlk; omega) (by unfold mkCur mkBlk; omega))
    · intro p hp
      rw [writeHash_getReg]
      exact hknown p (by simpa [mkLvlK] using hp)
    · intro r hr; rw [writeHash_getReg]; exact hkeep r hr
    · exact DigAt.writeHash_lo t a _ h12 hd
    · have hw2 := Orig_writeHash horig a _ h12 hd
      exact hw2.mono (fun o ⟨h1, h2, h3⟩ => ⟨⟨h1, by omega⟩, by unfold WIT; omega⟩)
    · rw [writeHash_getReg]; exact h12
    · intro _; rw [writeHash_getReg]; exact h4
  · have hbl := hBlast hk1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [writeHash_pc, hpc, pcOf_add4]
    · exact Glob_writeHash hglob a _ h12 (safeDest_dst lay leaf hlay)
    · intro p hp; rw [writeHash_getReg]; exact hknown p hp
    · intro r hr; rw [writeHash_getReg]; exact hkeep r hr
    · exact DigAt.writeHash_lo t a _ h12 (by have := (mkDst_bound lay leaf).2; omega)
    · have hw2 := Orig_writeHash horig a _ h12 (by have := (mkDst_bound lay leaf).2; omega)
      apply hw2.mono
      intro o ho
      refine ⟨⟨ho.1,by omega⟩,?_⟩
      by_cases hl : lay = 0
      · simp [hl,mkBase] at ho; omega
      · right; simp [mkDst,hl,WIT]; omega
    · rw [writeHash_getReg]; exact h12

/-! ## One level -/

/-- The chunk-1 dispatch of layer 0 jumps to the `stab_0_1` word of the leaf's bits 6..11. -/
theorem dispTgt_eval (leaf : Nat) (hleaf : leaf < 4096) (s : MachineState)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 (2 ^ hL 0 + leaf)) :
    mkDispTgt.eval s = pcOf (mkTab 0 1 + mkSh 0 1 leaf) := by
  have hsh : mkSh 0 1 leaf = leaf / 64 := by simp only [mkSh, mkLo, mkBits]; norm_num; omega
  rw [hsh, show mkTab 0 1 = 209832 from rfl]
  simp only [mkDispTgt, E.eval, BinOp.eval, kw, h23, show hL 0 = 12 from rfl]
  have hq : (BitVec.ofNat 64 (2 ^ 12 + leaf) >>> ((BitVec.ofNat 64 6).toNat % 64)) =
      BitVec.ofNat 64 (64 + leaf / 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_srl _ _ (by norm_num)]
    simp only [BitVec.toNat_ofNat]
    norm_num
    omega
  rw [hq]
  have hm : (BitVec.ofNat 64 (64 + leaf / 64) <<< ((BitVec.ofNat 64 2).toNat % 64)) =
      BitVec.ofNat 64 (256 + 4 * (leaf / 64)) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sll _ _ (by norm_num)]
    simp only [BitVec.toNat_ofNat]
    norm_num
    omega
  rw [hm, ofNat_add_ofNat, even_andNot1' _ (by omega)]
  unfold pcOf; congr 1; omega

theorem lfK_mkK (lay : Nat) : ∀ p ∈ mkK lay, p ∈ lfK lay := by
  intro p hp
  simp only [mkK, baseK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [lfK, postLf, leafK, lfKeepK, baseK]

/-- **One level**: from `MAfter … k v s`, the level's body (and for layer 0's level 5 the chunk dispatch and the
`stab_0_1` word) to the `ecall` of the HASH of block `k` (`mkIn`), then `MAfter (k + 1)` or `MkEnd`. -/
theorem lvl_step (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState) (hidx : index < 2 ^ 31)
    (hs7 : u.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1))
    (ht5 : u.getReg .x30 = BitVec.ofNat 64 (route index lay).2)
    (k : Nat) (hk : k < hL lay.val) (v : Digest) (s : MachineState)
    (hs : MAfter w pk lay.val (route index lay).1 u k v s) :
    ∃ t, Steps image s (mkLvlSt lay.val k) (mkLvlSt lay.val k) t ∧ fetch image t = some (.base .ECALL) ∧
      t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (mkIn w index lay v k)) ∧
      ∀ a : BitVec 256,
        (k + 1 < hL lay.val →
          MAfter w pk lay.val (route index lay).1 u (k + 1) (a.extractLsb' 0 128) (writeHash t a)) ∧
        (k + 1 = hL lay.val → MkEnd w pk lay.val (route index lay).1 u (a.extractLsb' 0 128) (writeHash t a)) := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  obtain ⟨hci, hlo, hkk, hdisp, hnext, hlast⟩ := mk_facts lay.val k hlay hk
  obtain ⟨hB8, hBlo, hBhi, hBase, -, -, -⟩ := mkBo_facts lay.val k hlay hk
  have hlk : mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)) = k := by omega
  have hblk := mkBlockCheck_at lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) hlay hci
    (mkSh_lt _ _ _)
  have hlvl := mkLvl_of hblk _ hkk
  have hpc0 : s.pc = pcOf (mkShp lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) +
      mkOff lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k)) + 2) := by rw [hs.pc]; rfl
  have hkn0 : KnownOK (mkLvlK lay.val (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)))) s := by
    rw [hlk]; exact hs.known
  have h23 : s.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1) :=
    (hs.keep .x23 (by simp [mkKeep])).trans hs7
  by_cases hd : lay.val = 0 ∧ k = 5
  · -- layer 0, level 5: the level body, the chunk-1 dispatch, the `stab_0_1` word and the entry of chunk 1
    obtain ⟨hl0, hk5⟩ := hd
    have hdt : mkIsDisp lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k)) = true := by
      rw [hdisp]; simp [hl0, hk5]
    have hD : mkLvlCheckD lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
        (k - mkLo lay.val (mkCi lay.val k)) = true := by
      simp only [mkLvlCheck, hdt, if_true] at hlvl; exact hlvl
    obtain ⟨t1, ht1⟩ := spec_run hD s hpc0 hkn0 (by simp [mkLvlSpecD]) (by simp)
    have hleaf0 : (route index lay).1 < 4096 := by rw [hl0] at hleaf; simpa [hL] using hleaf
    have hpc1 : t1.pc = pcOf (mkTab 0 1 + mkSh 0 1 (route index lay).1) := by
      rw [ht1.spc mkDispTgt rfl, dispTgt_eval _ hleaf0 s (by rw [h23, hl0])]
    have hkn1 : KnownOK (mkKc 0) t1 := fun p hp => ht1.known p (List.mem_append_left _ (by rw [hl0]; exact hp))
    have hent := mkEnt_of (mkBlockCheck_at 0 1 (mkSh 0 1 (route index lay).1) (by decide) (by decide) (mkSh_lt _ _ _))
    obtain ⟨t, ht⟩ := spec_run hent t1 hpc1 hkn1 (by simp [mkEntSpec]) (by simp)
    have hst : Steps image s (mkLvlSt lay.val k) (mkLvlSt lay.val k) t := by
      have := ht1.steps.trans ht.steps
      simp only [mkLvlSpecD, mkEntSpec, hlk] at this
      rw [show mkLvlSt lay.val k = mkBody lay.val k + 3 + 2 by simp [mkLvlSt,hl0,hk5,mkMove]]
      exact this
    have hmem : ∀ A, t.getMem A =
        memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k) A := by
      intro A
      rw [ht.mem]
      show memEval t1 [] A = _
      rw [memEval_nil, ht1.mem]
      show memEval s (mkLvlMem _ _ _ (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)))) A = _
      rw [hlk]
    have hkt1 : KnownOK (mkLvlPostD lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k))) t1 := ht1.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay.val k) := by
      rw [ht.keep .x10 (by simp [mkEntKeep])]
      have := hkt1 (.x10, BitVec.ofNat 64 (mkBlk lay.val (mkLo lay.val (mkCi lay.val k) +
        (k - mkLo lay.val (mkCi lay.val k))))) (by simp [mkLvlPostD])
      rw [this, hlk]
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := by
      rw [ht.keep .x11 (by simp [mkEntKeep])]
      exact hkt1 (.x11, 64) (by simp [mkLvlPostD])
    have hkt : KnownOK (mkEntPost 0 1 (mkSh 0 1 (route index lay).1)) t := ht.known
    have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkCur lay.val (k + 1) ((route index lay).1 / 2 ^ (k + 1) % 2)) := by
      have hb : mkSh 0 1 (route index lay).1 % 2 = (route index lay).1 / 64 % 2 := by
        have := mkSh_bit 0 1 (route index lay).1 0 (by decide)
        rw [show mkLo 0 1 = 6 from rfl] at this
        simpa using this
      rw [hkt (.x12, BitVec.ofNat 64 (mkCur 0 (mkLo 0 1) (mkSh 0 1 (route index lay).1 % 2))) (by simp [mkEntPost]),
        hl0, hk5, show mkLo 0 1 = 6 from rfl, hb]
      rfl
    obtain ⟨hinp, horig⟩ := lvl_input w pk index lay u hidx hs7 ht5 k hk v s t hs hmem h10 h11
    have hglob : Glob baseK w pk t := ht.glob _ _ _ (ht1.glob _ _ _ hs.glob (RelOK.nil s)) (RelOK.nil t1)
    have hknown : KnownOK (mkKc lay.val ++ [(.x11, 64)]) t := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hkt p (by rw [← hl0]; simp [mkEntPost, hp])
      · simp only [List.mem_singleton] at hp; subst hp; exact h11
    have hkeep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r := by
      intro r hr
      rw [ht.keep r (mkKeep_sub _ r hr), ht1.keep r (mkKeep_sub _ r hr)]; exact hs.keep r hr
    have hkp4 : Reg.x4 ∈ mkLvlKeep (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k))) := by
      rw [hlk]; simp [mkLvlKeep, hk5]
    have h4 : t.getReg .x4 = StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay.val)) 4 (u.getReg .x30) := by
      rw [ht.keep .x4 (by simp [mkEntKeep]), ht1.keep .x4 (List.mem_append_right _ hkp4)]
      exact hs.x4 (by omega)
    have hk6 : k + 1 < hL lay.val := by rw [hl0, hk5]; decide
    refine ⟨t, hst, ht.ecall rfl, hknown (.x5, 0) (by simp [mkKc, baseK]),
      hashArgs_of t _ 64 _ h10 h11 h12 (by unfold mkBlk; omega) (by decide) (by unfold mkBlk; omega)
        (by have := mkBit_lt (route index lay).1 (k + 1); have := (mkBo_facts lay.val (k + 1) hlay hk6).1
            unfold mkCur mkBlk; omega)
        (by have := mkBit_lt (route index lay).1 (k + 1); have := (mkBo_facts lay.val (k + 1) hlay hk6).2.2.1
            unfold mkCur mkBlk; omega), hinp, fun a => ?_⟩
    obtain ⟨hA1, -⟩ := lvl_after w pk lay.val (route index lay).1 u hlay k hk t hglob hknown hkeep h4 horig a
    refine ⟨fun _ => hA1 hk6 ?_ h12, fun h => absurd h (by omega)⟩
    rw [ht.pc rfl]
    simp only [mkEntSpec, mkEc, hl0, hk5, show mkCi 0 6 = 1 from rfl, show mkLo 0 1 = 6 from rfl]
    rfl
  · -- an ordinary level
    have hdf : mkIsDisp lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k)) = false := by
      rw [hdisp]; exact decide_eq_false hd
    have hN : mkLvlCheckN lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
        (k - mkLo lay.val (mkCi lay.val k)) = true := by
      simp only [mkLvlCheck, hdf, Bool.false_eq_true, if_false] at hlvl; exact hlvl
    have hknN : KnownOK (mkLvlKN lay.val (mkCi lay.val k)
        (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k-mkLo lay.val (mkCi lay.val k))) s := by
      intro p hp
      simp only [mkLvlKN,List.mem_append] at hp
      rcases hp with hp | hp
      · exact hkn0 p hp
      · split_ifs at hp with hret
        · simp only [List.mem_singleton] at hp
          subst p
          have hk11 : k=11 := by omega
          rw [hs.dstReg]
          simp only [hret.1,hk11]
          rw [show mkCi 0 11=1 from rfl,mkDst_chunk]
          rfl
        · simp at hp
    obtain ⟨t, ht⟩ := spec_run hN s hpc0 hknN (by simp [mkLvlSpecN]) (by simp)
    have hst : Steps image s (mkLvlSt lay.val k) (mkLvlSt lay.val k) t := by
      have := ht.steps
      simp only [mkLvlSpecN, hlk] at this
      rw [mkLvlSt_ne _ _ hd]; exact this
    have hmem : ∀ A, t.getMem A =
        memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k) A := by
      intro A; rw [ht.mem]; simp only [mkLvlSpecN, hlk]
    have hkt : KnownOK (mkLvlPostN lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
        (k - mkLo lay.val (mkCi lay.val k))) t := ht.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay.val k) := by
      have := hkt (.x10, BitVec.ofNat 64 (mkBlk lay.val (mkLo lay.val (mkCi lay.val k) +
        (k - mkLo lay.val (mkCi lay.val k))))) (by simp [mkLvlPostN])
      rw [this, hlk]
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := hkt (.x11, 64) (by simp [mkLvlPostN])
    have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkNextA2 lay.val (mkCi lay.val k)
        (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k))) :=
      hkt (.x12, BitVec.ofNat 64 (mkNextA2 lay.val (mkCi lay.val k)
        (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k)))) (by simp [mkLvlPostN])
    obtain ⟨hinp, horig⟩ := lvl_input w pk index lay u hidx hs7 ht5 k hk v s t hs hmem h10 h11
    have hglob : Glob baseK w pk t := ht.glob _ _ _ hs.glob (RelOK.nil s)
    have hknown : KnownOK (mkKc lay.val ++ [(.x11, 64)]) t := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hkt p (by simp [mkLvlPostN, hp])
      · simp only [List.mem_singleton] at hp; subst hp; exact h11
    have hkeep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r := by
      intro r hr; rw [ht.keep r (mkKeep_sub _ r hr)]; exact hs.keep r hr
    -- BIG2: level 0's `ld tp` merges the header word 0; later levels keep `tp`
    have h4 : t.getReg .x4 = StoreKind.merge .w (BitVec.ofNat 64 (hw 3 lay.val)) 4 (u.getReg .x30) := by
      by_cases hk0 : k = 0
      · have hreg : mkLvlRegs lay.val (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k))) =
            [(.x4, mkX4 lay.val)] := by
          rw [hlk, hk0]; simp [mkLvlRegs]
        have hr : t.getReg .x4 = (mkX4 lay.val).eval s :=
          ht.regs (.x4, mkX4 lay.val) (by simp only [mkLvlSpecN]; rw [hreg]; exact List.mem_singleton.mpr rfl)
        rw [hr, mkX4_eval, hs.keep .x30 (by simp [mkKeep])]
      · have hkp4 : Reg.x4 ∈ mkLvlKeep (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k))) := by
          rw [hlk]; simp [mkLvlKeep, hk0]
        rw [ht.keep .x4 (List.mem_append_right _ (List.mem_cons_of_mem _ hkp4))]
        exact hs.x4 hk0
    have hpcT : t.pc = pcOf (mkShp lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) +
        mkOff lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k) + 1) + mkMove lay.val k) := by
      have h := ht.pc rfl
      simpa only [mkLvlSpecN,hlk] using h
    -- the HASH destination: the next level's current slot or the root destination
    have hdst : ∃ d, t.getReg .x12 = BitVec.ofNat 64 d ∧ d % 8 = 0 ∧ d + 32 ≤ 2 ^ 24 := by
      by_cases hk1 : k + 1 < hL lay.val
      · obtain ⟨hn1, hn2, hn3⟩ := hnext hk1 hd
        refine ⟨_, h12, ?_⟩
        have := (mkBo_facts lay.val (k + 1) hlay hk1)
        simp only [mkNextA2, if_pos hn3, mkCur, mkBlk]
        have := mkBit_lt (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k) + 1)
        rw [show mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)) + 1 = k + 1 by omega]
        omega
      · have hk1' : k + 1 = hL lay.val := by omega
        obtain ⟨-, hn2, -⟩ := hlast hk1'
        refine ⟨_, h12, ?_⟩
        simp only [mkNextA2, if_neg hn2]
        have hm : mkSh lay.val (mkCi lay.val k) (route index lay).1 / 32 % 2 < 2 := Nat.mod_lt _ (by decide)
        split <;> omega
    obtain ⟨d, hd12, hd8, hd32⟩ := hdst
    refine ⟨t, hst, ht.ecall rfl, hknown (.x5, 0) (by simp [mkKc, baseK]),
      hashArgs_of t _ 64 _ h10 h11 hd12 (by unfold mkBlk; omega) (by decide) (by unfold mkBlk; omega) hd8 hd32,
      hinp, fun a => ?_⟩
    obtain ⟨hA1, hA2⟩ := lvl_after w pk lay.val (route index lay).1 u hlay k hk t hglob hknown hkeep h4 horig a
    refine ⟨fun hk1 => hA1 hk1 ?_ ?_, fun hk1 => hA2 hk1 ?_ ?_⟩
    · obtain ⟨hn1, hn2, hn3⟩ := hnext hk1 hd
      rw [hpcT,mkMove_next _ _ hk1]; unfold mkEc; rw [hn1, hn2]
    · obtain ⟨hn1, hn2, hn3⟩ := hnext hk1 hd
      rw [h12]; simp only [mkNextA2, if_pos hn3]
      rw [mkSh_bit _ _ _ _ hn3, show mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)) + 1 = k + 1 by omega,
        show mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k) + 1) = k + 1 by omega]
    · obtain ⟨hl1, hl2, hl3⟩ := hlast hk1
      rw [hpcT,mkMove_last _ _ hk1]; unfold mkFin; rw [← hl1, hl3]
    · obtain ⟨hl1, hl2, hl3⟩ := hlast hk1
      rw [h12]; simp only [mkNextA2, if_neg hl2]
      by_cases h0 : lay.val = 0
      · have hk11 : k=11 := by norm_num [h0,hL] at hk1; omega
        simp only [h0,hk11,if_true]
        rw [show mkCi 0 11=1 from rfl,mkDst_chunk]
      · simp [h0,mkDst]

/-! ## The levels -/

/-- Cycles from after HASH `k` through the `n` remaining levels (each: its instructions and one 1-block HASH). -/
def mkCycR (lay : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => mkLvlSt lay k + 8 + mkCycR lay (k + 1) n

/-- Steps (fuel) of the same. -/
def mkFuelR (lay : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => mkLvlSt lay k + 1 + mkFuelR lay (k + 1) n

/-- **The levels**: from `MAfter … k v s`, the remaining `n = h - k` levels refine the rest of `merkleP`'s fold. -/
theorem merkle_rest (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState) (hidx : index < 2 ^ 31)
    (hs7 : u.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1))
    (ht5 : u.getReg .x30 = BitVec.ofNat 64 (route index lay).2)
    (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ root t, MkEnd w pk lay.val (route index lay).1 u root t → GoodQ t N C Q A (K root)) :
    ∀ n k v s, k + n = hL lay.val → 0 < n → MAfter w pk lay.val (route index lay).1 u k v s →
      GoodQ s (N + mkFuelR lay.val k n) (C + mkCycR lay.val k n) Q (A + mkCycR lay.val k n)
        (ccM ((List.range' k n).foldlM (mkStep w index lay) v) K) := by
  intro n
  induction n with
  | zero => intro k v s _ h; omega
  | succ m ih =>
    intro k v s hkn _ hs
    have hk : k < hL lay.val := by omega
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := lvl_step w pk index lay u hidx hs7 ht5 k hk v s hs
    rw [List.range'_succ, List.foldlM_cons, mkStep_eq]
    have H : ∀ a : BitVec 256, GoodQ (writeHash t a) (N + mkFuelR lay.val (k + 1) m) (C + mkCycR lay.val (k + 1) m) Q
        (A + mkCycR lay.val (k + 1) m)
        (ccM ((fun v' => (List.range' (k + 1) m).foldlM (mkStep w index lay) v') (a.extractLsb' 0 128)) K) := by
      intro a
      by_cases hm : m = 0
      · subst hm
        simp only [List.range'_zero, List.foldlM_nil, ccM_pure, mkFuelR, mkCycR, Nat.add_zero]
        exact hK _ _ ((hpost a).2 (by omega))
      · exact ih (k + 1) _ _ (by omega) (by omega) ((hpost a).1 (by omega))
    have hg := GoodQ.shortHash_bind (f := fun v' => (List.range' (k + 1) m).foldlM (mkStep w index lay) v') hf h5 hv hin H
    rw [mkIn_blocks] at hg
    simp only [mkFuelR, mkCycR]
    exact GoodQ.steps' hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)

/-! ## From `LeafOut` -/

/-- Steps of a layer's Merkle phase: the entry (2), the leaf-pk HASH (1), the levels. -/
def mkFuel (lay : Nat) : Nat := 3 + mkFuelR lay 0 (hL lay)
/-- Cycles of a layer's Merkle phase: the entry (2), the leaf-pk HASH (`8 · lfBlocks`), the levels. -/
def mkCyc (lay : Nat) : Nat := 2 + 8 * lfBlocks lay + mkCycR lay 0 (hL lay)

theorem mkCyc_vals : mkCyc 0 = 273 ∧ mkCyc 1 = 181 ∧ mkCyc 2 = 168 ∧ mkCyc 3 = 168 := by decide
theorem mkFuel_vals : mkFuel 0 = 78 ∧ mkFuel 1 = 45 ∧ mkFuel 2 = 39 ∧ mkFuel 3 = 39 := by decide

theorem mkBits_stabBits (lay : Nat) (hlay : lay < 4) : mkBits lay 0 = stabBits lay := by
  interval_cases lay <;> decide

/-- **The Merkle phase of a layer** (V3): from V1's `LeafOut`, the shape block(s) of the leaf refine
`leafHash lay tree leaf ends >>= merkleP w index lay` with fuel `mkFuel lay` and exactly `mkCyc lay` cycles on every
path (273 / 181 / 168 / 168 for layers 0..3), continued by `K` at `MkEnd`. -/
theorem merkle_good (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (ends : List Digest) (u : MachineState)
    (hidx : index < 2 ^ 31) (hu : LeafOut w pk index lay ends u)
    (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ root t, MkEnd w pk lay.val (route index lay).1 u root t → GoodQ t N C Q A (K root)) :
    GoodQ u (N + mkFuel lay.val) (C + mkCyc lay.val) Q (A + mkCyc lay.val)
      (ccM (leafHash lay (route index lay).2 (route index lay).1 ends >>= merkleP w index lay) K) := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  have hkU : KnownOK (lfK lay.val) u := hu.glob.1
  have hknown : KnownOK (mkKc lay.val) u := fun p hp => hkU p (lfK_mkK _ p (mkKc_mkK _ p hp))
  have hhL : 0 < hL lay.val := by interval_cases lay.val <;> decide
  -- the table word and the first `addi a2`
  have hent := mkEnt_of (mkBlockCheck_at lay.val 0 (mkSh lay.val 0 (route index lay).1) hlay
    (by unfold mkNch; split <;> omega) (mkSh_lt _ _ _))
  have hpc : u.pc = pcOf (mkTab lay.val 0 + mkSh lay.val 0 (route index lay).1) := by
    rw [hu.pc]
    have e1 : mkTab lay.val 0 = stabIdx lay.val := by simp [mkTab]
    have e2 : mkSh lay.val 0 (route index lay).1 = (route index lay).1 % 2 ^ stabBits lay.val := by
      simp only [mkSh, show mkLo lay.val 0 = 0 by simp [mkLo], Nat.pow_zero, Nat.div_one, mkBits_stabBits _ hlay]
    rw [e1, e2]
  obtain ⟨t, ht⟩ := spec_run hent u hpc hknown (by simp [mkEntSpec]) (by simp)
  have hmem : ∀ A, t.getMem A = u.getMem A := fun A => by rw [ht.mem]; rfl
  have h10u : u.getReg .x10 = BitVec.ofNat 64 (lfBase lay.val) :=
    hkU (.x10, BitVec.ofNat 64 (if lay.val = 0 then 512 else 768)) (by simp [lfK, postLf])
  have h11u : u.getReg .x11 = BitVec.ofNat 64 (lfBytes lay.val) :=
    hkU (.x11, BitVec.ofNat 64 (if lay.val = 0 then 896 else 704)) (by simp [lfK, postLf])
  have h10 : t.getReg .x10 = u.getReg .x10 := ht.keep .x10 (by simp [mkEntKeep])
  have h11 : t.getReg .x11 = u.getReg .x11 := ht.keep .x11 (by simp [mkEntKeep])
  have hkt : KnownOK (mkEntPost lay.val 0 (mkSh lay.val 0 (route index lay).1)) t := ht.known
  have hb0 : mkSh lay.val 0 (route index lay).1 % 2 = (route index lay).1 / 2 ^ 0 % 2 := by
    have := mkSh_bit lay.val 0 (route index lay).1 0 (by unfold mkBits; split <;> [decide; (interval_cases lay.val <;> decide)])
    simpa [mkLo] using this
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkCur lay.val 0 ((route index lay).1 / 2 ^ 0 % 2)) := by
    rw [hkt (.x12, BitVec.ofNat 64 (mkCur lay.val (mkLo lay.val 0) (mkSh lay.val 0 (route index lay).1 % 2)))
      (by simp [mkEntPost]), hb0, show mkLo lay.val 0 = 0 by simp [mkLo]]
  obtain ⟨hB8, hBlo, hBhi, hBase, -, -, hBtop⟩ := mkBo_facts lay.val 0 hlay hhL
  have hb := mkBit_lt (route index lay).1 0
  have hd : mkCur lay.val 0 ((route index lay).1 / 2 ^ 0 % 2) + 32 < 2 ^ 64 := by unfold mkCur mkBlk; omega
  have hin : hashInput t = toQ (pad64 (leafInput lay (route index lay).2 (route index lay).1 ends)) := by
    rw [mkHashInput_congr h10 h11 hmem]; exact hu.hashInput.1
  have hv : hashArgumentsValid t = true := by
    refine hashArgs_of t (lfBase lay.val) (lfBytes lay.val) _ (h10.trans h10u) (h11.trans h11u) h12
      (by unfold lfBase; split <;> decide) (by unfold lfBytes; split <;> decide) (by unfold lfBase lfBytes; split <;> decide)
      (by unfold mkCur mkBlk; omega) (by unfold mkCur mkBlk; omega)
  have hG : Glob baseK w pk t := ht.glob _ _ _ hu.glob (RelOK.nil u)
  -- after the leaf-pk HASH: `MAfter 0`
  have H : ∀ a : BitVec 256, GoodQ (writeHash t a) (N + mkFuelR lay.val 0 (hL lay.val))
      (C + mkCycR lay.val 0 (hL lay.val)) Q (A + mkCycR lay.val 0 (hL lay.val))
      (ccM (merkleP w index lay (a.extractLsb' 0 128)) K) := by
    intro a
    have hA : MAfter w pk lay.val (route index lay).1 u 0 (a.extractLsb' 0 128) (writeHash t a) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd rfl h⟩
      · rw [writeHash_pc, ht.pc rfl, pcOf_add4]
        simp only [mkEntSpec, mkEc, show mkCi lay.val 0 = 0 by simp [mkCi], show mkLo lay.val 0 = 0 by simp [mkLo]]
        rfl
      · exact Glob_writeHash hG a _ h12 (safeDest_hi _ (by unfold mkCur mkBlk WLO WIT; omega)
          (by unfold mkCur mkBlk; omega) (by unfold mkCur mkBlk; omega))
      · intro p hp
        rw [writeHash_getReg]
        have hp' : p ∈ mkK lay.val := by simpa [mkLvlK] using hp
        rcases mkK_cases _ p hp' with hp'' | hp''
        · exact hkt p (List.mem_append_left _ hp'')
        · -- `tp = T(3)`'s word 0, kept from the leaf-pk block (BIG2)
          rw [ht.keep p.1 (by rw [hp'']; simp [mkEntKeep])]
          exact hkU p (lfK_mkK _ p hp')
      · intro r hr; rw [writeHash_getReg]; exact ht.keep r (mkKeep_sub _ r hr)
      · exact DigAt.writeHash_lo t a _ h12 hd
      · have hO : Orig w (fun o => 11288 ≤ o ∧ o < layerBase lay + 64 * height lay) t :=
          hu.orig.frame (fun j _ _ => hmem _)
        have hw2 := Orig_writeHash hO a _ h12 hd
        exact hw2.mono (fun o ⟨h1, h2, h3⟩ => ⟨⟨h1, by rw [layerBase_add]; omega⟩, by unfold WIT; omega⟩)
      · rw [writeHash_getReg]; exact h12
    rw [merkleP_eq, List.range_eq_range', ← hL_eq]
    exact merkle_rest w pk index lay u hidx hu.s7 hu.t5 K N C A Q hK (hL lay.val) 0 _ _ (by omega) hhL hA
  have h5 : t.getReg .x5 = 0 := hkt (.x5, 0) (by simp [mkEntPost, mkKc, baseK])
  have hg := GoodQ.shortHash_bind (f := merkleP w index lay) (K := K) (ht.ecall rfl) h5 hv hin H
  rw [hu.hashInput.2] at hg
  rw [leafHash_eq]
  have hst := ht.steps
  simp only [mkEntSpec] at hst
  exact GoodQ.steps' hst hg (by unfold mkFuel; omega) (by unfold mkCyc; omega) (fun q => ⟨q, by unfold mkCyc; omega⟩)

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart87
