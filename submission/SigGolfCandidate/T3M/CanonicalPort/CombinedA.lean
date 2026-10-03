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

/-- The encoding block `[L | T(4) | LE32 c | pad | R]` (E8: one full block, `pad64` is the identity). -/
theorem encodingInput_length' (lay : Layer) (tree leaf : Nat) (msg : T3.LayerMessage) (c : BitVec 32) :
    (T3.encodingInput lay tree leaf msg c).length = 64 := by
  simp only [T3.encodingInput, List.length_append, bytesLE_length]

theorem pad64_encodingInput (lay : Layer) (tree leaf : Nat) (msg : T3.LayerMessage) (c : BitVec 32) :
    pad64 (T3.encodingInput lay tree leaf msg c) = T3.encodingInput lay tree leaf msg c :=
  pad64_of_aligned _ (by rw [encodingInput_length'])

theorem readLE_bytesLE4_pad (c : BitVec 32) : T3.readLE (bytesLE 4 c ++ List.replicate 4 0) = c.toNat := by
  rw [readLE_append, readLE_bytesLE, readLE_replicate_zero]
  simp

theorem readLE_ctr_pad (c : BitVec 32) (p : BitVec 96) :
    T3.readLE (bytesLE 4 c ++ bytesLE 12 p) = c.toNat + 4294967296 * p.toNat := by
  rw [readLE_append, readLE_bytesLE, readLE_bytesLE, bytesLE_length]
  norm_num

theorem wordsOf_ctr_pad (c : BitVec 32) (p : BitVec 96) :
    wordsOf (bytesLE 4 c ++ bytesLE 12 p) =
      [BitVec.ofNat 64 (c.toNat + 2 ^ 32 * (p.toNat % 2 ^ 32)), BitVec.ofNat 64 (p.toNat / 2 ^ 32)] := by
  rw [wordsOf_eq_range 2 _ (by simp only [List.length_append, bytesLE_length]), readLE_ctr_pad]
  have hc := c.isLt
  have hp := p.isLt
  simp only [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  norm_num at hc hp ⊢
  constructor <;> apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem wordsOf_encodingInput (lay : Layer) (tree leaf : Nat) (msg : T3.LayerMessage) (c : BitVec 32) :
    wordsOf (pad64 (T3.encodingInput lay tree leaf msg c)) =
      [dlo msg.1, dhi msg.1, BitVec.ofNat 64 (hdr0 4 lay.val tree 0), BitVec.ofNat 64 (hdr1 tree leaf),
        BitVec.ofNat 64 (c.toNat + 2 ^ 32 * (msg.2.1.toNat % 2 ^ 32)), BitVec.ofNat 64 (msg.2.1.toNat / 2 ^ 32),
        dlo msg.2.2, dhi msg.2.2] := by
  rw [pad64_encodingInput]
  unfold T3.encodingInput
  have e : bytesLE 16 msg.1 ++ bytesLE 16 (header 4 lay.val tree 0 leaf) ++ bytesLE 4 c ++ bytesLE 12 msg.2.1 ++
      bytesLE 16 msg.2.2 = bytesLE 16 msg.1 ++ (bytesLE 16 (header 4 lay.val tree 0 leaf) ++
        ((bytesLE 4 c ++ bytesLE 12 msg.2.1) ++ bytesLE 16 msg.2.2)) := by
    simp only [List.append_assoc]
  rw [e, wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_append _ _ (by simp only [bytesLE_length]),
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]), wordsOf_bytesLE16, wordsOf_header,
    wordsOf_ctr_pad, wordsOf_bytesLE16]
  rfl

theorem blocks_encodingInput (lay : Layer) (tree leaf : Nat) (msg : T3.LayerMessage) (c : BitVec 32) :
    (toQ (pad64 (T3.encodingInput lay tree leaf msg c))).blocks = 1 := by
  have hl : (pad64 (T3.encodingInput lay tree leaf msg c)).length = 64 := by
    rw [pad64_encodingInput, encodingInput_length']
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
