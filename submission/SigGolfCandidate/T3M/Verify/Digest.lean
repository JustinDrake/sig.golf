import SigGolfCandidate.T3M.Verify.Init

/-!
# Prologue and digest (T3M verify words 0 .. 16)

`li s2, 4095; lwu gp, dc(s2); srli tp, gp, 20; bne tp, zero, rej0` (dc check, `dc < 2^20`), the header
`T(12, 0, 0, 0, dc)` at `0x30` (`w0 = 0xc01`, `w1 = dc << 32`), `rho` copied to `0x20`, then the digest HASH of the
block `[rho | T | m]` at `0x20` (one block, the message in place at `0x40`) into `N` at `0x60`.

* `proCheck`, `proRejCheck` : the two path runs (kernel-checked);
* `digest_step` : from `InitOK`, either HALT(1) after 8 steps (`dc ≥ 2^20`) or the digest `ECALL` after 16 steps with
  `hashInput = toQ (pad64 (digestInput (wrho w) m (wdc w)))`;
* **`digestP_good`** : `GoodQ` of `ccM (digestP m w) K` from the initial state, given the continuation's judgment
  on every post-digest state (`DgOut`).
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput attemptLimit pad64 digestInput)

/-- A constant symbolic word. -/
abbrev cw (k : Nat) : E := .c (BitVec.ofNat 64 k)

/-- The HALT(1) of the reject stubs (`reject: li t0, 1; li a0, 1; ecall` at word 741). -/
def rejectPc : Nat := 743

def rejSpec (steps : Nat) (brs : List Br) : Spec :=
  ⟨[(.x5, cw 1), (.x10, cw 1)], [], rejectPc, true, steps, brs, none, steps⟩

/-! ## The prologue run -/

/-- `lwu gp, dc(s2)`: the low half of witness doubleword 2. -/
def lwuDc : E := .un (.ld .wu 0) (.ld (cw 0x810))
def proBr (d : Bool) : Br := ⟨.ne, .bin .srl lwuDc (cw 20), .c 0, d⟩

def proSpec : Spec :=
  ⟨[(.x4, cw 3073)],
    [(⟨none, BitVec.ofNat 64 0x28⟩, .ld (cw 0x808)), (⟨none, BitVec.ofNat 64 0x20⟩, .ld (cw 0x800)),
      (⟨none, BitVec.ofNat 64 0x30⟩, cw 0xc01), (⟨none, BitVec.ofNat 64 0x38⟩, .bin .sll lwuDc (cw 32))],
    16, true, 16, [proBr false], none, 16⟩

def proPost : List (Reg × Word) := baseK ++ [(.x10, 32), (.x11, 64), (.x12, 96)]

theorem proCheck : specB [] [] baseK (runAt k0 [] 0 [.br false]) proSpec [] proPost [] = true := by
  decide +kernel

theorem proRejCheck : specB [] [] [] (runAt k0 [] 0 [.br true]) (rejSpec 8 [proBr true]) [] [] [] = true := by
  decide +kernel

/-! ## Semantics -/

theorem lwuDc_eval (w : WBytes) (s : MachineState) (hW : WitAll w s) :
    lwuDc.eval s = BitVec.ofNat 64 (wdc w).toNat := by
  have h2 : s.getMem (BitVec.ofNat 64 0x810) = wword w 2 := hW 2 (by unfold WX; omega)
  apply BitVec.eq_of_toNat_eq
  show (LoadKind.wu.fromWord (s.getMem (BitVec.ofNat 64 0x810)) 0).toNat = _
  rw [h2]
  simp only [LoadKind.fromWord, extractWord32, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, wword_toNat, wdc, wle32, dcOff,
    BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
  have : (w.toNat / 2 ^ (64 * 2) % 2 ^ 64 / 2 ^ (0 / 4 * 32) % 2 ^ 32) = w.toNat / 2 ^ 128 % 2 ^ 32 := by
    rw [show 0 / 4 * 32 = 0 by rfl, pow_zero, Nat.div_one, show 64 * 2 = 128 by rfl,
      Nat.mod_mod_of_dvd _ (by norm_num)]
  rw [this]

theorem dc_lt (w : WBytes) : (wdc w).toNat < 2 ^ 32 := (wdc w).isLt

theorem proBr_iff (w : WBytes) (s : MachineState) (hW : WitAll w s) (d : Bool) :
    Br.holds s (proBr d) ↔ d = decide ((wdc w).toNat ≥ attemptLimit) := by
  have hd := dc_lt w
  simp only [proBr, Br.holds, CmpOp.eval, E.eval, BinOp.eval, lwuDc_eval w s hW]
  have e : (BitVec.ofNat 64 (wdc w).toNat >>> ((BitVec.ofNat 64 20).toNat % 64)) =
      BitVec.ofNat 64 ((wdc w).toNat / 2 ^ 20) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show (wdc w).toNat < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (wdc w).toNat / 2 ^ 20 < 2 ^ 64 by omega)]
  rw [e]
  by_cases h : (wdc w).toNat ≥ attemptLimit
  · have hne : BitVec.ofNat 64 ((wdc w).toNat / 2 ^ 20) ≠ 0 := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [toNat_ofNat_lt (by omega)] at this
      unfold attemptLimit at h
      simp at this; omega
    rw [show (BitVec.ofNat 64 ((wdc w).toNat / 2 ^ 20) != (0 : Word)) = true from bne_iff_ne.mpr hne,
      decide_eq_true h]
    exact eq_comm
  · have h0 : (wdc w).toNat / 2 ^ 20 = 0 := by unfold attemptLimit at h; omega
    rw [h0, decide_eq_false h, show (BitVec.ofNat 64 0 != (0 : Word)) = false by decide]
    exact eq_comm

/-- After the prologue, before the digest `ECALL`: `s2`, `t0`, the HASH arguments, the digest block. -/
structure DgPre (m : T3.Message) (pk : Digest) (w : WBytes) (t : MachineState) : Prop where
  pc : t.pc = pcOf 16
  known : KnownOK proPost t
  wit : WitAll w t
  pk : PkOK pk t
  zero : ∀ A, A < WIT → (A < 0x20 ∨ (0x60 ≤ A ∧ A < 0xA0) ∨ 0xB0 ≤ A) → t.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK t

/-- After the digest `HASH` (answer `a`, the output `N` at `0x60`). -/
structure DgOut (m : T3.Message) (pk : Digest) (w : WBytes) (a : HashOutput) (u : MachineState) : Prop where
  pc : u.pc = pcOf 17
  known : KnownOK proPost u
  wit : WitAll w u
  pk : PkOK pk u
  nwords : ∀ k, k < 4 → u.getMem (BitVec.ofNat 64 (0x60 + 8 * k)) = a.extractLsb' (64 * k) 64
  zero : ∀ A, A < WIT → (A < 0x20 ∨ (0x80 ≤ A ∧ A < 0xA0) ∨ 0xB0 ≤ A) → u.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK u

theorem digest_step (m : T3.Message) (pk : Digest) (w : WBytes) (s : MachineState) (hs : InitOK m pk w s) :
    ((wdc w).toNat ≥ attemptLimit → ∃ u, Steps image s 8 8 u ∧ fetch image u = some (.base .ECALL) ∧
        u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    ((wdc w).toNat < attemptLimit → ∃ t, Steps image s 16 16 t ∧ fetch image t = some (.base .ECALL) ∧
        hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (digestInput (wrho w) m (wdc w))) ∧
        DgPre m pk w t) := by
  have hk : KnownOK k0 s := hs.known
  constructor
  · intro hge
    obtain ⟨u, hu⟩ := spec_run proRejCheck s hs.pc hk (by
      intro b hb; simp only [rejSpec, List.mem_singleton] at hb; subst hb
      exact (proBr_iff w s hs.wit true).mpr (by simp [hge])) (by simp)
    exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [rejSpec]),
      hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
  · intro hlt
    obtain ⟨t, ht⟩ := spec_run proCheck s hs.pc hk (by
      intro b hb; simp only [proSpec, List.mem_singleton] at hb; subst hb
      exact (proBr_iff w s hs.wit false).mpr (by simp; omega)) (by simp)
    have hm : ∀ A, t.getMem A = memEval s proSpec.mem A := ht.mem
    have hkt : KnownOK proPost t := ht.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 32 := hkt (.x10, 32) (by simp [proPost])
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := hkt (.x11, 64) (by simp [proPost])
    have h12 : t.getReg .x12 = BitVec.ofNat 64 96 := hkt (.x12, 96) (by simp [proPost])
    have frame : ∀ A, A < 2 ^ 64 → A ≠ 0x20 → A ≠ 0x28 → A ≠ 0x30 → A ≠ 0x38 →
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3 h4
      rw [hm]
      apply memEval_frame_ofNat s _ A hA
      intro p hp
      simp only [proSpec, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨rfl, by simpa using fun h => by omega⟩
    refine ⟨t, ht.steps, ht.ecall rfl, ?_, ?_, ?_⟩
    · exact hashArgs_of t 32 64 96 h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
    · have hl := digestInput_length (wrho w) m (wdc w)
      rw [pad64_digestInput]
      apply hashInput_words8 t _ 32 hl h10 (by decide) (by decide) h11
      rw [wordsOf_digestInput]
      have e20 : t.getMem (BitVec.ofNat 64 32) = dlo (wrho w) := by
        rw [hm]; simp only [proSpec, memEval, Addr.eval]
        simp only [show (BitVec.ofNat 64 32 = BitVec.ofNat 64 0x28) = False by decide,
          show (BitVec.ofNat 64 32 = BitVec.ofNat 64 0x20) = True by decide, if_true, if_false, E.eval]
        have h0 : s.getMem (BitVec.ofNat 64 0x800) = wword w 0 := hs.wit 0 (by unfold WX; omega)
        rw [h0]
        exact (wdig_lo w 0).symm
      have e28 : t.getMem (BitVec.ofNat 64 (32 + 8)) = dhi (wrho w) := by
        rw [hm]; simp only [proSpec, memEval, Addr.eval]
        simp only [show (BitVec.ofNat 64 (32 + 8) = BitVec.ofNat 64 0x28) = True by decide, if_true, E.eval]
        have h1 : s.getMem (BitVec.ofNat 64 0x808) = wword w 1 := hs.wit 1 (by unfold WX; omega)
        rw [h1]
        exact (wdig_hi w 0).symm
      have e30 : t.getMem (BitVec.ofNat 64 (32 + 16)) = BitVec.ofNat 64 (hdr0 12 0 0 0) := by
        rw [hm]; simp only [proSpec, memEval, Addr.eval]
        simp only [show (BitVec.ofNat 64 (32 + 16) = BitVec.ofNat 64 0x28) = False by decide,
          show (BitVec.ofNat 64 (32 + 16) = BitVec.ofNat 64 0x20) = False by decide,
          show (BitVec.ofNat 64 (32 + 16) = BitVec.ofNat 64 0x30) = True by decide, if_true, if_false, E.eval]
        rfl
      have e38 : t.getMem (BitVec.ofNat 64 (32 + 24)) = BitVec.ofNat 64 (hdr1 0 (wdc w).toNat) := by
        rw [hm]; simp only [proSpec, memEval, Addr.eval]
        simp only [show (BitVec.ofNat 64 (32 + 24) = BitVec.ofNat 64 0x28) = False by decide,
          show (BitVec.ofNat 64 (32 + 24) = BitVec.ofNat 64 0x20) = False by decide,
          show (BitVec.ofNat 64 (32 + 24) = BitVec.ofNat 64 0x30) = False by decide,
          show (BitVec.ofNat 64 (32 + 24) = BitVec.ofNat 64 0x38) = True by decide, if_true, if_false]
        show BinOp.eval .sll (lwuDc.eval s) (BitVec.ofNat 64 32) = _
        rw [lwuDc_eval w s hs.wit]
        simp only [BinOp.eval]
        rw [ofNat_shl' _ 32, hdr1_eq 0 _ (by norm_num) (dc_lt w)]
        congr 1
        rw [show 32 % 2 ^ 64 % 64 = 32 by norm_num]; ring
      have em : ∀ k, k < 4 → t.getMem (BitVec.ofNat 64 (32 + 32 + 8 * k)) = m.extractLsb' (64 * k) 64 := by
        intro k hk
        rw [frame _ (by omega) (by omega) (by omega) (by omega) (by omega), ← hs.msg k hk]
      rw [e20, e28, e30, e38, show 32 + 32 = 32 + 32 + 8 * 0 by rfl, em 0 (by omega),
        show 32 + 40 = 32 + 32 + 8 * 1 by rfl, em 1 (by omega), show 32 + 48 = 32 + 32 + 8 * 2 by rfl,
        em 2 (by omega), show 32 + 56 = 32 + 32 + 8 * 3 by rfl, em 3 (by omega)]
    · refine ⟨ht.pc rfl, hkt, ?_, ?_, ?_, ?_⟩
      · intro j hj
        rw [frame _ (by unfold WIT WX at *; omega) (by unfold WIT; omega) (by unfold WIT; omega)
          (by unfold WIT; omega) (by unfold WIT; omega)]
        exact hs.wit j hj
      · exact ⟨(frame 0xA0 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hs.pk.1,
          (frame 0xA8 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hs.pk.2⟩
      · intro A hA hz
        unfold WIT at hA
        rw [frame A (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hs.zero A hA (by omega)
      · apply hs.data.congr
        intro A hA hEnd
        exact frame A (by omega) (by unfold Nonbinary.PAIR_DATA at hA; omega)
          (by unfold Nonbinary.PAIR_DATA at hA; omega) (by unfold Nonbinary.PAIR_DATA at hA; omega)
          (by unfold Nonbinary.PAIR_DATA at hA; omega)

theorem digest_out (m : T3.Message) (pk : Digest) (w : WBytes) (t : MachineState) (ht : DgPre m pk w t)
    (a : HashOutput) : DgOut m pk w a (writeHash t a) := by
  have h12 : t.getReg .x12 = BitVec.ofNat 64 96 := ht.known (.x12, 96) (by simp [proPost])
  refine ⟨?_, ht.known.writeHash a, ?_, ?_, ?_, ?_, ?_⟩
  · rw [writeHash_pc, ht.pc]; rfl
  · intro j hj
    rw [writeHash_frame t a 96 _ h12 (by unfold WIT WX at *; omega) (by omega) (Or.inr (by unfold WIT; omega))]
    exact ht.wit j hj
  · exact ⟨(writeHash_frame t a 96 0xA0 h12 (by omega) (by omega) (Or.inr (by omega))).trans ht.pk.1,
      (writeHash_frame t a 96 0xA8 h12 (by omega) (by omega) (Or.inr (by omega))).trans ht.pk.2⟩
  · intro k hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · exact writeHash_at0 t a 96 h12 (by omega)
    · exact writeHash_at8 t a 96 h12 (by omega)
    · exact writeHash_at16 t a 96 h12 (by omega)
    · exact writeHash_at24 t a 96 h12 (by omega)
  · intro A hA hz
    unfold WIT at hA
    rw [writeHash_frame t a 96 A h12 (by omega) (by omega) (by omega)]
    exact ht.zero A (by unfold WIT; omega) (by omega)
  · apply ht.data.congr
    intro A hA hEnd
    exact writeHash_frame t a 96 A h12 (by omega) (by omega)
      (Or.inr (by unfold Nonbinary.PAIR_DATA at hA; omega))

/-- The digest piece of `verifyP`: rejection (`dc ≥ 2^20`, HALT(1), no query) or the digest query (one block)
followed by the continuation on the post-digest state. -/
theorem digestP_good (m : T3.Message) (pk : Digest) (w : WBytes) (s : MachineState) (hs : InitOK m pk w s)
    {N C A : Nat} {Q : Prop} (K : Option HashOutput → OracleComp HashSpec Obs)
    (hK : K none = pure (false, 0))
    (hcont : ∀ a u, DgOut m pk w a u → GoodQ u N C Q A (K (some a))) :
    GoodQ s (N + 17) (C + 24) Q (A + 24) (ccM (digestP m w) K) := by
  obtain ⟨hrej, hacc⟩ := digest_step m pk w s hs
  unfold digestP
  by_cases hdc : (wdc w).toNat ≥ attemptLimit
  · rw [if_pos hdc, ccM_pure, hK]
    obtain ⟨u, hst, hf, h5, h10⟩ := hrej hdc
    exact GoodQ.steps' hst (GoodQ.reject (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega)
      (fun q => ⟨q, by omega⟩)
  · rw [if_neg hdc, ccM_map]
    obtain ⟨t, hst, hf, hv, hin, hpre⟩ := hacc (by omega)
    unfold T3.digest
    have h5 : t.getReg .x5 = 0 := hpre.known (.x5, 0) (by simp [proPost, baseK])
    have := GoodQ.publicHash_bind (f := pure) (K := fun a => K (some a)) hf h5 hv hin (fun a => by
      rw [ccM_pure]; exact hcont a _ (digest_out m pk w t hpre a))
    rw [bind_pure, blocks_digestInput] at this
    exact GoodQ.steps' hst this (by omega) (by omega) (fun q => ⟨q, by omega⟩)

end SigGolfCandidate.T3M.Verify
