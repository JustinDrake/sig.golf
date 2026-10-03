import SigGolfCandidate.T3M.Verify.CanonicalInit
import SigGolfCandidate.T3M.Verify.CanonicalForest

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput attemptLimit pad64 digestInput)

def proSpecC : Spec := { proSpec with steps:=21,cycles:=21 }
def proPostC : List (Reg × Word) := proPost++[(.x2,BitVec.ofNat 64 TAB)]
theorem pro_checked_c :
    specB [] [] baseK (runAtC {} k0 [] 0 [.br false]) proSpecC [] proPostC []=true := by decide +kernel
theorem pro_rej_checked_c :
    specB [] [] [] (runAtC {} k0 [] 0 [.br true]) (rejSpec 12 [proBr true]) [] [] []=true := by decide +kernel

theorem hash_input_write_c (t : MachineState) (a : BitVec 256)
    (h10 : t.getReg .x10=32) (h11 : t.getReg .x11=64) (h12 : t.getReg .x12=96) :
    hashInput (writeHash t a)=hashInput t := by
  rw [hashInput_eq_words (writeHash t a) 0 (by simpa [writeHash_getReg] using h11)
      (by decide) (by simp [writeHash_getReg,h10]),
    hashInput_eq_words t 0 (by simpa using h11) (by decide) (by simp [h10])]
  simp only [writeHash_getReg,h10,Nat.zero_add,Nat.mul_one,
    show (32 : Word)=BitVec.ofNat 64 32 by decide]
  rw [SigGolfCandidate.T3M.Verify.readWords_eight (writeHash t a) 32 (by decide),
    SigGolfCandidate.T3M.Verify.readWords_eight t 32 (by decide)]
  have hf : ∀ b, b+8≤96 → (writeHash t a).getMem (BitVec.ofNat 64 b)=t.getMem (BitVec.ofNat 64 b) :=
    fun b hb => writeHash_frame t a 96 b h12 (by omega) (by decide) (Or.inl hb)
  rw [hf 32 (by decide),hf 40 (by decide),hf 48 (by decide),hf 56 (by decide),
    hf 64 (by decide),hf 72 (by decide),hf 80 (by decide),hf 88 (by decide)]

/-- After the prologue, before the digest `ECALL`: `s2`, `t0`, the HASH arguments, the digest block. -/
structure DgPreC (m : T3.Message) (pk : Digest) (w : WBytes) (t : MachineState) : Prop where
  pc : t.pc = pcOf 17
  known : KnownOK proPostC t
  wit : WitAll w t
  pk : PkOK pk t
  zero : ∀ A, A < WIT → (A < 0x20 ∨ (0x60 ≤ A ∧ A < 0xA0) ∨ 0xB0 ≤ A) → t.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK t
  sp : t.getReg .x2 = BitVec.ofNat 64 TAB
  tables : TablesOK t

/-- After the digest `HASH` (answer `a`, the output `N` at `0x60`). -/
structure DgOutC (m : T3.Message) (pk : Digest) (w : WBytes) (a : HashOutput) (u : MachineState) : Prop where
  pc : u.pc = pcOf 18
  known : KnownOK proPostC u
  wit : WitAll w u
  pk : PkOK pk u
  nwords : ∀ k, k < 4 → u.getMem (BitVec.ofNat 64 (0x60 + 8 * k)) = a.extractLsb' (64 * k) 64
  zero : ∀ A, A < WIT → (A < 0x20 ∨ (0x80 ≤ A ∧ A < 0xA0) ∨ 0xB0 ≤ A) → u.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK u
  sp : u.getReg .x2 = BitVec.ofNat 64 TAB
  tables : TablesOK u
  input : hashInput u=toQ (pad64 (digestInput (wrho w) m (wdc w)))

theorem digest_step (m : T3.Message) (pk : Digest) (w : WBytes) (s : MachineState) (hs : InitC m pk w s) :
    ((wdc w).toNat ≥ attemptLimit → ∃ u, Steps fixture s 12 12 u ∧ fetch fixture u = some (.base .ECALL) ∧
        u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    ((wdc w).toNat < attemptLimit → ∃ t, Steps fixture s 21 21 t ∧ fetch fixture t = some (.base .ECALL) ∧
        hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (digestInput (wrho w) m (wdc w))) ∧
        DgPreC m pk w t) := by
  have hk : KnownOK k0 s := hs.known
  constructor
  · intro hge
    obtain ⟨u, hu⟩ := spec_runC pro_rej_checked_c s hs.pc hk (by
      intro b hb; simp only [rejSpec, List.mem_singleton] at hb; subst hb
      exact (proBr_iff w s hs.wit true).mpr (by simp [hge])) (by simp)
    exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, SigGolfCandidate.T3M.Verify.cw 1) (by simp [rejSpec]),
      hu.regs (.x10, SigGolfCandidate.T3M.Verify.cw 1) (by simp [rejSpec])⟩
  · intro hlt
    obtain ⟨t, ht⟩ := spec_runC pro_checked_c s hs.pc hk (by
      intro b hb; simp only [proSpecC,proSpec, List.mem_singleton] at hb; subst hb
      exact (proBr_iff w s hs.wit false).mpr (by simp; omega)) (by simp)
    have hm : ∀ A, t.getMem A = memEval s proSpecC.mem A := ht.mem
    have hkt : KnownOK proPostC t := ht.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 32 := hkt (.x10, 32) (by simp [proPostC,proPost])
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := hkt (.x11, 64) (by simp [proPostC,proPost])
    have h12 : t.getReg .x12 = BitVec.ofNat 64 96 := hkt (.x12, 96) (by simp [proPostC,proPost])
    have frame : ∀ A, A < 2 ^ 64 → A ≠ 0x20 → A ≠ 0x28 → A ≠ 0x30 → A ≠ 0x38 →
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3 h4
      rw [hm]
      apply memEval_frame_ofNat s _ A hA
      intro p hp
      simp only [proSpecC,proSpec, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨rfl, by simpa using fun h => by omega⟩
    refine ⟨t, ht.steps, ht.ecall rfl, ?_, ?_, ?_⟩
    · exact hashArgs_of t 32 64 96 h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
    · have hl := digestInput_length (wrho w) m (wdc w)
      rw [pad64_digestInput]
      apply hashInput_words8 t _ 32 hl h10 (by decide) (by decide) h11
      rw [wordsOf_digestInput]
      have e20 : t.getMem (BitVec.ofNat 64 32) = dlo (wrho w) := by
        rw [hm]; simp only [proSpecC,proSpec, memEval, Addr.eval]
        simp only [show (BitVec.ofNat 64 32 = BitVec.ofNat 64 0x28) = False by decide,
          show (BitVec.ofNat 64 32 = BitVec.ofNat 64 0x20) = True by decide, if_true, if_false, E.eval]
        have h0 : s.getMem (BitVec.ofNat 64 0x800) = wword w 0 := hs.wit 0 (by unfold WX; omega)
        rw [h0]
        exact (wdig_lo w 0).symm
      have e28 : t.getMem (BitVec.ofNat 64 (32 + 8)) = dhi (wrho w) := by
        rw [hm]; simp only [proSpecC,proSpec, memEval, Addr.eval]
        simp only [show (BitVec.ofNat 64 (32 + 8) = BitVec.ofNat 64 0x28) = True by decide, if_true, E.eval]
        have h1 : s.getMem (BitVec.ofNat 64 0x808) = wword w 1 := hs.wit 1 (by unfold WX; omega)
        rw [h1]
        exact (wdig_hi w 0).symm
      have e30 : t.getMem (BitVec.ofNat 64 (32 + 16)) = BitVec.ofNat 64 (hdr0 12 0 0 0) := by
        rw [hm]; simp only [proSpecC,proSpec, memEval, Addr.eval]
        simp only [show (BitVec.ofNat 64 (32 + 16) = BitVec.ofNat 64 0x28) = False by decide,
          show (BitVec.ofNat 64 (32 + 16) = BitVec.ofNat 64 0x20) = False by decide,
          show (BitVec.ofNat 64 (32 + 16) = BitVec.ofNat 64 0x30) = True by decide, if_true, if_false, E.eval]
        rfl
      have e38 : t.getMem (BitVec.ofNat 64 (32 + 24)) = BitVec.ofNat 64 (hdr1 0 (wdc w).toNat) := by
        rw [hm]; simp only [proSpecC,proSpec, memEval, Addr.eval]
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
    · refine ⟨ht.pc rfl, hkt, ?_, ?_, ?_, ?_, ?_,?_⟩
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
        exact frame A (by omega) (by unfold TAB at hA; omega)
          (by unfold TAB at hA; omega) (by unfold TAB at hA; omega)
          (by unfold TAB at hA; omega)
      · exact ht.known (.x2,BitVec.ofNat 64 TAB) (by simp [proPostC,proPost])
      · exact ht.tables hs.tables (RelOK.nil s)

theorem digest_out (m : T3.Message) (pk : Digest) (w : WBytes) (t : MachineState) (ht : DgPreC m pk w t)
    (a : HashOutput) (hin : hashInput t=toQ (pad64 (digestInput (wrho w) m (wdc w)))) : DgOutC m pk w a (writeHash t a) := by
  have h12 : t.getReg .x12 = BitVec.ofNat 64 96 := ht.known (.x12, 96) (by simp [proPostC,proPost])
  refine ⟨?_, ht.known.writeHash a, ?_, ?_, ?_, ?_, ?_, ?_,?_,?_⟩
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
      (Or.inr (by unfold TAB at hA; omega))
  · rw [writeHash_getReg]; exact ht.sp
  · exact ht.tables.hash_frame t a 96 h12 (by decide)
  · rw [hash_input_write_c t a
      (ht.known (.x10,32) (by simp [proPostC,proPost]))
      (ht.known (.x11,64) (by simp [proPostC,proPost])) h12,hin]

/-- The digest piece of `verifyP`: rejection (`dc ≥ 2^20`, HALT(1), no query) or the digest query (one block)
followed by the continuation on the post-digest state. -/
theorem digestP_good (m : T3.Message) (pk : Digest) (w : WBytes) (s : MachineState) (hs : InitC m pk w s)
    {N C A : Nat} {Q : Prop} (K : Option HashOutput → OracleComp HashSpec CanonicalPort.Verify.Obs)
    (hK : K none = pure (false, 0))
    (hcont : ∀ a u, (wdc w).toNat<attemptLimit → DgOutC m pk w a u → CanonicalPort.Verify.GoodQ u N C Q A (K (some a))) :
    CanonicalPort.Verify.GoodQ s (N + 22) (C + 29) Q (A + 29) (CanonicalPort.Verify.ccM (digestP m w) K) := by
  obtain ⟨hrej, hacc⟩ := digest_step m pk w s hs
  unfold digestP
  by_cases hdc : (wdc w).toNat ≥ attemptLimit
  · rw [if_pos hdc, CanonicalPort.Verify.ccM_pure, hK]
    obtain ⟨u, hst, hf, h5, h10⟩ := hrej hdc
    exact CanonicalPort.Verify.GoodQ.steps' hst (CanonicalPort.Verify.GoodQ.reject (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega)
      (fun q => ⟨q, by omega⟩)
  · rw [if_neg hdc, CanonicalPort.Verify.ccM_map]
    obtain ⟨t, hst, hf, hv, hin, hpre⟩ := hacc (by omega)
    unfold T3.digest
    have h5 : t.getReg .x5 = 0 := hpre.known (.x5, 0) (by simp [proPostC,proPost, baseK])
    have := CanonicalPort.Verify.GoodQ.publicHash_bind (f := pure) (K := fun a => K (some a)) hf h5 hv hin (fun a => by
      rw [CanonicalPort.Verify.ccM_pure]; exact hcont a _ (by omega) (digest_out m pk w t hpre a hin))
    rw [bind_pure, blocks_digestInput] at this
    exact CanonicalPort.Verify.GoodQ.steps' hst this (by omega) (by omega) (fun q => ⟨q, by omega⟩)


#print axioms digestP_good
end SigGolfCandidate.T3M.CanonicalNative
