import SigGolfCandidate.T3M.Search.TopUnpackLoop

namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem init_inv {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (v : Digest) (hpc : s.pc=pcOf (b+362))
    (h6 : s.getReg .x6=BitVec.ofNat 64 v.toNat)
    (h7 : s.getReg .x7=BitVec.ofNat 64 (v.toNat/2^64))
    (h30 : s.getReg .x30=BitVec.ofNat 64 TOP_DATA) :
    ∃ t, Steps image s 4 4 t ∧ Inv b s v 0 t := by
  obtain ⟨t,hs,hp,h20,h21,h30',hr,hf⟩ := init_spec hK s hpc
  refine ⟨t,hs,⟨by omega,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · simpa using hp
  · simpa using (hr.get (r:=.x6) (by decide)).trans h6
  · simpa using (hr.get (r:=.x7) (by decide)).trans h7
  · exact h20
  · simpa using h21
  · rw [h30',h30,ofNat_add_ofNat]
  · intro j hj; omega
  · exact hr.mono (by decide)
  · exact hf.mono (by simp)

theorem iter {image : Image} {b : Nat} (hK : KernAt image b) {s t : MachineState}
    (ht : TableOK s) (v : Digest) (hvalid : T3.topRanksValid v=true)
    (hI : Inv b s v 0 t) (n : Nat) (hn : n≤17) :
    ∃ u, Steps image t (17*n) (17*n) u ∧ Inv b s v n u := by
  induction n with
  | zero => exact ⟨t,Steps.refl t,hI⟩
  | succ n ih =>
      obtain ⟨u,hs,hu⟩ := ih (by omega)
      obtain ⟨w,hw,hwI⟩ := body hK ht v hvalid n (by omega) hu
      exact ⟨w,(hs.trans hw).of_eq (by omega) (by omega),hwI⟩

end SigGolfCandidate.T3M.Search.TopUnpack
