import SigGolfCandidate.T3M.Sign.BoundaryInvariant
import SigGolfCandidate.T3M.Sign.BoundaryEntry
import SigGolfCandidate.T3M.Sign.InitState
import SigGolfCandidate.T3M.Sign.WctTable
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Defs
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Fts
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Search
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Compact
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Compose
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Pending

section





namespace SigGolfCandidate.T3M.Sign.Boundary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open ClaudeWCT.W9.Machine.Sign (TableAt TBL tblBytes HookPre)
theorem sinit_wct_table (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    TableAt (sinit sk cache m) := by
  intro k hk
  rw [sinit_getMem _ _ _ _ (by unfold TBL; omega), if_neg (by unfold TBL; omega), if_neg (by unfold TBL; omega), if_neg (by unfold TBL; omega), sdata_getMem _ (by unfold TBL; omega), if_pos (by unfold SIGN_DATA TBL; omega)]
  rw [show TBL + 8 * k - SIGN_DATA = 8 * k by unfold TBL SIGN_DATA; omega, table_bytes, Images.signData]
  rw [List.drop_append_of_le_length (by rw [Images.signPrefixData_length]; omega), List.take_append_of_le_length (by rw [List.length_drop, Images.signPrefixData_length]; omega)]
theorem NoncePost.hook {sk : SecretKey} {cache : Bytes 131072} {m : Message}
    {rho : T3.Digest} {t : MachineState} (h : NoncePost sk cache m rho t) :
    HookPre sk m rho t := by
  refine ⟨⟨h.search.pc, h.search.x5, h.search.x19, h.search.rho, h.search.msg⟩, h.rho, ?_, ?_, ?_⟩
  · intro k hk
    change t.getMem (BitVec.ofNat 64 (SK + 8 * k)) = _
    rw [h.frame.get (by sg_omega) (by unfold FrontW; sg_omega)]
    exact sinit_sk sk cache m k hk
  · intro A hA
    simp only [ClaudeWCT.W9.Machine.Sign.ScrZero, ClaudeWCT.W9.Machine.Sign.PRIVW, ClaudeWCT.W9.Machine.Sign.CHAINW, ClaudeWCT.W9.Machine.Sign.NODEW, ClaudeWCT.W9.Machine.Sign.FORW] at hA
    rw [h.frame.get (by omega) (by unfold FrontW; sg_omega)]
    exact sinit_zero sk cache m A (by unfold SIGN_DATA; omega) (by sg_omega)
  · intro k hk
    rw [h.frame.get (by unfold TBL; omega) (by unfold FrontW TBL; sg_omega)]
    exact sinit_wct_table sk cache m k hk
theorem wct_unchanged : ClaudeWCT.W9.Machine.Sign.Unchanged submission.image
    (fun sk cache _m => Inv sk cache) := by
  refine ⟨?_, ?_, ?_⟩
  · intro sk cache m
    refine ⟨sinit sk cache m, initialState_sign sk cache m, ?_⟩
    intro α W Q K hfail hrest
    exact nonce_front K (fun t ht => hfail t ⟨ht.pc, ht.x5, ht.x10⟩)
      (fun rho t ht => hrest rho t ht.hook ht.inv)
  · intro sk cache m t u h hf hr
    exact Inv.stable h hf hr (by decide)
  · intro sk cache m index root s hp hi
    have hs := layers_from370 hp.pc hi.1 hp.hidx hp.idx hp.root (by rw [hi.2]; decide)
    refine TBSim.mono hs le_rfl (fun r u hu => ?_)
    cases r with
    | none => exact ⟨hu.pc, hu.x5, hu.x10⟩
    | some ps =>
      obtain ⟨hpc, hlen, hpieces, hf⟩ := hu
      exact ⟨hpc, hlen, fun lay => hpieces lay lay.isLt, hf.mono (fun A _ h => h.1)⟩
end SigGolfCandidate.T3M.Sign.Boundary
end

section




namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
theorem signMain : SignMain := signMain_of searchGood ftsGood compactGood
theorem sign_refines_w (imgs : Phase → Image) (Inv : BitVec 256 → Bytes 131072 → Message → MachineState → Prop)
    (hcode : SignCodeAt (imgs .sign)) (hU : Unchanged imgs Inv) : SignRefinesW imgs :=
  (signMain imgs Inv hcode hU).1
theorem sign_terminates_w (imgs : Phase → Image) (Inv : BitVec 256 → Bytes 131072 → Message → MachineState → Prop)
    (hcode : SignCodeAt (imgs .sign)) (hU : Unchanged imgs Inv) : SignTerminatesW imgs :=
  (signMain imgs Inv hcode hU).2
theorem newCodeAt_of_codeAt {im : Image} (h : CodeAt im (pcOf 2074) signNew) : NewCodeAt im := by
  obtain ⟨-, -, -, hpre⟩ := h
  have hp : ((pcOf 2074).toNat - 0x1000) / 4 = 2074 := by decide
  rwa [hp] at hpre
theorem newCodeAt_of_drop {im : Image} (h : im.code.drop 2074 = signNew) : NewCodeAt im := by
  rw [NewCodeAt, h]
end ClaudeWCT.W9.Machine.Sign
end

section


namespace SigGolfCandidate.T3M.Sign.Boundary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open ClaudeWCT.W9.Machine.Sign (SignCodeAt SignRefinesW SignTerminatesW signNew)
set_option maxRecDepth 100000
theorem wct_signCodeAt : SignCodeAt Images.signImage := by
  refine ⟨?_, ?_⟩
  · apply ClaudeWCT.W9.Machine.Sign.newCodeAt_of_drop
    decide +kernel
  · exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem wct_sign_certified : SignRefinesW submission.image ∧ SignTerminatesW submission.image := by
  exact ClaudeWCT.W9.Machine.Sign.signMain submission.image
    (fun sk cache _m => Inv sk cache) wct_signCodeAt wct_unchanged
end SigGolfCandidate.T3M.Sign.Boundary
end

section


namespace SigGolfCandidate.T3M.Sign.Boundary
def finalImages : ClaudeWCT.W9.T3M.Images :=
  ⟨Images.signImage, Images.expandImage, Images.verifyImage⟩
theorem wct_final_sign_refines : ClaudeWCT.W9.T3M.Final.SignRefines finalImages := by
  exact wct_sign_certified.1
theorem wct_final_sign_terminates : ClaudeWCT.W9.T3M.Final.SignTerminates finalImages := by
  exact wct_sign_certified.2
end SigGolfCandidate.T3M.Sign.Boundary
end
