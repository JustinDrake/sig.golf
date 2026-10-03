import SigGolfCandidate.T3M.Verify.CanonicalTwin
import SigGolfCandidate.T3M.Witness.CanonicalSource

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace SigGolfCandidate.T3M.CanonicalNative
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput attemptLimit selections pad64 digestInput)

theorem tail_after_sel (pk : Digest) (w : WBytes) (a : HashOutput) :
    verifyTailP pk w a=(if !selectionsOk (selections a) then pure false else afterSel pk w a) := by
  unfold verifyTailP afterSel afterFts
  rfl

theorem twin_guard_good {m pk w a b s} (h : TwinOut m pk w a b s) :
    GQ s 10908 10908 True 8413
      (CanonicalPort.Verify.ccM
        (if b≠a then pure false else verifyTailP pk (CanonicalAdapter.normalize (selections a) w) a)
        CanonicalPort.Verify.Kb) := by
  by_cases he : b=a
  · simp only [he,ne_eq,not_true_eq_false,if_false]
    obtain ⟨t,hguard,ht⟩ := twin_guard_accept h he
    obtain ⟨u,hsetup,hu⟩ := twin_sel_ready ht
    rw [tail_after_sel]
    have hs := select_from_ready pk w a u hu
      (afterSel pk (CanonicalAdapter.normalize (selections a) w) a)
      CanonicalPort.Verify.Kb rfl (fun z hz => after_sel_c_good pk w a z hz)
    exact CanonicalPort.Verify.GoodQ.steps' (hguard.trans hsetup) hs
      (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)
  · simp only [if_pos he,CanonicalPort.Verify.ccM_pure,CanonicalPort.Verify.Kb]
    obtain ⟨t,k,hsteps,hk,hh⟩ := twin_guard_reject h he
    exact CanonicalPort.Verify.GoodQ.steps' hsteps
      (CanonicalPort.Verify.GoodQ.reject (Q:=True) (A:=0) hh.1 hh.2.1 hh.2.2)
      (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)

theorem twin_ecall (s : MachineState) (hpc : s.pc=pcOf 221960) :
    fetch fixture s=some (.base .ECALL) := by
  have hi := look_ok 221960 0x73 (by decide +kernel)
  simp only [fetch,hpc,show (pcOf 221960).toNat=891936 from rfl]
  change (fixture.code[221960]? >>= decodeInstruction)=some (.base .ECALL)
  rw [hi]
  rfl

theorem second_digest_good (m pk w a s) (h : DgOutC m pk w a s)
    (hdc : (wdc w).toNat<attemptLimit) :
    GQ s 10914 10921 True 8426
      (CanonicalPort.Verify.ccM (do
        let some b ← digestP m w | pure false
        if b≠a then return false
        verifyTailP pk (CanonicalAdapter.normalize (selections a) w) a)
        CanonicalPort.Verify.Kb) := by
  obtain ⟨t,hsteps,ht⟩ := twin_load m pk w a s h
  have hf := twin_ecall t ht.pc
  have h5 : t.getReg .x5=0 := ht.old.known (.x5,0) (by simp [proPostC,proPost,baseK])
  have h10 : t.getReg .x10=32 := ht.old.known (.x10,32) (by simp [proPostC,proPost])
  have h11 : t.getReg .x11=64 := ht.old.known (.x11,64) (by simp [proPostC,proPost])
  have h12 : t.getReg .x12=96 := ht.old.known (.x12,96) (by simp [proPostC,proPost])
  have hv := hashArgs_of t 32 64 96 h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hin : hashInput t=toQ (pad64 (digestInput (wrho w) m (wdc w))) := ht.old.input
  simp only [digestP,show ¬(wdc w).toNat≥attemptLimit by omega,if_false,T3.digest,
    map_bind,pure_bind]
  have hg := CanonicalPort.Verify.GoodQ.publicHash_bind
    (N:=10908) (C:=10908) (A:=8413) (Q:=True)
    (f:=fun b => if b≠a then pure false else verifyTailP pk (CanonicalAdapter.normalize (selections a) w) a)
    (K:=CanonicalPort.Verify.Kb) hf h5 hv hin (fun b => twin_guard_good (twin_hash_out ht b))
  rw [blocks_digestInput] at hg
  exact CanonicalPort.Verify.GoodQ.steps' hsteps hg
    (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)

theorem verify_c_good (m : T3.Message) (pk : Digest) (w : WBytes) (s : MachineState)
    (hs : InitC m pk w s) :
    GQ s 10936 10950 True 8455
      (CanonicalPort.Verify.ccM (CanonicalSource.verifyC m pk w) CanonicalPort.Verify.Kb) := by
  unfold CanonicalSource.verifyC
  rw [CanonicalPort.Verify.ccM_bind]
  have h := digestP_good m pk w s hs
    (fun o => CanonicalPort.Verify.ccM (match o with
      | none => pure false
      | some a => do
        let some b ← digestP m w | pure false
        if b≠a then return false
        verifyTailP pk (CanonicalAdapter.normalize (selections a) w) a)
      CanonicalPort.Verify.Kb)
    (by simp only [CanonicalPort.Verify.ccM_pure,CanonicalPort.Verify.Kb])
    (fun a u hdc hu => second_digest_good m pk w a u hu hdc)
  convert h using 1
  congr 1
  funext o
  cases o <;> rfl

#print axioms verify_c_good
end SigGolfCandidate.T3M.CanonicalNative
