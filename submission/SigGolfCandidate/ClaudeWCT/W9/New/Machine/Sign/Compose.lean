import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Common

section

namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest Pieces Layer chainCount height piecesSignature)
open SphincsSecurity (bytesLE bytesLE_length)
local macro "so" : tactic => `(tactic| ((try simp only [SIG] at *) <;> omega))
theorem readOutput_sig (imgs : Phase → Image) (t : MachineState) (sig : WCT9.Signature)
    (h : ∀ k < 341, DigAt t (SIG + 16 * k) ((W9.T3M.sigDigests sig).getD k 0)) :
    readOutput (wsub imgs).sizes (wsub imgs).layout .sign t = W9.T3M.sigB sig := by
  have hd : DigsAt t SIG (W9.T3M.sigDigests sig) := fun k hk =>
    h k (by rw [W9.T3M.length_sigDigests] at hk; exact hk)
  have hw := hd.words
  rw [W9.T3M.length_sigDigests] at hw
  have hl : ((W9.T3M.sigDigests sig).flatMap (bytesLE 16)).length = 8 * 682 := by
    have : ∀ ds : List Digest, (ds.flatMap (bytesLE 16)).length = 16 * ds.length := fun ds => by
      induction ds with
      | nil => rfl
      | cons d ds ih => rw [List.flatMap_cons, List.length_append, bytesLE_length, ih, List.length_cons]; ring
    rw [this, W9.T3M.length_sigDigests]
  have e := readBuffer_of_words t SIG 682 ((W9.T3M.sigDigests sig).flatMap (bytesLE 16)) (by decide) (by decide)
    hl hw
  show readBuffer t SIG (8 * 682) = W9.T3M.sigB sig
  rw [e, W9.T3M.sigB, W9.T3M.serialize_eq]
theorem DigAt.of_mem {X Y : MachineState} {a b : Nat} {d : Digest} (h : DigAt X a d)
    (h0 : Y.getMem (BitVec.ofNat 64 b) = X.getMem (BitVec.ofNat 64 a))
    (h1 : Y.getMem (BitVec.ofNat 64 (b + 8)) = X.getMem (BitVec.ofNat 64 (a + 8))) : DigAt Y b d :=
  ⟨h0.trans h.1, h1.trans h.2⟩
theorem t3LayIdx_eq (lay : Layer) : t3LayIdx lay = W9.T3M.layIdx lay + 10 := by
  fin_cases lay <;> rfl
theorem piece_digest {w : MachineState} {sig : WCT9.Signature} {lay : Layer} {p : Pieces}
    (hp : PieceAt w lay p) (hl : sig.layers lay = piecesSignature lay p) (i : Nat)
    (hi : i < chainCount lay + height lay) :
    DigAt w (SIG + 16 * (t3LayIdx lay + i)) ((W9.T3M.sigDigests sig).getD (W9.T3M.layIdx lay + i) 0) := by
  by_cases hc : i < chainCount lay
  · rw [W9.T3M.sigDigests_layValue sig lay i hc, hl]
    exact hp.1 i hc
  · have e := W9.T3M.sigDigests_layPath sig lay (i - chainCount lay) (by omega)
    rw [show chainCount lay + (i - chainCount lay) = i by omega] at e
    rw [e, hl]
    have := hp.2 (i - chainCount lay) (by omega)
    rwa [show t3LayIdx lay + chainCount lay + (i - chainCount lay) = t3LayIdx lay + i by omega] at this
theorem final_digests {v w x : MachineState} {rho : Digest} {ops : List WCT9.Opening} {ps : List Pieces}
    (hrho : DigAt v SIG rho) (hops : ∀ k < 9, OpeningAt v k (ops.getD k ⟨fun _ => 0, fun _ => 0⟩))
    (hfw : Frame v w (fun A => ¬ (SIG ≤ A ∧ A < SIG + 2192)))
    (hpieces : ∀ lay : Layer, PieceAt w lay (ps.getD lay.val ([], []))) (hc : CompactPost w x) :
    ∀ k < 341, DigAt x (SIG + 16 * k)
      ((W9.T3M.sigDigests (WCT9.assembledSignature rho ops ps)).getD k 0) := by
  intro k hk
  obtain ⟨-, -, -, hmove, hfx⟩ := hc
  set sig := WCT9.assembledSignature rho ops ps with hsig
  by_cases hlow : k < 127
  ·
    have keep : ∀ A, SIG ≤ A → A < SIG + 2032 → x.getMem (BitVec.ofNat 64 A) = v.getMem (BitVec.ofNat 64 A) := by
      intro A hS hA
      rw [hfx.get (by so) (by so), hfw.get (by so) (by so)]
    have keepD : ∀ d, DigAt v (SIG + 16 * k) d → DigAt x (SIG + 16 * k) d := fun d hd =>
      DigAt.of_mem hd (keep _ (by so) (by so)) (keep _ (by so) (by so))
    apply keepD
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [W9.T3M.sigDigests_rho, hsig, WCT9.assembledSignature_rho]; simpa using hrho
    · obtain ⟨c, i, hc9, hi14, rfl⟩ : ∃ c i, c < 9 ∧ i < 14 ∧ k = 1 + 14 * c + i :=
        ⟨(k - 1) / 14, (k - 1) % 14, by omega, by omega, by omega⟩
      have ho := hops c hc9
      by_cases hi7 : i < 7
      · have e := W9.T3M.sigDigests_value sig ⟨c, hc9⟩ ⟨i, hi7⟩
        simp only at e
        rw [e, hsig, WCT9.assembledSignature_openings]
        have := ho.1 ⟨i, hi7⟩
        simp only at this
        rwa [show SIG + 16 * (1 + 14 * c + i) = SIG + 16 + 224 * c + 16 * i by ring]
      · have e := W9.T3M.sigDigests_path sig ⟨c, hc9⟩ ⟨i - 7, by omega⟩
        simp only at e
        rw [show 1 + 14 * c + 7 + (i - 7) = 1 + 14 * c + i by omega] at e
        rw [e, hsig, WCT9.assembledSignature_openings]
        have := ho.2 ⟨i - 7, by omega⟩
        simp only at this
        rwa [show SIG + 16 * (1 + 14 * c + i) = SIG + 128 + 224 * c + 16 * (i - 7) by omega]
  ·
    have moveD : ∀ d, DigAt w (SIG + 16 * (k + 10)) d → DigAt x (SIG + 16 * k) d := fun d hd => by
      refine DigAt.of_mem hd ?_ ?_
      · have := hmove (2 * (k - 127)) (by omega)
        rw [show SIG + 2032 + 8 * (2 * (k - 127)) = SIG + 16 * k by so,
          show SIG + 2192 + 8 * (2 * (k - 127)) = SIG + 16 * (k + 10) by so] at this
        exact this
      · have := hmove (2 * (k - 127) + 1) (by omega)
        rw [show SIG + 2032 + 8 * (2 * (k - 127) + 1) = SIG + 16 * k + 8 by so,
          show SIG + 2192 + 8 * (2 * (k - 127) + 1) = SIG + 16 * (k + 10) + 8 by so] at this
        exact this
    apply moveD
    have key : ∀ lay : Layer, ∀ i, i < chainCount lay + height lay → k = W9.T3M.layIdx lay + i →
        DigAt w (SIG + 16 * (k + 10)) ((W9.T3M.sigDigests sig).getD k 0) := by
      intro lay i hi hk'
      have := piece_digest (hpieces lay) (sig := sig) rfl i hi
      rw [t3LayIdx_eq] at this
      rw [hk', show W9.T3M.layIdx lay + i + 10 = W9.T3M.layIdx lay + 10 + i by omega]
      exact this
    by_cases h1 : k < 193
    · exact key 0 (k - 127) (by simp [chainCount, height]; omega) (by simp [W9.T3M.layIdx]; omega)
    by_cases h2 : k < 243
    · exact key 1 (k - 193) (by simp [chainCount, height]; omega) (by simp [W9.T3M.layIdx]; omega)
    by_cases h3 : k < 292
    · exact key 2 (k - 243) (by simp [chainCount, height]; omega) (by simp [W9.T3M.layIdx]; omega)
    · exact key 3 (k - 292) (by simp [chainCount, height]; omega) (by simp [W9.T3M.layIdx]; omega)
end ClaudeWCT.W9.Machine.Sign
end

section

namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M Pieces Layer signLayers privateMac privateNonce)
local macro "so" : tactic =>
  `(tactic| ((try simp only [SIG, SK, DIG, NBUF, FOUT, IDXV, TBL, PRIVW, CHAINW, NODEW, FORW, SCREND,
    SearchW, FtsW, ScrZero, NewW] at *) <;> omega))
def Kw (cache : Bytes 131072) (m : Message) (rho : Digest) : M (Option WCT9.Signature) := do
  let some (_, output) ← WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit | pure none
  let forest ← WCT9.signForest (output.toNat % 2 ^ 31) output
  let some pieces ← signLayers (cacheDec cache) (output.toNat % 2 ^ 31) 4 forest.2 | pure none
  pure (some (WCT9.assembledSignature rho forest.1 pieces))
theorem rev3_sign_eq (cache : Bytes 131072) (m : Message) :
    WCT9.Rev3.sign (cacheDec cache) m = (do
      let tag ← privateMac (cacheDec cache).region
      if tag ≠ (cacheDec cache).tag then pure none else privateNonce m >>= Kw cache m) := by
  rw [WCT9.Rev3.sign_eq, WCT9.Rev3.signPayload_eq]
  rfl
def FinalQ : Option WCT9.Signature → MachineState → Prop
  | none, t => FailedT t ∨ FailedS t
  | some sig, t => t.pc = pcOf 10946 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
      ∀ k < 341, DigAt t (SIG + 16 * k) ((W9.T3M.sigDigests sig).getD k 0)
def restC : Nat := searchC + (ftsC + (layC + compactK))
def signCW : Nat := frontC + restC
theorem signCW_eq : signCW = 3198752146 := by
  norm_num [signCW, restC, frontC, searchC, trialC, WCT9.digestAttemptLimit, ftsC, layC, compactK]
theorem signCW_lt : signCW + 1 < CYCLE_LIMIT := by
  rw [signCW_eq]; norm_num [CYCLE_LIMIT]
section rest
variable {im : Image} {sk : BitVec 256} {cache : Bytes 131072} {m : Message}
theorem rest_tbsim (hcode : SignCodeAt im) (hS : SearchGood im) (hF : FtsGood im) (hC : CompactGood im)
    {Inv : MachineState → Prop} (hstab : InvStable Inv) (hlay : LayersSpec im sk cache Inv)
    (rho : Digest) (t : MachineState) (hp : HookPre sk m rho t) (hinv : Inv t) :
    TBSim im sk t restC (Kw cache m rho) FinalQ := by
  obtain ⟨hnew, hhooks⟩ := hcode
  unfold Kw restC
  refine TBSim.bind (hS hnew hhooks sk rho m t hp.search) (fun r u hu => ?_)
  rcases r with _ | ⟨c, N⟩
  · exact TBSim.mono (TBSim.pure (Or.inr hu)) (Nat.zero_le _) (fun _ _ h => h)
  obtain ⟨upc, u5, uadm, unb, u22, uidx, -, ur, uf⟩ := hu
  have gu : ∀ A, A < 2 ^ 64 → ¬ SearchW A → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn => uf.get hA hn
  have hpre : FtsPre sk N u :=
    { pc := upc
      x5 := u5
      x22 := u22
      adm := uadm
      nbuf := unb
      sk := fun k hk => by rw [gu _ (by so) (by so)]; exact hp.sk k hk
      zero := fun A hA => by
        rw [gu _ (by unfold ScrZero at hA; so) (by unfold ScrZero at hA; so)]; exact hp.zero A hA
      table := fun k hk => by rw [gu _ (by so) (by so)]; exact hp.table k hk }
  refine TBSim.bind (hF hnew sk N u hpre) (fun fr v hv => ?_)
  obtain ⟨ops, root⟩ := fr
  obtain ⟨vpc, v5, vroot, -, vops, vr, vf⟩ := hv
  have hlp : LayPre (N.toNat % 2 ^ 31) root v :=
    ⟨vpc, v5, Nat.mod_lt _ (by norm_num), by rw [vf.get (by so) (by so)]; exact uidx, vroot⟩
  have hinv' : Inv v := hstab t v hinv ((uf.trans vf).mono (fun A _ h => h))
    ((ur.trans vr).mono (by decide))
  refine TBSim.bind (hlay _ root v hlp hinv') (fun r w hw => ?_)
  rcases r with _ | ps
  · exact TBSim.mono (TBSim.pure (Or.inl hw)) (Nat.zero_le _) (fun _ _ h => h)
  obtain ⟨wpc, -, wpieces, wf⟩ := hw
  obtain ⟨x, st, hx⟩ := hC hnew hhooks w wpc
  have hrho : DigAt v SIG rho :=
    (hp.sigRho.frame uf (by so) (by so) (by so)).frame vf (by so) (by so) (by so)
  exact TBSim.pure_steps' st ⟨hx.1, hx.2.1, hx.2.2.1, final_digests hrho vops wf wpieces hx⟩
end rest
theorem sign_tbsim_w (hS : ∀ im, SearchGood im) (hF : ∀ im, FtsGood im) (hC : ∀ im, CompactGood im)
    {imgs : Phase → Image} {Inv : BitVec 256 → Bytes 131072 → Message → MachineState → Prop}
    (hcode : SignCodeAt (imgs .sign)) (hU : Unchanged imgs Inv) (sk : BitVec 256) (cache : Bytes 131072)
    (m : Message) :
    ∃ s0, initialState (wsub imgs) .sign (sk, cache, m) = some s0 ∧
      TBSim (imgs .sign) sk s0 signCW (WCT9.Rev3.sign (cacheDec cache) m) FinalQ := by
  obtain ⟨s0, hinit, hfs⟩ := hU.front sk cache m
  refine ⟨s0, hinit, ?_⟩
  rw [rev3_sign_eq]
  exact hfs restC FinalQ (Kw cache m) (fun t ht => Or.inl ht)
    (fun rho t hp hi => rest_tbsim hcode (hS _) (hF _) (hC _) (hU.stable sk cache m) (hU.layers sk cache m) rho t hp hi)
theorem fetch_ecall {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) (n : Nat)
    (hn : look n = some 0x00000073) (hn' : n < 2 ^ 32) (t : MachineState) (ht : t.pc = pcOf n) :
    fetch im t = some (.base .ECALL) := by
  have e : (pcOf n).toNat = 0x1000 + 4 * n := by
    simp only [pcOf, BitVec.toNat_ofNat]; omega
  rw [fetch_of_look hl (pc := pcOf n) (by rw [e]; simp) (by rw [e]; simpa using hn) t ht]
  rfl
theorem finalQ_fetch {imgs : Phase → Image} (hcode : SignCodeAt (imgs .sign)) :
    ∀ o t, FinalQ o t → fetch (imgs .sign) t = some (.base .ECALL) ∧ t.getReg .x5 = 1 := by
  obtain ⟨hnew, hhooks⟩ := hcode
  intro o t ht
  rcases o with _ | sig
  · rcases ht with h | h
    · exact ⟨fetch_ecall (hookLook_ok hhooks) 545 (by decide) (by decide) t h.pc, h.x5⟩
    · exact ⟨fetch_ecall (headLook_ok hnew) 2214 (by decide +kernel) (by decide) t h.pc, h.x5⟩
  · exact ⟨fetch_ecall (tailLook_ok hnew) 10946 (by decide +kernel) (by decide) t ht.1, ht.2.1⟩
theorem signMain_of (hS : ∀ im, SearchGood im) (hF : ∀ im, FtsGood im) (hC : ∀ im, CompactGood im) :
    SignMain := by
  intro imgs Inv hcode hU
  refine ⟨fun sk cache m => ?_, fun hash sk cache m => ?_⟩
  · obtain ⟨s0, hinit, hsim⟩ := sign_tbsim_w hS hF hC hcode hU sk cache m
    refine Sim.run_eq (wsub imgs) .sign (sk, cache, m) hinit hsim (by have := signCW_lt; omega)
      (fun o => o.map W9.T3M.sigB) (fun o t ht => ?_)
    obtain ⟨hf, h5⟩ := finalQ_fetch hcode o t ht
    refine ⟨hf, h5, ?_⟩
    rcases o with _ | sig
    · rcases ht with h | h
      · rw [if_neg (by rw [h.x10]; decide)]; rfl
      · rw [if_neg (by rw [h.x10]; decide)]; rfl
    · rw [if_pos ht.2.2.1, readOutput_sig imgs t sig ht.2.2.2]; rfl
  · obtain ⟨s0, hinit, hsim⟩ := sign_tbsim_w hS hF hC hcode hU sk cache m
    obtain ⟨h1, h2⟩ := Sim.runWith (wsub imgs) .sign (sk, cache, m) hinit hsim signCW_lt
      (finalQ_fetch hcode) hash
    exact ⟨h1, by have := signCW_lt; omega⟩
end ClaudeWCT.W9.Machine.Sign
end
