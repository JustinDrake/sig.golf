import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Conditional
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.Final
import SigGolfCandidate.W9Machine.WctImage
import SigGolfCandidate.T3M.Verify.Code
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.ExpandLink.Link
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCNearFinal
import SigGolfCandidate.ClaudeWCT.W9.New.G6.PairFinal
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingCert
import SigGolfCandidate.T3M.Sign.WctFinal
import SigGolfCandidate.W9Drv.FtsDefs
import SigGolfCandidate.W9Drv.CoordReturn
import SigGolfCandidate.W9Drv.Forest
import SigGolfCandidate.W9Machine.WctChainSplit
import SigGolfCandidate.W9Machine.WctChainAllGood
import SigGolfCandidate.W9ChS.SourceEquiv
import SigGolfCandidate.W9Fin.Main

section


namespace ClaudeWCT.W9.Final
open ClaudeWCT.W9.T3M (Images)
abbrev submission (I : Images) : SigGolf.Submission := ClaudeWCT.W9.T3M.Final.submissionNew I
theorem signature_bytes (I : Images) : (submission I).sizes.signature = 5456 := rfl
theorem witness_bytes (I : Images) : (submission I).sizes.witness = 24264 := rfl
theorem cache_bytes (I : Images) : (submission I).sizes.cache = 131072 := rfl
theorem layout_offsets (I : Images) : (submission I).layout =
    { message := 64, secretKey := 128, publicKey := 160,
      cache := 524288, signature := 28672, witness := 2048 } := rfl
theorem keygen_image (I : Images) :
    (submission I).image .keygen =
      ⟨SigGolfCandidate.T3M.Images.keygenImage.code, SigGolfCandidate.T3M.Images.keygenImage.data⟩ :=
  rfl
structure PendingInputs (I : Images) : Prop where
  large_route : ClaudeWCT.W9.T3.Secc.LargeRouteBound
  pair_bound : ClaudeWCT.W9.T3.Security.WPair.PairGuessBound SigGolfCandidate.T3.Security.BPair.pairTerm
  near_bound : ClaudeWCT.W9.T3.Security.CaseC.NearBound ClaudeWCT.W9.T3.Security.CaseC.caseCExtraction
    ClaudeWCT.W9.T3.Security.CaseC.NearQ ClaudeWCT.W9.T3.Security.Wots.nearTerm
  admissible : (ClaudeWCT.W9.T3M.submission I).Admissible
  verify_refines : ClaudeWCT.W9.T3M.Final.VerifyRefines I
  verify_terminates : ClaudeWCT.W9.T3M.Final.VerifyTerminates I
  verify_accept_cycles : ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I
  sign_refines : ClaudeWCT.W9.T3M.Final.SignRefines I
  sign_terminates : ClaudeWCT.W9.T3M.Final.SignTerminates I
  expand_refines : ClaudeWCT.W9.T3M.Final.ExpandRefines I
  expand_terminates : ClaudeWCT.W9.T3M.Final.ExpandTerminates I
theorem PendingInputs.machine {I : Images} (h : PendingInputs I) : ClaudeWCT.W9.T3M.Final.MachineFacts I where
  admissible := h.admissible
  sign_refines := h.sign_refines
  sign_terminates := h.sign_terminates
  expand_refines := h.expand_refines
  expand_terminates := h.expand_terminates
  verify_refines := h.verify_refines
  verify_terminates := h.verify_terminates
  verify_accept_cycles := h.verify_accept_cycles
theorem PendingInputs.securityP {I : Images} (h : PendingInputs I) : ClaudeWCT.W9.T3M.Final.SecurityP :=
  ClaudeWCT.W9.T3.Secc.t3_securityP h.near_bound h.pair_bound h.large_route
theorem certificate_of_pending {I : Images} (h : PendingInputs I) : SigGolf.Certificate (submission I) 7941 :=
  ClaudeWCT.W9.T3M.Final.certificate_of_security h.securityP h.machine
end ClaudeWCT.W9.Final
end

section


namespace SigGolfCandidate.Packaging
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem verify_code_eq : W9Machine.Frozen.image.code = T3M.Images.verifyImage.code := by
  change W9Machine.Frozen.codeChunks.flatten = T3M.Images.verifyCode
  rw [T3M.Verify.verifyCode_eq]
  rfl
theorem verify_data_eq : W9Machine.Frozen.image.data = T3M.Images.verifyImage.data := by
  decide +kernel
theorem verify_image_eq : W9Machine.Frozen.image = T3M.Images.verifyImage := by
  cases h : W9Machine.Frozen.image
  cases h' : T3M.Images.verifyImage
  have hc := verify_code_eq
  have hd := verify_data_eq
  simp only [h, h'] at hc hd
  cases hc
  cases hd
  rfl
end SigGolfCandidate.Packaging
end

section







namespace SigGolfCandidate.Packaging
open SigGolfCandidate.T3M.Sign.Boundary (finalImages)
theorem submission_eq : ClaudeWCT.W9.T3M.submission finalImages =
    SigGolfCandidate.T3M.submission := rfl
theorem certificate_of_machine_inputs
    (vr : ClaudeWCT.W9.T3M.Final.VerifyRefines finalImages)
    (vt : ClaudeWCT.W9.T3M.Final.VerifyTerminates finalImages)
    (vc : ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles finalImages)
    (er : ClaudeWCT.W9.T3M.Final.ExpandRefines finalImages)
    (et : ClaudeWCT.W9.T3M.Final.ExpandTerminates finalImages) :
    SigGolf.Certificate
      (SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.submission) 7941 := by
  exact ClaudeWCT.W9.Final.certificate_of_pending (I := finalImages)
    { large_route := ClaudeWCT.W9.T3.Security.LargeCoupling.large_route_hlarge
      pair_bound := ClaudeWCT.W9.T3.Security.WPair.pair_guess_bound
      near_bound := ClaudeWCT.W9.T3.Security.CaseC.nearBound
      admissible := SigGolfCandidate.T3M.submission_admissible
      verify_refines := vr
      verify_terminates := vt
      verify_accept_cycles := vc
      sign_refines := SigGolfCandidate.T3M.Sign.Boundary.wct_final_sign_refines
      sign_terminates := SigGolfCandidate.T3M.Sign.Boundary.wct_final_sign_terminates
      expand_refines := er
      expand_terminates := et }
def verifyImages : ClaudeWCT.W9.T3M.Images :=
  ⟨T3M.Images.signImage, T3M.Images.expandImage, W9Machine.Frozen.image⟩
theorem verifyImages_eq : verifyImages = finalImages := by
  exact congrArg (fun v => ClaudeWCT.W9.T3M.Images.mk
    T3M.Images.signImage T3M.Images.expandImage v) verify_image_eq
theorem certificate_of_verify_inputs
    (vr : ClaudeWCT.W9.T3M.Final.VerifyRefines verifyImages)
    (vt : ClaudeWCT.W9.T3M.Final.VerifyTerminates verifyImages)
    (vc : ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles verifyImages) :
    SigGolf.Certificate
      (SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.submission) 7941 := by
  rw [verifyImages_eq] at vr vt vc
  exact certificate_of_machine_inputs vr vt vc
    ClaudeWCT.W9.Machine.ExpandLink.expand_pending_v1.1
    ClaudeWCT.W9.Machine.ExpandLink.expand_pending_v1.2
end SigGolfCandidate.Packaging
end

section



namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
open W9Machine
def finishFts (a : HashOutput) (state : Option (List Digest)) : M (Option Digest) :=
  match state with
  | none => pure none
  | some roots => some <$> ClaudeWCT.WCT9.forestPk (idxOf a) roots
def coordsCost (ks : List (Fin 9)) : Nat :=
  (ks.map (fun k => if k.val = 0 then 214 else 216)).sum
theorem fold_none (w : WBytes) (a : HashOutput) (ks : List (Fin 9)) :
    ks.foldlM (ClaudeWCT.W9.T3M.wctStep w a) none = pure none := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simpa only [List.foldlM_cons, ClaudeWCT.W9.T3M.wctStep, pure_bind] using ih
theorem coordinates_good (chains : Chain.AllGood) (pk : Digest) (w : WBytes) (a : HashOutput)
    (ks : List (Fin 9)) (n : Nat) (roots : List Digest) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option Digest → OracleComp HashSpec Obs)
    (horder : ks.map Fin.val = List.range' n ks.length) (hend : n + ks.length = 9)
    (hu : CoordPre pk w a n roots u) (hnone : K none = pure (false, 0))
    (hnext : ∀ root t, FtsOut ⟨pk,w,a⟩ root t →
      GoodQFor Frozen.image t N C Q A (K (some root))) :
    GoodQFor Frozen.image u (N + (coordsCost ks + 39)) (C + (coordsCost ks + 39)) Q
      (A + (coordsCost ks + 39))
      (ccM (ks.foldlM (ClaudeWCT.W9.T3M.wctStep w a) (some roots) >>= finishFts a) K) := by
  induction ks generalizing n roots u with
  | nil =>
    have hn : n = 9 := by simpa using hend
    subst n
    simp only [List.foldlM_nil, pure_bind, finishFts]
    have hf := forest_good pk w a roots u N C A Q (fun root => K (some root)) hu hnext
    rw [map_eq_bind_pure_comp, ccM_bind]
    simp only [Function.comp_apply, ccM_pure]
    exact hf.mono (by change N + 16 ≤ N + 39; omega) (by rfl) (fun hq => ⟨hq, by rfl⟩)
  | cons k ks ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at horder
    obtain ⟨hn, ht⟩ := horder
    subst n
    let K' : Option (List Digest) → OracleComp HashSpec Obs := fun state =>
      ccM (ks.foldlM (ClaudeWCT.W9.T3M.wctStep w a) state >>= finishFts a) K
    have hkNone : K' none = pure (false, 0) := by
      simp only [K', fold_none, pure_bind, finishFts, ccM_pure, hnone]
    have hstep := coord_good chains pk w a k roots u (N + (coordsCost ks + 39))
      (C + (coordsCost ks + 39)) (A + (coordsCost ks + 39)) Q K' hu hkNone
      (fun root t hh => ih (k.val + 1) (roots ++ [root]) t ht (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hend) hh)
    simp only [List.foldlM_cons, bind_assoc, ccM_bind]
    convert hstep using 1 <;> simp [coordsCost, Nat.add_left_comm, Nat.add_comm,
      K', ccM_bind]
theorem fts_good (chains : Chain.AllGood) : FtsGood := by
  intro pk w a u N C A Q K hu hnone hnext
  let KG : Bool → OracleComp HashSpec Obs := fun b =>
    if b then ccM (ClaudeWCT.W9.T3M.wctP w a) K else K none
  have hg := gate_good pk w a u (N + 1981) (C + 1981) (A + 1981) Q KG hu
    (by simpa only [KG, Bool.false_eq_true, ↓reduceIte] using hnone)
    (fun t ht => by
      have hc := coordinates_good chains pk w a (List.finRange 9) 0 [] t N C A Q K
        (by decide)
        (by simp) ht hnone hnext
      rw [show coordsCost (List.finRange 9) + 39 = 1981 by decide] at hc
      apply hc.congr
      change ccM (_ >>= finishFts a) K = ccM (ClaudeWCT.W9.T3M.wctP w a) K
      apply congrArg (fun p : M (Option Digest) => ccM p K)
      unfold ClaudeWCT.W9.T3M.wctP
      apply congrArg (fun f : Option (List Digest) → M (Option Digest) =>
        (List.finRange 9).foldlM (ClaudeWCT.W9.T3M.wctStep w a) (some []) >>= f)
      funext state
      cases state <;> rfl)
  change GoodQFor Frozen.image u (N + 2023) (C + 2023) Q (A + 2023)
    (KG (ClaudeWCT.W9.T3M.gateOk a)) at hg
  apply hg.congr
  cases ClaudeWCT.W9.T3M.gateOk a <;> simp [KG, ccM_pure]
end W9Drv
end

section

namespace W9ChE
open W9Machine W9Machine.Chain
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
theorem extract_lo (X : BitVec 256) :
    (X.extractLsb' 0 128).extractLsb' 0 64 = X.extractLsb' 0 64 := by
  ext i hi
  have h : i < 128 := by omega
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb', Nat.zero_add, h,
    decide_true, Bool.true_and]
theorem extract_hi (X : BitVec 256) :
    (X.extractLsb' 0 128).extractLsb' 64 64 = X.extractLsb' 64 64 := by
  ext i hi
  have h : 64 + i < 128 := by omega
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb', h, decide_true,
    Bool.true_and, Nat.zero_add]
theorem traceLeafSlot_bound (t : Nat) (ht : t < 7) :
    traceLeafSlot t + 16 ≤ 1008 ∧ traceLeafSlot t % 8 = 0 := by
  unfold traceLeafSlot; split <;> omega
theorem sourceEnds_getD (w : WBytes) (k : Fin 9) (rank : Fin 728)
    (answers : List (BitVec 256)) (t : Nat) (ht : t < 7) :
    (sourceEnds w k rank answers).getD t 0 =
      if (ClaudeWCT.WCT9.codeword rank).getD t 0 = 0 then ClaudeWCT.W9.T3M.wleaf w k.val t
      else (answers.getD (((ClaudeWCT.WCT9.codeword rank).take (t + 1)).sum - 1) 0).extractLsb'
        0 128 := by
  unfold sourceEnds
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa only [List.length_finRange] using ht)]
  simp only [Option.map_some, Option.getD_some, List.getElem_finRange, Fin.cast_mk]
theorem endpointsCorrect : W9Machine.Chain.EndpointsCorrect := by
  intro w index k j rank u s tr answers hu hs hend t ht
  have hb := traceLeafSlot_bound t ht
  have hmem : ∀ word, word < 2 →
      s.getMem (BitVec.ofNat 64 (base k + traceLeafSlot t + 8 * word)) =
        chainValue (originalValue u index k j) answers
          (expectedEndpoint (ClaudeWCT.WCT9.codeword rank) t word) := by
    intro word hw
    rw [Nat.add_assoc, hs.memory _ (by omega), hend t ht word hw]
  have h0 := hmem 0 (by decide)
  have h1 := hmem 1 (by decide)
  rw [sourceEnds_getD w k rank answers t ht]
  unfold expectedEndpoint at h0 h1
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  split_ifs at h0 h1 ⊢ with hd
  · simp only [chainValue, originalValue] at h0 h1
    have hw0 : OrigW w s (base k + traceLeafSlot t) :=
      h0.trans (hu.witness _ (by omega) hb.2)
    have hw1 : OrigW w s (base k + traceLeafSlot t + 8) := by
      have := hu.witness (traceLeafSlot t + 8) (by omega) (by omega)
      rw [← Nat.add_assoc] at this
      exact h1.trans this
    have hdig := DigAt_origW hw0 hw1 (by unfold base; omega)
    have he : base k + traceLeafSlot t - 0x800 = ClaudeWCT.W9.T3M.wctLeafSlot k.val t := by
      unfold base traceLeafSlot ClaudeWCT.W9.T3M.wctLeafSlot ClaudeWCT.W9.T3M.regionBase
      split <;> omega
    rw [he] at hdig
    exact hdig
  · simp only [chainValue, Nat.mul_zero, Nat.mul_one] at h0 h1
    exact ⟨h0.trans (extract_lo _).symm, h1.trans (extract_hi _).symm⟩
end W9ChE
end

section



namespace W9Machine.Chain
theorem allGood : AllGood := by
  exact allGood_of W9ChS.sourceEquivalent W9ChE.endpointsCorrect
end W9Machine.Chain
end

section



namespace W9Fin
open ClaudeWCT.W9.Machine.ExpandLink (I0)
theorem verify_inputs'
    (hbridge : W9Machine.Frozen.image = SigGolfCandidate.T3M.Images.verifyImage)
    (chains : W9Machine.Chain.AllGood) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I0 ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I0 ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I0 :=
  verify_inputs hbridge (W9Drv.fts_good chains)
theorem verify_final
    (hbridge : W9Machine.Frozen.image = SigGolfCandidate.T3M.Images.verifyImage) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I0 ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I0 ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I0 :=
  verify_inputs hbridge (W9Drv.fts_good W9Machine.Chain.allGood)
end W9Fin
#print axioms W9Fin.verify_inputs'
#print axioms W9Fin.verify_final
end

section


namespace SigGolfCandidate.Packaging
theorem certificate_ready :
    SigGolf.Certificate
      (SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.submission) 7941 := by
  obtain ⟨vr, vt, vc⟩ := W9Fin.verify_final verify_image_eq
  exact certificate_of_machine_inputs vr vt vc
    ClaudeWCT.W9.Machine.ExpandLink.expand_pending_v1.1
    ClaudeWCT.W9.Machine.ExpandLink.expand_pending_v1.2
end SigGolfCandidate.Packaging
end
