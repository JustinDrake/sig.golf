import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingInteraction
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.VerifyP
import SigGolfCandidate.T3.Secc.LargeCouplingKeygen
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccSufRoute
import SigGolfCandidate.T3.Secc.LargeCouplingShort

section



namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell observedRun runWith_bind)
open SigGolfCandidate.T3.Security.LargeCoupling (cacheRegion_congr)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] buildFts buildTree keygen
noncomputable local instance instDecidableEqCache_w9largeCouplingKeygen : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
noncomputable def keyValues (vals : Coord → Digest) : Coord → Digest :=
  lookupVal (keygenDisclosed.map fun c => (c, vals c))
theorem treeChild_top_some (level node : Nat) (hl : 0 ≤ level) (hl' : level ≤ 12) (hn : node < 2 ^ (12 - level)) :
    ∃ c, treeChild 0 0 level node = some c := by
  by_cases hz : level=0
  · subst level
    have hn' : node < 4096 := by simpa using hn
    simp only [treeChild,ite_true,dif_pos hn']
    exact ⟨_,rfl⟩
  unfold treeChild treeNodeAt
  rw [if_neg hz]
  have h1 : level - 1 < height 0 := by simp [height]; omega
  have h2 : node < 2 ^ (height 0 - (level - 1) - 1) := by
    have : height 0 - (level - 1) - 1 = 12 - level := by simp [height]; omega
    rw [this]; exact hn
  rw [dif_pos ⟨h1, h2⟩]
  exact ⟨_, rfl⟩
theorem treeChild_mem_keygen (level node : Nat) (hl : 0 ≤ level) (hl' : level ≤ 12) (hn : node < 2 ^ (12 - level))
    (c : Coord) (hc : treeChild 0 0 level node = some c) : c ∈ keygenDisclosed := by
  unfold keygenDisclosed
  simp only [List.mem_flatMap, List.mem_range'_1, List.mem_filterMap, List.mem_range]
  exact ⟨level, ⟨by omega, by omega⟩, node, hn, hc⟩
section Keygen
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}
theorem Coherent.topValue_eq (hcoh : Coherent U T vals nv τ a) (level node : Nat) (hl : 0 ≤ level) (hl' : level < 12)
    (hn : node < 2 ^ (12 - level)) : topValue (keyValues vals) level node = treeValue (builtTree T 0 0) level node := by
  obtain ⟨c, hc⟩ := treeChild_top_some level node (by omega) (by omega) hn
  have hmem := treeChild_mem_keygen level node hl (by omega) hn c hc
  have hb := builtTree_eq hcoh.agrees 0 ⟨0, by decide⟩ level node (by simp [height]; omega)
    (by simpa [height] using hn)
  change _ = treeValue (builtTree T 0 (⟨0, by decide⟩ : Fin (2 ^ 31)).val) level node
  rw [hb, treeLabel_eq (secretsOf T), ← honestValue_eq hcoh.agrees, hcoh.honestValue]
  have hc' : treeChild 0 ⟨0, by decide⟩ level node = some c := hc
  unfold LargeResidual.topValue
  rw [hc, hc']
  simp only [Option.map_some, Option.getD_some]
  exact lookupVal_map vals keygenDisclosed c hmem
theorem Coherent.private_header (hcoh : Coherent U T vals nv τ a)
    (tag level node : Nat) (h0 : tag%256 ≠ 0) (h8 : tag%256 ≠ 8) :
    T (.inr (.inl (header tag 0 0 level node))) = a.priv (.inl (header tag 0 0 level node)) := by
  apply hcoh.priv
  · intro i hi
    obtain ⟨s, hs⟩ := hi
    have hp := congrArg Prod.fst hs
    cases s with
    | inl x =>
        change Sum.inl (header 0 _ _ _ _) = (Sum.inl (header tag 0 0 level node) : Coordinate) at hp
        exact QuerySpace.header_ne_of_tag (Ne.symm h0) (Sum.inl.inj hp)
    | inr f =>
        change Sum.inl (header 8 _ _ _ _) = (Sum.inl (header tag 0 0 level node) : Coordinate) at hp
        exact QuerySpace.header_ne_of_tag (Ne.symm h8) (Sum.inl.inj hp)
  · intro m h
    cases h
theorem Coherent.mask_eq (hcoh : Coherent U T vals nv τ a) (level node : Nat) :
    maskOf a level node = evalWithAnswerFn T (SigGolfCandidate.T3.mask level node) := by
  have hp := hcoh.private_header 13 level (node/2) (by decide) (by decide)
  unfold maskOf SigGolfCandidate.T3.mask pairedMask privatePair privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [← hp]
  rfl
theorem Coherent.mac_eq (hcoh : Coherent U T vals nv τ a) (region : Region) :
    macOf a region = evalWithAnswerFn T (SigGolfCandidate.T3.privateMac region) := by
  have hk : (fun i : Fin 2 => a.priv (.inl (header 14 0 0 0 i.val))) =
      (fun i : Fin 2 => if i=0 then T (.inr (.inl (header 14 0 0 0 0)))
        else T (.inr (.inl (header 14 0 0 0 1)))) := by
    funext i
    fin_cases i <;> simp [hcoh.private_header 14 0 0 (by decide) (by decide),
      hcoh.private_header 14 0 1 (by decide) (by decide)]
  unfold macOf SigGolfCandidate.T3.privateMac SigGolfCandidate.T3.privateMacKey privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [hk]
  rfl
theorem Coherent.region (hcoh : Coherent U T vals nv τ a) :
    Correctness.cacheRegion (fun level node => topValue (keyValues vals) level node ^^^ maskOf a level node) =
      Correctness.cacheRegion (Correctness.maskedTop T) := by
  apply cacheRegion_congr
  intro level node hl hl' hn
  rw [hcoh.topValue_eq level node hl hl' hn, hcoh.mask_eq]
  rfl
theorem rootNode_coord : treeChild 0 0 12 0 = some (.inl (.node (rootNode 0 0))) := by
  unfold treeChild treeNodeAt
  rw [if_neg (by decide), dif_pos (by simp [height])]
  rfl
theorem Coherent.pk (hcoh : Coherent U T vals nv τ a) :
    keyValues vals (.inl (.node (rootNode 0 0))) = (evalWithAnswerFn T keygen).1 := by
  rw [show (evalWithAnswerFn T keygen).1 = Extract.honestRoot T 0 0 from Extract.keygen_pk T,
    honestRoot_label hcoh.agrees 0 ⟨0, by decide⟩]
  have hmem := treeChild_mem_keygen 12 0 (by decide) le_rfl (by decide) _ rootNode_coord
  unfold keyValues
  rw [lookupVal_map vals keygenDisclosed _ hmem]
  exact (joinLabels_low (fun N => vals (.inl N)) a.high _).symm
theorem Coherent.published (hcoh : Coherent U T vals nv τ a) :
    (⟨macOf a (Correctness.cacheRegion fun level node =>
        topValue (keyValues vals) level node ^^^ maskOf a level node),
      Correctness.cacheRegion fun level node => topValue (keyValues vals) level node ^^^ maskOf a level node⟩ :
        SigGolfCandidate.T3.Cache) = (evalWithAnswerFn T keygen).2 := by
  obtain ⟨-, hreg, htag⟩ := Correctness.keygen_correct T
  rw [hcoh.region, hcoh.mac_eq]
  unfold Correctness.CacheTagCorrect at htag
  cases hk : (evalWithAnswerFn T keygen).2 with
  | mk tag region =>
      rw [hk] at hreg htag
      simp only at hreg htag
      subst hreg
      rw [htag]
end Keygen
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section



namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeCoupling (publicHash_respects)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingShort : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Short
variable {A T : Answers} (hAT : Wots.Ref.ShortAgree A T)
include hAT
theorem secretsOf_short : secretsOf A = secretsOf T := by
  funext s
  cases s with
  | inl x => exact Wots.Ref.leafSeed_short hAT _ _ _ _
  | inr f =>
      change wctSeedOf A f = wctSeedOf T f
      unfold wctSeedOf
      dsimp only
      rw [Wots.Ref.ShortRespects.privatePair 8 f.2.1.val f.1.val 0 (4 * f.2.2.1.val + f.2.2.2.val / 2) A T hAT]
theorem honestValue_short : LargeResidual.honestValue A = LargeResidual.honestValue T := by
  funext c
  cases c with
  | inl N =>
      change (A (.inl (.inr (Extract.honestInput A N.toPos)))).extractLsb' 0 128 =
        (T (.inl (.inr (Extract.honestInput T N.toPos)))).extractLsb' 0 128
      rw [Wots.Ref.honestInput_short hAT _ (toPos_bounded N),
        hAT.public _ (Wots.Ref.honestInput_length T N.toPos)]
  | inr s =>
      change secretsOf A s = secretsOf T s
      rw [secretsOf_short hAT]
theorem contactTest_short (K : Coord → Prop) (X : HashInput) (y : HashOutput) :
    ContactTest A K X y ↔ ContactTest T K X y := by
  have hin : ∀ N : CanonGraph.Node, Extract.honestInput A N.toPos = Extract.honestInput T N.toPos :=
    fun N => Wots.Ref.honestInput_short hAT _ (toPos_bounded N)
  unfold ContactTest StructuralContact EncodingContact
  simp only [honestValue_short hAT, hin, Wots.Ref.referenceInput_short hAT, Wots.Ref.referenceDigits_short hAT]
theorem digestSearch_short (rho : Digest) (m : Message) :
    ∀ fuel c, evalWithAnswerFn A (WCT9.digestSearch rho m c fuel) = evalWithAnswerFn T (WCT9.digestSearch rho m c fuel) := by
  intro fuel
  induction fuel with
  | zero => intro c; rfl
  | succ fuel ih =>
      intro c
      simp only [WCT9.digestSearch, digest, evalWithAnswerFn_bind]
      have hlen : (pad64 (digestInput rho m (BitVec.ofNat 32 c))).length ≤ SeccLaw.maxInputLength := by
        rw [BPB.pad64_digestInput, BPB.digestInput_length]
        unfold SeccLaw.maxInputLength
        omega
      rw [publicHash_respects hAT _ hlen A T hAT]
      split_ifs
      · rfl
      · exact ih (c + 1)
theorem signDigest_short (m : Message) : LargeResidual.signDigest A m = LargeResidual.signDigest T m := by
  unfold LargeResidual.signDigest
  have hn : evalWithAnswerFn A (SigGolfCandidate.T3.privateNonce m) = evalWithAnswerFn T (SigGolfCandidate.T3.privateNonce m) := by
    simp only [SigGolfCandidate.T3.privateNonce, privateHash, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    change (A (.inr (.inr (.inl m)))).extractLsb' 0 128 = (T (.inr (.inr (.inl m)))).extractLsb' 0 128
    rw [hAT.priv]
  rw [hn]
  exact digestSearch_short hAT _ _ _ _
theorem signDisclosed_short (published : SigGolfCandidate.T3.Cache) (request : Security.Request) :
    signDisclosed A published request = signDisclosed T published request := by
  have hd : Wots.referenceDigits A = Wots.referenceDigits T := funext (Wots.Ref.referenceDigits_short hAT)
  have hok : ∀ index, RouteOk A index ↔ RouteOk T index := by
    intro index
    unfold RouteOk
    simp only [Wots.Ref.referenceSearch_short hAT]
  unfold signDisclosed LargeResidual.signItems
  rw [signDigest_short hAT, hd]
  split_ifs
  · rcases LargeResidual.signDigest T request.message with _ | ⟨c, N⟩
    · rfl
    · simp only [hok]
  · rfl
theorem query_short (U : Finset HashInput) (q : Nat) (mon : Monitor) (X : HashInput) (y : HashOutput) :
    mon.query U A q X y = mon.query U T q X y := by
  unfold Monitor.query
  simp only [contactTest_short hAT]
theorem event_short (U : Finset HashInput) (q : Nat) (mon : Monitor) (e : FirstHit.QueryEvent) :
    mon.event U A q e = mon.event U T q e := by
  rcases e with ⟨before, (n | X) | c, answer⟩
  · rfl
  · exact query_short hAT U q mon X answer
  · rfl
theorem events_short (U : Finset HashInput) (q : Nat) (events : List FirstHit.QueryEvent) (mon : Monitor) :
    events.foldl (Monitor.event U A q) mon = events.foldl (Monitor.event U T q) mon := by
  induction events generalizing mon with
  | nil => rfl
  | cons e rest ih => rw [List.foldl_cons, List.foldl_cons, event_short hAT, ih]
theorem steps_short (U : Finset HashInput) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep) (mon : Monitor) :
    steps.foldl (Monitor.step U A q published) mon = steps.foldl (Monitor.step U T q published) mon := by
  induction steps generalizing mon with
  | nil => rfl
  | cons s rest ih =>
      rw [List.foldl_cons, List.foldl_cons]
      have h1 : Monitor.step U A q published mon s = Monitor.step U T q published mon s := by
        cases s with
        | world e => exact event_short hAT U q mon e
        | sign request out events =>
            simp only [Monitor.step, Monitor.sign, signDisclosed_short hAT]
      rw [h1, ih]
theorem monitorRun_short (U : Finset HashInput) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) :
    monitorRun U A q published steps verdict = monitorRun U T q published steps verdict := by
  unfold monitorRun
  rw [steps_short hAT, events_short hAT]
end Short
def ContactR (adversary : AdversaryP) (q : Nat) (result : FirstHit.Recorded Bool) (A : Answers) : Prop :=
  ∀ generated tagged checked, TaggedSplit adversary result generated tagged checked →
    (monitorRun (Wots.referenceInputs adversary) A q generated.value.2 tagged.steps checked.events).contact = true
theorem contact_eq_contactR (adversary : AdversaryP) (q : Nat) (z : PaddedGame.TraceResult × Answers) :
    Contact adversary q z = ContactR adversary q (QueryRecorded.recordedTrace z.1) z.2 := rfl
theorem contactR_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (adversary : AdversaryP) (q : Nat)
    (result : FirstHit.Recorded Bool) : ContactR adversary q result A ↔ ContactR adversary q result T := by
  unfold ContactR
  simp only [monitorRun_short hAT]
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
