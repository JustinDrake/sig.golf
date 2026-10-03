import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.StatementLemmas
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Cached
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Charge
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Execution

section


namespace SphincsSecurity.Concrete
open OracleComp
variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]
theorem layerMessage_bottomLayer (secretKey : SecretKey) (index : Index) :
    layerMessage (m := m) secretKey index bottomLayer
      = ftsKey secretKey.parameter index (secretKey.ftsSecret index) := by
  rw [layerMessage, dif_neg (by decide)]
theorem layerMessage_of_lt (secretKey : SecretKey) (index : Index) (lay : Layer)
    (hbelow : lay.val + 1 < numLayers) :
    layerMessage (m := m) secretKey index lay
      = treeRoot secretKey.parameter ⟨lay.val + 1, hbelow⟩
          (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
          (secretKey.otsSecret ⟨lay.val + 1, hbelow⟩ (treeIndexAt index ⟨lay.val + 1, hbelow⟩)) := by
  rw [layerMessage, dif_pos hbelow]
end SphincsSecurity.Concrete
end

section




namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
variable {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
  {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
  {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
  {cache : QueryCache HashSpec}
theorem counters_of_verify (publicKey : PublicKey) (message : Message) (signature : Signature)
    (hverify : evalWithAnswerFn f (verify publicKey message signature) = true) :
    CountersInRange signature := by
  by_contra hcounters
  rw [verify_eq_of_not_counters publicKey message signature hcounters] at hverify
  simp at hverify
theorem verify_extract (publicKey : PublicKey) (message : Message) (signature : Signature)
    (hverify : evalWithAnswerFn f (verify publicKey message signature) = true)
    (hrun : CachedRun cache f (verify publicKey message signature)) :
    ∃ digest : MessageDigest,
      evalWithAnswerFn f
          (messageDigest publicKey.parameter publicKey.root message signature.randomness) = digest
        ∧ CachedRun cache f
          (messageDigest publicKey.parameter publicKey.root message signature.randomness)
        ∧ ∃ ftsPublicKey : Digest,
          evalWithAnswerFn f (ftsRecover publicKey.parameter (digestIndex digest)
              (slotValue (digestLeaves digest)) signature.fts) = some ftsPublicKey
            ∧ evalWithAnswerFn f
              (verifyLayers publicKey.parameter (digestIndex digest) signature numLayers ftsPublicKey)
              = some publicKey.root
            ∧ CachedRun cache f (ftsRecover publicKey.parameter (digestIndex digest)
              (slotValue (digestLeaves digest)) signature.fts)
            ∧ CachedRun cache f
              (verifyLayers publicKey.parameter (digestIndex digest) signature numLayers ftsPublicKey) := by
  have hcounters := counters_of_verify publicKey message signature hverify
  let digest := evalWithAnswerFn f
    (messageDigest publicKey.parameter publicKey.root message signature.randomness)
  rw [verify_eq _ _ _ hcounters] at hverify hrun
  rw [evalWithAnswerFn_bind] at hverify
  have hmessageRun := hrun.bind_left
  have hafterDigest := hrun.bind_right
  change evalWithAnswerFn f (do
    match ← ftsRecover publicKey.parameter (digestIndex digest) (slotValue (digestLeaves digest))
        signature.fts with
    | none => pure false
    | some ftsPublicKey =>
        match ← verifyLayers publicKey.parameter (digestIndex digest) signature numLayers
            ftsPublicKey with
        | none => pure false
        | some root => pure (decide (root = publicKey.root))) = true at hverify
  change CachedRun cache f (do
    match ← ftsRecover publicKey.parameter (digestIndex digest) (slotValue (digestLeaves digest))
        signature.fts with
    | none => pure false
    | some ftsPublicKey =>
        match ← verifyLayers publicKey.parameter (digestIndex digest) signature numLayers
            ftsPublicKey with
        | none => pure false
        | some root => pure (decide (root = publicKey.root))) at hafterDigest
  have hfts := hafterDigest.bind_left
  rw [evalWithAnswerFn_bind] at hverify
  have hafterFts := hafterDigest.bind_right
  revert hverify hafterFts
  cases hkey : evalWithAnswerFn f (ftsRecover publicKey.parameter (digestIndex digest)
      (slotValue (digestLeaves digest)) signature.fts) with
  | none => intro hverify; simp at hverify
  | some ftsPublicKey =>
      intro hverify hafterFts
      simp only at hverify hafterFts
      rw [evalWithAnswerFn_bind] at hverify
      have hlayersRun := hafterFts.bind_left
      refine ⟨digest, rfl, hmessageRun, ftsPublicKey, hkey, ?_, hfts, hlayersRun⟩
      cases hresult : evalWithAnswerFn f
          (verifyLayers publicKey.parameter (digestIndex digest) signature numLayers ftsPublicKey) with
      | none =>
          rw [hresult] at hverify
          simp at hverify
      | some root =>
          rw [hresult] at hverify
          simp only [evalWithAnswerFn_pure, decide_eq_true_eq] at hverify
          simp [hverify]
theorem verifyLayers_succ_extract_cached (index : Index) (signature : Signature)
    (remaining : Nat) (hlayer : remaining < numLayers) (message target : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayers parameter index signature (remaining + 1) message) = some target)
    (hrun : CachedRun cache f
      (verifyLayers parameter index signature (remaining + 1) message)) :
    ∃ leafValue,
      let lay : Layer := ⟨remaining, hlayer⟩
      let tree := treeIndexAt index lay
      let leafIdx := leafIndexAt index lay
      let rootValue := foldValue f parameter lay tree leafIdx (signaturePath signature lay)
        leafValue (layerHeight lay)
      evalWithAnswerFn f (otsLeafAttempt parameter lay tree leafIdx message (signature.counter lay)
          (signature.chainValue lay)) = some leafValue
        ∧ evalWithAnswerFn f (verifyLayers parameter index signature remaining rootValue)
          = some target
        ∧ CachedRun cache f (otsLeafAttempt parameter lay tree leafIdx message (signature.counter lay)
          (signature.chainValue lay))
        ∧ CachedRun cache f (treeFold parameter lay tree leafIdx (signaturePath signature lay)
          (layerHeight lay) leafValue)
        ∧ CachedRun cache f (verifyLayers parameter index signature remaining rootValue) := by
  obtain ⟨leafValue, hleaf, hrest⟩ :=
    verifyLayers_succ_extract f parameter index signature remaining hlayer message target hverify
  rw [verifyLayers_succ_eq, dif_pos hlayer] at hrun
  have hots := hrun.bind_left
  have hafter := hrun.bind_right
  rw [hleaf] at hafter
  exact ⟨leafValue, hleaf, hrest, hots, hafter.bind_left, hafter.bind_right⟩
def LayerFrame (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (index : Index) (signature : Signature)
    (lay : Layer) (message target leafValue : Digest) : Prop :=
  evalWithAnswerFn f
        (otsLeafAttempt parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message
          (signature.counter lay) (signature.chainValue lay)) = some leafValue
      ∧ evalWithAnswerFn f
        (verifyLayers parameter index signature lay.val
          (foldValue f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (signaturePath signature lay) leafValue (layerHeight lay))) = some target
      ∧ CachedRun cache f
        (otsLeafAttempt parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message
          (signature.counter lay) (signature.chainValue lay))
      ∧ CachedRun cache f
        (treeFold parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (signaturePath signature lay) (layerHeight lay) leafValue)
      ∧ CachedRun cache f
        (verifyLayers parameter index signature lay.val
          (foldValue f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (signaturePath signature lay) leafValue (layerHeight lay)))
def LayerRun (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (index : Index) (signature : Signature)
    (lay : Layer) (message target : Digest) : Prop :=
  ∃ leafValue, LayerFrame f cache parameter index signature lay message target leafValue
theorem layerRun_of_verify (index : Index) (signature : Signature)
    (lay : Layer) (message target : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayers parameter index signature (lay.val + 1) message) = some target)
    (hrun : CachedRun cache f
      (verifyLayers parameter index signature (lay.val + 1) message)) :
    LayerRun f cache parameter index signature lay message target := by
  obtain ⟨leafValue, hleaf, hnext, hleafRun, hfoldRun, hnextRun⟩ :=
    verifyLayers_succ_extract_cached (f := f) (cache := cache) index signature lay.val lay.isLt
      message target hverify hrun
  exact ⟨leafValue, hleaf, hnext, hleafRun, hfoldRun, hnextRun⟩
theorem hypertree_walk (key : SecretKey) (index : Index) (signature : Signature) (Q : Layer → Prop)
    (hstep : ∀ lay message leafValue,
      LayerFrame f cache key.parameter index signature lay message key.root leafValue →
      foldValue f key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (signaturePath signature lay) leafValue (layerHeight lay) =
        honestNode f key.parameter lay (treeIndexAt index lay) (key.otsSecret lay (treeIndexAt index lay))
          (layerHeight lay) 0 →
      message = evalWithAnswerFn f (layerMessage key index lay) ∧ Q lay)
    (hroot : key.root = honestNode f key.parameter topLayer rootTree (key.otsSecret topLayer rootTree)
      (layerHeight topLayer) 0)
    (ftsPublicKey : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayers key.parameter index signature numLayers ftsPublicKey) = some key.root)
    (hrun : CachedRun cache f (verifyLayers key.parameter index signature numLayers ftsPublicKey)) :
    (∀ lay, Q lay) ∧ ftsPublicKey = evalWithAnswerFn f (layerMessage key index bottomLayer) := by
  have hwalk : ∀ remaining, (hr : remaining ≤ numLayers) → ∀ message,
      evalWithAnswerFn f (verifyLayers key.parameter index signature remaining message) = some key.root →
      CachedRun cache f (verifyLayers key.parameter index signature remaining message) →
      (∀ lay : Layer, lay.val < remaining → Q lay) ∧
        (∀ h : 0 < remaining,
          message = evalWithAnswerFn f (layerMessage key index ⟨remaining - 1, by have := hr; omega⟩)) ∧
        (remaining = 0 → message = key.root) := by
    intro remaining
    induction remaining with
    | zero =>
        intro _ message hv _
        simp only [verifyLayers_zero_eq, evalWithAnswerFn_pure, Option.some.injEq] at hv
        exact ⟨fun lay h => absurd h (Nat.not_lt_zero _), fun h => absurd h (Nat.lt_irrefl _),
          fun _ => hv⟩
    | succ r ih =>
        intro hr message hv hc
        have hlayer : r < numLayers := by omega
        let lay : Layer := ⟨r, hlayer⟩
        obtain ⟨leafValue, hframe⟩ :=
          layerRun_of_verify (f := f) (cache := cache) index signature lay message key.root hv hc
        have hrest := ih (by omega) _ hframe.2.1 hframe.2.2.2.2
        have hfold : foldValue f key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (signaturePath signature lay) leafValue (layerHeight lay) =
            honestNode f key.parameter lay (treeIndexAt index lay)
              (key.otsSecret lay (treeIndexAt index lay)) (layerHeight lay) 0 := by
          rcases Nat.eq_zero_or_pos r with hzero | hpos
          · have htop : lay = topLayer := Fin.ext hzero
            have htree : treeIndexAt index lay = rootTree := by
              rw [htop]
              exact Fin.ext (treeIndexAt_topLayer index)
            rw [hrest.2.2 hzero, hroot, htree, htop]
          · rw [hrest.2.1 hpos]
            have hbelow : r - 1 + 1 < numLayers := by omega
            rw [layerMessage_of_lt key index ⟨r - 1, by omega⟩ hbelow]
            have hl : (⟨r - 1 + 1, hbelow⟩ : Layer) = lay := Fin.ext (by simp [lay]; omega)
            simp only [hl]
            rfl
        obtain ⟨hmessage, hq⟩ := hstep lay message leafValue hframe hfold
        refine ⟨fun other hother => ?_, fun _ => hmessage, fun h => absurd h (Nat.succ_ne_zero r)⟩
        by_cases heq : other.val = r
        · have : other = lay := Fin.ext heq
          rw [this]
          exact hq
        · exact hrest.1 other (by omega)
  obtain ⟨hq, hmessage, _⟩ := hwalk numLayers le_rfl ftsPublicKey hverify hrun
  exact ⟨fun lay => hq lay lay.isLt, hmessage (by decide)⟩
def HonestLayerOpening (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (counter : Counter) (values : ChainIndex → Digest) (path : Nat → Digest) : Prop :=
  ∃ codeword : Encoding,
    evalWithAnswerFn f (encodeAttempt parameter lay tree leafIdx message counter) = some codeword
      ∧ (∀ chainIdx, values chainIdx
        = honestChain f parameter lay tree leafIdx chainIdx
          (otsSecret lay tree leafIdx chainIdx) (codeword chainIdx).val)
      ∧ ∀ level, level < layerHeight lay → path level
        = honestNode f parameter lay tree (otsSecret lay tree) level
          (Nat.xor (leafIdx.val / 2 ^ level) 1)
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity
open OracleComp OracleSpec
noncomputable def replayRomImpl (f : QueryImpl HashSpec Id) :
    QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec + (f.liftTarget ProbComp).withCaching
noncomputable def replayHashImpl (f : QueryImpl HashSpec Id) :
    QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp) :=
  (f.liftTarget ProbComp).withCaching
theorem replayRom_of_mem_support {alpha : Type} (oa : OracleComp OracleWorld alpha)
    (cache : QueryCache HashSpec) (a : alpha) (finalCache : QueryCache HashSpec)
    (hmem : (a, finalCache) ∈ support ((simulateQ romImpl oa).run cache))
    (f : QueryImpl HashSpec Id) (hf : finalCache.AgreesWithFn f) :
    (a, finalCache) ∈ support ((simulateQ (replayRomImpl f) oa).run cache) := by
  induction oa using OracleComp.inductionOn generalizing cache a finalCache with
  | pure value =>
      simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using hmem
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem ⊢
      obtain ⟨⟨answer, middleCache⟩, hquery, hrest⟩ := hmem
      refine ⟨⟨answer, middleCache⟩, ?_, ih answer middleCache a finalCache hrest hf⟩
      cases input with
      | inl sample =>
          change (answer, middleCache) ∈ support (((unifFwdImpl HashSpec) sample).run cache)
            at hquery ⊢
          exact hquery
      | inr hashInput =>
          change HashOutput at answer
          change (answer, middleCache) ∈ support
            (((randomOracle : QueryImpl HashSpec _) hashInput).run cache) at hquery
          have hmiddleLe : middleCache ≤ finalCache :=
            simulateQ_romImpl_cache_le (next answer) middleCache _ hrest
          change (answer, middleCache) ∈ support
            ((((f.liftTarget ProbComp).withCaching : QueryImpl HashSpec _) hashInput).run cache)
          cases hcache : cache hashInput with
          | some old =>
              rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache, support_pure,
                Set.mem_singleton_iff] at hquery
              obtain ⟨rfl, rfl⟩ := hquery
              rw [QueryImpl.withCaching_run_some _ hcache, support_pure, Set.mem_singleton_iff]
          | none =>
              rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map] at hquery
              obtain ⟨sampled, _, heq⟩ := hquery
              obtain ⟨rfl, rfl⟩ := heq
              have hfanswer : f hashInput = answer :=
                hf (hmiddleLe (QueryCache.cacheQuery_self cache hashInput answer))
              rw [QueryImpl.withCaching_run_none _ hcache, support_map]
              refine ⟨f hashInput, ?_, ?_⟩
              · change f hashInput ∈ support (pure (f hashInput) : ProbComp HashOutput)
                exact Set.mem_singleton _
              · rw [hfanswer]
theorem replayHash_mem_randomOracle {alpha : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) (cache : QueryCache HashSpec)
    (a : alpha) (finalCache : QueryCache HashSpec)
    (hmem : (a, finalCache) ∈ support
      ((simulateQ (replayHashImpl f) oa).run cache)) :
    (a, finalCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache) := by
  induction oa using OracleComp.inductionOn generalizing cache a finalCache with
  | pure value =>
      simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using hmem
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem ⊢
      obtain ⟨⟨answer, middleCache⟩, hquery, hrest⟩ := hmem
      refine ⟨⟨answer, middleCache⟩, ?_, ih answer middleCache a finalCache hrest⟩
      change (answer, middleCache) ∈ support
        ((((f.liftTarget ProbComp).withCaching : QueryImpl HashSpec _) input).run cache)
        at hquery
      change (answer, middleCache) ∈ support
        (((randomOracle : QueryImpl HashSpec _) input).run cache)
      cases hcache : cache input with
      | some old =>
          rw [QueryImpl.withCaching_run_some _ hcache, support_pure,
            Set.mem_singleton_iff] at hquery
          obtain ⟨rfl, rfl⟩ := hquery
          rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache, support_pure,
            Set.mem_singleton_iff]
      | none =>
          rw [QueryImpl.withCaching_run_none _ hcache, support_map] at hquery
          obtain ⟨sampled, hsampled, heq⟩ := hquery
          have hsampledEq : sampled = f input := by
            change sampled ∈ support (pure (f input) : ProbComp HashOutput) at hsampled
            simpa using hsampled
          subst sampled
          obtain ⟨rfl, rfl⟩ := heq
          rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map]
          exact ⟨f input, by simp [uniformSampleImpl], rfl⟩
theorem replayHash_of_mem_support {alpha : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) (cache : QueryCache HashSpec)
    (a : alpha) (finalCache : QueryCache HashSpec)
    (hmem : (a, finalCache) ∈ support
      ((simulateQ (replayHashImpl f) oa).run cache))
    (hf : finalCache.AgreesWithFn f) :
    cache ≤ finalCache ∧ evalWithAnswerFn f oa = a ∧ CachedRun finalCache f oa := by
  have hrandom := replayHash_mem_randomOracle f oa cache a finalCache hmem
  obtain ⟨hle, heval, hqueries⟩ := replay_of_mem_support oa cache a finalCache hrandom f hf
  exact ⟨hle, heval, hqueries⟩
theorem simulateQ_replayRom_liftM {alpha : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) :
    simulateQ (replayRomImpl f) (liftM oa : OracleComp OracleWorld alpha)
      = simulateQ (replayHashImpl f) oa :=
  QueryImpl.simulateQ_add_liftM_right _ _ oa
end SphincsSecurity
end

section



namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
abbrev LayerPart :=
  Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest)
def SuccessfulDigestRun (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) : Prop :=
  randomness ∈ support sampleRandomness
    ∧ evalWithAnswerFn f (signAttempt secretKey message randomness) = some (index, leaves)
    ∧ CachedRun cache f (signAttempt secretKey message randomness)
theorem SuccessfulDigestRun.extract {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {message : Message} {randomness : Randomness} {index : Index}
    {leaves : IndexGroup → FtsLeaf}
    (hrun : SuccessfulDigestRun f cache secretKey message randomness index leaves) :
    randomness ∈ support sampleRandomness
      ∧ ∃ digest : MessageDigest,
        evalWithAnswerFn f
            (messageDigest secretKey.parameter secretKey.root message randomness) = digest
          ∧ Admissible digest
          ∧ index = digestIndex digest
          ∧ leaves = digestLeaves digest
          ∧ CachedRun cache f
            (messageDigest secretKey.parameter secretKey.root message randomness) := by
  refine ⟨hrun.1, ?_⟩
  have heval := hrun.2.1
  simp only [signAttempt, evalWithAnswerFn_bind] at heval
  let digest := evalWithAnswerFn f
    (messageDigest secretKey.parameter secretKey.root message randomness)
  by_cases hadmissible : Admissible digest
  · simp only [show Admissible (evalWithAnswerFn f
        (messageDigest secretKey.parameter secretKey.root message randomness)) from hadmissible,
      if_true, evalWithAnswerFn_pure] at heval
    have hresult : (digestIndex digest, digestLeaves digest) = (index, leaves) :=
      Option.some.inj heval
    have hfields := Prod.mk.inj hresult
    refine ⟨digest, rfl, hadmissible, hfields.1.symm, hfields.2.symm, ?_⟩
    exact hrun.2.2.bind_left
  · simp only [show ¬ Admissible (evalWithAnswerFn f
        (messageDigest secretKey.parameter secretKey.root message randomness)) from hadmissible,
      if_false, evalWithAnswerFn_pure] at heval
    simp at heval
theorem successfulDigestLoop_of_mem_support (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (message : Message) (attempts : Nat) (randomness : Randomness)
    (index : Index) (leaves : IndexGroup → FtsLeaf)
    (beforeCache afterCache finalCache : QueryCache HashSpec)
    (hmem : (some (randomness, index, leaves), afterCache) ∈ support
      ((simulateQ (replayRomImpl f) (signDigestLoop attempts secretKey message)).run beforeCache))
    (hleFinal : afterCache ≤ finalCache) (hf : finalCache.AgreesWithFn f) :
    SuccessfulDigestRun f finalCache secretKey message randomness index leaves := by
  induction attempts generalizing beforeCache afterCache randomness index leaves with
  | zero =>
      simp only [signDigestLoop, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      cases hmem.1
  | succ attempts ih =>
      rw [signDigestLoop, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨sampledRandomness, sampleCache⟩, hsample, hrest⟩ := hmem
      have hsample' : (sampledRandomness, sampleCache) ∈ support
          ((simulateQ (unifFwdImpl HashSpec) sampleRandomness).run beforeCache) := by
        simpa only [replayRomImpl, QueryImpl.simulateQ_add_liftM_left] using hsample
      rw [unifFwdImpl.simulateQ_run, support_map] at hsample'
      obtain ⟨sampledRandomness', hsampled, heq⟩ := hsample'
      obtain ⟨rfl, rfl⟩ := heq
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨attempt, attemptCache⟩, hattempt, hfinish⟩ := hrest
      cases attempt with
      | none =>
          exact ih (randomness := randomness) (index := index) (leaves := leaves)
            (beforeCache := attemptCache) (afterCache := afterCache) hfinish hleFinal
      | some selected =>
          obtain ⟨selectedIndex, selectedLeaves⟩ := selected
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hfinish
          obtain ⟨hresult, hcache⟩ := hfinish
          obtain ⟨rfl, rfl, rfl⟩ := hresult
          have hleAttempt : attemptCache ≤ finalCache := by
            rw [← hcache]
            exact hleFinal
          have hattempt' : (some (index, leaves), attemptCache) ∈ support
              ((simulateQ (replayHashImpl f)
                (signAttempt secretKey message randomness)).run beforeCache) := by
            simpa only [simulateQ_replayRom_liftM] using hattempt
          have hfAttempt : attemptCache.AgreesWithFn f :=
            fun _ _ hcached => hf (hleAttempt hcached)
          obtain ⟨_, heval, hcached⟩ := replayHash_of_mem_support f
            (signAttempt secretKey message randomness) beforeCache (some (index, leaves))
            attemptCache hattempt' hfAttempt
          exact ⟨hsampled, heval, hcached.mono hleAttempt⟩
theorem index_eq_of_bottom_position_eq {left right : Index}
    (htree : treeIndexAt left bottomLayer = treeIndexAt right bottomLayer)
    (hleaf : leafIndexAt left bottomLayer = leafIndexAt right bottomLayer) : left = right := by
  apply Fin.ext
  have htreeVal := congrArg Fin.val htree
  have hleafVal := congrArg Fin.val hleaf
  have habove : heightAbove bottomLayer = 29 := by decide
  have hheight : layerHeight bottomLayer = 5 := by decide
  have hleftTree : (treeIndexAt left bottomLayer).val = left.val / 32 := by
    rw [treeIndexAt_val, habove]
    norm_num [totalHeight]
  have hrightTree : (treeIndexAt right bottomLayer).val = right.val / 32 := by
    rw [treeIndexAt_val, habove]
    norm_num [totalHeight]
  have hleftLeaf : (leafIndexAt left bottomLayer).val = left.val % 32 := by
    rw [leafIndexAt_bottomLayer, hheight]
    norm_num
  have hrightLeaf : (leafIndexAt right bottomLayer).val = right.val % 32 := by
    rw [leafIndexAt_bottomLayer, hheight]
    norm_num
  rw [hleftTree, hrightTree] at htreeVal
  rw [hleftLeaf, hrightLeaf] at hleafVal
  omega
theorem nextTree_eq_of_position_eq {left right : Index} (lay : Layer)
    (hbelow : lay.val + 1 < numLayers)
    (htree : treeIndexAt left lay = treeIndexAt right lay)
    (hleaf : leafIndexAt left lay = leafIndexAt right lay) :
    treeIndexAt left ⟨lay.val + 1, hbelow⟩ = treeIndexAt right ⟨lay.val + 1, hbelow⟩ := by
  apply Fin.ext
  rw [layers_link left lay hbelow, layers_link right lay hbelow, congrArg Fin.val htree,
    congrArg Fin.val hleaf]
theorem layerMessage_eq_of_position_eq (secretKey : SecretKey) (left right : Index)
    (lay : Layer) (htree : treeIndexAt left lay = treeIndexAt right lay)
    (hleaf : leafIndexAt left lay = leafIndexAt right lay) :
    layerMessage (m := OracleComp HashSpec) secretKey left lay =
      layerMessage secretKey right lay := by
  by_cases hbelow : lay.val + 1 < numLayers
  · rw [layerMessage_of_lt secretKey left lay hbelow, layerMessage_of_lt secretKey right lay hbelow,
      nextTree_eq_of_position_eq lay hbelow htree hleaf]
  · have hbottom : lay = bottomLayer := Fin.ext (by
      have := lay.isLt
      simp only [bottomLayer]
      omega)
    subst hbottom
    have hindex := index_eq_of_bottom_position_eq htree hleaf
    subst right
    rfl
end SphincsSecurity.Concrete
end
