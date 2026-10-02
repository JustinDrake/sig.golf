import SigGolfCandidate.SphincsSecurity.Completeness
import SigGolfCandidate.SphincsSecurity.Completeness.Recovery
import SigGolfCandidate.Equiv.Honest
import SigGolfCandidate.Equiv.Expand

/-!
# The abstract honest game over the hash oracle alone

`game seed m` is `Completeness.seededGameCore seed m` without the lift into `OracleWorld`:
generate the key from the seed, sign, verify. `seededExperiment_eq` runs it against the lazy random
oracle; `hq_game`: all its queries are `Honest`.

`gameX seed m` is the organizer's honest pipeline in abstract form: it also expands the compressed
signature (`Equiv.aExpand`, one digest query) and verifies the decoded witness. Under every answer
function it computes what `game` computes (`eval_gameX`): the expansion's digest query of `rho` returns
the digest the signer accepted, so (relation R4, `Equiv.expandOf_honest`) the witness decodes to the
signature itself.
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Final
open SphincsSecurity

/-- The honest abstract run from a fixed seed, over the hash oracle alone. -/
def game (seed : MasterSeed) (message : Message) : OracleComp SphincsSecurity.HashSpec Bool := do
  let (pk, cache, sk) ← Seeded.keygenFromSeed seed
  let some signature ←
      (Seeded.sign sk cache message : OracleComp SphincsSecurity.HashSpec (Option Signature))
    | return false
  (Concrete.verify pk message signature : OracleComp SphincsSecurity.HashSpec Bool)

/-- The honest abstract run with the expansion: key generation, signing, the expansion of the
compressed signature, verification of the decoded witness. -/
def gameX (seed : MasterSeed) (message : Message) : OracleComp SphincsSecurity.HashSpec Bool := do
  let (pk, cache, sk) ← Seeded.keygenFromSeed seed
  let some signature ←
      (Seeded.sign sk cache message : OracleComp SphincsSecurity.HashSpec (Option Signature))
    | return false
  let some witness ← Equiv.aExpand message pk (Equiv.compress signature) | return false
  (Concrete.verify pk message (Equiv.witDec witness) : OracleComp SphincsSecurity.HashSpec Bool)

theorem seededGameCore_eq (seed : MasterSeed) (message : Message) :
    Completeness.seededGameCore seed message =
      (liftM (game seed message) : OracleComp OracleWorld Bool) := by
  unfold Completeness.seededGameCore game
  simp only [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_bind]
  refine bind_congr fun kp => ?_
  rcases kp with ⟨pk, cache, sk⟩
  refine bind_congr fun s => ?_
  rcases s with _ | σ
  · simp
  · rfl

theorem seededExperiment_eq (seed : MasterSeed) (message : Message) :
    Completeness.seededExperiment seed message =
      (simulateQ (randomOracle : QueryImpl SphincsSecurity.HashSpec
        (StateT (QueryCache SphincsSecurity.HashSpec) ProbComp)) (game seed message)).run' ∅ := by
  unfold Completeness.seededExperiment Completeness.romImpl
  rw [seededGameCore_eq, QueryImpl.simulateQ_add_liftM_right]

theorem hq_game (seed : MasterSeed) (message : Message) : Equiv.HQ (game seed message) := by
  unfold game Seeded.keygenFromSeed Seeded.maskRegion
  simp only [bind_assoc, pure_bind]
  refine Equiv.hq_bind (Equiv.hq_buildLayerTablePaired _ rfl _ _ _ (fun _ _ => Equiv.hq_otsSecret _ _ _ _ _ _) _ _)
    fun t => ?_
  refine Equiv.hq_bind (Equiv.hq_sequenceFin _ fun _ => Equiv.hq_bind (Equiv.hq_sequenceFin _ fun _ =>
    Equiv.hq_bind (Equiv.hq_maskSecret _ _ _ _) fun _ => Equiv.hq_pure _) fun _ => Equiv.hq_pure _)
    fun _ => ?_
  refine Equiv.hq_bind (Equiv.hq_mac _ _ _) fun _ => ?_
  refine Equiv.hq_bind (Equiv.hq_sign _ rfl _ _) fun s => ?_
  rcases s with _ | σ
  · exact Equiv.hq_pure _
  · exact Equiv.hq_verify _ rfl _ _

theorem hq_gameX (seed : MasterSeed) (message : Message) : Equiv.HQ (gameX seed message) := by
  unfold gameX Seeded.keygenFromSeed Seeded.maskRegion
  simp only [bind_assoc, pure_bind]
  refine Equiv.hq_bind (Equiv.hq_buildLayerTablePaired _ rfl _ _ _ (fun _ _ => Equiv.hq_otsSecret _ _ _ _ _ _) _ _)
    fun t => ?_
  refine Equiv.hq_bind (Equiv.hq_sequenceFin _ fun _ => Equiv.hq_bind (Equiv.hq_sequenceFin _ fun _ =>
    Equiv.hq_bind (Equiv.hq_maskSecret _ _ _ _) fun _ => Equiv.hq_pure _) fun _ => Equiv.hq_pure _)
    fun _ => ?_
  refine Equiv.hq_bind (Equiv.hq_mac _ _ _) fun _ => ?_
  refine Equiv.hq_bind (Equiv.hq_sign _ rfl _ _) fun s => ?_
  rcases s with _ | σ
  · exact Equiv.hq_pure _
  · refine Equiv.hq_bind (Equiv.hq_aExpand _ _ _) fun w => ?_
    rcases w with _ | w
    · exact Equiv.hq_pure _
    · exact Equiv.hq_verify _ rfl _ _

/-! ## The expansion under a fixed answer function -/

section eval

variable (f : QueryImpl SphincsSecurity.HashSpec Id)

-- Both values stand for a whole tree build under `f`; unfolding them runs it.
attribute [local irreducible] Completeness.keygenTableValue Completeness.keygenRegionValue

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

theorem ofList_sigRho_compress (σ : Signature) :
    Ref.ofList 16 (Ref.sigRho (Ref.toList (Equiv.compress σ))) = σ.randomness := by
  rw [Equiv.toList_compress]
  unfold Ref.sigRho Equiv.compressList
  simp only [List.append_assoc]
  rw [Equiv.slice_append_left _ _ _ _ (by simp), Equiv.slice_full _ _ (Equiv.length_dv _)]
  exact Ref.ofList_toList (n := 16) _

/-- A signature signed with the key and cache of key generation is the honest opening of the admissible
digest of its randomness. -/
theorem sign_shape (seed : MasterSeed) (message : Message) {pk : PublicKey} {cache : TopCache}
    {sk : Seeded.SecretKey} {S : Signature}
    (hkeys : evalWithAnswerFn f (Seeded.keygenFromSeed seed) = (pk, cache, sk))
    (hsign : evalWithAnswerFn f (Seeded.sign sk cache message
      : OracleComp SphincsSecurity.HashSpec (Option Signature)) = some S) :
    pk = ⟨sk.root, 0⟩ ∧ sk.parameter = 0 ∧
    Concrete.Admissible (Completeness.digestValue f sk message S.randomness) ∧
    ∃ (secret : FtsLeaf → Digest) (node : Nat → Nat → Digest),
      S = ⟨S.randomness, Concrete.honestFts
        (Concrete.digestLeaves (Completeness.digestValue f sk message S.randomness)) secret node,
        S.layers⟩ := by
  rw [Completeness.eval_keygenFromSeed] at hkeys
  simp only [Prod.mk.injEq] at hkeys
  obtain ⟨rfl, rfl, rfl⟩ := hkeys
  refine ⟨rfl, rfl, ?_⟩
  obtain ⟨hadm, hsig⟩ := Completeness.signChecked_spec f _ _ (Completeness.keygen_cacheHonest f seed _)
    message (Completeness.signChecked_of_sign f _ _ message hsign)
  refine ⟨hadm, ?_⟩
  unfold Concrete.signatureValue at hsig
  cases hparts : SphincsSecurity.Concrete.sequenceFin (m := Option) (fun lay =>
      evalWithAnswerFn f (Concrete.signLayer (Completeness.tableKey f
        ⟨seed, 0, Completeness.keygenTableValue f seed (layerHeight topLayer) 0⟩)
        (Concrete.digestIndex (Completeness.digestValue f _ message S.randomness)) lay)) with
  | none => rw [hparts] at hsig; simp at hsig
  | some parts =>
    rw [hparts] at hsig
    simp only [Option.map_some, Option.some.injEq] at hsig
    rw [Concrete.eval_ftsOpen] at hsig
    rcases S with ⟨r, fts, layers⟩
    simp only [Signature.mk.injEq] at hsig
    obtain ⟨-, hfts, -⟩ := hsig
    subst hfts
    exact ⟨_, _, rfl⟩

/-! ### The counter phase of an honest signature

Each layer's signer ran the counter search from `0` on the layer's message; the expansion runs the
same search on the message it recomputes (the PORS root, then each layer's root), so it finds the
signer's counter, and the verifier's chains, leaf and fold give the next message. -/

open SphincsSecurity.Concrete (treeIndexAt leafIndexAt encodingSearch recoverChain leafHash treeFold
  signaturePath) in
/-- What one layer of the specification signs, read as the expansion reads it: the least-counter
search from `0` on the layer's message returns the layer's counter with an encoding whose chains,
from the layer's chain values, end at the specification's leaf. -/
theorem signLayer_search (key : SphincsSecurity.SecretKey) (index : Index) (lay : Layer)
    {part : PaddedLayer} (h : evalWithAnswerFn f (Concrete.signLayer key index lay) = some part) :
    ∃ enc, evalWithAnswerFn f (encodingSearch key.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay)
        (evalWithAnswerFn f (Concrete.layerMessage key index lay : OracleComp SphincsSecurity.HashSpec EncMessage))
        encodingAttemptLimit 0 : OracleComp SphincsSecurity.HashSpec (Option (Counter × Encoding)))
        = some (part.1, enc) ∧
      evalWithAnswerFn f (do
        let ends ← Concrete.sequenceFin (m := OracleComp SphincsSecurity.HashSpec) fun ch =>
          recoverChain key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay) ch (enc ch)
            (part.2.1 ch)
        leafHash key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay) ends :
          OracleComp SphincsSecurity.HashSpec Digest)
        = Concrete.honestNode f key.parameter lay (treeIndexAt index lay)
            (key.otsSecret lay (treeIndexAt index lay)) 0 (leafIndexAt index lay).val := by
  rw [Concrete.signLayer, evalWithAnswerFn_bind, Concrete.otsSign, evalWithAnswerFn_bind,
    Concrete.eval_otsSignFrom] at h
  cases hsearch : evalWithAnswerFn f (encodingSearch key.parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) (evalWithAnswerFn f (Concrete.layerMessage key index lay : OracleComp SphincsSecurity.HashSpec EncMessage))
      encodingAttemptLimit 0 : OracleComp SphincsSecurity.HashSpec (Option (Counter × Encoding))) with
  | none =>
      rw [hsearch] at h
      simp at h
  | some result =>
      obtain ⟨counter, word⟩ := result
      rw [hsearch] at h
      simp only [Option.map_some, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
        Option.some.injEq] at h
      subst h
      refine ⟨word, rfl, ?_⟩
      simp only [evalWithAnswerFn_bind, Concrete.evalWithAnswerFn_sequenceFin, Concrete.eval_recoverChain]
      rw [Concrete.honestNode_zero_eq_leafHash, Concrete.honestEndpoints_def]
      simp only [leafHash, Concrete.eval_tweakableHash]

/-- The counters a signature carries, layer `0` first. -/
def ctrOf (S : Signature) (j : Nat) : Nat :=
  if h : j < SphincsSecurity.numLayers then (S.layers ⟨j, h⟩).counter.toNat else 0

open SphincsSecurity.Concrete (treeIndexAt leafIndexAt encodingSearch recoverChain leafHash treeFold
  signaturePath) in
/-- **The counter phase recovers the signer's counters**: from the message entering layer `n - 1`,
on a witness-shaped signature with the signer's chain values and paths. -/
theorem eval_aLayers (key : SphincsSecurity.SecretKey) (hP : key.parameter = 0) (index : Index)
    (S S0 : Signature)
    (hlayers : ∀ lay : Layer, ∃ part, evalWithAnswerFn f (Concrete.signLayer key index lay) = some part
      ∧ S.layers lay = LayerSignature.ofPadded lay part)
    (hS0 : ∀ lay : Layer, (S0.layers lay).chainValues = (S.layers lay).chainValues ∧
      (S0.layers lay).path = (S.layers lay).path) :
    ∀ n : Nat, n ≤ SphincsSecurity.numLayers →
      evalWithAnswerFn f (Equiv.aLayers index S0 n (Completeness.enterMessage f key index n))
        = some ((List.range n).map (ctrOf S)) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro hn
  match n, hn with
  | 0, _ => simp [Equiv.aLayers]
  | 1, _ =>
    let lay : Layer := ⟨0, by decide⟩
    obtain ⟨part, hpart, hsig⟩ := hlayers lay
    obtain ⟨enc, hsearch, -⟩ := signLayer_search f key index lay hpart
    rw [hP] at hsearch
    unfold Equiv.aLayers
    rw [evalWithAnswerFn_bind]
    have hm : Completeness.enterMessage f key index 1 =
        evalWithAnswerFn f (Concrete.layerMessage key index lay : OracleComp SphincsSecurity.HashSpec EncMessage) := by
      rw [Completeness.enterMessage, dif_pos (by decide)]
    rw [hm]
    erw [hsearch]
    simp only [evalWithAnswerFn_pure, List.range_one, List.map_cons, List.map_nil]
    congr 2
    unfold ctrOf
    rw [dif_pos (by decide)]
    rw [show (⟨0, _⟩ : Layer) = lay from rfl, hsig]
  | k + 2, hk =>
    have hlk : k + 1 < SphincsSecurity.numLayers := by omega
    let lay : Layer := ⟨k + 1, hlk⟩
    obtain ⟨part, hpart, hsig⟩ := hlayers lay
    obtain ⟨enc, hsearch, hleaf⟩ := signLayer_search f key index lay hpart
    rw [hP] at hsearch hleaf
    obtain ⟨-, hleafSpec, hpath⟩ := Completeness.signLayer_spec f key index lay hpart
    have hm : Completeness.enterMessage f key index (k + 2) =
        evalWithAnswerFn f (Concrete.layerMessage key index lay : OracleComp SphincsSecurity.HashSpec EncMessage) := by
      rw [Completeness.enterMessage, dif_pos hlk]
    have hvals : (S0.layers lay).chainValues = part.2.1 := by rw [(hS0 lay).1, hsig]
    have hpos := SphincsSecurity.layerHeight_pos lay
    have hsigPath : ∀ level, level < SphincsSecurity.layerHeight lay →
        signaturePath S0 lay level =
          Concrete.honestNode f key.parameter lay (treeIndexAt index lay)
            (key.otsSecret lay (treeIndexAt index lay)) level
            (Nat.xor ((leafIndexAt index lay).val / 2 ^ level) 1) := fun level hlevel => by
      rw [signaturePath, dif_pos hlevel, (hS0 lay).2, hsig]
      exact hpath level hlevel
    have hfold := Completeness.eval_treeFold_honest f key.parameter lay
      (treeIndexAt index lay) (key.otsSecret lay (treeIndexAt index lay))
      (leafIndexAt index lay) (signaturePath S0 lay)
      (SphincsSecurity.layerHeight lay - 1) (fun level hlevel => hsigPath level (by omega))
    have hsib := hsigPath (SphincsSecurity.layerHeight lay - 1) (by omega)
    rw [hP] at hfold hsib
    unfold Equiv.aLayers
    rw [dif_pos hlk, evalWithAnswerFn_bind, hm]
    erw [hsearch]
    simp only [evalWithAnswerFn_bind]
    rw [hvals]
    have hleaf' := hleaf
    simp only [evalWithAnswerFn_bind] at hleaf'
    erw [hleaf']
    erw [hfold]
    rw [hsib, Concrete.topPair_honest f 0 lay (treeIndexAt index lay)
        (key.otsSecret lay (treeIndexAt index lay)) (leafIndexAt index lay)
        (Equiv.leafIndexAt_lt index lay) hpos,
      show Concrete.honestPair f 0 lay (treeIndexAt index lay) (key.otsSecret lay (treeIndexAt index lay))
        = Completeness.layerTop f key index lay by rw [Completeness.layerTop, hP],
      Completeness.layerTop_eq_enterMessage f key index (k + 1) hlk,
      ih (k + 1) (by omega) (by omega)]
    simp only [evalWithAnswerFn_pure]
    rw [show List.range (k + 2) = List.range (k + 1) ++ [k + 1] from List.range_succ, List.map_append]
    congr 3
    unfold ctrOf
    rw [dif_pos hlk, show (⟨k + 1, hlk⟩ : Layer) = lay from rfl, hsig]

/-- `LE32` of a counter's value decodes back to the counter. -/
theorem ofList_le32_counter (c : Counter) : Ref.ofList 4 (Ref.le32 c.toNat) = c := by
  rw [Ref.le32, Equiv.leBytes_eq_toList, BitVec.ofNat_toNat, BitVec.setWidth_eq, Ref.ofList_toList]

/-- Under a fixed answer function, the expansion of an honestly produced signature succeeds with a
witness decoding to the signature: the digest and the partial witness as before (R4), the PORS root
the verifier's recovery gives, and per layer the signer's counter (`eval_aLayers`). -/
theorem eval_aExpand_sign' (seed : MasterSeed) (message : Message) {pk : PublicKey} {cache : TopCache}
    {sk : Seeded.SecretKey} {S : Signature}
    (hkeys : evalWithAnswerFn f (Seeded.keygenFromSeed seed) = (pk, cache, sk))
    (hsign : evalWithAnswerFn f (Seeded.sign sk cache message
      : OracleComp SphincsSecurity.HashSpec (Option Signature)) = some S) :
    ∃ wl : List Legacy.Byte, wl.length = 16384 ∧ wl.take Ref.witLead = Ref.zeros Ref.witLead ∧
      evalWithAnswerFn f (Equiv.aExpand message pk (Equiv.compress S)) =
        some (Ref.ofList 13712 (Ref.cutW (Ref.withCounters wl ((List.range numLayers).map (ctrOf S))))) ∧
      Equiv.witDec (Ref.ofList 13712 (Ref.cutW (Ref.withCounters wl ((List.range numLayers).map (ctrOf S))))) =
        S := by
  rw [Completeness.eval_keygenFromSeed] at hkeys
  simp only [Prod.mk.injEq] at hkeys
  obtain ⟨rfl, rfl, rfl⟩ := hkeys
  set key := Completeness.tableKey f ⟨seed, 0, Completeness.keygenTableValue f seed (layerHeight topLayer) 0⟩
    with hkey
  obtain ⟨hadm, hsig⟩ := Completeness.signChecked_spec f _ _ (Completeness.keygen_cacheHonest f seed _)
    message (Completeness.signChecked_of_sign f _ _ message hsign)
  set d := Completeness.digestValue f ⟨seed, 0, Completeness.keygenTableValue f seed (layerHeight topLayer) 0⟩
    message S.randomness with hd
  set index := Concrete.digestIndex d with hindex
  set leaves := Concrete.digestLeaves d with hleaves
  have hP : key.parameter = 0 := rfl
  unfold Concrete.signatureValue at hsig
  rw [Concrete.sequenceFin_option_eq] at hsig
  split at hsig
  swap
  · simp at hsig
  rename_i hall
  simp only [Option.map_some, Option.some.injEq] at hsig
  have hlayers : ∀ lay : Layer, ∃ part, evalWithAnswerFn f (Concrete.signLayer key index lay) = some part
      ∧ S.layers lay = LayerSignature.ofPadded lay part := fun lay => by
    rw [← hsig]
    exact ⟨_, (Option.some_get (hall lay)).symm, rfl⟩
  have hfts : S.fts = Concrete.honestFts leaves (key.ftsSecret index Concrete.porsTree)
      (Concrete.honestFtsNode f key.parameter index Concrete.porsTree (key.ftsSecret index Concrete.porsTree)) := by
    rw [← hsig, Concrete.eval_ftsOpen]
  have hfts0 : S.fts = evalWithAnswerFn f (Concrete.ftsOpen 0 index leaves (key.ftsSecret index)) := by
    rw [← hsig, hP]
  have hS : S = ⟨S.randomness, Concrete.honestFts leaves (key.ftsSecret index Concrete.porsTree)
      (Concrete.honestFtsNode f key.parameter index Concrete.porsTree (key.ftsSecret index Concrete.porsTree)), S.layers⟩ := by
    rw [← hfts]
  obtain ⟨wl, hlen, hexp, hwit0, hwit⟩ := Equiv.expandOf_honest leaves hadm d.toNat
    (fun r => Equiv.leafOf_eq d r) S.randomness _ _ S.layers
  rw [← hS] at hexp
  -- the decoded partial witness
  have hW0 : Equiv.witSig wl = ⟨S.randomness, S.fts, fun lay =>
      ⟨0, (S.layers lay).chainValues, (S.layers lay).path⟩⟩ := by
    rw [hwit0, ← hfts]
  have hwf : Equiv.witFts wl = S.fts := by
    have := congrArg Signature.fts hW0
    exact this
  have hS0 : ∀ lay : Layer, ((Equiv.witSig wl).layers lay).chainValues = (S.layers lay).chainValues ∧
      ((Equiv.witSig wl).layers lay).path = (S.layers lay).path := fun lay => by
    rw [hW0]; exact ⟨rfl, rfl⟩
  have hbottom : Completeness.enterMessage f key index numLayers
      = (0, evalWithAnswerFn f (Concrete.ftsKey key.parameter index (key.ftsSecret index)
        : OracleComp SphincsSecurity.HashSpec Digest)) := by
    rw [show numLayers = 4 + 1 from rfl, Completeness.enterMessage, dif_pos (by decide)]
    change evalWithAnswerFn f (Concrete.layerMessage key index bottomLayer) = _
    rw [Concrete.layerMessage_bottomLayer_eq]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  have hL := eval_aLayers f key hP index S (Equiv.witSig wl) hlayers hS0 numLayers le_rfl
  rw [hbottom] at hL
  set cs := (List.range numLayers).map (ctrOf S) with hcs
  have hcsl : cs.length = 5 := by simp [hcs, numLayers]
  have hwc : (Ref.withCounters wl cs).length = 16384 := by
    rw [Equiv.length_withCounters _ _ (by omega), hlen]
  -- W1: the partial witness starts with the view's zero lead
  have hz : wl.take Ref.witLead = Ref.zeros Ref.witLead := by
    obtain ⟨-, -, -, hwl⟩ := Equiv.expandOf_some _ _ _ hexp
    rw [hwl]; exact Ref.take_witnessList _ _ _ _
  refine ⟨wl, hlen, hz, ?_, ?_⟩
  · unfold Equiv.aExpand
    rw [ofList_sigRho_compress, evalWithAnswerFn_bind]
    have e1 : evalWithAnswerFn f (Concrete.messageDigest (m := Equiv.AComp) 0 (⟨Completeness.keygenTableValue f seed (layerHeight topLayer) 0, 0⟩ : PublicKey).root message S.randomness)
        = d := by
      rw [hd, Completeness.digestValue]
    have hR := Completeness.eval_ftsRecover_ftsOpen f 0 index leaves hadm (key.ftsSecret index)
    rw [e1, Equiv.toList_compress, hexp]
    simp only
    rw [evalWithAnswerFn_bind, hwf, hfts0]
    rw [hR]
    simp only
    have hL' : evalWithAnswerFn f (Equiv.aLayers (Concrete.digestIndex d) (Equiv.witSig wl) numLayers
        (0, evalWithAnswerFn f (Concrete.ftsKey (m := OracleComp SphincsSecurity.HashSpec) 0 index
          (key.ftsSecret index)))) = some cs := hL
    rw [evalWithAnswerFn_bind, hL']
    rfl
  · unfold Equiv.witDec
    rw [Ref.extW_toList_cutW_withCounters wl cs hwc (by rw [hlen]; decide) hz, hwit]
    conv_rhs => rw [hS]
    congr 1
    funext lay
    apply LayerSignature.ext
    · show Ref.ofList 4 (Ref.le32 (cs.getD lay.val 0)) = (S.layers lay).counter
      have hlay := lay.isLt
      rw [hcs, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range hlay]
      simp only [Option.map_some, Option.getD_some]
      unfold ctrOf
      rw [dif_pos hlay, ofList_le32_counter]
    · rfl
    · rfl

/-- Under a fixed answer function, the expansion of an honestly produced signature succeeds with a
witness decoding to the signature. -/
theorem eval_aExpand_sign (seed : MasterSeed) (message : Message) {pk : PublicKey} {cache : TopCache}
    {sk : Seeded.SecretKey} {S : Signature}
    (hkeys : evalWithAnswerFn f (Seeded.keygenFromSeed seed) = (pk, cache, sk))
    (hsign : evalWithAnswerFn f (Seeded.sign sk cache message
      : OracleComp SphincsSecurity.HashSpec (Option Signature)) = some S) :
    ∃ w, evalWithAnswerFn f (Equiv.aExpand message pk (Equiv.compress S)) = some w ∧
      Equiv.witDec w = S := by
  obtain ⟨wl, -, -, h1, h2⟩ := eval_aExpand_sign' f seed message hkeys hsign
  exact ⟨_, h1, h2⟩

/-- **The expansion does not change the honest game** under any answer function. -/
theorem eval_gameX (seed : MasterSeed) (message : Message) :
    evalWithAnswerFn f (gameX seed message) = evalWithAnswerFn f (game seed message) := by
  unfold gameX game
  simp only [evalWithAnswerFn_bind]
  generalize hk : evalWithAnswerFn f (Seeded.keygenFromSeed seed) = kp
  obtain ⟨pk, cache, sk⟩ := kp
  dsimp only
  generalize hs : evalWithAnswerFn f (Seeded.sign sk cache message
    : OracleComp SphincsSecurity.HashSpec (Option Signature)) = s
  cases s with
  | none => rfl
  | some S =>
    obtain ⟨w, hw, hwS⟩ := eval_aExpand_sign f seed message hk hs
    simp only [evalWithAnswerFn_bind, hw, hwS]

end eval

end SigGolfCandidate.Final
