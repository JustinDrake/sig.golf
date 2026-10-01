import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.CacheLeafReplay
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.GameExpansion

/-!
# Security bridge for omitting the top tree's leaf cache

A reconstruction query is removed only after an honest keygen run has cached it. The intermediate
pure getter reads its level-zero value from the mathematical secret-key table; positive levels
continue to use the authenticated cache. This keeps the existing MAC argument applicable.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded.InternalCache

open Concrete
set_option backward.isDefEq.respectTransparency false

/-- The level-zero computation which the implementation will reconstruct. -/
abbrev rebuiltNode := rebuiltTableNode

/-- The same getter after erasing the cached leaf computation. -/
def pureNode (key : SphincsSecurity.SecretKey) (cache : TopCache) (masks : MaskOutputs)
    (level nodeIdx : Nat) : OracleComp HashSpec Digest :=
  if level = 0 then pure (key.top 0 (leafOfNat nodeIdx).val)
  else pure (cache.node level nodeIdx ^^^ maskValue masks level nodeIdx)

/-- The checked signer with its top-node getter as an explicit argument. -/
def checkedSign (randomizers : RandomizerOutputs) (key : SphincsSecurity.SecretKey)
    (topNode : Nat → Nat → OracleComp HashSpec Digest) (message : Message) :
    OracleComp HashSpec (Option Signature) := do
  match ← pairedTableDigestLoop randomizers key message digestPairLimit 0 with
  | none => pure none
  | some (randomness, index, leaves) =>
      signFrom key.parameter index (fun tree leaf => pure (key.ftsSecret index tree leaf))
        (fun lay tree leaf i => pure (key.otsSecret lay tree leaf i)) topNode randomness leaves

theorem erases_rebuiltNode {known : QueryCache HashSpec} {f : QueryImpl HashSpec Id}
    (key : SphincsSecurity.SecretKey)
    (hcache : CachedRun known f (keygenTable key.parameter (key.otsSecret topLayer rootTree)))
    (hf : known.AgreesWithFn f)
    (htop : key.top = evalWithAnswerFn f (keygenTable key.parameter (key.otsSecret topLayer rootTree)))
    (cache : TopCache) (masks : MaskOutputs) (level nodeIdx : Nat) :
    Erases known (rebuiltNode key cache masks level nodeIdx) (pureNode key cache masks level nodeIdx) := by
  unfold rebuiltNode rebuiltTableNode pureNode
  split
  · rw [htop]
    exact keygenLeaf_erases hcache hf (leafOfNat nodeIdx)
  · exact .pure _

theorem erases_checkedSign {known : QueryCache HashSpec} {f : QueryImpl HashSpec Id}
    (key : SphincsSecurity.SecretKey)
    (hcache : CachedRun known f (keygenTable key.parameter (key.otsSecret topLayer rootTree)))
    (hf : known.AgreesWithFn f)
    (htop : key.top = evalWithAnswerFn f (keygenTable key.parameter (key.otsSecret topLayer rootTree)))
    (randomizers : RandomizerOutputs) (cache : TopCache) (masks : MaskOutputs) (message : Message) :
    Erases known (checkedSign randomizers key (rebuiltNode key cache masks) message)
      (checkedSign randomizers key (pureNode key cache masks) message) := by
  unfold checkedSign
  apply (Erases.refl known _).bind
  intro attempt
  rcases attempt with _ | ⟨randomness, index, leaves⟩
  · exact .pure _
  · exact erases_signFrom key.parameter index (fun _ _ => .pure _) (fun _ _ _ _ => .pure _)
      (fun level nodeIdx => erases_rebuiltNode key hcache hf htop cache masks level nodeIdx) randomness leaves

/-- The full cache-authenticated table signer for a chosen top-node implementation. -/
def authenticatedSign (node : SphincsSecurity.SecretKey → TopCache → MaskOutputs → Nat → Nat →
      OracleComp HashSpec Digest)
    (randomizers : RandomizerOutputs) (key : SphincsSecurity.SecretKey)
    (masks : MaskOutputs) (macs : MacOutputs) (cache : TopCache) (message : Message) :
    OracleComp HashSpec (Option Signature) :=
  if macs cache.region = cache.tag then checkedSign randomizers key (node key cache masks) message
  else pure none

/-- Leaf reconstruction is erased after keygen even for adversarial cache requests: both sides
perform the same MAC check, and only the implementation's cached computation is removed. -/
theorem erases_authenticatedSign {known : QueryCache HashSpec} {f : QueryImpl HashSpec Id}
    (key : SphincsSecurity.SecretKey)
    (hcache : CachedRun known f (keygenTable key.parameter (key.otsSecret topLayer rootTree)))
    (hf : known.AgreesWithFn f)
    (htop : key.top = evalWithAnswerFn f (keygenTable key.parameter (key.otsSecret topLayer rootTree)))
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs)
    (cache : TopCache) (message : Message) :
    Erases known (authenticatedSign rebuiltNode randomizers key masks macs cache message)
      (authenticatedSign pureNode randomizers key masks macs cache message) := by
  unfold authenticatedSign
  split
  · exact erases_checkedSign key hcache hf htop randomizers cache masks message
  · exact .pure _

/-- The replay erasure preserves the required winning event with an upper bound on HASH calls.
No equality of the two programs' query counts is asserted. -/
theorem rebuilt_game_budget_le {known : QueryCache HashSpec} {f : QueryImpl HashSpec Id}
    (key : SphincsSecurity.SecretKey)
    (hcache : CachedRun known f (keygenTable key.parameter (key.otsSecret topLayer rootTree)))
    (hf : known.AgreesWithFn f)
    (htop : key.top = evalWithAnswerFn f (keygenTable key.parameter (key.otsSecret topLayer rootTree)))
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs)
    (adversary : Security.Adversary) (pk : PublicKey) (published : TopCache) (budget : Nat) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ budget |
      (simulateQ romImpl (countHashQueries (cachedGameRest
        (authenticatedSign rebuiltNode randomizers key masks macs) adversary pk published))).run' known] ≤
    Pr[fun result => result.1 = true ∧ result.2 ≤ budget |
      (simulateQ romImpl (countHashQueries (cachedGameRest
        (authenticatedSign pureNode randomizers key masks macs) adversary pk published))).run' known] := by
  have he := erases_cachedGameRest known
    (fun cache message => erases_authenticatedSign key hcache hf htop randomizers masks macs cache message)
    adversary pk published
  exact he.probEvent_counted_le known le_rfl (fun value count => value = true ∧ count ≤ budget)
    (fun value count count' hc h => ⟨h.1, hc.trans h.2⟩)

end SphincsSecurity.Seeded.InternalCache
