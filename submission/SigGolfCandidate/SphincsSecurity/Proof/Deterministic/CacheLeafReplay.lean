import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Cached
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.BuildEval
import SigGolfCandidate.SphincsSecurity.Proof.Event.Erasure

/-!
# Replaying a top-tree leaf after key generation

The internal-node cache omits level-zero nodes. Reconstructing such a node must be erased only
under the cache produced by key generation, not under an arbitrary node table. These lemmas
establish that bridge without changing any signature, security, or budget statement.
-/

open OracleComp OracleSpec

namespace SphincsSecurity

set_option backward.isDefEq.respectTransparency false

/-- Every query of a cached computation can be erased to its answer-function result. -/
theorem CachedRun.erases {α : Type} {cache : QueryCache HashSpec}
    {f : QueryImpl HashSpec Id} {computation : OracleComp HashSpec α}
    (h : CachedRun cache f computation) (hf : cache.AgreesWithFn f) :
    Seeded.Erases cache computation (Pure.pure (evalWithAnswerFn f computation)) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact .pure value
  | query_bind input next ih =>
      obtain ⟨answer, ha⟩ := Option.ne_none_iff_exists'.mp
        (h input (by simp only [queriedInputs_query_bind]; exact List.mem_cons_self))
      have he : f input = answer := hf ha
      have hc : cache input = some (f input) := by rw [he]; exact ha
      have ht : CachedRun cache f (next (f input)) := by
        intro x hx
        exact h x (by simp only [queriedInputs_query_bind, List.mem_cons]; exact Or.inr hx)
      change Seeded.Erases cache (liftM (HashSpec.query input) >>= next)
        (Pure.pure (evalWithAnswerFn f (next (f input))))
      exact .skip input (f input) hc next _ (ih (f input) ht)

/-- A component of a cached finite sequence is cached. -/
theorem CachedRun.sequenceFin {α : Type} {n : Nat} {cache : QueryCache HashSpec}
    {f : QueryImpl HashSpec Id} {computation : Fin n → OracleComp HashSpec α}
    (h : CachedRun cache f (Concrete.sequenceFin computation)) (i : Fin n) :
    CachedRun cache f (computation i) := by
  intro input hi
  exact h input (Concrete.sequenceFin_component_query_mem f computation i hi)

namespace Concrete

/-- Every top-tree leaf computation occurs inside key generation. -/
theorem keygenLeaf_query_mem (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) {input : HashInput}
    (hinput : input ∈ queriedInputs f
      (buildLeaf parameter topLayer rootTree leaf (fun i => pure (secret leaf i)) zeroEncoding)) :
    input ∈ queriedInputs f (keygenTable parameter secret) := by
  unfold keygenTable
  apply queriedInputs_mono_bind_left
  unfold buildLayerTable
  apply queriedInputs_mono_bind_left
  apply sequenceFin_component_query_mem f _ (⟨leaf.val, leaf.isLt⟩ : Fin (2 ^ layerHeight topLayer))
  simpa only [ite_self, leafOfNat_val] using hinput

/-- Key generation's cached execution includes every full top-tree leaf. -/
theorem keygenLeaf_cached {cache : QueryCache HashSpec} {f : QueryImpl HashSpec Id}
    {parameter : PublicParameter} {secret : LeafIndex → ChainIndex → Digest}
    (h : CachedRun cache f (keygenTable parameter secret)) (leaf : LeafIndex) :
    CachedRun cache f
      (buildLeaf parameter topLayer rootTree leaf (fun i => pure (secret leaf i)) zeroEncoding) :=
  fun input hi => h input (keygenLeaf_query_mem f parameter secret leaf hi)

/-- Reconstructing a top-tree leaf erases to the stored mathematical node, provided the keygen
queries are actually cached and the table is the result of that keygen execution. -/
theorem keygenLeaf_erases {cache : QueryCache HashSpec} {f : QueryImpl HashSpec Id}
    {parameter : PublicParameter} {secret : LeafIndex → ChainIndex → Digest}
    (h : CachedRun cache f (keygenTable parameter secret)) (hf : cache.AgreesWithFn f)
    (leaf : LeafIndex) :
    Seeded.Erases cache
      (Prod.snd <$> buildLeaf parameter topLayer rootTree leaf (fun i => pure (secret leaf i)) zeroEncoding)
      (Pure.pure (evalWithAnswerFn f (keygenTable parameter secret) 0 leaf.val)) := by
  have he := ((keygenLeaf_cached h leaf).erases hf).map Prod.snd
  simp only [map_pure] at he
  rw [eval_buildLeaf f parameter topLayer rootTree (fun l i => pure (secret l i))] at he
  rw [eval_keygenTable f parameter secret 0 (Nat.zero_le _) leaf.val leaf.isLt]
  simpa only [evalWithAnswerFn_pure] using he

/-- The leaf replay premise follows from an actual keygen run, including any starting cache. -/
theorem keygenLeaf_erases_of_run (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (before after : QueryCache HashSpec)
    (top : Nat → Nat → Digest)
    (h : (top, after) ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (keygenTable parameter secret)).run before)) (leaf : LeafIndex) :
    Seeded.Erases after
      (Prod.snd <$> buildLeaf parameter topLayer rootTree leaf (fun i => pure (secret leaf i)) zeroEncoding)
      (pure (top 0 leaf.val)) := by
  obtain ⟨_, f, hf, heval, hqueries⟩ :=
    exists_answerFn_replay_of_mem_support (keygenTable parameter secret) before top after h
  have hc : CachedRun after f (keygenTable parameter secret) := hqueries
  rw [← heval]
  exact keygenLeaf_erases hc hf leaf

end Concrete
end SphincsSecurity
