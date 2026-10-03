import SigGolfCandidate.SphincsSecurity.Proof.Reference.FiniteHashWorld
import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeSignerView
import SigGolfCandidate.SphincsSecurity.Proof.Ots.SecretProbe
import SigGolfCandidate.SphincsSecurity.Proof.Reference.DirectQueryBudget
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeLoop
import SigGolfCandidate.SphincsSecurity.Proof.Reference.SigningTrace
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Secrets
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.ForgeryClassify
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingSelectionCache
import SigGolfCandidate.SphincsSecurity.Proof.Base.RomQueryChargeBind

section

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] hashInputs
def FixedHashQueryBound {α : Type} (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) (q : Nat) : Prop :=
  ∀ result ∈ support (simulateQ (fixedHashWorld oracle) (countHashQueries computation)), result.2 ≤ q
theorem fixedHashWorld_congr {α : Type} (computation : OracleComp OracleWorld α)
    (first second : QueryImpl HashSpec Id) (h : ∀ input ∈ hashInputs computation, first input = second input) :
    simulateQ (fixedHashWorld first) computation = simulateQ (fixedHashWorld second) computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind input next ih =>
      have hnext := fun answer => ih answer (fun row hr => h row (hashInputs_next_subset input next answer hr))
      simp only [simulateQ_bind, simulateQ_spec_query]
      cases input with
      | inl input => exact bind_congr hnext
      | inr input => simp only [fixedHashWorld, h input (mem_hashInputs_hash_bind input next), pure_bind, hnext]
theorem fixedHashWorld_support_rom {α : Type} (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) (result : α)
    (hresult : result ∈ support (simulateQ (fixedHashWorld oracle) computation)) :
    result ∈ support ((simulateQ romImpl computation).run' ∅) := by
  classical
  let inputs := hashInputs computation
  letI : SampleableType (inputs → HashOutput) := SampleableType.ofFintype _
  have heq := evalDist_romRun_eq_finiteHash computation inputs (Finset.Subset.refl _) ∅
  have hs : support ((simulateQ romImpl computation).run' ∅) =
      support (do
        let table ← ($ᵗ (inputs → HashOutput) : ProbComp _)
        simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs table)) computation) := by
    ext value
    simp only [mem_support_iff, probOutput_def, heq]
  rw [hs, mem_support_bind_iff]
  refine ⟨(fun input => oracle input.val), by simp, ?_⟩
  rw [fixedHashWorld_congr computation (finiteHashAnswer ∅ inputs (fun input => oracle input.val)) oracle]
  · exact hresult
  · intro input hin
    simp only [finiteHashAnswer, QueryCache.empty_apply, Option.getD_none, inputs, dif_pos hin]
theorem hashQueryBound_fixed {α : Type} (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) (q : Nat) (hbound : HashQueryBound computation ∅ q) :
    FixedHashQueryBound oracle computation q := by
  intro result hresult
  exact hbound result (fixedHashWorld_support_rom oracle (countHashQueries computation) result hresult)
theorem fixedHashQueryBound_map_iff {α β : Type} (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) (f : α → β) (q : Nat) :
    FixedHashQueryBound oracle (f <$> computation) q ↔ FixedHashQueryBound oracle computation q := by
  simp only [FixedHashQueryBound, countHashQueries_map, simulateQ_map, support_map, Set.forall_mem_image]
theorem fixedHashQueryBound_iff_of_map_eq {α β : Type} (oracle : QueryImpl HashSpec Id)
    {first : OracleComp OracleWorld α} {second : OracleComp OracleWorld β} {f : α → β}
    (heq : f <$> first = second) (q : Nat) :
    FixedHashQueryBound oracle first q ↔ FixedHashQueryBound oracle second q := by
  rw [← heq, fixedHashQueryBound_map_iff]
theorem fixedHashQueryBound_bind {α β : Type} (oracle : QueryImpl HashSpec Id)
    (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) (q : Nat)
    (hbound : FixedHashQueryBound oracle (first >>= next) q) (result : α × Nat)
    (hresult : result ∈ support (simulateQ (fixedHashWorld oracle) (countHashQueries first))) :
    result.2 ≤ q ∧ FixedHashQueryBound oracle (next result.1) (q - result.2) := by
  simp only [FixedHashQueryBound, countHashQueries_bind, simulateQ_bind,
    bind_pure_comp, simulateQ_map] at hbound ⊢
  have hsum : ∀ tail ∈ support (simulateQ (fixedHashWorld oracle) (countHashQueries (next result.1))),
      result.2 + tail.2 ≤ q := by
    intro tail ht
    apply hbound (tail.1, result.2 + tail.2)
    rw [mem_support_bind_iff]
    refine ⟨result, hresult, ?_⟩
    rw [support_map]
    exact ⟨tail, ht, rfl⟩
  obtain ⟨tail, ht⟩ := probComp_support_nonempty (simulateQ (fixedHashWorld oracle) (countHashQueries (next result.1)))
  exact ⟨(Nat.le_add_right _ _).trans (hsum tail ht), fun tail ht => by have := hsum tail ht; omega⟩
theorem fixedHashQueryBound_query_bind {α : Type} (oracle : QueryImpl HashSpec Id)
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp OracleWorld α) (q : Nat)
    (hbound : FixedHashQueryBound oracle (liftM (OracleWorld.query input) >>= next) q)
    (answer : OracleWorld.Range input) (ha : answer ∈ support (fixedHashWorld oracle input)) :
    (if input matches .inr _ then 1 else 0) ≤ q ∧
      FixedHashQueryBound oracle (next answer) (q - (if input matches .inr _ then 1 else 0)) := by
  apply fixedHashQueryBound_bind oracle _ next q hbound (answer, if input matches .inr _ then 1 else 0)
  rw [← bind_pure (liftM (OracleWorld.query input)), countHashQueries_query_bind]
  simp only [countHashQueries_pure, map_pure, Nat.add_zero, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, support_map]
  exact ⟨answer, ha, by cases input <;> rfl⟩
theorem fixedBoundaryRun_count {α : Type} (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) :
    (fun result => (result.1, result.2.hashCalls)) <$> fixedBoundaryRun parameter oracle computation =
      simulateQ (fixedHashWorld oracle) (countHashQueries computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [fixedBoundaryRun_pure, map_pure, countHashQueries_pure, simulateQ_pure]; rfl
  | query_bind input next ih =>
      simp only [fixedBoundaryRun, simulateQ_bind, WriterT.run_bind, simulateQ_spec_query,
        QueryImpl.withTrace_apply, WriterT.run_bind, WriterT.run_liftM, WriterT.run_tell,
        WriterT.run_map, map_pure, one_mul,
        bind_pure_comp, map_bind, bind_map_left, Functor.map_map]
      rw [countHashQueries_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, bind_pure_comp, simulateQ_map]
      apply bind_congr
      intro answer
      rw [← ih]
      simp only [fixedBoundaryRun, Functor.map_map, SigningBoundaryTrace.hashCalls_mul,
        signingBoundaryTrace_hashCalls_eq]
      cases input <;> rfl
theorem fixedBoundaryRun_bind_query_bound {α β : Type} (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) (q : Nat)
    (hbound : FixedHashQueryBound oracle (computation >>= next) q)
    (result : α × SigningBoundaryTrace) (hresult : 𝒮[fixedBoundaryRun parameter oracle computation] result ≠ 0) :
    result.2.hashCalls ≤ q ∧ FixedHashQueryBound oracle (next result.1) (q - result.2.hashCalls) := by
  apply fixedHashQueryBound_bind oracle computation next q hbound (result.1, result.2.hashCalls)
  rw [← fixedBoundaryRun_count parameter oracle computation, support_map]
  exact ⟨result, (mem_support_iff _ _).mpr hresult, rfl⟩
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete.FtsProbeSimulation
open OracleComp OracleSpec ENNReal
abbrev Coordinate := Index × FtsTree × FtsLeaf
noncomputable local instance instNonemptyCoordinate : Nonempty Coordinate :=
  ⟨(⟨0, by norm_num [totalHeight]⟩,
    ⟨0, by decide⟩,
    ⟨0, by norm_num [ftsTreeHeight]⟩)⟩
noncomputable def decodeProbe? (parameter : PublicParameter) (input : HashInput) :
    Option FtsSecretProbe := by
  classical
  exact if hexists : ∃ probe : FtsSecretProbe, probe.input parameter = input then
    some hexists.choose
  else none
theorem decodeProbe?_eq_some_iff (parameter : PublicParameter) (input : HashInput)
    (probe : FtsSecretProbe) :
    decodeProbe? parameter input = some probe ↔ probe.input parameter = input := by
  classical
  unfold decodeProbe?
  split
  · rename_i hexists
    constructor
    · intro heq
      have hprobe : hexists.choose = probe := Option.some.inj heq
      rw [← hprobe]
      exact hexists.choose_spec
    · intro hinput
      congr 1
      apply FtsSecretProbe.input_injective parameter
      exact hexists.choose_spec.trans hinput.symm
  · rename_i hnone
    constructor
    · simp
    · intro hinput
      exact (hnone ⟨probe, hinput⟩).elim
theorem decodeProbe?_eq_none_iff (parameter : PublicParameter) (input : HashInput) :
    decodeProbe? parameter input = none ↔
      ∀ probe : FtsSecretProbe, probe.input parameter ≠ input := by
  constructor
  · intro hnone probe hinput
    have hsome := (decodeProbe?_eq_some_iff parameter input probe).2 hinput
    rw [hnone] at hsome
    simp at hsome
  · intro hnone
    cases hdecode : decodeProbe? parameter input with
    | none => rfl
    | some probe =>
        exact (hnone probe ((decodeProbe?_eq_some_iff parameter input probe).1 hdecode)).elim
end SphincsSecurity.Concrete.FtsProbeSimulation
end

section


namespace SphincsSecurity.Concrete.FtsProbeSimulation
open OracleComp OracleSpec
theorem sibling_node_bound (height leaf level : Nat)
    (hlevel : level < height) (hleaf : leaf < 2 ^ height) :
    2 ^ level * (Nat.xor (leaf / 2 ^ level) 1 + 1) ≤ 2 ^ height := by
  let bound := 2 ^ (height - level)
  have hquotient : leaf / 2 ^ level < bound := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos level)).2
    change leaf < 2 ^ (height - level) * 2 ^ level
    rw [← pow_add]
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt hlevel)] using hleaf
  have hboundEven : ∃ half, bound = 2 * half := by
    refine ⟨2 ^ (height - level - 1), ?_⟩
    change 2 ^ (height - level) = _
    rw [show height - level = (height - level - 1) + 1 by omega, pow_succ]
    exact Nat.mul_comm _ _
  have hsibling : Nat.xor (leaf / 2 ^ level) 1 < bound := by
    obtain ⟨parent, hcase⟩ := index_sibling_cases (leaf / 2 ^ level)
    obtain ⟨half, hbound⟩ := hboundEven
    rcases hcase with hcase | hcase <;> omega
  calc
    2 ^ level * (Nat.xor (leaf / 2 ^ level) 1 + 1) ≤ 2 ^ level * bound :=
      Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hsibling)
    _ = 2 ^ height := by
      change 2 ^ level * 2 ^ (height - level) = _
      rw [← pow_add]
      congr 1
      omega
end SphincsSecurity.Concrete.FtsProbeSimulation
end

section



set_option autoImplicit true
namespace SphincsSecurity.Concrete.FtsProbeSimulation
open OracleComp OracleSpec
def signingTraceComputation
    (computation : OracleComp (OracleWorld + SigningSpec) alpha) :
    OracleComp (OracleWorld + SigningSpec) (alpha × QueryLog SigningSpec) :=
  OracleComp.construct
    (C := fun _ => OracleComp (OracleWorld + SigningSpec)
      (alpha × QueryLog SigningSpec))
    (fun value => pure (value, []))
    (fun input _next recursivelyTrace => do
      let output ← liftM ((OracleWorld + SigningSpec).query input)
      let result ← recursivelyTrace output
      pure (result.1, signingLogFragment input output ++ result.2))
    computation
theorem simulateQ_withTraceAppend_run_eq_signingTraceComputation
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (handler : QueryImpl (OracleWorld + SigningSpec) m)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha) :
    (simulateQ (QueryImpl.withTraceAppend handler signingLogFragment)
        computation).run =
      simulateQ handler (signingTraceComputation computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp [signingTraceComputation]
  | query_bind input next ih =>
      simp [signingTraceComputation, ih]
noncomputable def liftOracleWorldLeft
    (computation : OracleComp OracleWorld alpha) :
    OracleComp (OracleWorld + SigningSpec) alpha := by
  letI directLift : MonadLift (OracleQuery OracleWorld)
      (OracleQuery (OracleWorld + SigningSpec)) :=
    (OracleQuery.subSpec_add_left
      (spec₁ := OracleWorld) (spec₂ := SigningSpec)).toMonadLift
  exact liftM computation
theorem simulateQ_liftOracleWorldLeft
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (left : QueryImpl OracleWorld m) (right : QueryImpl SigningSpec m)
    (computation : OracleComp OracleWorld alpha) :
    simulateQ (left + right) (liftOracleWorldLeft computation) =
      simulateQ left computation := by
  unfold liftOracleWorldLeft
  exact QueryImpl.simulateQ_add_liftM_left left right computation
noncomputable def tracedGameRestComputation (adversary : Adversary)
    (publicKey : PublicKey) :
    OracleComp (OracleWorld + SigningSpec) Bool := do
  let (forgery, log) ← signingTraceComputation (adversary.main publicKey)
  let verified ← liftOracleWorldLeft
    (scheme.verify publicKey forgery.message forgery.signature)
  pure (decide (SigningTranscript.Valid log ∧
    ¬SigningTranscript.Contains log forgery) && verified)
end SphincsSecurity.Concrete.FtsProbeSimulation
end

section


set_option autoImplicit true
namespace SphincsSecurity.AdaptiveRevealProbe
open OracleComp OracleSpec
variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
end SphincsSecurity.AdaptiveRevealProbe
namespace SphincsSecurity.Concrete.FtsProbeSimulation
open OracleComp OracleSpec
theorem signingTraceComputation_query_bind
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input →
      OracleComp (OracleWorld + SigningSpec) alpha) :
    signingTraceComputation
        ((liftM ((OracleWorld + SigningSpec).query input) :
          OracleComp (OracleWorld + SigningSpec) _) >>= next) = (do
      let output ← liftM ((OracleWorld + SigningSpec).query input)
      (fun result => (result.1, signingLogFragment input output ++ result.2)) <$>
        signingTraceComputation (next output)) := by
  simp [signingTraceComputation]
end SphincsSecurity.Concrete.FtsProbeSimulation
end

section


set_option autoImplicit true
namespace SphincsSecurity.Concrete.FtsProbeSimulation
open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational
theorem simulateQ_expanded_liftOracleWorldLeft
    (secretKey : SecretKey) (computation : OracleComp OracleWorld alpha) :
    simulateQ (expandedAdversaryImpl secretKey)
        (liftOracleWorldLeft computation) = computation := by
  have hhandler : expandedAdversaryImpl secretKey =
      QueryImpl.id' OracleWorld +
        (fun request => scheme.sign secretKey request) := by
    funext input
    cases input <;> rfl
  rw [hhandler, simulateQ_liftOracleWorldLeft, simulateQ_id']
theorem simulateQ_expanded_tracedGameRestComputation
    (adversary : Adversary) (secretKey : SecretKey) :
    simulateQ (expandedAdversaryImpl secretKey)
        (tracedGameRestComputation adversary
          ⟨secretKey.root, secretKey.parameter⟩) =
      gameRest scheme adversary ⟨secretKey.root, secretKey.parameter⟩ secretKey := by
  unfold tracedGameRestComputation gameRest
  rw [simulateQ_bind,
    ← simulateQ_withTraceAppend_run_eq_signingTraceComputation,
    ← forwardOracles_add_signingOracle_eq_withTraceAppend]
  apply bind_congr
  intro result
  rcases result with ⟨forgery, log⟩
  rw [simulateQ_bind,
    simulateQ_expanded_liftOracleWorldLeft]
  simp [simulateQ_pure]
end SphincsSecurity.Concrete.FtsProbeSimulation
end

section




namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
theorem sequenceFin_some {alpha : Type} {count : Nat}
    (values : Fin count → alpha) :
    sequenceFin (m := Option) (fun position => some (values position)) = some values := by
  induction count with
  | zero =>
      rw [sequenceFin]
      congr
      funext position
      exact Fin.elim0 position
  | succ count ih =>
      rw [sequenceFin, ih]
      change some (Fin.cases (values 0) (fun position => values position.succ)) = some values
      rw [Option.some.injEq]
      funext position
      cases position using Fin.cases <;> rfl
end SphincsSecurity.Concrete
end

section





namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
namespace Concrete.FtsProbeSimulation
attribute [local semireducible] sampleFtsSecrets
abbrev RetainedRestResult := (Forgery × QueryLog SigningSpec) × Bool
noncomputable def retainedGameRestComputation (adversary : Adversary)
    (publicKey : PublicKey) :
    OracleComp (OracleWorld + SigningSpec) RetainedRestResult := do
  let (forgery, log) ← signingTraceComputation (adversary.main publicKey)
  let verified ← liftOracleWorldLeft
    (scheme.verify publicKey forgery.message forgery.signature)
  pure ((forgery, log), verified)
theorem retainedGameRestComputation_verdict_projection
    (adversary : Adversary) (publicKey : PublicKey) :
    (fun result : RetainedRestResult =>
      decide (SigningTranscript.Valid result.1.2 ∧
        ¬SigningTranscript.Contains result.1.2 result.1.1) && result.2) <$>
        retainedGameRestComputation adversary publicKey =
      tracedGameRestComputation adversary publicKey := by
  simp [retainedGameRestComputation, tracedGameRestComputation]
theorem simulateQ_expanded_retainedGameRestComputation_fixedHashQueryBound
    (oracle : QueryImpl HashSpec Id) (adversary : Adversary) (secretKey : SecretKey) (q : Nat)
    (hbound : FixedHashQueryBound oracle (gameRest scheme adversary
      ⟨secretKey.root, secretKey.parameter⟩ secretKey) q) :
    FixedHashQueryBound oracle (simulateQ (expandedAdversaryImpl secretKey)
      (retainedGameRestComputation adversary
        ⟨secretKey.root, secretKey.parameter⟩)) q := by
  let verdict := fun result : RetainedRestResult =>
        decide (SigningTranscript.Valid result.1.2 ∧
          ¬SigningTranscript.Contains result.1.2 result.1.1) && result.2
  have heq : verdict <$>
        simulateQ (expandedAdversaryImpl secretKey)
          (retainedGameRestComputation adversary
            ⟨secretKey.root, secretKey.parameter⟩) =
      simulateQ (expandedAdversaryImpl secretKey)
        (tracedGameRestComputation adversary
          ⟨secretKey.root, secretKey.parameter⟩) := by
            rw [← retainedGameRestComputation_verdict_projection]
            simp [verdict]
  have hmap : FixedHashQueryBound oracle (verdict <$>
      simulateQ (expandedAdversaryImpl secretKey)
        (retainedGameRestComputation adversary
          ⟨secretKey.root, secretKey.parameter⟩)) q := by
    rw [heq, simulateQ_expanded_tracedGameRestComputation adversary secretKey]
    exact hbound
  exact (fixedHashQueryBound_map_iff oracle _ verdict q).mp hmap
end Concrete.FtsProbeSimulation
end SphincsSecurity
end

section




set_option autoImplicit true
namespace SphincsSecurity.Concrete.OtsProbeSimulation
open OracleComp OracleSpec
inductive Coordinate where
  | chainStart (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
      (chainIdx : ChainIndex)
  | position (position : Position)
abbrev RetainedRestResult := (Forgery × QueryLog SigningSpec) × Bool
def signingTraceComputation
    (computation : OracleComp (OracleWorld + SigningSpec) alpha) :
    OracleComp (OracleWorld + SigningSpec) (alpha × QueryLog SigningSpec) :=
  OracleComp.construct
    (C := fun _ => OracleComp (OracleWorld + SigningSpec)
      (alpha × QueryLog SigningSpec))
    (fun value => pure (value, []))
    (fun input _next recursivelyTrace => do
      let output ← liftM ((OracleWorld + SigningSpec).query input)
      let result ← recursivelyTrace output
      pure (result.1, signingLogFragment input output ++ result.2))
    computation
theorem simulateQ_withTraceAppend_run_eq_signingTraceComputation
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (handler : QueryImpl (OracleWorld + SigningSpec) m)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha) :
    (simulateQ (QueryImpl.withTraceAppend handler signingLogFragment)
        computation).run =
      simulateQ handler (signingTraceComputation computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [signingTraceComputation]
  | query_bind input next ih => simp [signingTraceComputation, ih]
noncomputable def liftOracleWorldLeft
    (computation : OracleComp OracleWorld alpha) :
    OracleComp (OracleWorld + SigningSpec) alpha := by
  letI directLift : MonadLift (OracleQuery OracleWorld)
      (OracleQuery (OracleWorld + SigningSpec)) :=
    (OracleQuery.subSpec_add_left
      (spec₁ := OracleWorld) (spec₂ := SigningSpec)).toMonadLift
  exact liftM computation
noncomputable def retainedGameRestComputation (adversary : Adversary)
    (publicKey : PublicKey) :
    OracleComp (OracleWorld + SigningSpec) RetainedRestResult := do
  let (forgery, log) ← signingTraceComputation (adversary.main publicKey)
  let verified ← liftOracleWorldLeft
    (scheme.verify publicKey forgery.message forgery.signature)
  pure ((forgery, log), verified)
end SphincsSecurity.Concrete.OtsProbeSimulation
end

section



set_option autoImplicit true
namespace SphincsSecurity.Concrete.OtsProbeSimulation
open OracleComp OracleSpec
theorem signingTraceComputation_query_bind
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input →
      OracleComp (OracleWorld + SigningSpec) alpha) :
    signingTraceComputation
        ((liftM ((OracleWorld + SigningSpec).query input) :
          OracleComp (OracleWorld + SigningSpec) _) >>= next) = (do
      let output ← liftM ((OracleWorld + SigningSpec).query input)
      (fun result => (result.1, signingLogFragment input output ++ result.2)) <$>
        signingTraceComputation (next output)) := by
  simp [signingTraceComputation]
end SphincsSecurity.Concrete.OtsProbeSimulation
end

section





set_option autoImplicit true
namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
theorem expectedQueryCharge_map
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (computation : OracleComp OracleWorld α) (f : α → β) (cache : QueryCache HashSpec) :
    expectedQueryCharge charge (f <$> computation) cache = expectedQueryCharge charge computation cache := by
  rw [map_eq_bind_pure_comp, expectedQueryCharge_bind]
  simp only [Function.comp_apply, expectedQueryCharge_pure, mul_zero, tsum_zero, add_zero]
namespace Concrete.OtsProbeSimulation
theorem gameRest_eq_map_retained
    (adversary : Adversary) (secretKey : SecretKey) (publicKey : PublicKey) :
    gameRest scheme adversary publicKey secretKey =
      (fun result : RetainedRestResult =>
        decide (SigningTranscript.Valid result.1.2 ∧ ¬SigningTranscript.Contains result.1.2 result.1.1) && result.2) <$>
        simulateQ (expandedAdversaryImpl secretKey) (retainedGameRestComputation adversary publicKey) := by
  unfold gameRest retainedGameRestComputation
  rw [simulateQ_bind, ← simulateQ_withTraceAppend_run_eq_signingTraceComputation,
    ← forwardOracles_add_signingOracle_eq_withTraceAppend, map_bind]
  apply bind_congr
  intro result
  rcases result with ⟨forgery, log⟩
  rw [simulateQ_bind]
  have hlift : simulateQ (expandedAdversaryImpl secretKey)
      (liftOracleWorldLeft (scheme.verify publicKey forgery.message forgery.signature)) =
      scheme.verify publicKey forgery.message forgery.signature :=
    FtsProbeSimulation.simulateQ_expanded_liftOracleWorldLeft secretKey _
  rw [hlift]
  simp only [simulateQ_pure, map_bind, map_pure]
theorem expectedQueryCharge_retained_eq_gameRest
    (adversary : Adversary) (secretKey : SecretKey) (publicKey : PublicKey)
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞) (cache : QueryCache HashSpec) :
    expectedQueryCharge charge (simulateQ (expandedAdversaryImpl secretKey)
      (retainedGameRestComputation adversary publicKey)) cache =
      expectedQueryCharge charge (gameRest scheme adversary publicKey secretKey) cache := by
  rw [gameRest_eq_map_retained, expectedQueryCharge_map]
end Concrete.OtsProbeSimulation
end SphincsSecurity
end
