import SigGolfCandidate.T3.FullCache.NativeMac

namespace SigGolfCandidate.T3.Security.FullGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (OracleWorld romImpl)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem uniform_product {A B : Type} [Finite A] [Finite B]
    [SampleableType A] [SampleableType B] [SampleableType (A × B)] :
    𝒮[do let a ← ($ᵗ A : ProbComp _); let b ← $ᵗ B; pure (a,b)]=𝒮[$ᵗ (A × B)] := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  apply evalSPMF_ext
  rintro ⟨a,b⟩
  change Pr[=(a,b) | do let x ← ($ᵗ A : ProbComp _); let y ← $ᵗ B; pure (id x,id y)]=_
  rw [probOutput_bind_bind_prod_mk_eq_mul' _ _ id id a b]
  simp only [id_map,probOutput_uniformSample,Nat.card_eq_fintype_card,Fintype.card_prod,
    Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

abbrev OtherCoordinate := SiggolfT3Mac4.Source.OtherCoordinate
abbrev OtherTable := OtherCoordinate → HashOutput
abbrev FullTable := Coordinate → HashOutput
abbrev MacTable := CacheAuthentication.MacTable

@[irreducible] noncomputable def otherFintype : Fintype OtherCoordinate := by
  classical
  let _ : Fintype Coordinate := coordinateFintype
  exact inferInstance
noncomputable local instance : Fintype OtherCoordinate := otherFintype
noncomputable local instance : Fintype Region := CacheAuthentication.regionFintype
noncomputable local instance : Fintype Coordinate := coordinateFintype

@[irreducible] noncomputable def otherSampler : SampleableType OtherTable := by
  classical
  exact SampleableType.ofFintype _
noncomputable local instance : SampleableType OtherTable := otherSampler
noncomputable local instance : SampleableType MacTable := CacheAuthentication.macTableSampler
noncomputable local instance : SampleableType FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : SampleableType (OtherTable × MacTable) :=
  SampleableType.ofFintype _

noncomputable def joinTable (other : OtherTable) (mac : MacTable) : FullTable :=
  SiggolfT3Mac4.Source.joinTable other mac

noncomputable def tableEquiv : (OtherTable × MacTable) ≃ FullTable := SiggolfT3Mac4.Source.tableEquiv

/-- The secret-coordinate table splits into independent non-MAC and MAC tables. -/
theorem uniform_table_split :
    𝒮[do let other ← ($ᵗ OtherTable : ProbComp _); let mac ← $ᵗ MacTable; pure (joinTable other mac)] =
      𝒮[$ᵗ FullTable] := by
  have h := congrArg (Functor.map tableEquiv) (uniform_product (A := OtherTable) (B := MacTable))
  simp only [← evalSPMF_map,map_bind,map_pure] at h
  exact h.trans (evalSPMF_map_bijective_uniform_cross (α := OtherTable × MacTable) (β := FullTable) tableEquiv tableEquiv.bijective)

theorem uniform_table_split_bind {α : Type} (next : FullTable → ProbComp α) :
    𝒮[do let table ← ($ᵗ FullTable : ProbComp _); next table]=
      𝒮[do let other ← ($ᵗ OtherTable : ProbComp _); let mac ← $ᵗ MacTable; next (joinTable other mac)] := by
  rw [evalSPMF_bind,← uniform_table_split,← evalSPMF_bind]
  simp only [bind_assoc,pure_bind]

abbrev RCache := QueryCache SphincsSecurity.HashSpec
abbrev CountState := Nat × RCache

def queryCharge (input : T3.Spec.Domain) : Nat := if Derivation.charged input then 1 else 0

/-- Attach a counter to an arbitrary source interpreter. Every private query and
public hash query costs one; random coin queries cost zero. -/
noncomputable def countHandler (handler : QueryImpl T3.Spec (StateT RCache ProbComp)) :
    QueryImpl T3.Spec (StateT CountState ProbComp) := fun input => StateT.mk fun state => do
  let result ← (handler input).run state.2
  pure (result.1,(state.1+queryCharge input,result.2))

noncomputable def plainHandler (table : FullTable) : QueryImpl T3.Spec (StateT RCache ProbComp) :=
  PrivateTable.fixedImpl romImpl table

noncomputable def tableHandler (table : FullTable) : QueryImpl T3.Spec (StateT CountState ProbComp) :=
  countHandler (plainHandler table)

noncomputable def baseHandler (other : OtherTable) : QueryImpl T3.Spec (StateT CountState ProbComp) :=
  tableHandler (joinTable other (fun _ => 0))

noncomputable def run {α : Type} (table : FullTable) (program : M α) (state : CountState) :
    ProbComp (α × CountState) := (simulateQ (tableHandler table) program).run state

theorem tableHandler_split (other : OtherTable) (mac : MacTable) :
    tableHandler (joinTable other mac)=MacGame.sourceHandler (baseHandler other) mac := by
  funext input
  apply StateT.ext
  intro state
  cases input with
  | inl world => rfl
  | inr coordinate =>
      simp only [tableHandler,countHandler,plainHandler,PrivateTable.fixedImpl,
        QueryImpl.add_apply_inr,StateT.run_pure,StateT.run_mk,baseHandler,
        MacGame.sourceHandler,StateT.run_bind,pure_bind,queryCharge,Derivation.charged,ite_true]
      simp only [joinTable,SiggolfT3Mac4.Source.joinTable]
      dsimp only [HAdd.hAdd,QueryImpl.instHAddSumHAddOracleSpec,QueryImpl.add]
      simp only [StateT.run_pure,pure_bind]
      split_ifs <;> rfl


theorem run_pure {α : Type} (table : FullTable) (value : α) (state : CountState) :
    run table (pure value) state=pure (value,state) := rfl

theorem run_bind {α β : Type} (table : FullTable) (program : M α) (next : α → M β)
    (state : CountState) :
    run table (program >>= next) state=
      (do let result ← run table program state; run table (next result.1) result.2) := by
  simp only [run,simulateQ_bind,StateT.run_bind]

theorem run_map {α β : Type} (table : FullTable) (f : α → β) (program : M α) (state : CountState) :
    run table (f <$> program) state=Prod.map f id <$> run table program state := by
  simp only [run,simulateQ_map,StateT.run_map]
  rfl

theorem countHandler_run {α : Type} (handler : QueryImpl T3.Spec (StateT RCache ProbComp))
    (program : M α) (state : CountState) :
    (simulateQ (countHandler handler) program).run state=
      (fun result => (result.1.1,(state.1+result.1.2,result.2))) <$>
        (simulateQ handler (SphincsSecurity.QueryCap.counted Derivation.charged program)).run state.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp [SphincsSecurity.QueryCap.counted_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,countHandler,
        StateT.run_mk,SphincsSecurity.QueryCap.counted_query_bind]
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,
        simulateQ_pure,StateT.run_pure,map_bind,bind_assoc,pure_bind]
      apply bind_congr
      intro step
      rw [ih]
      simp only [map_pure,queryCharge,Nat.add_assoc,bind_pure_comp]

theorem plainHandler_eq (table : FullTable) :
    plainHandler table=QueryImpl.compose romImpl (Derivation.tableHandler table) :=
  LazyPrivate.fixedImpl_eq table

theorem plain_run {α : Type} (table : FullTable) (program : M α) (cache : RCache) :
    (simulateQ (plainHandler table) program).run cache=
      (simulateQ romImpl (Derivation.tableRun table program)).run cache := by
  rw [plainHandler_eq,QueryImpl.simulateQ_compose]
  rfl

end SigGolfCandidate.T3.Security.FullGame
