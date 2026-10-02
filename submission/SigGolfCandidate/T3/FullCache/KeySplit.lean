import SigGolfCandidate.T3.Core
import SigGolfCandidate.T3.FullCache.PublicationHop

namespace SiggolfT3Mac4.Source
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

abbrev T3Coordinate := SigGolfCandidate.T3.Coordinate

def keyTweak (i : Fin 2) : BitVec 128 := SigGolfCandidate.T3.header 14 0 0 0 i.val

def keyCoordinate (i : Fin 2) : T3Coordinate := .inl (keyTweak i)

theorem keyCoordinate_injective : Function.Injective keyCoordinate := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    norm_num [keyCoordinate,keyTweak,SigGolfCandidate.T3.header,SigGolfCandidate.T3.packedNodeTag] at h ⊢
  all_goals have h' := congrArg BitVec.toNat h; norm_num at h'

theorem keyCoordinate_zero_ne_one : keyCoordinate 0 ≠ keyCoordinate 1 := by
  intro h
  have := keyCoordinate_injective h
  exact (by decide : (0 : Fin 2) ≠ 1) this

/-- Every other coordinate of the actual T3 private domain is retained. This
includes mask answers, nonce answers, all seed/reserved tweak coordinates, and
the unused old region-MAC coordinates. -/
abbrev OtherCoordinate := {c : T3Coordinate // c ≠ keyCoordinate 0 ∧ c ≠ keyCoordinate 1}
abbrev OtherTable := OtherCoordinate → HashOutput
abbrev FullTable := T3Coordinate → HashOutput

noncomputable def joinTable (other : OtherTable) (key : MacKey) : FullTable := fun c => by
  classical
  exact if h0 : c = keyCoordinate 0 then key 0 else
    if h1 : c = keyCoordinate 1 then key 1 else other ⟨c,h0,h1⟩

theorem joinTable_key (other : OtherTable) (key : MacKey) (i : Fin 2) :
    joinTable other key (keyCoordinate i) = key i := by
  fin_cases i
  · simp [joinTable]
  · simp [joinTable,Ne.symm keyCoordinate_zero_ne_one]

theorem joinTable_other (other : OtherTable) (key : MacKey) (c : OtherCoordinate) :
    joinTable other key c = other c := by
  simp [joinTable,c.property.1,c.property.2]

noncomputable def tableEquiv : (OtherTable × MacKey) ≃ FullTable where
  toFun tables := joinTable tables.1 tables.2
  invFun table := ((fun c => table c),fun i => table (keyCoordinate i))
  left_inv tables := by
    apply Prod.ext
    · funext c; exact joinTable_other tables.1 tables.2 c
    · funext i; exact joinTable_key tables.1 tables.2 i
  right_inv table := by
    funext c
    classical
    unfold joinTable
    dsimp only
    split_ifs with h0 h1
    · rw [h0]
    · rw [h1]
    · rfl

theorem uniform_product {A B : Type} [Finite A] [Finite B]
    [SampleableType A] [SampleableType B] [SampleableType (A × B)] :
    𝒮[do let a ← ($ᵗ A : ProbComp _); let b ← $ᵗ B; pure (a,b)] = 𝒮[$ᵗ (A × B)] := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  apply evalSPMF_ext
  rintro ⟨a,b⟩
  change Pr[=(a,b) | do let x ← ($ᵗ A : ProbComp _); let y ← $ᵗ B; pure (id x,id y)] = _
  rw [probOutput_bind_bind_prod_mk_eq_mul' _ _ id id a b]
  simp only [id_map,probOutput_uniformSample,Nat.card_eq_fintype_card,Fintype.card_prod,Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

/-- Exact complete-table joint law: the two MAC key answers are uniform and
independent of ALL other private coordinates, not merely a chosen marginal. -/
theorem uniform_table_split [SampleableType OtherTable] [SampleableType MacKey]
    [SampleableType FullTable] [SampleableType (OtherTable × MacKey)] :
    𝒮[do
      let other ← ($ᵗ OtherTable : ProbComp _)
      let key ← $ᵗ MacKey
      pure (joinTable other key)] = 𝒮[$ᵗ FullTable] := by
  have h := congrArg (Functor.map tableEquiv) (uniform_product (A := OtherTable) (B := MacKey))
  simp only [← evalSPMF_map,map_bind,map_pure] at h
  exact h.trans (evalSPMF_map_bijective_uniform_cross (α := OtherTable × MacKey) (β := FullTable)
    tableEquiv tableEquiv.bijective)

theorem uniform_table_split_bind [SampleableType OtherTable] [SampleableType MacKey]
    [SampleableType FullTable] [SampleableType (OtherTable × MacKey)]
    {α : Type} (next : FullTable → ProbComp α) :
    𝒮[do let table ← ($ᵗ FullTable : ProbComp _); next table] =
      𝒮[do
        let other ← ($ᵗ OtherTable : ProbComp _)
        let key ← $ᵗ MacKey
        next (joinTable other key)] := by
  rw [evalSPMF_bind,← uniform_table_split,← evalSPMF_bind]
  simp only [bind_assoc,pure_bind]

end SiggolfT3Mac4.Source
