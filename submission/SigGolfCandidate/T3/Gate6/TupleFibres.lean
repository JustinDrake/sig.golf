import SigGolfCandidate.T3.Gate6.CappedCounting
namespace SigGolfResearch.Gate6
open SigGolfCandidate.Budget.Octopus Finset
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

noncomputable def tripleSet (v : Triple) (hv : Function.Injective v) : ChildSet :=
  ⟨slotSet v,mem_powersetCard.mpr ⟨fun x hx => by
    rw [slotSet,List.mem_toFinset,mem_valList] at hx
    obtain ⟨i,rfl⟩ := hx
    exact mem_range.mpr (v i).isLt,by
      rw [slotSet,List.toFinset_card_of_nodup ((valList_nodup v).mpr hv)]
      simp [valList]⟩⟩

abbrev Enumeration (s : ChildSet) := {v : Triple // Function.Injective v ∧ slotSet v=s.val}

noncomputable def orderedEquiv : {s : Slots // SlotsAccepted s} ≃
    (Σ f : {s : SetFamily // familyCost s≤89}, (bank : Bank) → Enumeration (f.val bank)) where
  toFun s := ⟨⟨fun b => tripleSet (s.val b) (s.property.1 b),s.property.2⟩,
    fun b => ⟨s.val b,s.property.1 b,rfl⟩⟩
  invFun x := ⟨fun b => (x.2 b).val,fun b => (x.2 b).property.1,by
    change (∑ b,octH 7 (slotSet (x.2 b).val).sort)≤89
    simp_rw [(x.2 _).property.2]
    exact x.1.property⟩
  left_inv s := by apply Subtype.ext;rfl
  right_inv x := by
    apply Sigma.ext
    · apply Subtype.ext
      funext b
      exact Subtype.ext (x.2 b).property.2
    · apply Function.hfunext rfl
      intro b b' hb
      have hb' : b=b' := eq_of_heq hb
      subst b'
      refine (Subtype.heq_iff_coe_eq (fun v => ?_)).mpr ?_
      · change (Function.Injective v ∧ slotSet v=slotSet (x.2 b).val) ↔
          (Function.Injective v ∧ slotSet v=(x.1.val b).val)
        rw [(x.2 b).property.2]
      · rfl

theorem enumeration_card (s : ChildSet) : Fintype.card (Enumeration s) = 6 := by
  rw [Fintype.card_subtype]
  exact (card_fiber 3 128 s.val s.property).trans (by decide)

theorem sigma_card_constant {α : Type} {β : α → Type} [Fintype α] [∀a,Fintype (β a)]
    (c : Nat) (hc : ∀ a,Fintype.card (β a)=c) : Fintype.card (Sigma β)=Fintype.card α*c := by
  rw [Fintype.card_sigma]
  simp only [hc,sum_const,card_univ,smul_eq_mul]

theorem enumeration_family_card (f : {s : SetFamily // familyCost s≤89}) :
    Fintype.card ((bank : Bank) → Enumeration (f.val bank))=6^7 := by
  rw [Fintype.card_pi]
  simp only [enumeration_card,prod_const,card_univ,Bank,Fintype.card_fin]

theorem ordered_accepted_card : Fintype.card {s : Slots // SlotsAccepted s} =
    6^7 * 4788386417148790282433944980488716288 := by
  have hfirst := Fintype.card_congr orderedEquiv
  have hmiddle := sigma_card_constant (β:=fun f : {s : SetFamily // familyCost s≤89} =>
    (bank : Bank) → Enumeration (f.val bank)) (6^7) enumeration_family_card
  have hlast : Fintype.card {s : SetFamily // familyCost s≤89}=4788386417148790282433944980488716288 := by
    rw [Fintype.card_subtype]
    exact capped_family_card
  exact hfirst.trans (hmiddle.trans ((congrArg (fun n => n*6^7) hlast).trans (Nat.mul_comm _ _)))

end SigGolfResearch.Gate6
#print axioms SigGolfResearch.Gate6.ordered_accepted_card
