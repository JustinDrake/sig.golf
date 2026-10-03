import SigGolfCandidate.Bridge.Basic

namespace SigGolfCandidate.Bridge
open OracleComp OracleSpec

variable {ι ι' : Type} {spec : OracleSpec.{0,0} ι} {spec' : OracleSpec.{0,0} ι'}

theorem Ext.simulateQ {α : Type} {p q : OracleComp spec α}
    (h : Ext p q) (impl : QueryImpl spec (OracleComp spec')) :
    Ext (_root_.simulateQ impl p) (_root_.simulateQ impl q) := by
  induction h with
  | leaf x q =>
    simp only [simulateQ_pure,simulateQ_map]
    exact Ext.leaf x (_root_.simulateQ impl q)
  | queryBind t k k' hk ih =>
    simp only [simulateQ_bind]
    exact Ext.bind_congr (_root_.simulateQ impl (spec.query t)) ih

theorem Rel.simulateQ {α β : Type} {p : OracleComp spec α} {q : OracleComp spec β}
    {R : α → β → Prop} (h : Rel p q R) (impl : QueryImpl spec (OracleComp spec')) :
    Rel (_root_.simulateQ impl p) (_root_.simulateQ impl q) R := by
  obtain ⟨J,h1,h2⟩ := h
  refine ⟨_root_.simulateQ impl J,?_,?_⟩
  · rw [← simulateQ_map]
    exact h1.simulateQ impl
  · rw [← simulateQ_map,h2]

end SigGolfCandidate.Bridge
