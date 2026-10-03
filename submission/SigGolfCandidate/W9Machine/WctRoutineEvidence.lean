import SigGolfCandidate.W9Machine.WctChainTrace
import SigGolfCandidate.W9Machine.WctRoutineReady

section

namespace W9Machine
instance chainWordLawfulBEq : LawfulBEq ChainWord := by
  refine { rfl := ?_, eq_of_beq := ?_ }
  · intro a
    cases a <;> simp [BEq.beq, instBEqChainWord.beq]
  · intro a b h
    cases a <;> cases b <;> simp_all [BEq.beq, instBEqChainWord.beq]
end W9Machine
end

section


namespace W9Machine.Chain
theorem ready_of_checks (rank : Fin 728) (r : ChainRoutine) (hrank : r.rank = rank.val)
    (hc : r.checked = true) (hg : planGuard r.pieces {} = true) (hl : PlanLinked r.pieces)
    (ht : terminalChecked r = true) : RoutineReady rank r := by
  have hcost := r.checked_cycles hc
  simp only [ChainRoutine.checked, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨_, hd⟩, he⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  have hd' : r.digits = ClaudeWCT.WCT9.codeword rank := by
    rw [hrank] at hd
    have hb : rank.val < (ClaudeWCT.WCT9.compositions 4 7 6).length := by
      simpa only [ClaudeWCT.WCT9.codebook_card] using rank.isLt
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb,
      Option.getD_some, ClaudeWCT.WCT9.codeword] using hd
  simp only [terminalChecked, Bool.and_eq_true, beq_iff_eq] at ht
  refine ⟨hg, hl, by simpa only [hrank] using he, ht.1.trans (congrArg expectedQueries hd'),
    ?_, (planCycles_eq r).trans_le hcost⟩
  intro t ht7 word hw2
  have h := List.all_eq_true.mp (List.all_eq_true.mp ht.2 t (List.mem_range.mpr ht7))
    word (List.mem_range.mpr hw2)
  simpa only [beq_iff_eq, hd'] using h
end W9Machine.Chain
end
