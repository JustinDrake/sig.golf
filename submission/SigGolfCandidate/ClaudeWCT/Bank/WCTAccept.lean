import SigGolfCandidate.ClaudeWCT.WCT9.Basic
import SigGolfCandidate.ClaudeWCT.Bank.WCTSpec

section

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev DigestCoordinates := (Fin (2 ^ 31) × Fin 4096) ×
  (Coord → Fin 128 × Fin 16384) × (BitVec 1 × BitVec 1 × BitVec 22)
def digestCoordinates (output : HashOutput) : DigestCoordinates :=
  (((output.extractLsb' 0 31).toFin, (output.extractLsb' 31 12).toFin),
    (fun coord => ((output.extractLsb' (coordBase coord.val) 7).toFin,
      (output.extractLsb' (coordBase coord.val + 7) 14).toFin)),
    (output.extractLsb' 127 1, output.extractLsb' 191 1, output.extractLsb' 234 22))
def admissibleView (view : DigestCoordinates) : Bool :=
  decide (view.1.2.val = 0) &&
    (List.finRange 9).all (fun coord => decide ((view.2.1 coord).2.val < 16016))
theorem bit_cover : ∀ position, position < 256 →
    position < 31 ∨ (31 ≤ position ∧ position < 43) ∨ position = 127 ∨ position = 191 ∨
      234 ≤ position ∨
      ∃ coord : Coord, coordBase coord.val ≤ position ∧ position < coordBase coord.val + 21 := by
  decide
theorem digestCoordinates_injective : Function.Injective digestCoordinates := by
  intro left right he
  apply BitVec.eq_of_getLsbD_eq
  intro position hp
  rcases bit_cover position hp with hindex | hgate | h127 | h191 | hhigh | ⟨coord, hlo, hhi⟩
  · have hc := congrArg (fun x : DigestCoordinates => BitVec.ofFin x.1.1) he
    change left.extractLsb' 0 31 = right.extractLsb' 0 31 at hc
    have hb := congrArg (fun bits : BitVec 31 => bits.getLsbD position) hc
    simpa only [BitVec.getLsbD_extractLsb', hindex, decide_true, Bool.true_and, Nat.zero_add] using hb
  · have hc := congrArg (fun x : DigestCoordinates => (BitVec.ofFin x.1.2 : BitVec 12)) he
    change left.extractLsb' 31 12 = right.extractLsb' 31 12 at hc
    have hb := congrArg (fun bits : BitVec 12 => bits.getLsbD (position - 31)) hc
    have hbit : position - 31 < 12 := by omega
    have hoff : 31 + (position - 31) = position := by omega
    simpa only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and, hoff] using hb
  · subst position
    have hc := congrArg (fun x : DigestCoordinates => x.2.2.1) he
    change left.extractLsb' 127 1 = right.extractLsb' 127 1 at hc
    have hb := congrArg (fun bits : BitVec 1 => bits.getLsbD 0) hc
    simpa only [BitVec.getLsbD_extractLsb', Nat.zero_lt_one, decide_true, Bool.true_and,
      Nat.add_zero] using hb
  · subst position
    have hc := congrArg (fun x : DigestCoordinates => x.2.2.2.1) he
    change left.extractLsb' 191 1 = right.extractLsb' 191 1 at hc
    have hb := congrArg (fun bits : BitVec 1 => bits.getLsbD 0) hc
    simpa only [BitVec.getLsbD_extractLsb', Nat.zero_lt_one, decide_true, Bool.true_and,
      Nat.add_zero] using hb
  · have hc := congrArg (fun x : DigestCoordinates => x.2.2.2.2) he
    change left.extractLsb' 234 22 = right.extractLsb' 234 22 at hc
    have hb := congrArg (fun bits : BitVec 22 => bits.getLsbD (position - 234)) hc
    have hbit : position - 234 < 22 := by omega
    have hoff : 234 + (position - 234) = position := by omega
    simpa only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and, hoff] using hb
  · let within := position - coordBase coord.val
    have hoff : coordBase coord.val + within = position := by dsimp only [within]; omega
    by_cases hchild : within < 7
    · have hc := congrArg (fun x : DigestCoordinates =>
        (BitVec.ofFin (x.2.1 coord).1 : BitVec 7)) he
      change left.extractLsb' (coordBase coord.val) 7 =
        right.extractLsb' (coordBase coord.val) 7 at hc
      have hb := congrArg (fun bits : BitVec 7 => bits.getLsbD within) hc
      simpa only [BitVec.getLsbD_extractLsb', hchild, decide_true, Bool.true_and, hoff] using hb
    · let bit := within - 7
      have hbit : bit < 14 := by dsimp only [bit, within]; omega
      have hoff' : coordBase coord.val + 7 + bit = position := by dsimp only [bit, within]; omega
      have hc := congrArg (fun x : DigestCoordinates =>
        (BitVec.ofFin (x.2.1 coord).2 : BitVec 14)) he
      change left.extractLsb' (coordBase coord.val + 7) 14 =
        right.extractLsb' (coordBase coord.val + 7) 14 at hc
      have hb := congrArg (fun bits : BitVec 14 => bits.getLsbD bit) hc
      simpa only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and, hoff'] using hb
theorem digestCoordinates_bijective : Function.Bijective digestCoordinates := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨digestCoordinates_injective, ?_⟩
  simp only [DigestCoordinates, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bitVec]
  norm_num
theorem index_decode (output : HashOutput) :
    (digestCoordinates output).1.1.val = output.toNat % 2 ^ 31 := by
  simp only [digestCoordinates, BitVec.val_toFin, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
theorem gate_decode (output : HashOutput) :
    (digestCoordinates output).1.2.val = output.toNat / 2 ^ 31 % 2 ^ 12 := by
  simp only [digestCoordinates, BitVec.val_toFin, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
theorem child_decode (output : HashOutput) (coord : Coord) :
    ((digestCoordinates output).2.1 coord).1 = child output coord := by
  apply Fin.ext
  simp only [digestCoordinates, child, BitVec.val_toFin, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
theorem field_decode (output : HashOutput) (coord : Coord) :
    ((digestCoordinates output).2.1 coord).2.val = field output coord := by
  simp only [digestCoordinates, field, BitVec.val_toFin, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
theorem rank_decode (output : HashOutput) (coord : Coord) :
    (rank output coord).val = ((digestCoordinates output).2.1 coord).2.val % 728 := by
  rw [field_decode, rank_val]
theorem admissible_decode (output : HashOutput) :
    admissibleView (digestCoordinates output) = admissible output := by
  rw [Bool.eq_iff_iff, admissible_iff]
  unfold admissibleView
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    forall_true_left, gate_decode, field_decode]
theorem uniform_coordinates :
    𝒮[digestCoordinates <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒮[($ᵗ DigestCoordinates : ProbComp DigestCoordinates)] := by
  exact evalSPMF_map_bijective_uniform_cross (α := HashOutput) (β := DigestCoordinates)
    digestCoordinates digestCoordinates_bijective
end ClaudeWCT.WCT9
end

section


namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open ClaudeWCT.WCT9 (Coord Child Rank child rank DigestCoordinates digestCoordinates admissibleView)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def viewProposal (v : DigestCoordinates) : WProposal :=
  (v.1.1, fun k => ((v.2.1 k).1, ⟨(v.2.1 k).2.val % 728, Nat.mod_lt _ (by decide)⟩))
theorem viewProposal_decode (x : HashOutput) : viewProposal (digestCoordinates x) = proposal x := by
  refine Prod.ext (Fin.ext ?_) (funext fun k => Prod.ext (WCT9.child_decode x k) (Fin.ext ?_))
  · exact WCT9.index_decode x
  · exact (WCT9.rank_decode x k).symm
theorem admissibleView_iff (v : DigestCoordinates) :
    admissibleView v = true ↔ v.1.2.val = 0 ∧ ∀ k : Coord, (v.2.1 k).2.val < 16016 := by
  unfold admissibleView
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange, forall_true_left]
abbrev FibreData := (Coord → Fin 22) × (BitVec 1 × BitVec 1 × BitVec 22)
def fibreEquiv (p : WProposal) :
    {v : DigestCoordinates // admissibleView v = true ∧ viewProposal v = p} ≃ FibreData where
  toFun v := (fun k => ⟨(v.1.2.1 k).2.val / 728, by
      have := ((admissibleView_iff v.1).1 v.2.1).2 k
      omega⟩, v.1.2.2)
  invFun s := ⟨((p.1, 0), fun k => ((p.2 k).1, ⟨(p.2 k).2.val + 728 * (s.1 k).val, by
      have h1 := (p.2 k).2.isLt
      have h2 := (s.1 k).isLt
      omega⟩), s.2), by
    refine ⟨(admissibleView_iff _).2 ⟨rfl, fun k => ?_⟩, ?_⟩
    · have h1 := (p.2 k).2.isLt
      have h2 := (s.1 k).isLt
      show (p.2 k).2.val + 728 * (s.1 k).val < 16016
      omega
    · refine Prod.ext rfl (funext fun k => Prod.ext rfl (Fin.ext ?_))
      have h1 := (p.2 k).2.isLt
      show ((p.2 k).2.val + 728 * (s.1 k).val) % 728 = (p.2 k).2.val
      omega⟩
  left_inv v := by
    obtain ⟨⟨⟨i, g⟩, f, u⟩, hadm, hp⟩ := v
    subst hp
    have hg := ((admissibleView_iff _).1 hadm).1
    apply Subtype.ext
    refine Prod.ext (Prod.ext rfl (Fin.ext hg.symm)) (Prod.ext (funext fun k => Prod.ext rfl (Fin.ext ?_)) rfl)
    show (f k).2.val % 728 + 728 * ((f k).2.val / 728) = (f k).2.val
    omega
  right_inv s := by
    obtain ⟨q, u⟩ := s
    refine Prod.ext (funext fun k => Fin.ext ?_) rfl
    have h1 := (p.2 k).2.isLt
    show ((p.2 k).2.val + 728 * (q k).val) / 728 = (q k).val
    omega
theorem card_fibreData : Fintype.card FibreData = 22 ^ 9 * 2 ^ 24 := by
  simp only [FibreData, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bitVec]
  norm_num
theorem card_fibre (p : WProposal) :
    (Finset.univ.filter (fun x : HashOutput => WCT9.admissible x = true ∧ proposal x = p)).card =
      22 ^ 9 * 2 ^ 24 := by
  have e : {x : HashOutput // WCT9.admissible x = true ∧ proposal x = p} ≃
      {v : DigestCoordinates // admissibleView v = true ∧ viewProposal v = p} :=
    (Equiv.ofBijective digestCoordinates WCT9.digestCoordinates_bijective).subtypeEquiv
      (fun x => by
        change WCT9.admissible x = true ∧ proposal x = p ↔
          admissibleView (digestCoordinates x) = true ∧ viewProposal (digestCoordinates x) = p
        rw [WCT9.admissible_decode, viewProposal_decode])
  have hc := Fintype.card_congr (e.trans (fibreEquiv p))
  rw [card_fibreData, Fintype.card_subtype] at hc
  exact hc
theorem sum_admissible (g : WProposal → ENNReal) :
    (∑ x : HashOutput, if WCT9.admissible x = true then g (proposal x) else 0) =
      ((22 ^ 9 * 2 ^ 24 : Nat) : ENNReal) * ∑ p, g p := by
  rw [← Finset.sum_filter, ← Finset.sum_fiberwise _ proposal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const,
    Finset.filter_filter, card_fibre, nsmul_eq_mul]
theorem sum_admissible_one :
    (∑ x : HashOutput, if WCT9.admissible x = true then (1 : ENNReal) else 0) =
      ((22 ^ 9 * 2 ^ 24 : Nat) : ENNReal) * (Fintype.card WProposal : ENNReal) := by
  rw [sum_admissible (fun _ => 1), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
theorem acceptance_eq_ratio :
    Pr[fun x : HashOutput => WCT9.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ((22 ^ 9 * 2 ^ 24 : Nat) : ENNReal) * (Fintype.card WProposal : ENNReal) /
        (Fintype.card HashOutput : ENNReal) := by
  rw [← expectedValue_ite_one, BPORS.expected_uniform_eq_finiteAverage]
  unfold SigGolfResearch.Gate6.Moments.finiteAverage
  rw [sum_admissible_one]
theorem acceptedProposalUniform : AcceptedProposalUniform := by
  intro g
  rw [acceptance_eq_ratio, BPORS.expected_uniform_eq_finiteAverage]
  unfold SigGolfResearch.Gate6.Moments.finiteAverage
  rw [sum_admissible]
  have hP : (Fintype.card WProposal : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hP' : (Fintype.card WProposal : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  simp only [div_eq_mul_inv]
  calc ((22 ^ 9 * 2 ^ 24 : Nat) : ENNReal) * (∑ p, g p) * (Fintype.card HashOutput : ENNReal)⁻¹
      = ((22 ^ 9 * 2 ^ 24 : Nat) : ENNReal) * (∑ p, g p) * (Fintype.card HashOutput : ENNReal)⁻¹ *
          ((Fintype.card WProposal : ENNReal)⁻¹ * (Fintype.card WProposal : ENNReal)) := by
        rw [ENNReal.inv_mul_cancel hP hP', mul_one]
    _ = _ := by ring
theorem acceptance_eq :
    Pr[fun x : HashOutput => WCT9.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (16016 ^ 9 : ENNReal) / 2 ^ 138 := by
  rw [acceptance_eq_ratio]
  simp only [WProposal, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bitVec]
  rw [ENNReal.div_eq_div_iff (by positivity) (by finiteness) (by positivity) (by finiteness)]
  norm_num
theorem acceptanceBound : AcceptanceBound := by
  unfold AcceptanceBound
  rw [acceptance_eq]
  have h0 : (16016 ^ 9 : ENNReal) ≤ 2 ^ 132 := by
    exact_mod_cast (show (16016 ^ 9 : Nat) ≤ 2 ^ 132 by norm_num)
  have h : (16016 ^ 9 : ENNReal) / 2 ^ 138 ≤ 2 ^ 132 / 2 ^ 138 := ENNReal.div_le_div_right h0 _
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.div_eq_div_iff (by positivity) (by finiteness) (by positivity) (by finiteness)]
  norm_num
noncomputable def wctSpec' (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate) :
    FtsBankSpec WProposal :=
  wctSpec acceptedProposalUniform acceptanceBound horizon rate hexc
theorem wctSpec'_eq (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate) :
    wctSpec' horizon rate hexc = wctSpec acceptedProposalUniform acceptanceBound horizon rate hexc := rfl
end ClaudeWCT.Bank.WCT
end
