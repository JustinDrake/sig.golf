import SigGolfCandidate.SphincsSecurity.Completeness.Uniform
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingProbability

/-!
# Three overlapping windows with a gated upper branch

Write an answer as four 64-bit words A,B,C,D, low to high. If B's high bit is set,
select CD when A's high four bits encode a value at least 1, and otherwise retain
AB. If B's high bit is clear, select BC when A's high bit is set, and otherwise
select AB. The gate accepts 15 of its 16 inputs. Every padding-clear digest has
(1 + 1/2 + 15/32) times 2^128 preimages. This is also the global maximum fibre
size, including outputs with nonzero padding.
-/
namespace SphincsSecurity
open OracleComp ENNReal Finset Completeness
set_option allowUnsafeReducibility true in
attribute [local reducible] hashOutputBits digestBits
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option linter.constructorNameAsVariable false

@[simp] theorem truncateHash_getLsbD_63 (a : HashOutput) :
    (truncateHash a).getLsbD 63 = a.getLsbD 63 := by
  simp [truncateHash, BitVec.getLsbD_extractLsb', digestBits]
@[simp] theorem truncateHash_getLsbD_127 (a : HashOutput) :
    (truncateHash a).getLsbD 127 = a.getLsbD 127 := by
  simp [truncateHash, BitVec.getLsbD_extractLsb', digestBits]
@[simp] theorem truncateHash_getLsbD_62 (a : HashOutput) :
    (truncateHash a).getLsbD 62 = a.getLsbD 62 := by
  simp [truncateHash, BitVec.getLsbD_extractLsb', digestBits]

/-- The selector gate only reads bits below 64. -/
theorem encodingGate_extractLsb'_zero {n w : Nat} (a : BitVec n) (hw : 64 ≤ w) :
    encodingGate (a.extractLsb' 0 w) = encodingGate a := by
  unfold encodingGate
  rw [BitVec.extractLsb'_extractLsb'_of_le (show 60 + 4 ≤ w by omega)]

@[simp] theorem encodingGate_truncateHash (a : HashOutput) :
    encodingGate (truncateHash a) = encodingGate a := by
  exact encodingGate_extractLsb'_zero a (by decide : 64 ≤ digestBits)

theorem truncateHash_shiftRight (a : HashOutput) (k : Nat) :
    truncateHash (a >>> k) = a.extractLsb' k digestBits := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hiRaw : i < hashOutputBits := lt_trans hi (by decide)
  simp [truncateHash, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
    hi, hiRaw, Nat.add_comm]

def middleSplit (a : HashOutput) : Digest × Digest :=
  (a.extractLsb' 64 128, (a.extractLsb' 0 64) ++ (a.extractLsb' 192 64))

theorem middleSplit_injective : Function.Injective middleSplit := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change (a.extractLsb' 0 64 ++ a.extractLsb' 192 64) = (b.extractLsb' 0 64 ++ b.extractLsb' 192 64) at h2
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change i < 256 at hi
  by_cases h64 : i < 64
  · have hh := congrArg (fun d : BitVec 128 => d.getLsbD (i + 64)) h2
    simpa only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
      Nat.add_sub_cancel, Nat.zero_add, if_false, if_true, decide_true, Bool.true_and,
      show ¬i + 64 < 64 by omega, h64] using hh
  · by_cases h192 : i < 192
    · have hh := congrArg (fun d : Digest => d.getLsbD (i - 64)) h1
      simpa [middleSplit, BitVec.getLsbD_extractLsb', show i - 64 < 128 by omega,
        show 64 + (i - 64) = i by omega] using hh
    · have hh := congrArg (fun d : BitVec 128 => d.getLsbD (i - 192)) h2
      simpa only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
      Nat.add_sub_cancel, Nat.zero_add, if_false, if_true, decide_true, Bool.true_and,
        show i - 192 < 64 by omega, show 192 + (i - 192) = i by omega] using hh

theorem middleSplit_bijective : Function.Bijective middleSplit := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨middleSplit_injective, ?_⟩
  norm_num [Fintype.card_prod, Fintype.card_bitVec, hashOutputBits, digestBits]

namespace EncodingSelection

def lowKeep (d : Digest) : Prop :=
  (d.getLsbD 127 = false ∧ d.getLsbD 63 = false) ∨
    (d.getLsbD 127 = true ∧ encodingGate d = false)
def highGate (d : Digest) : Prop :=
  d.getLsbD 127 = true ∧ encodingGate d = true

instance (d : Digest) : Decidable (lowKeep d) := inferInstanceAs (Decidable (_ ∨ _))
instance (d : Digest) : Decidable (highGate d) := inferInstanceAs (Decidable (_ ∧ _))

theorem card_highBit64 (v : Bool) :
    (univ.filter fun d : BitVec 64 => d.getLsbD 63 = v).card = 2 ^ 63 := by
  have hbit : (univ.filter fun b : BitVec 1 => b.getLsbD 0 = v).card = 1 := by cases v <;> decide
  have h := card_filter_high (n := 64) (w := 63) (by decide)
    (fun b : BitVec 1 => b.getLsbD 0 = v)
  simpa only [BitVec.getLsbD_extractLsb', show (0:Nat)<1 by decide,
    decide_true, Bool.true_and, Nat.add_zero, hbit, mul_one] using h

theorem card_highBit128 (v : Bool) :
    (univ.filter fun d : BitVec 128 => d.getLsbD 127 = v).card = 2 ^ 127 := by
  have hbit : (univ.filter fun b : BitVec 1 => b.getLsbD 0 = v).card = 1 := by cases v <;> decide
  have h := card_filter_high (n := 128) (w := 127) (by decide)
    (fun b : BitVec 1 => b.getLsbD 0 = v)
  simpa only [BitVec.getLsbD_extractLsb', show (0:Nat)<1 by decide,
    decide_true, Bool.true_and, Nat.add_zero, hbit, mul_one] using h


/-- Count the gate by its interval of accepted four-bit values, without enumerating vectors. -/
theorem card_gate4 :
    (univ.filter fun b : BitVec 4 => (!b.ult 1#4) = true).card = 15 := by
  have he : (univ.filter fun b : BitVec 4 => (!b.ult 1#4) = true) =
      (univ.filter fun b : BitVec 4 => 1 ≤ b.toNat) := by
    ext b
    simp [BitVec.ult_eq_decide, BitVec.toNat_ofNat, Nat.not_lt]
    omega
  rw [he, Octopus.card_bitVec_filter']
  have hr : ((range (2 ^ 4)).filter fun k : Nat => 1 ≤ k) = Ico 1 16 := by
    ext k
    simp only [mem_filter, mem_range, mem_Ico]
    norm_num <;> omega
  rw [hr]
  norm_num

theorem card_selector_set : (univ.filter highGate).card = 15 * 2 ^ 123 := by
  classical
  let A : Finset (BitVec 64) := univ.filter fun a => encodingGate a = true
  let B : Finset (BitVec 64) := univ.filter fun b => b.getLsbD 63 = true
  have hA : A.card = 15 * 2 ^ 60 := by
    have h := card_filter_high (n:=64) (w:=60) (by decide)
      (fun b : BitVec 4 => (!b.ult 1#4) = true)
    change (univ.filter fun a : BitVec 64 => encodingGate a = true).card =
      2 ^ 60 * (univ.filter fun b : BitVec 4 => (!b.ult 1#4) = true).card at h
    rw [card_gate4] at h
    simpa only [A, Nat.mul_comm] using h
  have hB : B.card = 2 ^ 63 := card_highBit64 true
  have h := card_filter_splitBits (n:=128) (w:=64) (by decide)
    (fun p => p.2.getLsbD 63 = true ∧ encodingGate p.1 = true)
  have hs : (univ.filter highGate) = (univ.filter fun a : BitVec 128 =>
      (splitBits 128 64 a).2.getLsbD 63 = true ∧
        encodingGate (splitBits 128 64 a).1 = true) := by
    ext a
    simp only [mem_filter,mem_univ,true_and,highGate,splitBits,
      encodingGate_extractLsb'_zero a (by decide : 64 ≤ 64), BitVec.getLsbD_extractLsb']
    norm_num
  have hp : (univ.filter fun p : BitVec 64 × BitVec 64 =>
      p.2.getLsbD 63 = true ∧ encodingGate p.1 = true) = A ×ˢ B := by
    ext p; simp [A,B,and_comm]
  rw [hs,h,hp,card_product,hA,hB]; norm_num

theorem card_low (targets : Finset Digest) :
    (univ.filter fun a : HashOutput => lowKeep (truncateHash a) ∧ truncateHash a ∈ targets).card =
      (targets.filter lowKeep).card * 2 ^ 128 := by
  have h := card_filter_low (n:=256) (w:=128) (by decide)
    (fun d : Digest => lowKeep d ∧ d ∈ targets)
  have he : (univ.filter fun d : Digest => lowKeep d ∧ d ∈ targets) = targets.filter lowKeep := by
    ext d; simp [and_comm]
  simpa only [truncateHash, digestBits, he, show (256:Nat)-128=128 by decide] using h

theorem card_mid (targets : Finset Digest) :
    (univ.filter fun a : HashOutput => a.getLsbD 127 = false ∧ a.getLsbD 63 = true ∧
      a.extractLsb' 64 128 ∈ targets).card =
      (targets.filter fun d => d.getLsbD 63 = false).card * 2 ^ 127 := by
  classical
  let P : Digest × Digest → Prop := fun p => p.1 ∈ targets ∧ p.1.getLsbD 63 = false ∧ p.2.getLsbD 127 = true
  have hc : (univ.filter fun a : HashOutput => P (middleSplit a)).card = (univ.filter P).card := by
    apply Finset.card_bij (fun a _ => middleSplit a)
    · intro a ha; simpa using ha
    · intro a _ b _ he; exact middleSplit_injective he
    · intro p hp
      obtain ⟨a,ha⟩ := middleSplit_bijective.2 p
      refine ⟨a,?_,ha⟩
      simp only [mem_filter,mem_univ,true_and] at hp ⊢
      rw [ha]; exact hp
  have hp : (univ.filter P) = (targets.filter fun d => d.getLsbD 63 = false) ×ˢ
      (univ.filter fun d : Digest => d.getLsbD 127 = true) := by
    ext p; simp only [P,mem_filter,mem_univ,true_and,mem_product,and_assoc]
  have hs : (univ.filter fun a : HashOutput => a.getLsbD 127 = false ∧ a.getLsbD 63 = true ∧
      a.extractLsb' 64 128 ∈ targets) = (univ.filter fun a => P (middleSplit a)) := by
    ext a
    clear hc hp
    simp only [P,middleSplit,mem_filter,mem_univ,true_and,BitVec.getLsbD_append,BitVec.getLsbD_extractLsb',digestBits]
    norm_num only
    simp only [decide_true, decide_false, if_false, Bool.true_and, and_assoc,and_left_comm,and_comm]
  rw [hs,hc,hp,card_product]
  have hbit : (univ.filter fun d : Digest => d.getLsbD 127 = true).card = 2 ^ 127 :=
    card_highBit128 true
  rw [hbit]

theorem card_high (targets : Finset Digest) :
    (univ.filter fun a : HashOutput => highGate (truncateHash a) ∧ a.extractLsb' 128 128 ∈ targets).card =
      (15 * 2 ^ 123) * targets.card := by
  have h := card_filter_splitBits (n:=256) (w:=128) (by decide)
    (fun p => highGate p.1 ∧ p.2 ∈ targets)
  have hp : (univ.filter fun p : Digest × Digest => highGate p.1 ∧ p.2 ∈ targets) =
      (univ.filter highGate) ×ˢ targets := by ext p; simp
  simpa only [splitBits, truncateHash, digestBits, hp, card_product, card_selector_set, show (256:Nat)-128=128 by decide] using h

theorem card_select_mem (targets : Finset Digest) :
    (univ.filter fun a : HashOutput => selectEncodingDigest a ∈ targets).card =
      (targets.filter lowKeep).card * 2 ^ 128 +
      (targets.filter fun d => d.getLsbD 63 = false).card * 2 ^ 127 +
      (15 * 2 ^ 123) * targets.card := by
  classical
  let L := univ.filter fun a : HashOutput => lowKeep (truncateHash a) ∧ truncateHash a ∈ targets
  let M := univ.filter fun a : HashOutput => a.getLsbD 127 = false ∧ a.getLsbD 63 = true ∧ a.extractLsb' 64 128 ∈ targets
  let H := univ.filter fun a : HashOutput => highGate (truncateHash a) ∧ a.extractLsb' 128 128 ∈ targets
  have he : (univ.filter fun a : HashOutput => selectEncodingDigest a ∈ targets) = (L ∪ M) ∪ H := by
    ext a
    simp only [L,M,H,mem_filter,mem_univ,true_and,mem_union,lowKeep,highGate,
      truncateHash_getLsbD_63,truncateHash_getLsbD_127,encodingGate_truncateHash]
    cases h127 : a.getLsbD 127 <;> cases h63 : a.getLsbD 63 <;> cases hgate : encodingGate a <;>
      simp [selectEncodingDigest,selectEncodingAnswer,h127,h63,hgate,truncateHash_shiftRight,digestBits]
  have hLM : Disjoint L M := by
    apply Finset.disjoint_left.mpr; intro a ha hb
    simp only [L,M,mem_filter,mem_univ,true_and,lowKeep,
      truncateHash_getLsbD_63,truncateHash_getLsbD_127] at ha hb
    rcases ha.1 with ha | ha
    · exact Bool.noConfusion (ha.2.symm.trans hb.2.1)
    · exact Bool.noConfusion (hb.1.symm.trans ha.1)
  have hLH : Disjoint L H := by
    apply Finset.disjoint_left.mpr; intro a ha hb
    simp only [L,H,mem_filter,mem_univ,true_and,lowKeep,highGate] at ha hb
    rcases ha.1 with ha | ha
    · exact Bool.noConfusion (ha.1.symm.trans hb.1.1)
    · exact Bool.noConfusion (ha.2.symm.trans hb.1.2)
  have hMH : Disjoint M H := by
    apply Finset.disjoint_left.mpr; intro a ha hb
    simp only [M,H,mem_filter,mem_univ,true_and,highGate,truncateHash_getLsbD_127] at ha hb
    exact Bool.noConfusion (ha.1.symm.trans hb.1.1)
  rw [he,card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hLH,hMH⟩),
    card_union_of_disjoint hLM]
  exact congrArg₂ (·+·) (congrArg₂ (·+·) (card_low targets) (card_mid targets)) (card_high targets)

theorem card_select_mem_of_padding (targets : Finset Digest)
    (hpad : ∀ d ∈ targets, (d.getLsbD 63 || d.getLsbD 127) = false) :
    (univ.filter fun a : HashOutput => selectEncodingDigest a ∈ targets).card =
      (2 ^ 128 + 2 ^ 127 + 15 * 2 ^ 123) * targets.card := by
  have h1 : ∀ d ∈ targets, lowKeep d := by
    intro d hd; obtain ⟨ha,hb⟩ := Bool.or_eq_false_iff.mp (hpad d hd); exact Or.inl ⟨hb,ha⟩
  have h2 : ∀ d ∈ targets, d.getLsbD 63 = false := fun d hd => (Bool.or_eq_false_iff.mp (hpad d hd)).1
  rw [card_select_mem,filter_eq_self.mpr h1,filter_eq_self.mpr h2]; ring

theorem prob_select_mem_of_padding (targets : Finset Digest)
    (hpad : ∀ d ∈ targets, (d.getLsbD 63 || d.getLsbD 127) = false) :
    Pr[fun a : HashOutput => selectEncodingDigest a ∈ targets | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (63 / 32 : ENNReal) * ((targets.card : ENNReal) / (Fintype.card Digest : ENNReal)) := by
  rw [probEvent_uniform,card_select_mem_of_padding targets hpad]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Fintype.card_bitVec]
  norm_num [hashOutputBits,digestBits] <;> ring

theorem card_select_eq_le (target : Digest) :
    (univ.filter fun a : HashOutput => selectEncodingDigest a = target).card ≤ 2 ^ 128 + 2 ^ 127 + 15 * 2 ^ 123 := by
  have h := card_select_mem ({target} : Finset Digest)
  simp only [mem_singleton,card_singleton,mul_one] at h
  rw [h]
  have h1 : (({target} : Finset Digest).filter lowKeep).card ≤ 1 := (card_filter_le _ _).trans_eq (card_singleton _)
  have h2 : (({target} : Finset Digest).filter fun d => d.getLsbD 63 = false).card ≤ 1 := (card_filter_le _ _).trans_eq (card_singleton _)
  nlinarith

theorem prob_select_eq_le (target : Digest) :
    Pr[fun a : HashOutput => selectEncodingDigest a = target | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (63 / 32 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [probEvent_uniform]
  calc
    _ ≤ ((2 ^ 128 + 2 ^ 127 + 15 * 2 ^ 123 : Nat) : ENNReal) / 2 ^ hashOutputBits :=
      ENNReal.div_le_div_right (by exact_mod_cast card_select_eq_le target) _
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [hashOutputBits,digestBits,ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow]

theorem prob_select_eq_le_pmf (target : Digest) :
    Pr[fun a : HashOutput => selectEncodingDigest a = target | PMF.uniformOfFintype HashOutput] ≤
      (63 / 32 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  simpa only [probEvent_eq_tsum_ite,probOutput_uniformSample,PMF.probOutput_eq_apply,PMF.uniformOfFintype_apply] using prob_select_eq_le target
end EncodingSelection
end SphincsSecurity
