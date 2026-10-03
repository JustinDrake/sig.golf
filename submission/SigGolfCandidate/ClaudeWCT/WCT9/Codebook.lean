import Mathlib

namespace ClaudeWCT.WCT9
def compositions (width : Nat) : Nat → Nat → List (List Nat)
  | 0, total => if total = 0 then [[]] else []
  | parts + 1, total =>
    (List.range (min width (total + 1))).flatMap fun x =>
      (compositions width parts (total - x)).map (x :: ·)
theorem mem_compositions {width parts total : Nat} {xs : List Nat}
    (h : xs ∈ compositions width parts total) :
    xs.length = parts ∧ xs.sum = total ∧ ∀ x ∈ xs, x < width := by
  induction parts generalizing total xs with
  | zero =>
      simp only [compositions] at h
      split_ifs at h with ht
      · simp only [List.mem_singleton] at h
        subst xs
        simp [ht]
      · simp at h
  | succ parts ih =>
      simp only [compositions, List.mem_flatMap, List.mem_range, List.mem_map] at h
      obtain ⟨x, hx, ys, hy, rfl⟩ := h
      obtain ⟨hlen, hsum, hbound⟩ := ih hy
      have hxw : x < width := lt_of_lt_of_le hx (Nat.min_le_left _ _)
      have hxt : x < total + 1 := lt_of_lt_of_le hx (Nat.min_le_right _ _)
      refine ⟨by simp [hlen], by simp [hsum]; omega, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hxw
      · exact hbound y hy
theorem compositions_nodup (width parts total : Nat) :
    (compositions width parts total).Nodup := by
  induction parts generalizing total with
  | zero => simp [compositions]; split_ifs <;> simp
  | succ parts ih =>
      rw [compositions, List.nodup_flatMap]
      refine ⟨fun x _ => (ih (total - x)).map (fun xs ys h => (List.cons.inj h).2), ?_⟩
      exact List.nodup_range.imp fun {x y} hne zs hx hy => by
        obtain ⟨xs, _, rfl⟩ := List.mem_map.mp hx
        obtain ⟨ys, _, he⟩ := List.mem_map.mp hy
        exact hne (List.cons.inj he).1.symm
theorem valid_mem {width parts total : Nat} {values : List Nat}
    (hlen : values.length = parts) (hsum : values.sum = total)
    (hbound : ∀ value ∈ values, value < width) : values ∈ compositions width parts total := by
  induction parts generalizing total values with
  | zero =>
      have hv : values = [] := List.length_eq_zero_iff.mp hlen
      subst values
      simp only [List.sum_nil] at hsum
      simp [compositions, ← hsum]
  | succ parts ih =>
      cases values with
      | nil => simp at hlen
      | cons value rest =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          have hs : value + rest.sum = total := hsum
          have hv := hbound value (by simp)
          have hx : value < min width (total + 1) := by omega
          apply List.mem_flatMap.mpr
          refine ⟨value, List.mem_range.mpr hx, ?_⟩
          apply List.mem_map.mpr
          refine ⟨rest, ?_, rfl⟩
          apply ih hlen (by omega)
          intro x hx
          exact hbound x (List.mem_cons_of_mem _ hx)
theorem mem_compositions_iff {width parts total : Nat} {xs : List Nat} :
    xs ∈ compositions width parts total ↔
      xs.length = parts ∧ xs.sum = total ∧ ∀ x ∈ xs, x < width :=
  ⟨mem_compositions, fun ⟨hlen, hsum, hbound⟩ => valid_mem hlen hsum hbound⟩
theorem compositions_lex (width parts total : Nat) :
    (compositions width parts total).Pairwise (List.Lex (· < ·)) := by
  induction parts generalizing total with
  | zero =>
      simp only [compositions]
      split_ifs <;> simp
  | succ parts ih =>
      rw [compositions, List.pairwise_flatMap]
      refine ⟨fun x _ => (ih (total - x)).map _ (fun xs ys h => List.Lex.cons h), ?_⟩
      refine List.pairwise_lt_range.imp_of_mem ?_
      intro x y _ _ hxy xs hx ys hy
      obtain ⟨xs', _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨ys', _, rfl⟩ := List.mem_map.mp hy
      exact List.Lex.rel hxy
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem codebook_card : (compositions 4 7 6).length = 728 := by decide
def codeword (rank : Fin 728) : List Nat :=
  (compositions 4 7 6)[rank.val]'(by rw [codebook_card]; exact rank.isLt)
def digit (rank : Fin 728) (chain : Fin 7) : Nat :=
  (codeword rank).getD chain.val 0
theorem codeword_valid (rank : Fin 728) :
    (codeword rank).length = 7 ∧ (codeword rank).sum = 6 ∧
      ∀ value ∈ codeword rank, value < 4 :=
  mem_compositions (List.getElem_mem _)
theorem codeword_injective : Function.Injective codeword := by
  intro left right he
  apply Fin.ext
  exact (compositions_nodup 4 7 6).getElem_inj_iff.mp he
theorem codeword_mem (rank : Fin 728) : codeword rank ∈ compositions 4 7 6 :=
  List.getElem_mem _
theorem codeword_surjective {values : List Nat} (hlen : values.length = 7)
    (hsum : values.sum = 6) (hbound : ∀ value ∈ values, value < 4) :
    ∃ rank : Fin 728, codeword rank = values := by
  have hm := valid_mem hlen hsum hbound
  obtain ⟨n, hn, he⟩ := List.mem_iff_getElem.mp hm
  exact ⟨⟨n, by rwa [codebook_card] at hn⟩, he⟩
set_option maxRecDepth 100000 in
theorem codeword_zero : codeword 0 = [0, 0, 0, 0, 0, 3, 3] := by decide +kernel
set_option maxRecDepth 100000 in
theorem codeword_one : codeword 1 = [0, 0, 0, 0, 1, 2, 3] := by decide +kernel
set_option maxRecDepth 100000 in
theorem codeword_last : codeword 727 = [3, 3, 0, 0, 0, 0, 0] := by decide +kernel
theorem digit_lt (rank : Fin 728) (chain : Fin 7) : digit rank chain < 4 := by
  have hi : chain.val < (codeword rank).length := by
    rw [(codeword_valid rank).1]
    exact chain.isLt
  rw [digit, List.getD_eq_getElem _ _ hi]
  exact (codeword_valid rank).2.2 _ (List.getElem_mem hi)
theorem digit_le_three (rank : Fin 728) (chain : Fin 7) : digit rank chain ≤ 3 := by
  have := digit_lt rank chain
  omega
theorem ofFn_digit (rank : Fin 728) :
    List.ofFn (fun chain : Fin 7 => digit rank chain) = codeword rank := by
  apply List.ext_getElem
  · simp [(codeword_valid rank).1]
  · intro i hi hj
    simp only [List.getElem_ofFn, digit, List.getD_eq_getElem _ _ hj]
theorem step_count (rank : Fin 728) : (∑ chain : Fin 7, digit rank chain) = 6 := by
  rw [← List.sum_ofFn, ofFn_digit, (codeword_valid rank).2.1]
theorem revealed_count (rank : Fin 728) : (∑ chain : Fin 7, (3 - digit rank chain)) = 15 := by
  have h := step_count rank
  have hle := digit_le_three rank
  have hsum : (∑ chain : Fin 7, (3 - digit rank chain)) + (∑ chain : Fin 7, digit rank chain) =
      ∑ _chain : Fin 7, 3 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun chain _ => Nat.sub_add_cancel (hle chain))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega
abbrev Encoding := Fin 7 → Fin 4
abbrev ValidEncoding := {values : Encoding // (∑ chain, (values chain).val) = 6}
def encode (rank : Fin 728) : ValidEncoding :=
  ⟨fun chain => ⟨digit rank chain, digit_lt rank chain⟩, step_count rank⟩
theorem encode_injective : Function.Injective encode := by
  intro left right he
  apply codeword_injective
  apply List.ext_getElem
  · rw [(codeword_valid left).1, (codeword_valid right).1]
  · intro i hi hj
    have hi7 : i < 7 := by rwa [(codeword_valid left).1] at hi
    have hd := congrArg (fun value : ValidEncoding => (value.val ⟨i, hi7⟩).val) he
    simpa only [encode, digit, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using hd
theorem encode_surjective : Function.Surjective encode := by
  intro values
  let xs := List.ofFn fun chain : Fin 7 => (values.val chain).val
  have hlen : xs.length = 7 := List.length_ofFn
  have hsum : xs.sum = 6 := by rw [List.sum_ofFn]; exact values.property
  have hbound : ∀ value ∈ xs, value < 4 := by
    intro value hv
    obtain ⟨chain, rfl⟩ := List.mem_ofFn.mp hv
    exact (values.val chain).isLt
  obtain ⟨rank, hr⟩ := codeword_surjective hlen hsum hbound
  refine ⟨rank, ?_⟩
  apply Subtype.ext
  funext chain
  apply Fin.ext
  change digit rank chain = (values.val chain).val
  rw [digit, hr, List.getD_eq_getElem _ _ (by rw [hlen]; exact chain.isLt)]
  exact List.getElem_ofFn _
theorem encode_bijective : Function.Bijective encode :=
  ⟨encode_injective, encode_surjective⟩
noncomputable def equivalence : Fin 728 ≃ ValidEncoding :=
  Equiv.ofBijective encode encode_bijective
theorem validEncoding_card : Fintype.card ValidEncoding = 728 := by
  rw [← Fintype.card_fin 728]
  exact (Fintype.card_congr equivalence).symm
theorem antichain (left right : Fin 728)
    (h : ∀ chain, digit left chain ≤ digit right chain) : left = right := by
  have hsum : (∑ chain, digit left chain) = ∑ chain, digit right chain := by
    rw [step_count, step_count]
  have he := (Finset.sum_eq_sum_iff_of_le (fun chain _ => h chain)).mp hsum
  apply encode_injective
  apply Subtype.ext
  funext chain
  apply Fin.ext
  exact he chain (Finset.mem_univ chain)
section Walk
variable {Value : Type}
def walk (step : Nat → Value → Value) (start : Nat) : Nat → Value → Value
  | 0, value => value
  | count + 1, value => step (start + count) (walk step start count value)
theorem walk_add (step : Nat → Value → Value) (start first second : Nat) (value : Value) :
    walk step start (first + second) value =
      walk step (start + first) second (walk step start first value) := by
  induction second with
  | zero => simp [walk]
  | succ second ih =>
      change step (start + (first + second)) (walk step start (first + second) value) =
        step ((start + first) + second)
          (walk step (start + first) second (walk step start first value))
      rw [ih, Nat.add_assoc]
def opening (step : Fin 7 → Nat → Value → Value) (secrets : Fin 7 → Value)
    (rank : Fin 728) (chain : Fin 7) : Value :=
  walk (step chain) 0 (3 - digit rank chain) (secrets chain)
def recover (step : Fin 7 → Nat → Value → Value) (rank : Fin 728)
    (values : Fin 7 → Value) (chain : Fin 7) : Value :=
  walk (step chain) (3 - digit rank chain) (digit rank chain) (values chain)
theorem recover_opening (step : Fin 7 → Nat → Value → Value) (secrets : Fin 7 → Value)
    (rank : Fin 728) (chain : Fin 7) :
    recover step rank (opening step secrets rank) chain = walk (step chain) 0 3 (secrets chain) := by
  have hd := digit_lt rank chain
  unfold recover opening
  have h := (walk_add (step chain) 0 (3 - digit rank chain)
    (digit rank chain) (secrets chain)).symm
  simpa only [Nat.zero_add, Nat.sub_add_cancel (by omega : digit rank chain ≤ 3)] using h
theorem padded_backward_hit {Input : Type} (hash : Input → Value)
    (actualInput : Nat → Value → Input) (honestInput : Nat → Input)
    (honest : Nat → Value)
    (honest_step : ∀ position, honest (position + 1) = hash (honestInput position))
    (decode_input : ∀ position value, actualInput position value = honestInput position →
      value = honest position)
    (start count : Nat) (value : Value)
    (endpoint : walk (fun position value => hash (actualInput position value)) start count value =
      honest (start + count)) :
    (value = honest start ∧ ∀ offset < count,
      actualInput (start + offset)
        (walk (fun position value => hash (actualInput position value)) start offset value) =
      honestInput (start + offset)) ∨
    ∃ offset < count,
      actualInput (start + offset)
        (walk (fun position value => hash (actualInput position value)) start offset value) ≠
      honestInput (start + offset) ∧
      hash (actualInput (start + offset)
        (walk (fun position value => hash (actualInput position value)) start offset value)) =
      honest (start + offset + 1) := by
  induction count with
  | zero =>
      refine Or.inl ⟨?_, ?_⟩
      · simpa only [walk, Nat.add_zero] using endpoint
      · intro offset ho
        omega
  | succ count ih =>
      rcases Classical.em (actualInput (start + count)
          (walk (fun position value => hash (actualInput position value)) start count value) =
          honestInput (start + count)) with he | he
      · have hprior := decode_input (start + count) _ he
        rcases ih hprior with ⟨hv, hinputs⟩ | ⟨offset, ho, hne, hhash⟩
        · refine Or.inl ⟨hv, ?_⟩
          intro offset ho
          by_cases hc : offset < count
          · exact hinputs offset hc
          · have hoff : offset = count := by omega
            subst offset
            exact he
        · exact Or.inr ⟨offset, by omega, hne, hhash⟩
      · refine Or.inr ⟨count, by omega, he, ?_⟩
        have hcollision :
            hash (actualInput (start + count)
              (walk (fun position value => hash (actualInput position value)) start count value)) =
            hash (honestInput (start + count)) := by
          rw [← honest_step]
          simpa only [walk, Nat.add_assoc] using endpoint
        exact hcollision.trans (honest_step (start + count)).symm
end Walk
end ClaudeWCT.WCT9
