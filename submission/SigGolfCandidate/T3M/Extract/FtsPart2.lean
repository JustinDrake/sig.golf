import SigGolfCandidate.T3M.Extract.FtsPart1

namespace SigGolfCandidate.T3M.FtsExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem ftsStepP_extract (answers : Answers) (sig : Signature) (pads : Pads) (index : Nat)
    (chosen : List Selection) (secret : Nat → Digest) (R : List Digest) (u coord : Nat)
    (hb : (chosen.getD coord ⟨0, []⟩).bucket < 16) (R' : List Digest) (u' : Nat)
    (hrun : evalWithAnswerFn answers (ftsStepP sig pads index chosen (some (R, u)) coord) = some (R', u')) :
    ∃ root, R' = R ++ [root] ∧ (root = honL answers index coord secret 11 0 →
      (AllHonest answers index coord secret (queried answers (ftsStepP sig pads index chosen (some (R, u)) coord)) ∧
        LeavesHonest coord (selectedLeaves (chosen.getD coord ⟨0, []⟩)) (coordValues sig coord) pads secret 7
          (chosen.getD coord ⟨0, []⟩).bucket) ∨
      TreeHit answers index coord secret (queried answers (ftsStepP sig pads index chosen (some (R, u)) coord))) := by
  rw [ftsStepP_some] at hrun ⊢
  rw [evalWithAnswerFn_bind] at hrun
  rcases h1 : evalWithAnswerFn answers (recoverChildP index coord (selectedLeaves (chosen.getD coord ⟨0, []⟩))
      (coordValues sig coord) sig.proof pads 7 (chosen.getD coord ⟨0, []⟩).bucket u) with _ | ⟨value, next⟩
  · simp only [coordValues] at h1; rw [h1] at hrun; simp at hrun
  simp only [coordValues] at h1
  rw [h1] at hrun
  dsimp only at hrun
  rw [evalWithAnswerFn_bind] at hrun
  rcases h2 : evalWithAnswerFn answers ((List.range 4).foldlM
      (outerStepP sig pads index coord (chosen.getD coord ⟨0, []⟩).bucket) (some (value, next))) with _ | ⟨root, n2⟩
  · rw [h2] at hrun; simp at hrun
  rw [h2] at hrun
  simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rfl, -⟩ := hrun
  refine ⟨root, rfl, fun hroot => ?_⟩
  rw [queried_bind, h1]
  dsimp only
  rw [queried_bind, h2]
  dsimp only
  rw [queried_pure, List.append_nil]
  have hv : root = honL answers index coord secret (7 + 4) ((chosen.getD coord ⟨0, []⟩).bucket / 2 ^ 4) := by
    rw [Nat.div_eq_of_lt (by simpa using hb)]; exact hroot
  rcases outer_extract answers sig pads index coord _ secret hb value next 4 (le_refl _) root n2 h2 hv with
    ⟨hv0, a2⟩ | t2
  · rcases recoverChildP_extract answers index coord _ _ sig.proof pads secret 7 _ u value next (by decide)
        (by simpa using hb) h1 hv0 with ⟨a1, l1⟩ | t1
    · left
      exact ⟨allHonest_append a1 a2, l1⟩
    · right
      exact treeHit_mono t1 fun q hq => List.mem_append_left _ hq
  · right
    exact treeHit_mono t2 fun q hq => List.mem_append_right _ hq
theorem ftsFold_runs (answers : Answers) (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection)
    (secret : Nat → Nat → Digest) : ∀ n (roots : List Digest) (used : Nat),
      (∀ c < n, (chosen.getD c ⟨0, []⟩).bucket < 16) →
      evalWithAnswerFn answers ((List.range n).foldlM (ftsStepP sig pads index chosen) (some ([], 0))) =
        some (roots, used) →
      roots.length = n ∧ ∃ us : Nat → Nat, us n = used ∧
        (∀ c < n, evalWithAnswerFn answers (ftsStepP sig pads index chosen (some (roots.take c, us c)) c) =
          some (roots.take (c + 1), us (c + 1))) ∧
        queried answers ((List.range n).foldlM (ftsStepP sig pads index chosen) (some ([], 0))) =
          (List.range n).flatMap (fun c =>
            queried answers (ftsStepP sig pads index chosen (some (roots.take c, us c)) c)) := by
  intro n
  induction n with
  | zero =>
      intro roots used _ hrun
      simp only [List.range_zero, List.foldlM_nil, evalWithAnswerFn_pure, Option.some.injEq,
        Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨rfl, fun _ => 0, rfl, fun c hc => by omega, by simp⟩
  | succ n ih =>
      intro roots used hb hrun
      rw [List.range_succ, List.foldlM_append] at hrun ⊢
      rw [queried_bind]
      rw [evalWithAnswerFn_bind] at hrun
      rcases hs : evalWithAnswerFn answers ((List.range n).foldlM (ftsStepP sig pads index chosen)
          (some ([], 0))) with _ | ⟨R, u⟩
      · rw [hs] at hrun; simp [ftsStepP] at hrun
      try rw [hs] at hrun
      simp only [List.foldlM_cons, List.foldlM_nil, bind_pure] at hrun ⊢
      obtain ⟨hlen, us, hus, hsteps, hq⟩ := ih R u (fun c hc => hb c (by omega)) hs
      obtain ⟨root, rfl, -⟩ := ftsStepP_extract answers sig pads index chosen (secret n) R u n (hb n (by omega))
        roots used hrun
      have htake : ∀ c, c ≤ n → (R ++ [root]).take c = R.take c := fun c hc =>
        List.take_append_of_le_length (by omega)
      refine ⟨by simp [hlen], fun c => if c = n + 1 then used else us c, by simp, fun c hc => ?_, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
        · dsimp only
          rw [htake c (by omega), htake (c + 1) (by omega), if_neg (by omega), if_neg (by omega)]
          exact hsteps c hc
        · dsimp only
          have e1 : R.take c = R := List.take_of_length_le (by omega)
          have e2 : (R ++ [root]).take (c + 1) = R ++ [root] := List.take_of_length_le (by simp; omega)
          rw [htake c le_rfl, if_neg (by omega), if_pos rfl, hus, e1, e2]
          exact hrun
      · dsimp only
        have e1 : R.take n = R := List.take_of_length_le (by omega)
        rw [hq, List.flatMap_append, List.flatMap_singleton, htake n le_rfl, if_neg (by omega), hus, e1]
        congr 1
        apply List.flatMap_congr
        intro c hc
        have hc := List.mem_range.mp hc
        rw [htake c (by omega), if_neg (by omega)]
theorem forestPk_eq_shortHash (index : Nat) (roots : List Digest) :
    forestPk index roots = shortHash (Extract.forestInput index roots) := rfl
theorem sameHeader_forest (index : Nat) (roots roots' : List Digest) :
    Extract.SameHeader (pad64 (Extract.forestInput index roots)) (pad64 (Extract.forestInput index roots')) := by
  unfold Extract.SameHeader Extract.forestInput Extract.listInput pad64
  rw [List.append_assoc _ _ (List.replicate _ 0), List.append_assoc _ _ (List.replicate _ 0),
    hdrBlock_append _ (bytesLE_length _ _) (bytesLE_length _ _),
    hdrBlock_append _ (bytesLE_length _ _) (bytesLE_length _ _)]
def honRoots (answers : Answers) (index : Nat) (secret : Nat → Nat → Digest) : List Digest :=
  (List.range 7).map fun c => honL answers index c (secret c) 11 0
theorem flatMap_bytesLE_length (l : List Digest) : (l.flatMap (bytesLE 16)).length = 16 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, bytesLE_length, ih, List.length_cons]; ring
theorem flatMap_bytesLE_injective : ∀ (l l' : List Digest), l.length = l'.length →
    l.flatMap (bytesLE 16) = l'.flatMap (bytesLE 16) → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, a' :: l', h, he => by
      simp only [List.flatMap_cons] at he
      obtain ⟨ha, hl⟩ := List.append_inj he (by simp only [bytesLE_length])
      rw [bytesLE_injective ha, flatMap_bytesLE_injective l l' (by simpa using h) hl]
theorem pad64_injective_of_length {x y : HashInput} (hl : x.length = y.length) (h : pad64 x = pad64 y) : x = y := by
  unfold pad64 at h
  rw [hl] at h
  exact (List.append_inj h hl).1
theorem forestInput_injective {index : Nat} {roots roots' : List Digest} (hl : roots.length = 7)
    (hl' : roots'.length = 7) (h : pad64 (Extract.forestInput index roots) = pad64 (Extract.forestInput index roots')) :
    roots = roots' := by
  have hlen : (Extract.forestInput index roots).length = (Extract.forestInput index roots').length := by
    simp only [Extract.forestInput, Extract.listInput, List.length_append, bytesLE_length, flatMap_bytesLE_length, List.length_drop, hl, hl']
  have h := pad64_injective_of_length hlen h
  unfold Extract.forestInput Extract.listInput at h
  obtain ⟨h12, h3⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h1, -⟩ := List.append_inj h12 (by simp only [bytesLE_length])
  have hd := flatMap_bytesLE_injective _ _ (by simp only [List.length_drop, hl, hl']) h3
  have h0 := bytesLE_injective h1
  rcases roots with _ | ⟨a, t⟩
  · simp at hl
  rcases roots' with _ | ⟨a', t'⟩
  · simp at hl'
  simp only [List.getD_cons_zero] at h0
  simp only [List.drop_succ_cons, List.drop_zero] at hd
  rw [h0, hd]
theorem recoverFtsP_extract (answers : Answers) (sig : Signature) (pads : Pads) (index : Nat)
    (chosen : List Selection) (secret : Nat → Nat → Digest) (v : Digest)
    (hb : ∀ c < 7, (chosen.getD c ⟨0, []⟩).bucket < 16)
    (hrun : evalWithAnswerFn answers (recoverFtsP sig pads index chosen) = some v)
    (hroot : v = evalWithAnswerFn answers (forestPk index (honRoots answers index secret))) :
    ((∀ q ∈ queried answers (recoverFtsP sig pads index chosen),
        q = .inl (.inr (pad64 (Extract.forestInput index (honRoots answers index secret)))) ∨
        ∃ c < 7, ∃ l n, l ≤ 11 ∧ n < 2 ^ (11 - l) ∧ q = .inl (.inr (honInputL answers index c (secret c) l n))) ∧
      ∀ c < 7, LeavesHonest c (selectedLeaves (chosen.getD c ⟨0, []⟩)) (coordValues sig c) pads (secret c) 7
        (chosen.getD c ⟨0, []⟩).bucket) ∨
    ∃ actual, .inl (.inr actual) ∈ queried answers (recoverFtsP sig pads index chosen) ∧
      ((HashHit answers (pad64 (Extract.forestInput index (honRoots answers index secret))) actual ∧
          Extract.SameHeader actual (pad64 (Extract.forestInput index (honRoots answers index secret)))) ∨
        ∃ c < 7, ∃ l n, l ≤ 11 ∧ n < 2 ^ (11 - l) ∧ HashHit answers (honInputL answers index c (secret c) l n) actual ∧
          Extract.SameHeader actual (honInputL answers index c (secret c) l n)) := by
  rw [recoverFtsP_eq] at hrun ⊢
  rw [queried_bind]
  rw [evalWithAnswerFn_bind] at hrun
  rcases hs : evalWithAnswerFn answers ((List.range 7).foldlM (ftsStepP sig pads index chosen) (some ([], 0)))
    with _ | ⟨roots, used⟩
  · rw [hs] at hrun; simp at hrun
  try rw [hs] at hrun
  dsimp only at hrun ⊢
  by_cases hz : (!(List.range (115 - used)).all (fun j =>
      decide (sig.proof ⟨(used + j) % 115, Nat.mod_lt _ (by decide)⟩ = 0))) = true
  · rw [if_pos hz] at hrun; simp at hrun
  rw [if_neg hz] at hrun ⊢
  rw [queried_bind, forestPk_eq_shortHash, queried_shortHash, queried_pure, List.append_nil]
  rw [evalWithAnswerFn_bind, forestPk_eq_shortHash, eval_shortHash] at hrun
  simp only [evalWithAnswerFn_pure, Option.some.injEq] at hrun
  rw [forestPk_eq_shortHash, eval_shortHash] at hroot
  obtain ⟨hlen, us, -, hsteps, hq⟩ := ftsFold_runs answers sig pads index chosen secret 7 roots used hb hs
  rw [hq]
  by_cases heq : pad64 (Extract.forestInput index roots) = pad64 (Extract.forestInput index (honRoots answers index secret))
  · have hR : roots = honRoots answers index secret :=
      forestInput_injective hlen (by simp [honRoots]) heq
    have hcoord : ∀ c < 7,
        (AllHonest answers index c (secret c)
            (queried answers (ftsStepP sig pads index chosen (some (roots.take c, us c)) c)) ∧
          LeavesHonest c (selectedLeaves (chosen.getD c ⟨0, []⟩)) (coordValues sig c) pads (secret c) 7
            (chosen.getD c ⟨0, []⟩).bucket) ∨
        TreeHit answers index c (secret c)
          (queried answers (ftsStepP sig pads index chosen (some (roots.take c, us c)) c)) := by
      intro c hc
      obtain ⟨root, hrt, himp⟩ := ftsStepP_extract answers sig pads index chosen (secret c) (roots.take c) (us c) c
        (hb c hc) _ _ (hsteps c hc)
      apply himp
      have h1 : (roots.take (c + 1)).getD c 0 = roots.getD c 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_take]; try simp
      have h2 : (roots.take c ++ [root]).getD c 0 = root := by
        rw [List.getD_append_right _ _ _ _ (by simp only [List.length_take]; omega)]
        simp [show c - min c roots.length = 0 by omega]
      rw [← h2, ← hrt, h1, hR]
      simp [honRoots, hc]
    by_cases hhit : ∃ c < 7, TreeHit answers index c (secret c)
        (queried answers (ftsStepP sig pads index chosen (some (roots.take c, us c)) c))
    · right
      obtain ⟨c, hc, actual, hmem, l, n, hl, hn, hh, hsh⟩ := hhit
      exact ⟨actual, List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, hmem⟩),
        Or.inr ⟨c, hc, l, n, hl, hn, hh, hsh⟩⟩
    · left
      have hall : ∀ c < 7, _ := fun c hc => (hcoord c hc).resolve_right fun ht => hhit ⟨c, hc, ht⟩
      refine ⟨fun q hq => ?_, fun c hc => (hall c hc).2⟩
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨c, hc, hmem⟩ := List.mem_flatMap.mp hq
        have hc := List.mem_range.mp hc
        exact Or.inr ⟨c, hc, (hall c hc).1 q hmem⟩
      · rw [List.mem_singleton] at hq
        exact Or.inl (by rw [hq, hR])
  · right
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), Or.inl ⟨⟨heq, hrun.trans hroot⟩, sameHeader_forest ..⟩⟩
end SigGolfCandidate.T3M.FtsExtract
