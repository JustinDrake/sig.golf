import SigGolfCandidate.Verify.ChainSem
import SigGolfCandidate.Verify.ChainCheckAll
import SigGolfCandidate.Verify.Judg

/-! # W1a chains: the simulation judgment for one chain and for all 42 chains of a layer

From `ChainIn c i` (chain `i`'s code start, the table slot of its triple for `A = 3t`, the shared
block for `B`, `C`) the machine performs chain `i`'s abstract steps `chainFromP` (with the chain's
witness pad) and, after a triple's `C`, the extraction and dispatch of the next triple, or after
chain 41 the return `jalr zero, ra` (`ChainNext`).

Cycle cost of chain `i` at digit `d` (`chainCost`): `A`'s table slot jump (1), the head and
rungs `6 + 9 (7 - d)` (head 5, each rung `sb` 1 + ecall 8, the last rung's `li a2` 1) or the
digit-7 copy 5, and after `C` the dispatch 4 (`srli/slli; and; add; jalr`) or the return 1.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

/-! ## The kernel checks at a chain context -/

theorem kOf_lt (c : CCtx) (t : Nat) : kOf c t < 512 := by
  unfold kOf; have := dig_lt c (3 * t); have := dig_lt c (3 * t + 1); have := dig_lt c (3 * t + 2); omega

theorem kOf_digits (c : CCtx) (t : Nat) :
    kOf c t % 8 = dig c (3 * t) ∧ kOf c t / 8 % 8 = dig c (3 * t + 1) ∧ kOf c t / 64 = dig c (3 * t + 2) := by
  unfold kOf; have := dig_lt c (3 * t); have := dig_lt c (3 * t + 1); have := dig_lt c (3 * t + 2)
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem tb_eq (c : CCtx) (i : Nat) :
    triBase (i / 3) (dig c (3 * (i / 3) + 1)) (dig c (3 * (i / 3) + 2)) = tb c i := rfl

/-- The part check (`B` or `C`) of chain `i` at its digit. -/
theorem part_at (c : CCtx) (i : Nat) (hi : i < 42) (h0 : i % 3 ≠ 0) :
    partCheck i (dig c i) (startPc c i) (endPc c i) = true := by
  obtain ⟨t, r, rfl, hr⟩ : ∃ t r, i = 3 * t + r ∧ r < 3 := ⟨i / 3, i % 3, by omega, by omega⟩
  have et : (3 * t + r) / 3 = t := by omega
  have hb := blkCheck_at t (dig c (3 * t + 1)) (dig c (3 * t + 2)) (by omega) (dig_lt _ _) (dig_lt _ _)
  unfold blkCheck at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨-, hB⟩, hC⟩, -⟩ := hb
  unfold startPc endPc tB tC tX
  rw [et, if_neg h0, if_neg h0]
  rcases (show r = 1 ∨ r = 2 by omega) with rfl | rfl
  · rw [if_pos (by omega), if_pos (by omega)]; exact hB
  · rw [if_neg (by omega), if_neg (by omega)]; exact hC

theorem chk_head (c : CCtx) (i : Nat) (hi : i < 42) (hd : dig c i < 7) :
    runAt chK0 [] (startPc c i) [] =
      some (headExp i (dig c i) (rungPc c i (dig c i + 1)) (decide (i % 3 = 0))) := by
  by_cases h0 : i % 3 = 0
  · obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t := ⟨i / 3, by omega⟩
    have et : 3 * t / 3 = t := by omega
    have he := entCheck_at t (kOf c t) (by omega) (kOf_lt _ _)
    obtain ⟨k1, k2, k3⟩ := kOf_digits c t
    unfold entCheck at he
    simp only [] at he
    rw [k1, k2, k3, if_neg (by omega)] at he
    have hr : rungPc c (3 * t) (dig c (3 * t) + 1) =
        triBase t (dig c (3 * t + 1)) (dig c (3 * t + 2)) + 2 * dig c (3 * t) := by
      unfold rungPc tb; rw [if_pos h0, et]; omega
    have hs : startPc c (3 * t) = entW t (kOf c t) := by unfold startPc; rw [if_pos h0, et]
    rw [hs, hr, decide_eq_true h0]
    exact optBeq_eq he
  · have hp := part_at c i hi h0
    unfold partCheck at hp
    rw [if_neg (by omega), Bool.and_eq_true] at hp
    have hr : rungPc c i (dig c i + 1) = startPc c i + 4 := by
      unfold startPc rungPc; rw [if_neg h0, if_neg h0]; split <;> omega
    rw [hr, decide_eq_false h0]
    exact optBeq_eq hp.1

theorem chk_copy (c : CCtx) (i : Nat) (hi : i < 42) (hd : dig c i = 7) :
    runAt chK0 [endPc c i] (startPc c i) [] = some (copyExp i (endPc c i) (decide (i % 3 = 0))) := by
  by_cases h0 : i % 3 = 0
  · obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t := ⟨i / 3, by omega⟩
    have et : 3 * t / 3 = t := by omega
    have he := entCheck_at t (kOf c t) (by omega) (kOf_lt _ _)
    obtain ⟨k1, k2, k3⟩ := kOf_digits c t
    unfold entCheck at he
    simp only [] at he
    rw [k1, k2, k3, if_pos hd] at he
    have hs : startPc c (3 * t) = entW t (kOf c t) := by unfold startPc; rw [if_pos h0, et]
    have hq : endPc c (3 * t) = pcB t (dig c (3 * t + 1)) (dig c (3 * t + 2)) := by
      unfold endPc tB; rw [if_pos h0, et]
    rw [hs, hq, decide_eq_true h0]
    exact optBeq_eq he
  · have hp := part_at c i hi h0
    unfold partCheck at hp
    rw [if_pos hd] at hp
    rw [decide_eq_false h0]
    exact optBeq_eq hp

theorem chk_rung (c : CCtx) (i mu : Nat) (hi : i < 42) (h1 : dig c i + 2 ≤ mu) (h7 : mu ≤ 7) :
    rungCheck i mu (rungPc c i mu) = true := by
  by_cases h0 : i % 3 = 0
  · obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t := ⟨i / 3, by omega⟩
    have et : 3 * t / 3 = t := by omega
    have hb := blkCheck_at t (dig c (3 * t + 1)) (dig c (3 * t + 2)) (by omega) (dig_lt _ _) (dig_lt _ _)
    unfold blkCheck at hb
    simp only [Bool.and_eq_true] at hb
    have := List.all_eq_true.mp hb.1.1.1 mu (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    have hr : rungPc c (3 * t) mu = triBase t (dig c (3 * t + 1)) (dig c (3 * t + 2)) + 2 * (mu - 1) := by
      unfold rungPc tb; rw [if_pos h0, et]
    rw [hr]; exact this
  · have hp := part_at c i hi h0
    unfold partCheck at hp
    rw [if_neg (by omega), Bool.and_eq_true] at hp
    have := List.all_eq_true.mp hp.2 mu (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    have hr : rungPc c i mu = startPc c i + 4 + 2 * (mu - dig c i - 1) := by
      unfold rungPc startPc; rw [if_neg h0, if_neg h0]
    rw [hr]; exact this

theorem chk_x (c : CCtx) (t : Nat) (ht : t < 14) :
    runAt chK0 [] (tX c (3 * t + 2)) [.jmp] = some (xExp t) := by
  have hb := blkCheck_at t (dig c (3 * t + 1)) (dig c (3 * t + 2)) ht (dig_lt _ _) (dig_lt _ _)
  unfold blkCheck at hb
  simp only [Bool.and_eq_true] at hb
  have hx : tX c (3 * t + 2) = pcX t (dig c (3 * t + 1)) (dig c (3 * t + 2)) := by
    unfold tX; rw [show (3 * t + 2) / 3 = t by omega]
  rw [hx]
  exact optBeq_eq hb.2

/-! ## The abstract chain steps -/

/-- Steps `mu .. 7` of chain `i` from the value `v` with the chain's witness pad. -/
def restFold (c : CCtx) (i mu : Nat) (v : Val) : OracleComp HashSpec Val :=
  (List.range' mu (8 - mu)).foldlM (fun v mu => hash16 (chainInputP c.lay c.tau c.e i mu (witPad c.wl c.lay i) v)) v

theorem restFold_succ (c : CCtx) (i mu : Nat) (h : mu ≤ 7) (v : Val) :
    restFold c i mu v = hash16 (chainInputP c.lay c.tau c.e i mu (witPad c.wl c.lay i) v) >>= restFold c i (mu + 1) := by
  unfold restFold
  rw [show 8 - mu = (8 - (mu + 1)) + 1 by omega, List.range'_succ, List.foldlM_cons]

theorem restFold_8 (c : CCtx) (i : Nat) (v : Val) : restFold c i 8 v = pure v := rfl

theorem chainFromP_eq (c : CCtx) (i x : Nat) (hx : x < 7) (v : Val) :
    chainFromP c.lay c.tau c.e i x (witPad c.wl c.lay i) v = restFold c i (x + 1) v := by
  unfold chainFromP restFold; congr 2; omega

/-! ## After a chain: the dispatch of the next triple or the return -/

/-- The state before chain `j` (`j < 42`), or after the return of the chain code (`j = 42`). -/
def ChainNext (c : CCtx) (j : Nat) (acc : List Val) (s : MachineState) : Prop :=
  if j < 42 then ChainIn c j acc s else ChBase c 42 acc s ∧ Fresh c.wl c.lay 42 s ∧ s.pc = c.ret

/-- The dispatch cost after chain `i`: the next triple's extraction and `jalr` after a triple's `C`,
the return after chain 41. -/
def xCost (i : Nat) : Nat := if i % 3 = 2 then (if i = 41 then 1 else xSteps (i / 3)) else 0

theorem xCost_le (i : Nat) : xCost i ≤ 4 := by unfold xCost xSteps; split_ifs <;> omega

theorem end_next (c : CCtx) (hc : c.ok) (hret : c.ret &&& ~~~1#64 = c.ret) (i : Nat) (hi : i < 42)
    (acc : List Val) (s : MachineState) (hs : EndInv c i acc s) :
    ∃ u, Steps image s (xCost i) (xCost i) u ∧ ChainNext c (i + 1) acc u := by
  by_cases h2 : i % 3 = 2
  · obtain ⟨hx1, hx2⟩ := x_step c hc (i / 3) (by omega) acc (chk_x c (i / 3) (by omega)) hret s
      (by rw [show 3 * (i / 3) + 2 = i by omega]; exact hs)
    by_cases h41 : i = 41
    · subst h41
      obtain ⟨u, hu, h⟩ := hx2 rfl
      refine ⟨u, by simpa [xCost] using hu, ?_⟩
      unfold ChainNext; rw [if_neg (by omega)]; exact h
    · obtain ⟨u, hu, h⟩ := hx1 (by omega)
      refine ⟨u, by simpa [xCost, h2, h41] using hu, ?_⟩
      unfold ChainNext; rw [if_pos (by omega), show i + 1 = 3 * (i / 3) + 3 by omega]; exact h
  · refine ⟨s, by simpa [xCost, h2] using Steps.refl s, ?_⟩
    obtain ⟨hB, h25, hF, hpc⟩ := hs
    unfold ChainNext; rw [if_pos (by omega)]
    refine ⟨hB, h25, hF, ?_⟩
    rw [hpc]; unfold endPc startPc
    by_cases h0 : i % 3 = 0
    · rw [if_pos h0, if_neg (by omega), if_pos (by omega)]
      unfold tB; rw [show (i + 1) / 3 = i / 3 by omega]
    · rw [if_neg h0, if_pos (by omega), if_neg (by omega), if_neg (by omega)]
      unfold tC; rw [show (i + 1) / 3 = i / 3 by omega]

/-! ## One chain -/

/-- Cycles from just before step `mu`'s `ecall` to the chain's end. -/
def preCost (mu : Nat) : Nat := 9 * (7 - mu) + 8 + (if mu < 7 then 1 else 0)

theorem steps_good (c : CCtx) (hc : c.ok) (hret : c.ret &&& ~~~1#64 = c.ret) (i : Nat) (hi : i < 42)
    (acc : List Val) (K : List Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ v t, v.length = 16 → ChainNext c (i + 1) (acc ++ [v]) t → Good t N C (K (acc ++ [v]))) :
    ∀ k mu, mu + k = 7 → 1 ≤ mu → dig c i < mu → ∀ v s, PreHash c i acc mu v s →
      Good s (N + 3 * (8 - mu) + 4) (C + preCost mu + xCost i)
        (cc (restFold c i mu v) (fun v => K (acc ++ [v]))) := by
  intro k
  induction k with
  | zero =>
    intro mu hmu h1 hdm v s hs
    obtain rfl : mu = 7 := by omega
    have hvl := hs.2.2.2.2.2.2.2.2.1
    obtain ⟨h5, hv, hin, hpost⟩ := prehash_step c hc i 7 hi h1 (le_refl _) hdm acc v s hs
    rw [restFold_succ c i 7 (le_refl _), cc_bind]
    simp only [show 7 + 1 = 8 from rfl, restFold_8, cc_pure]
    have h2 : ∀ a, Good (writeHash s a) (N + xCost i) (C + xCost i) (K (acc ++ [answerBytes 16 a])) := by
      intro a
      obtain ⟨u, hu, hn⟩ := end_next c hc hret i hi _ _ ((hpost a).2 rfl)
      exact Good.steps hu (hK _ _ (by simp) hn)
    have h3 := Good.hash (K := fun v => K (acc ++ [v])) hs.2.2.2.2.2.2.2.2.2.2.2.2 h5 hv hin h2
    rw [addrFmt_blocks, blocks_chainInputP _ _ _ _ _ _ _ (length_witPad c hc i hi) hvl (by omega) (by omega) (by omega)] at h3
    have := xCost_le i
    exact h3.mono (by omega) (by simp [preCost]; omega)
  | succ k ih =>
    intro mu hmu h1 hdm v s hs
    have hvl := hs.2.2.2.2.2.2.2.2.1
    obtain ⟨h5, hv, hin, hpost⟩ := prehash_step c hc i mu hi h1 (by omega) hdm acc v s hs
    rw [restFold_succ c i mu (by omega), cc_bind]
    have h2 : ∀ a, Good (writeHash s a) (N + 3 * (8 - (mu + 1)) + 4 + 2)
        (C + preCost (mu + 1) + xCost i + (if mu + 1 = 7 then 2 else 1))
        (cc (restFold c i (mu + 1) (answerBytes 16 a)) (fun v => K (acc ++ [v]))) := by
      intro a
      obtain ⟨u, hu, hp⟩ := rung_step c hc i (mu + 1) (rungPc c i (mu + 1)) hi (by omega) (by omega)
        (chk_rung c i (mu + 1) hi (by omega) (by omega)) rfl acc _ _ ((hpost a).1 (by omega))
      have := ih (mu + 1) (by omega) (by omega) (by omega) _ _ hp
      exact Good.steps' hu this (by split <;> omega) (by omega)
    have h3 := Good.hash (K := fun v => cc (restFold c i (mu + 1) v) (fun v => K (acc ++ [v])))
      hs.2.2.2.2.2.2.2.2.2.2.2.2 h5 hv hin h2
    rw [addrFmt_blocks, blocks_chainInputP _ _ _ _ _ _ _ (length_witPad c hc i hi) hvl (by omega) (by omega) (by omega)] at h3
    refine h3.mono (by omega) ?_
    unfold preCost
    by_cases h6 : mu + 1 = 7
    · rw [if_pos h6, if_neg (by omega), if_pos (by omega)]; omega
    · rw [if_neg h6, if_pos (by omega), if_pos (by omega)]; omega

/-- Cycle cost of chain `i` at digit `d`. -/
def chainCost (i d : Nat) : Nat :=
  (if i % 3 = 0 then 1 else 0) + (if d = 7 then 4 else 5 + 9 * (7 - d)) + xCost i

theorem chain_good (c : CCtx) (hc : c.ok) (hret : c.ret &&& ~~~1#64 = c.ret) (i : Nat) (hi : i < 42)
    (acc : List Val) (K : List Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ v t, v.length = 16 → ChainNext c (i + 1) (acc ++ [v]) t → Good t N C (K (acc ++ [v])))
    (s : MachineState) (hs : ChainIn c i acc s) :
    Good s (N + 40) (C + chainCost i (dig c i))
      (cc (chainFromP c.lay c.tau c.e i (dig c i) (witPad c.wl c.lay i) (witChain c.wl c.lay i))
        (fun v => K (acc ++ [v]))) := by
  have hx := dig_lt c i
  have hw := length_witChain c hc i hi
  have := xCost_le i
  by_cases h7 : dig c i = 7
  · obtain ⟨t, hst, hE⟩ := copy_step c hc i hi h7 acc (chk_copy c i hi h7) s hs
    obtain ⟨u, hu, hn⟩ := end_next c hc hret i hi _ _ hE
    rw [h7]
    have : chainFromP c.lay c.tau c.e i 7 (witPad c.wl c.lay i) (witChain c.wl c.lay i) =
        pure (witChain c.wl c.lay i) := rfl
    rw [this, cc_pure]
    refine Good.steps' hst (Good.steps hu (hK _ u hw hn)) (by split <;> omega) ?_
    unfold chainCost; rw [if_pos rfl]; split <;> omega
  · obtain ⟨t, hst, hP⟩ := head_step c hc i hi (by omega) acc (chk_head c i hi (by omega)) s hs
    rw [chainFromP_eq c i _ (by omega)]
    have := steps_good c hc hret i hi acc K N C hK (6 - dig c i) (dig c i + 1) (by omega) (by omega)
      (by omega) _ _ hP
    refine Good.steps' hst this (by split <;> split <;> omega) ?_
    unfold chainCost preCost; rw [if_neg h7]
    by_cases h6 : dig c i = 6
    · rw [if_pos h6, if_neg (by omega)]; split <;> omega
    · rw [if_neg h6, if_pos (by omega)]; split <;> omega

/-! ## All chains -/

def chainF (c : CCtx) (xs : List Nat) (ends : List Val) (i : Nat) : OracleComp HashSpec (List Val) := do
  let v ← chainFromP c.lay c.tau c.e i (xs.getD i 0) (witPad c.wl c.lay i) (witChain c.wl c.lay i)
  pure (ends ++ [v])

def chainsCost (c : CCtx) (i k : Nat) : Nat :=
  ((List.range' i k).map fun j => chainCost j (dig c j)).sum

theorem chains_good (c : CCtx) (hc : c.ok) (hret : c.ret &&& ~~~1#64 = c.ret) (xs : List Nat)
    (hxs : ∀ i < 42, xs.getD i 0 = dig c i) (K : List Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ ends t, ChainNext c 42 ends t → Good t N C (K ends)) :
    ∀ k i, i + k = 42 → ∀ acc s, ChainNext c i acc s →
      Good s (N + 40 * k) (C + chainsCost c i k)
        (cc ((List.range' i k).foldlM (chainF c xs) acc) K) := by
  intro k
  induction k with
  | zero =>
    intro i hik acc s hs
    obtain rfl : i = 42 := by omega
    simpa [chainsCost] using hK acc s hs
  | succ k ih =>
    intro i hik acc s hs
    rw [List.range'_succ, List.foldlM_cons]
    simp only [chainF, bind_assoc, pure_bind, cc_bind]
    rw [hxs i (by omega)]
    have hs' : ChainIn c i acc s := by unfold ChainNext at hs; rwa [if_pos (by omega)] at hs
    have := chain_good c hc hret i (by omega) acc
      (fun ends => cc ((List.range' (i + 1) k).foldlM (chainF c xs) ends) K)
      (N + 40 * k) (C + chainsCost c (i + 1) k)
      (fun v t _ ht => by
        have := ih (i + 1) (by omega) (acc ++ [v]) t ht
        simpa [chainF] using this) s hs'
    refine this.mono (by omega) ?_
    simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons]
    omega

/-- All 42 chains, from the dispatch of triple 0. -/
theorem chains_good0 (c : CCtx) (hc : c.ok) (hret : c.ret &&& ~~~1#64 = c.ret) (xs : List Nat)
    (hxs : ∀ i < 42, xs.getD i 0 = dig c i) (K : List Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ ends t, ChainNext c 42 ends t → Good t N C (K ends)) (s : MachineState)
    (hs : ChainIn c 0 [] s) :
    Good s (N + 40 * 42) (C + chainsCost c 0 42) (cc ((List.range 42).foldlM (chainF c xs) []) K) := by
  have := chains_good c hc hret xs hxs K N C hK 42 0 rfl [] s (by unfold ChainNext; rwa [if_pos (by omega)])
  rwa [List.range_eq_range']

theorem sum_eq_getD (l : List Nat) : l.sum = ((List.range l.length).map (l.getD · 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.sum_cons,
      List.map_map, ih]
    rfl

/-- The layer-independent per-chain overhead: `A`'s table jump and the dispatch after `C`. -/
def xtra (i : Nat) : Nat := (if i % 3 = 0 then 1 else 0) + xCost i

theorem chain_xtra (c : CCtx) (i : Nat) : chainCost i (dig c i) + 9 * dig c i ≤ 68 + xtra i := by
  have := dig_lt c i
  unfold chainCost xtra
  split_ifs <;> omega

theorem chainsCost_aux (c : CCtx) : ∀ k i,
    ((List.range' i k).map fun j => chainCost j (dig c j)).sum + 9 * ((List.range' i k).map (dig c)).sum ≤
      68 * k + ((List.range' i k).map xtra).sum := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ k ih =>
    intro i
    have := ih (i + 1)
    have := chain_xtra c i
    simp only [List.range'_succ, List.map_cons, List.sum_cons] at *
    omega

/-- The chain-phase cycles of a layer (at most; each digit-7 chain saves one more cycle). -/
def chainsBound (lay : Nat) : Nat := 42 * 68 - 9 * targetFor lay + 65

theorem chainsCost_le (c : CCtx) (xs : List Nat) (hlen : xs.length = 42)
    (hxs : ∀ i < 42, xs.getD i 0 = dig c i) (hsum : xs.sum = targetFor c.lay) :
    chainsCost c 0 42 ≤ chainsBound c.lay := by
  have hs : ((List.range' 0 42).map (dig c)).sum = targetFor c.lay := by
    rw [← hsum, sum_eq_getD xs, hlen, List.range_eq_range']
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [hxs i (by simp at hi; omega)]
  have := chainsCost_aux c 42 0
  rw [hs, show ((List.range' 0 42).map xtra).sum = 65 by decide] at this
  unfold chainsCost chainsBound
  have hT := targetFor_le c.lay
  omega

end SigGolfCandidate.Verify
