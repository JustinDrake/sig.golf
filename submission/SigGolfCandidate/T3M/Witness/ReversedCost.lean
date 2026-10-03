import SigGolfCandidate.T3M.Witness.SideCost
namespace SigGolfCandidate.T3M.ReversedCost
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def credit (a : Nat) : Nat := min (a-1) 2
def segCost (a : Nat) : Nat := 15+14*a-credit a+(if 2≤a then 1 else 0)-(if a≤2 then 1 else 0)
def bankCost (xs : List Nat) : Nat := (xs.map segCost).sum

def foldCap : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 224, 238, 252, 266, 280, 294, 308, 322, 336, 350]
def dpRows : Array (Array Nat) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 224, 238, 252, 266, 280, 294, 308, 322, 336, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 224, 238, 252, 266, 280, 294, 308, 322, 336, 420, 434, 448, 462, 476, 490, 504, 518, 532, 546, 560, 574, 588, 602, 616, 630, 644, 658, 672, 686, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 224, 238, 252, 266, 280, 294, 308, 322, 336, 420, 434, 448, 462, 476, 490, 504, 518, 532, 546, 630, 644, 658, 672, 686, 700, 714, 728, 742, 756, 770, 784, 798, 812, 826, 840, 854, 868, 882, 896, 910, 924, 938, 952, 966, 980, 994, 1008, 1022, 1036, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050, 1050],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 224, 238, 252, 266, 280, 294, 308, 322, 336, 420, 434, 448, 462, 476, 490, 504, 518, 532, 546, 630, 644, 658, 672, 686, 700, 714, 728, 742, 756, 840, 854, 868, 882, 896, 910, 924, 938, 952, 966, 980, 994, 1008, 1022, 1036, 1050, 1064, 1078, 1092, 1106, 1120, 1134, 1148, 1162, 1176, 1190, 1204, 1218, 1232, 1246, 1260, 1274, 1288, 1302, 1316, 1330, 1344, 1358, 1372, 1386, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400, 1400],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 224, 238, 252, 266, 280, 294, 308, 322, 336, 420, 434, 448, 462, 476, 490, 504, 518, 532, 546, 630, 644, 658, 672, 686, 700, 714, 728, 742, 756, 840, 854, 868, 882, 896, 910, 924, 938, 952, 966, 1050, 1064, 1078, 1092, 1106, 1120, 1134, 1148, 1162, 1176, 1190, 1204, 1218, 1232, 1246, 1260, 1274, 1288, 1302, 1316, 1330, 1344, 1358, 1372, 1386, 1400, 1414, 1428, 1442, 1456, 1470, 1484, 1498, 1512, 1526, 1540, 1554, 1568, 1582, 1596, 1610, 1624, 1638, 1652, 1666, 1680, 1694, 1708, 1722, 1736, 1750, 1750, 1750, 1750, 1750, 1750, 1750, 1750, 1750, 1750, 1750, 1750, 1750, 1750, 1750, 1750],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 224, 238, 252, 266, 280, 294, 308, 322, 336, 420, 434, 448, 462, 476, 490, 504, 518, 532, 546, 630, 644, 658, 672, 686, 700, 714, 728, 742, 756, 840, 854, 868, 882, 896, 910, 924, 938, 952, 966, 1050, 1064, 1078, 1092, 1106, 1120, 1134, 1148, 1162, 1176, 1260, 1274, 1288, 1302, 1316, 1330, 1344, 1358, 1372, 1386, 1400, 1414, 1428, 1442, 1456, 1470, 1484, 1498, 1512, 1526, 1540, 1554, 1568, 1582, 1596, 1610, 1624, 1638, 1652, 1666, 1680, 1694, 1708, 1722, 1736, 1750, 1764, 1778, 1792, 1806, 1820, 1834, 1848, 1862, 1876, 1890, 1904, 1918, 1932, 1946, 1960, 1974, 1988, 2002, 2016, 2030],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 224, 238, 252, 266, 280, 294, 308, 322, 336, 420, 434, 448, 462, 476, 490, 504, 518, 532, 546, 630, 644, 658, 672, 686, 700, 714, 728, 742, 756, 840, 854, 868, 882, 896, 910, 924, 938, 952, 966, 1050, 1064, 1078, 1092, 1106, 1120, 1134, 1148, 1162, 1176, 1260, 1274, 1288, 1302, 1316, 1330, 1344, 1358, 1372, 1386, 1470, 1484, 1498, 1512, 1526, 1540, 1554, 1568, 1582, 1596, 1610, 1624, 1638, 1652, 1666, 1680, 1694, 1708, 1722, 1736, 1750, 1764, 1778, 1792, 1806, 1820, 1834, 1848, 1862, 1876, 1890, 1904, 1918, 1932, 1946, 1960, 1974, 1988, 2002, 2016, 2030, 2044, 2058, 2072, 2086, 2100]]
def cap (f : Nat) : Nat := foldCap[f]!
def bound (n b : Nat) : Nat := (dpRows[n]!)[b]!
theorem bank_cap : ∀ (x y : Fin 8), 0<x.val → 0<y.val → x≠y →
    let xs := SigGolfCandidate.T3M.SideCost.bankShape x.val y.val
    10 ≤ xs.sum ∧ xs.sum ≤ 20 ∧ bankCost xs ≤ cap xs.sum := by decide +kernel
theorem step0 : ∀ (b : Fin 116) (f : Fin 21), 10≤f.val → f.val≤b.val →
    cap f.val + bound 0 (b.val-f.val) ≤ bound 1 b.val := by decide +kernel
theorem step1 : ∀ (b : Fin 116) (f : Fin 21), 10≤f.val → f.val≤b.val →
    cap f.val + bound 1 (b.val-f.val) ≤ bound 2 b.val := by decide +kernel
theorem step2 : ∀ (b : Fin 116) (f : Fin 21), 10≤f.val → f.val≤b.val →
    cap f.val + bound 2 (b.val-f.val) ≤ bound 3 b.val := by decide +kernel
theorem step3 : ∀ (b : Fin 116) (f : Fin 21), 10≤f.val → f.val≤b.val →
    cap f.val + bound 3 (b.val-f.val) ≤ bound 4 b.val := by decide +kernel
theorem step4 : ∀ (b : Fin 116) (f : Fin 21), 10≤f.val → f.val≤b.val →
    cap f.val + bound 4 (b.val-f.val) ≤ bound 5 b.val := by decide +kernel
theorem step5 : ∀ (b : Fin 116) (f : Fin 21), 10≤f.val → f.val≤b.val →
    cap f.val + bound 5 (b.val-f.val) ≤ bound 6 b.val := by decide +kernel
theorem step6 : ∀ (b : Fin 116) (f : Fin 21), 10≤f.val → f.val≤b.val →
    cap f.val + bound 6 (b.val-f.val) ≤ bound 7 b.val := by decide +kernel
theorem step (n b f : Nat) (hn : n<7) (hb : b<116) (hf : 10≤f) (hf' : f<21) (hfb : f≤b) :
    cap f + bound n (b-f) ≤ bound (n+1) b := by
  interval_cases n
  · exact step0 ⟨b,hb⟩ ⟨f,hf'⟩ hf hfb
  · exact step1 ⟨b,hb⟩ ⟨f,hf'⟩ hf hfb
  · exact step2 ⟨b,hb⟩ ⟨f,hf'⟩ hf hfb
  · exact step3 ⟨b,hb⟩ ⟨f,hf'⟩ hf hfb
  · exact step4 ⟨b,hb⟩ ⟨f,hf'⟩ hf hfb
  · exact step5 ⟨b,hb⟩ ⟨f,hf'⟩ hf hfb
  · exact step6 ⟨b,hb⟩ ⟨f,hf'⟩ hf hfb
theorem bound_all (banks : List (List Nat)) (budget : Nat)
    (hn : banks.length≤7) (hb : budget<116) (hs : (banks.map List.sum).sum≤budget)
    (hc : ∀ xs∈banks, 10≤xs.sum ∧ xs.sum<21 ∧ bankCost xs≤cap xs.sum) :
    (banks.map bankCost).sum ≤ bound banks.length budget := by
  induction banks generalizing budget with
  | nil => simp only [List.map_nil,List.sum_nil];omega
  | cons xs rest ih =>
    have hh := hc xs (by simp)
    have hr : ∀ ys∈rest, 10≤ys.sum ∧ ys.sum<21 ∧ bankCost ys≤cap ys.sum :=
      fun ys hy => hc ys (by simp [hy])
    simp only [List.map_cons,List.sum_cons,List.length_cons] at hn hs ⊢
    have hi:=ih (budget-xs.sum) (by omega) (by omega) (by omega) hr
    have hd:=step rest.length budget xs.sum (by omega) hb hh.1 hh.2.1 (by omega)
    omega

theorem projected_seven_exact (banks : List (List Nat)) (hn : banks.length=7)
    (hf : (banks.map List.sum).sum≤115)
    (hc : ∀ xs∈banks, 10≤xs.sum ∧ xs.sum<21 ∧ bankCost xs≤cap xs.sum) :
    360+(banks.map bankCost).sum≤2460 := by
  have hh:=bound_all banks 115 (by omega) (by decide) hf hc
  rw [hn] at hh
  have hb : bound 7 115=2100 := by decide +kernel
  rw [hb] at hh
  omega

open SigGolfCandidate.T3 (Selection)
theorem coord_cap (c : Nat) (sel : Selection) (hs : SelOk sel) :
    let xs := (coordSchedule c sel).map Segment.a
    10≤xs.sum ∧ xs.sum≤20 ∧ bankCost xs≤cap xs.sum := by
  have g01 : selLeaf sel 0 < selLeaf sel 1 := by unfold selLeaf; have := hs.s01; omega
  have g12 : selLeaf sel 1 < selLeaf sel 2 := by unfold selLeaf; have := hs.s12; omega
  have bk0 : selLeaf sel 0 / 2 ^ 7 = sel.bucket := bucket_div_eight (by have := hs.s01; have := hs.s12; have := hs.l2; omega)
  have bk1 : selLeaf sel 1 / 2 ^ 7 = sel.bucket := bucket_div_eight (by have := hs.s12; have := hs.l2; omega)
  have bk2 : selLeaf sel 2 / 2 ^ 7 = sel.bucket := bucket_div_eight hs.l2
  have l01 : lcaLevel (selLeaf sel 0) (selLeaf sel 1) ≤ 7 :=
    (div_eq_iff_lca (by omega) 7).mp (by rw [bk0,bk1])
  have l12 : lcaLevel (selLeaf sel 1) (selLeaf sel 2) ≤ 7 :=
    (div_eq_iff_lca (by omega) 7).mp (by rw [bk1,bk2])
  have hne := lca_ne g01 g12
  rw [SideCost.coord_lengths]
  let x : Fin 8 := ⟨lcaLevel (selLeaf sel 0) (selLeaf sel 1),by omega⟩
  let y : Fin 8 := ⟨lcaLevel (selLeaf sel 1) (selLeaf sel 2),by omega⟩
  exact bank_cap x y (lcaLevel_pos _ _) (lcaLevel_pos _ _)
    (by intro hh; have := congrArg Fin.val hh; exact hne this)

theorem source_seven (chosen : List Selection)
    (hc : ∀ c, c<7 → SelOk (chosen.getD c ⟨0,[]⟩))
    (hf : ((SideCost.sourceBanks chosen).map List.sum).sum≤115) :
    360+((SideCost.sourceBanks chosen).map bankCost).sum≤2460 := by
  apply projected_seven_exact
  · simp [SideCost.sourceBanks]
  · exact hf
  · intro xs hx
    obtain ⟨c,hc7,rfl⟩ := List.mem_map.mp hx
    have h:=coord_cap c _ (hc c (List.mem_range.mp hc7))
    exact ⟨h.1,by omega,h.2.2⟩

def foldRemaining (i n : Nat) : Nat := 14*n-min (2-i) (n-1)-1
theorem foldRemaining_one (i : Nat) : foldRemaining i 1 = 13 := by simp [foldRemaining]
theorem foldRemaining_succ (i n : Nat) (hn : 0<n) :
    foldRemaining i (n+1)=(if i<2 then 13 else 14)+foldRemaining (i+1) n := by
  unfold foldRemaining
  split_ifs <;> omega
theorem foldRemaining_le (i n : Nat) : foldRemaining i n≤14*n-1 := by unfold foldRemaining;omega
theorem foldRemaining_segment (a : Nat) (ha : 0<a) :
    (16+(if 2≤a then 1 else 0)-(if a≤2 then 1 else 0))+foldRemaining 0 a=segCost a := by
  unfold foldRemaining segCost credit
  split_ifs <;> omega
end SigGolfCandidate.T3M.ReversedCost
