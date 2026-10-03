import SigGolfCandidate.T3M.Witness.SideCost
namespace SigGolfCandidate.T3M.FourCost
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def credit (a : Nat) : Nat := min (a-1) 3
def segCost (a : Nat) : Nat := 15+15*a-2*credit a+(if 0<a then 1 else 0)
def bankCost (xs : List Nat) : Nat := (xs.map segCost).sum

def foldCap : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 235, 251, 265, 276, 289, 302, 315, 328, 341, 355]
def dpRows : Array (Array Nat) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 235, 251, 265, 276, 289, 302, 315, 328, 341, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 235, 251, 265, 276, 289, 302, 315, 328, 341, 442, 456, 472, 486, 502, 516, 530, 541, 554, 567, 580, 593, 606, 620, 631, 644, 657, 670, 683, 696, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710, 710],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 235, 251, 265, 276, 289, 302, 315, 328, 341, 442, 456, 472, 486, 502, 516, 530, 541, 554, 567, 663, 677, 693, 707, 723, 737, 753, 767, 781, 795, 806, 819, 832, 845, 858, 871, 885, 896, 909, 922, 935, 948, 961, 975, 986, 999, 1012, 1025, 1038, 1051, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065, 1065],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 235, 251, 265, 276, 289, 302, 315, 328, 341, 442, 456, 472, 486, 502, 516, 530, 541, 554, 567, 663, 677, 693, 707, 723, 737, 753, 767, 781, 795, 884, 898, 914, 928, 944, 958, 974, 988, 1004, 1018, 1032, 1046, 1060, 1071, 1084, 1097, 1110, 1123, 1136, 1150, 1161, 1174, 1187, 1200, 1213, 1226, 1240, 1251, 1264, 1277, 1290, 1303, 1316, 1330, 1341, 1354, 1367, 1380, 1393, 1406, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420, 1420],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 235, 251, 265, 276, 289, 302, 315, 328, 341, 442, 456, 472, 486, 502, 516, 530, 541, 554, 567, 663, 677, 693, 707, 723, 737, 753, 767, 781, 795, 884, 898, 914, 928, 944, 958, 974, 988, 1004, 1018, 1105, 1119, 1135, 1149, 1165, 1179, 1195, 1209, 1225, 1239, 1255, 1269, 1283, 1297, 1311, 1325, 1336, 1349, 1362, 1375, 1388, 1401, 1415, 1426, 1439, 1452, 1465, 1478, 1491, 1505, 1516, 1529, 1542, 1555, 1568, 1581, 1595, 1606, 1619, 1632, 1645, 1658, 1671, 1685, 1696, 1709, 1722, 1735, 1748, 1761, 1775, 1775, 1775, 1775, 1775, 1775, 1775, 1775, 1775, 1775, 1775, 1775, 1775, 1775, 1775, 1775],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 235, 251, 265, 276, 289, 302, 315, 328, 341, 442, 456, 472, 486, 502, 516, 530, 541, 554, 567, 663, 677, 693, 707, 723, 737, 753, 767, 781, 795, 884, 898, 914, 928, 944, 958, 974, 988, 1004, 1018, 1105, 1119, 1135, 1149, 1165, 1179, 1195, 1209, 1225, 1239, 1326, 1340, 1356, 1370, 1386, 1400, 1416, 1430, 1446, 1460, 1476, 1490, 1506, 1520, 1534, 1548, 1562, 1576, 1590, 1601, 1614, 1627, 1640, 1653, 1666, 1680, 1691, 1704, 1717, 1730, 1743, 1756, 1770, 1781, 1794, 1807, 1820, 1833, 1846, 1860, 1871, 1884, 1897, 1910, 1923, 1936, 1950, 1961, 1974, 1987, 2000, 2013, 2026, 2040, 2051, 2064],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 235, 251, 265, 276, 289, 302, 315, 328, 341, 442, 456, 472, 486, 502, 516, 530, 541, 554, 567, 663, 677, 693, 707, 723, 737, 753, 767, 781, 795, 884, 898, 914, 928, 944, 958, 974, 988, 1004, 1018, 1105, 1119, 1135, 1149, 1165, 1179, 1195, 1209, 1225, 1239, 1326, 1340, 1356, 1370, 1386, 1400, 1416, 1430, 1446, 1460, 1547, 1561, 1577, 1591, 1607, 1621, 1637, 1651, 1667, 1681, 1697, 1711, 1727, 1741, 1757, 1771, 1785, 1799, 1813, 1827, 1841, 1855, 1866, 1879, 1892, 1905, 1918, 1931, 1945, 1956, 1969, 1982, 1995, 2008, 2021, 2035, 2046, 2059, 2072, 2085, 2098, 2111, 2125, 2136, 2149, 2162]]
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
    354+(banks.map bankCost).sum≤2516 := by
  have hh:=bound_all banks 115 (by omega) (by decide) hf hc
  rw [hn] at hh
  have hb : bound 7 115=2162 := by decide +kernel
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
    354+((SideCost.sourceBanks chosen).map bankCost).sum≤2516 := by
  apply projected_seven_exact
  · simp [SideCost.sourceBanks]
  · exact hf
  · intro xs hx
    obtain ⟨c,hc7,rfl⟩ := List.mem_map.mp hx
    have h:=coord_cap c _ (hc c (List.mem_range.mp hc7))
    exact ⟨h.1,by omega,h.2.2⟩

def foldRemaining (i n : Nat) : Nat := 15*n-2-2*min (3-i) (n-1)
theorem foldRemaining_one (i : Nat) : foldRemaining i 1 = 13 := by simp [foldRemaining]
theorem foldRemaining_succ (i n : Nat) (hn : 0<n) :
    foldRemaining i (n+1)=(if i<3 then 13 else 15)+foldRemaining (i+1) n := by
  unfold foldRemaining
  split_ifs <;> omega
theorem foldRemaining_le (i n : Nat) : foldRemaining i n≤15*n-2 := by unfold foldRemaining;omega
theorem foldRemaining_segment (a : Nat) (ha : 0<a) : 18+foldRemaining 0 a=segCost a := by
  unfold foldRemaining segCost credit
  rw [if_pos ha]
  omega
end SigGolfCandidate.T3M.FourCost
