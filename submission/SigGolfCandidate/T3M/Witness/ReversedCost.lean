import SigGolfCandidate.T3M.Witness.SideCost
namespace SigGolfCandidate.T3M.ReversedCost
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def credit (a : Nat) : Nat := min (a-1) 2
def segCost (a : Nat) : Nat := 15+14*a-credit a+(if 2≤a then 1 else 0)
def bankCost (xs : List Nat) : Nat := (xs.map segCost).sum

def foldCap : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 214, 228, 242, 255, 269, 283, 297, 310, 323, 337, 351]
def dpRows : Array (Array Nat) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 214, 228, 242, 255, 269, 283, 297, 310, 323, 337, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 214, 228, 242, 255, 269, 283, 297, 310, 323, 337, 428, 442, 456, 470, 484, 497, 511, 525, 539, 552, 566, 580, 594, 607, 620, 634, 648, 661, 674, 688, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702, 702],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 214, 228, 242, 255, 269, 283, 297, 310, 323, 337, 428, 442, 456, 470, 484, 497, 511, 525, 539, 552, 642, 656, 670, 684, 698, 712, 726, 739, 753, 767, 781, 794, 808, 822, 836, 849, 863, 877, 891, 904, 917, 931, 945, 958, 971, 985, 999, 1012, 1025, 1039, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053, 1053],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 214, 228, 242, 255, 269, 283, 297, 310, 323, 337, 428, 442, 456, 470, 484, 497, 511, 525, 539, 552, 642, 656, 670, 684, 698, 712, 726, 739, 753, 767, 856, 870, 884, 898, 912, 926, 940, 954, 968, 981, 995, 1009, 1023, 1036, 1050, 1064, 1078, 1091, 1105, 1119, 1133, 1146, 1160, 1174, 1188, 1201, 1214, 1228, 1242, 1255, 1268, 1282, 1296, 1309, 1322, 1336, 1350, 1363, 1376, 1390, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404, 1404],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 214, 228, 242, 255, 269, 283, 297, 310, 323, 337, 428, 442, 456, 470, 484, 497, 511, 525, 539, 552, 642, 656, 670, 684, 698, 712, 726, 739, 753, 767, 856, 870, 884, 898, 912, 926, 940, 954, 968, 981, 1070, 1084, 1098, 1112, 1126, 1140, 1154, 1168, 1182, 1196, 1210, 1223, 1237, 1251, 1265, 1278, 1292, 1306, 1320, 1333, 1347, 1361, 1375, 1388, 1402, 1416, 1430, 1443, 1457, 1471, 1485, 1498, 1511, 1525, 1539, 1552, 1565, 1579, 1593, 1606, 1619, 1633, 1647, 1660, 1673, 1687, 1701, 1714, 1727, 1741, 1755, 1755, 1755, 1755, 1755, 1755, 1755, 1755, 1755, 1755, 1755, 1755, 1755, 1755, 1755, 1755],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 214, 228, 242, 255, 269, 283, 297, 310, 323, 337, 428, 442, 456, 470, 484, 497, 511, 525, 539, 552, 642, 656, 670, 684, 698, 712, 726, 739, 753, 767, 856, 870, 884, 898, 912, 926, 940, 954, 968, 981, 1070, 1084, 1098, 1112, 1126, 1140, 1154, 1168, 1182, 1196, 1284, 1298, 1312, 1326, 1340, 1354, 1368, 1382, 1396, 1410, 1424, 1438, 1452, 1465, 1479, 1493, 1507, 1520, 1534, 1548, 1562, 1575, 1589, 1603, 1617, 1630, 1644, 1658, 1672, 1685, 1699, 1713, 1727, 1740, 1754, 1768, 1782, 1795, 1808, 1822, 1836, 1849, 1862, 1876, 1890, 1903, 1916, 1930, 1944, 1957, 1970, 1984, 1998, 2011, 2024, 2038],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 214, 228, 242, 255, 269, 283, 297, 310, 323, 337, 428, 442, 456, 470, 484, 497, 511, 525, 539, 552, 642, 656, 670, 684, 698, 712, 726, 739, 753, 767, 856, 870, 884, 898, 912, 926, 940, 954, 968, 981, 1070, 1084, 1098, 1112, 1126, 1140, 1154, 1168, 1182, 1196, 1284, 1298, 1312, 1326, 1340, 1354, 1368, 1382, 1396, 1410, 1498, 1512, 1526, 1540, 1554, 1568, 1582, 1596, 1610, 1624, 1638, 1652, 1666, 1680, 1694, 1707, 1721, 1735, 1749, 1762, 1776, 1790, 1804, 1817, 1831, 1845, 1859, 1872, 1886, 1900, 1914, 1927, 1941, 1955, 1969, 1982, 1996, 2010, 2024, 2037, 2051, 2065, 2079, 2092, 2105, 2119]]
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
    361+(banks.map bankCost).sum≤2480 := by
  have hh:=bound_all banks 115 (by omega) (by decide) hf hc
  rw [hn] at hh
  have hb : bound 7 115=2119 := by decide +kernel
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
    361+((SideCost.sourceBanks chosen).map bankCost).sum≤2480 := by
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
    (16+(if 2≤a then 1 else 0))+foldRemaining 0 a=segCost a := by
  unfold foldRemaining segCost credit
  omega
end SigGolfCandidate.T3M.ReversedCost
