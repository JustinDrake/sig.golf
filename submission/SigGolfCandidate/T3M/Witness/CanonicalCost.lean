import SigGolfCandidate.T3M.Witness.SideCost
namespace SigGolfCandidate.T3M.CanonicalCost
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Upper cost of a segment of the digest-derived schedule: the pending hash,
fixed stores, pointer advance, and the nonempty orientation ladder. The extra
cycle bounds the left ladder's jump. -/
def segCost (a : Nat) : Nat := 10+14*a+(if 0<a then 1 else 0)
/-- Dispatch/return and caller advances cost 38 per bank. -/
def bankCost (xs : List Nat) : Nat := 38+(xs.map segCost).sum
def foldCap : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 245, 260, 275, 289, 303, 317, 331, 345, 359, 372]
def dpRows : Array (Array Nat) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 245, 260, 275, 289, 303, 317, 331, 345, 359, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 245, 260, 275, 289, 303, 317, 331, 345, 359, 460, 475, 490, 505, 520, 535, 550, 564, 578, 592, 606, 620, 634, 648, 662, 676, 690, 704, 718, 731, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744, 744],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 245, 260, 275, 289, 303, 317, 331, 345, 359, 460, 475, 490, 505, 520, 535, 550, 564, 578, 592, 690, 705, 720, 735, 750, 765, 780, 795, 810, 825, 839, 853, 867, 881, 895, 909, 923, 937, 951, 965, 979, 993, 1007, 1021, 1035, 1049, 1063, 1077, 1090, 1103, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116, 1116],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 245, 260, 275, 289, 303, 317, 331, 345, 359, 460, 475, 490, 505, 520, 535, 550, 564, 578, 592, 690, 705, 720, 735, 750, 765, 780, 795, 810, 825, 920, 935, 950, 965, 980, 995, 1010, 1025, 1040, 1055, 1070, 1085, 1100, 1114, 1128, 1142, 1156, 1170, 1184, 1198, 1212, 1226, 1240, 1254, 1268, 1282, 1296, 1310, 1324, 1338, 1352, 1366, 1380, 1394, 1408, 1422, 1436, 1449, 1462, 1475, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488, 1488],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 245, 260, 275, 289, 303, 317, 331, 345, 359, 460, 475, 490, 505, 520, 535, 550, 564, 578, 592, 690, 705, 720, 735, 750, 765, 780, 795, 810, 825, 920, 935, 950, 965, 980, 995, 1010, 1025, 1040, 1055, 1150, 1165, 1180, 1195, 1210, 1225, 1240, 1255, 1270, 1285, 1300, 1315, 1330, 1345, 1360, 1375, 1389, 1403, 1417, 1431, 1445, 1459, 1473, 1487, 1501, 1515, 1529, 1543, 1557, 1571, 1585, 1599, 1613, 1627, 1641, 1655, 1669, 1683, 1697, 1711, 1725, 1739, 1753, 1767, 1781, 1795, 1808, 1821, 1834, 1847, 1860, 1860, 1860, 1860, 1860, 1860, 1860, 1860, 1860, 1860, 1860, 1860, 1860, 1860, 1860, 1860],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 245, 260, 275, 289, 303, 317, 331, 345, 359, 460, 475, 490, 505, 520, 535, 550, 564, 578, 592, 690, 705, 720, 735, 750, 765, 780, 795, 810, 825, 920, 935, 950, 965, 980, 995, 1010, 1025, 1040, 1055, 1150, 1165, 1180, 1195, 1210, 1225, 1240, 1255, 1270, 1285, 1380, 1395, 1410, 1425, 1440, 1455, 1470, 1485, 1500, 1515, 1530, 1545, 1560, 1575, 1590, 1605, 1620, 1635, 1650, 1664, 1678, 1692, 1706, 1720, 1734, 1748, 1762, 1776, 1790, 1804, 1818, 1832, 1846, 1860, 1874, 1888, 1902, 1916, 1930, 1944, 1958, 1972, 1986, 2000, 2014, 2028, 2042, 2056, 2070, 2084, 2098, 2112, 2126, 2140, 2154, 2167],
#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 245, 260, 275, 289, 303, 317, 331, 345, 359, 460, 475, 490, 505, 520, 535, 550, 564, 578, 592, 690, 705, 720, 735, 750, 765, 780, 795, 810, 825, 920, 935, 950, 965, 980, 995, 1010, 1025, 1040, 1055, 1150, 1165, 1180, 1195, 1210, 1225, 1240, 1255, 1270, 1285, 1380, 1395, 1410, 1425, 1440, 1455, 1470, 1485, 1500, 1515, 1610, 1625, 1640, 1655, 1670, 1685, 1700, 1715, 1730, 1745, 1760, 1775, 1790, 1805, 1820, 1835, 1850, 1865, 1880, 1895, 1910, 1925, 1939, 1953, 1967, 1981, 1995, 2009, 2023, 2037, 2051, 2065, 2079, 2093, 2107, 2121, 2135, 2149, 2163, 2177, 2191, 2205, 2219, 2233, 2247, 2261]]
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
    (banks.map bankCost).sum≤2261 := by
  have hh:=bound_all banks 115 (by omega) (by decide) hf hc
  rw [hn] at hh
  have hb : bound 7 115=2261 := by decide +kernel
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
    ((SideCost.sourceBanks chosen).map bankCost).sum≤2261 := by
  apply projected_seven_exact
  · simp [SideCost.sourceBanks]
  · exact hf
  · intro xs hx
    obtain ⟨c,hc7,rfl⟩ := List.mem_map.mp hx
    have h:=coord_cap c _ (hc c (List.mem_range.mp hc7))
    exact ⟨h.1,by omega,h.2.2⟩


/-- Pure schedule arithmetic. This theorem does not by itself certify the native
image or its security. A native refinement must account for setup/forest and
prove that every executed bank has the corresponding cost. -/
theorem fts_schedule_bound (chosen : List Selection)
    (hc : ∀ c, c<7 → SelOk (chosen.getD c ⟨0,[]⟩))
    (hf : ((SideCost.sourceBanks chosen).map List.sum).sum≤115) :
    45+((SideCost.sourceBanks chosen).map bankCost).sum≤2306 := by
  have h := source_seven chosen hc hf
  omega
end SigGolfCandidate.T3M.CanonicalCost
