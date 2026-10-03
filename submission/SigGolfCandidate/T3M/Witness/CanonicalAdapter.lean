import SigGolfCandidate.T3M.Witness.CanonicalBytes
import SigGolfCandidate.T3M.Witness.CanonicalCost

/-! A pure witness adapter for the digest-derived verifier. Only the unused
segment-control bytes change; payloads and hash pads stay byte-identical.
This is a component of the reduction, not a completed security certificate. -/
namespace SigGolfCandidate.T3M.CanonicalAdapter
open SigGolfCandidate.T3
open CanonicalBytes

theorem segPtr_slope (segs : List Segment) : ∀ m, m ≤ segs.length →
    ∀ n, n ≤ m → segPtr segs n+8*(m-n) ≤ segPtr segs m := by
  intro m
  induction m with
  | zero =>
      intro hm n hn
      have he : n=0 := by omega
      subst n
      omega
  | succ m ih =>
      intro hm n hn
      by_cases he : n=m+1
      · subst n; omega
      · have hs := ih (by omega) n (by omega)
        rw [segPtr_succ segs (by omega)]
        unfold segNext
        omega

theorem segPtr_inj (segs : List Segment) (n m : Nat) (hn : n ≤ segs.length)
    (hm : m ≤ segs.length) (h : segPtr segs n=segPtr segs m) : n=m := by
  by_cases hnm : n ≤ m
  · have hs := segPtr_slope segs m hm n hnm
    omega
  · have hs := segPtr_slope segs n hn m (by omega)
    omega

def replacement (segs : List Segment) (i : Nat) : Option UInt8 :=
  ((List.range segs.length).find? fun n => segPtr segs n==i).map fun n =>
    UInt8.ofNat (segs.getD n default).byte0

def normalize (chosen : List Selection) (w : WBytes) : WBytes :=
  patch w (replacement (schedule chosen))

theorem find_unique {α : Type} (l : List α) (p : α → Bool) (value : α)
    (hm : value∈l) (hp : p value=true)
    (hu : ∀ x∈l, p x=true → x=value) : l.find? p=some value := by
  induction l with
  | nil => simp at hm
  | cons x xs ih =>
      by_cases hx : p x=true
      · have he := hu x (by simp) hx
        subst x
        simp [List.find?,hp]
      · have htail : value∈xs := by
          rcases List.mem_cons.mp hm with he | he
          · subst x; contradiction
          · exact he
        have ht := ih htail (fun y hy => hu y (by simp [hy]))
        simp [List.find?,hx,ht]

theorem replacement_header (segs : List Segment) (n : Nat) (hn : n < segs.length) :
    replacement segs (segPtr segs n)=some (UInt8.ofNat (segs.getD n default).byte0) := by
  unfold replacement
  have hf : (List.range segs.length).find? (fun m => segPtr segs m==segPtr segs n)=some n := by
    apply find_unique _ _ n (by simp [hn]) (by simp)
    intro m hm he
    apply segPtr_inj segs m n (by have := List.mem_range.mp hm; omega) (by omega)
    exact beq_iff_eq.mp he
  rw [hf]
  rfl

theorem replacement_none (segs : List Segment) (i : Nat)
    (h : ∀ m, m < segs.length → segPtr segs m ≠ i) : replacement segs i=none := by
  unfold replacement
  have hf : (List.range segs.length).find? (fun m => segPtr segs m==i)=none := by
    rw [List.find?_eq_none]
    intro m hm
    simpa using h m (List.mem_range.mp hm)
  rw [hf]
  rfl

/-- Every hash payload lies strictly between consecutive segment headers. -/
theorem replacement_inside_segment (segs : List Segment) (n r off k : Nat)
    (hn : n < segs.length) (hr : r < (segs.getD n default).a) (hk : off+k ≤ 80)
    (j : Nat) (hj : j < k) :
    replacement segs (segPtr segs n+8+80*r+off+j)=none := by
  apply replacement_none
  intro m hm he
  by_cases hmn : m ≤ n
  · have hs := segPtr_slope segs n (by omega) m hmn
    omega
  · have hs := segPtr_slope segs m (by omega) (n+1) (by omega)
    have ht := segPtr_succ segs hn
    unfold segNext at ht
    omega

theorem replacement_before_stream (segs : List Segment) (i : Nat) (hi : i < 1088) :
    replacement segs i=none := by
  apply replacement_none
  intro m hm
  have h : 1088 ≤ segPtr segs m := by unfold segPtr streamBase; omega
  omega

theorem rho_normalize (chosen : List Selection) (w : WBytes) :
    wrho (normalize chosen w)=wrho w := by
  apply digest_patch_frame w (replacement (schedule chosen)) 0 (by decide)
  intro j hj
  apply replacement_before_stream
  omega

theorem dc_normalize (chosen : List Selection) (w : WBytes) :
    wdc (normalize chosen w)=wdc w := by
  apply le32_patch_frame w (replacement (schedule chosen)) 16 (by decide)
  intro j hj
  apply replacement_before_stream
  omega

theorem digestP_normalize (message : Message) (chosen : List Selection) (w : WBytes) :
    digestP message (normalize chosen w)=digestP message w := by
  simp only [digestP,dc_normalize,rho_normalize]

theorem header_bound (chosen : List Selection) (hc : ChosenOk chosen)
    (hf : slotBase chosen 7 ≤ 115) (n : Nat) (hn : n < (schedule chosen).length) :
    segPtr (schedule chosen) n < 25240 := by
  have hm := segPtr_slope (schedule chosen) 35 (by rw [schedule_length]) n
    (by rw [schedule_length] at hn; omega)
  have he := segPtr_end chosen hc
  unfold streamBase at he
  omega

/-- The rewritten stream has the exact source schedule on every live control
bit, including the up-to-three direction bits. -/
theorem normalize_streamMatches (chosen : List Selection) (w : WBytes)
    (hc : ChosenOk chosen) (hf : slotBase chosen 7 ≤ 115) :
    StreamMatches chosen (normalize chosen w) := by
  intro n hn
  have hn35 : n < 35 := by simpa [schedule_length] using hn
  have ha := schedule_a_le chosen hc hn35
  have hb := byte0_lt ((schedule chosen).getD n default) (by omega)
  unfold normalize
  rw [byte_patch _ _ _ (header_bound chosen hc hf n hn),
    replacement_header _ n hn]
  simp only [Option.getD_some,UInt8.toNat_ofNat',Nat.mod_eq_of_lt hb]
  exact Segment.matches_byte0 _ ha

/-- All used fold values and pads remain identical. The full 80-byte ownership
interval is bounded here so this lemma covers either sibling side and the pad. -/
theorem fold_digest_normalize (chosen : List Selection) (w : WBytes)
    (hc : ChosenOk chosen) (hf : slotBase chosen 7 ≤ 115)
    (n r off : Nat) (hn : n < (schedule chosen).length)
    (hr : r < ((schedule chosen).getD n default).a) (hoff : off+16 ≤ 80) :
    wdig (normalize chosen w) (segPtr (schedule chosen) n+8+80*r+off) =
      wdig w (segPtr (schedule chosen) n+8+80*r+off) := by
  apply digest_patch_frame
  · have ht := segPtr_succ (schedule chosen) hn
    have hm := segPtr_slope (schedule chosen) 35 (by rw [schedule_length]) (n+1)
      (by rw [schedule_length] at hn; omega)
    have he := segPtr_end chosen hc
    unfold segNext at ht
    unfold streamBase at he
    omega
  · intro j hj
    exact replacement_inside_segment _ n r off 16 hn hr hoff j hj

theorem replacement_after_stream (chosen : List Selection) (hc : ChosenOk chosen)
    (hf : slotBase chosen 7 ≤ 115) (i : Nat) (hi : 11288 ≤ i) :
    replacement (schedule chosen) i=none := by
  apply replacement_none
  intro m hm
  have hs := segPtr_slope (schedule chosen) 35 (by rw [schedule_length]) m
    (by rw [schedule_length] at hm; omega)
  have he := segPtr_end chosen hc
  unfold streamBase at he
  omega

theorem layer_digest_normalize (chosen : List Selection) (w : WBytes)
    (hc : ChosenOk chosen) (hf : slotBase chosen 7 ≤ 115)
    (off : Nat) (hlo : 11288 ≤ off) (hhi : off+16 ≤ 25240) :
    wdig (normalize chosen w) off=wdig w off := by
  apply digest_patch_frame _ _ off hhi
  intro j hj
  exact replacement_after_stream chosen hc hf (off+j) (by omega)

theorem normalize_eq_of_exact_headers (chosen : List Selection) (w : WBytes)
    (h : ∀ n, n < (schedule chosen).length →
      wbyte w (segPtr (schedule chosen) n)=
        UInt8.ofNat ((schedule chosen).getD n default).byte0) : normalize chosen w=w := by
  have he := extract_eq_of_bytes (normalize chosen w) w 0 25240 (by
    intro i hi
    simp only [Nat.zero_add]
    unfold normalize
    rw [byte_patch _ _ i hi]
    unfold replacement
    cases hf : (List.range (schedule chosen).length).find?
        (fun n => segPtr (schedule chosen) n==i) with
    | none => rfl
    | some n =>
      have hn := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      have hpred : (segPtr (schedule chosen) n==i)=true :=
        List.find?_some (p := fun k => segPtr (schedule chosen) k==i) hf
      have hp : segPtr (schedule chosen) n=i := beq_iff_eq.mp hpred
      simp only [Option.map_some,Option.getD_some]
      rw [← hp]
      exact (h n hn).symm)
  simpa only [Nat.mul_zero,BitVec.extractLsb'_eq_self] using he

/-- Expanded witnesses are fixed points of normalization. This preserves the
existing signature encoder rather than introducing a second signature format. -/
theorem normalize_witEnc (N : HashOutput) (w : Witness)
    (hc : ChosenOk (selections N)) (hf : slotBase (selections N) 7 ≤ 115) :
    normalize (selections N) (witEnc N w)=witEnc N w := by
  apply normalize_eq_of_exact_headers
  intro n hn
  apply UInt8.toNat.inj
  have hn35 : n < 35 := by simpa [schedule_length] using hn
  rw [wbyte_seg_witEnc N w hc hf hn35, UInt8.toNat_ofNat']
  have ha := schedule_a_le (selections N) hc hn35
  have hb := byte0_lt ((schedule (selections N)).getD n default) (by omega)
  exact (Nat.mod_eq_of_lt hb).symm

end SigGolfCandidate.T3M.CanonicalAdapter
