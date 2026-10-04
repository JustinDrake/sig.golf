import SigGolfCandidate.T3M.Witness.Shaped

namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem readLE_cons (b : UInt8) (L : List UInt8) : readLE (b :: L) = b.toNat + 256 * readLE L := rfl
theorem readLE_append (A B : List UInt8) : readLE (A ++ B) = readLE A + 256 ^ A.length * readLE B := by
  induction A with
  | nil => simp [readLE]
  | cons a A ih => rw [List.cons_append, readLE_cons, readLE_cons, ih, List.length_cons, pow_succ]; ring
theorem readLE_lt (L : List UInt8) : readLE L < 256 ^ L.length := by
  induction L with
  | nil => simp [readLE]
  | cons a L ih =>
      rw [readLE_cons, List.length_cons, pow_succ]
      have := a.toNat_lt
      omega
theorem readLE_drop : ∀ (L : List UInt8) (k : Nat), readLE L / 256 ^ k = readLE (L.drop k) := by
  intro L k
  induction k generalizing L with
  | zero => simp
  | succ k ih =>
      cases L with
      | nil => simp [readLE]
      | cons a L =>
          rw [List.drop_succ_cons, ← ih L, readLE_cons, pow_succ', ← Nat.div_div_eq_div_mul]
          congr 1
          have := a.toNat_lt
          omega
theorem readLE_take : ∀ (L : List UInt8) (k : Nat), readLE L % 256 ^ k = readLE (L.take k) := by
  intro L k
  induction k generalizing L with
  | zero => simp [readLE, Nat.mod_one]
  | succ k ih =>
      cases L with
      | nil => simp [readLE]
      | cons a L =>
          rw [List.take_succ_cons, readLE_cons, readLE_cons, ← ih L, pow_succ', Nat.mod_mul]
          have := a.toNat_lt
          have h1 : (a.toNat + 256 * readLE L) % 256 = a.toNat := by omega
          have h2 : (a.toNat + 256 * readLE L) / 256 = readLE L := by omega
          rw [h1, h2]
theorem extract_readLE (L : List UInt8) (n : Nat) (hL : L.length ≤ n) (off k : Nat) :
    (BitVec.ofNat (8 * n) (readLE L)).extractLsb' (8 * off) (8 * k) =
      BitVec.ofNat (8 * k) (readLE ((L.drop off).take k)) := by
  have hlt : readLE L < 2 ^ (8 * n) := by
    have := readLE_lt L
    calc readLE L < 256 ^ L.length := this
      _ ≤ 256 ^ n := Nat.pow_le_pow_right (by norm_num) hL
      _ = 2 ^ (8 * n) := by rw [pow_mul]; norm_num
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
    Nat.shiftRight_eq_div_pow, show 2 ^ (8 * off) = 256 ^ off by rw [pow_mul]; norm_num, readLE_drop,
    show 2 ^ (8 * k) = 256 ^ k by rw [pow_mul]; norm_num, readLE_take]
  rw [Nat.mod_eq_of_lt]
  have := readLE_lt ((L.drop off).take k)
  calc readLE ((L.drop off).take k) < 256 ^ ((L.drop off).take k).length := this
    _ ≤ 256 ^ k := Nat.pow_le_pow_right (by norm_num) (by simp)
theorem headerBytes_length (w : Witness) : (headerBytes w).length = 64 := by
  simp [headerBytes, zeros, bytesLE_length, List.length_flatMap, List.sum_replicate]
theorem leafBytes_length (sig : Signature) : (leafBytes sig).length = 1024 := by
  simp [leafBytes, zeros, bytesLE_length, List.length_flatMap, List.sum_replicate]
theorem streamBytes_length (chosen : List Selection) (proof : Fin 115 → Digest) :
    (streamBytes chosen proof).length = 10200 := by
  simp only [streamBytes, zeros, List.length_take, List.length_append, List.length_replicate]
  omega
theorem layerBytes_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    (layerBytes lay leaf ls).length = 64 * (height lay + chainCount lay) := by
  unfold layerBytes
  rw [List.length_append, List.length_flatMap, List.length_flatMap]
  have h1 : ∀ j : Fin (height lay), (if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (ls.path j)).length = 64 := by
    intro j; split <;> simp [zeros, bytesLE_length]
  simp only [h1]
  simp only [List.length_append, zeros, List.length_replicate, bytesLE_length, List.map_const',
    List.length_reverse, List.length_finRange, List.sum_replicate, smul_eq_mul]
  ring
theorem layerStorage_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    (layerStorage lay leaf ls).length = 64 * (height lay + chainCount lay) + (if lay = 0 then 256 else 0) := by
  simp only [layerStorage, List.length_append, layerBytes_length, zeros, List.length_replicate]
theorem witList_length_eq (N : HashOutput) (w : Witness) : (witList N w).length = 25240 := by
  unfold witList
  rw [List.length_append, List.length_append, List.length_append, headerBytes_length, leafBytes_length,
    streamBytes_length, List.length_flatMap]
  simp only [layerStorage_length]
  simp [List.finRange, height, chainCount]
theorem wdig_witEnc (N : HashOutput) (w : Witness) (off : Nat) :
    wdig (witEnc N w) off = readDigest (((witList N w).drop off).take 16) := by
  unfold wdig witEnc readDigest
  exact extract_readLE (witList N w) 25240 (by rw [witList_length_eq]) off 16
theorem wle32_witEnc (N : HashOutput) (w : Witness) (off : Nat) :
    wle32 (witEnc N w) off = BitVec.ofNat 32 (readLE (((witList N w).drop off).take 4)) := by
  unfold wle32 witEnc
  exact extract_readLE (witList N w) 25240 (by rw [witList_length_eq]) off 4
theorem take_one_drop (L : List UInt8) : ∀ i, readLE ((L.drop i).take 1) = (L.getD i 0).toNat := by
  induction L with
  | nil => intro i; simp [readLE]
  | cons a L ih =>
      intro i
      cases i with
      | zero => simp [readLE]
      | succ i => rw [List.drop_succ_cons, ih i]; simp
theorem wbyte_witEnc (N : HashOutput) (w : Witness) (i : Nat) :
    (wbyte (witEnc N w) i).toNat = ((witList N w).getD i 0).toNat := by
  have hlt : readLE (witList N w) < 2 ^ (8 * 25240) := by
    have := readLE_lt (witList N w)
    rw [witList_length_eq] at this
    calc readLE (witList N w) < 256 ^ 25240 := this
      _ = 2 ^ (8 * 25240) := by rw [pow_mul]; norm_num
  unfold wbyte witEnc
  rw [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
    Nat.shiftRight_eq_div_pow, show 2 ^ (8 * i) = 256 ^ i by rw [pow_mul]; norm_num, readLE_drop,
    show (2 : Nat) ^ 8 = 256 ^ 1 by norm_num, readLE_take, take_one_drop]
def window (L : List UInt8) (off n : Nat) : List UInt8 := (L.drop off).take n
theorem window_append_left (A B : List UInt8) (off n : Nat) (h : off + n ≤ A.length) :
    window (A ++ B) off n = window A off n := by
  unfold window
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
theorem window_append_right (A B : List UInt8) (off n : Nat) (h : A.length ≤ off) :
    window (A ++ B) off n = window B (off - A.length) n := by
  unfold window
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
theorem window_flatMap {β : Type} (l : List β) (f : β → List UInt8) :
    ∀ (i : Nat) (hi : i < l.length) (j n : Nat), j + n ≤ (f l[i]).length →
      window (l.flatMap f) (((l.take i).map fun b => (f b).length).sum + j) n = window (f l[i]) j n := by
  induction l with
  | nil => intro i hi; simp at hi
  | cons b l ih =>
      intro i hi j n hjn
      cases i with
      | zero =>
          simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatMap_cons,
            List.getElem_cons_zero] at hjn ⊢
          exact window_append_left _ _ _ _ hjn
      | succ i =>
          simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatMap_cons,
            List.getElem_cons_succ] at hjn ⊢
          rw [window_append_right _ _ _ _ (by omega), show (f b).length + ((l.take i).map fun b => (f b).length).sum + j
            - (f b).length = ((l.take i).map fun b => (f b).length).sum + j by omega]
          exact ih i (by simpa using hi) j n hjn
theorem window_flatMap_const {β : Type} (l : List β) (f : β → List UInt8) (k : Nat) (hk : ∀ b, (f b).length = k)
    (i : Nat) (hi : i < l.length) (j n : Nat) (hjn : j + n ≤ k) :
    window (l.flatMap f) (k * i + j) n = window (f l[i]) j n := by
  have := window_flatMap l f i hi j n (by rw [hk]; exact hjn)
  rwa [show ((l.take i).map fun b => (f b).length).sum = k * i by
    rw [List.map_congr_left (fun b _ => hk b), List.map_const', List.sum_replicate, List.length_take,
      Nat.min_eq_left hi.le, smul_eq_mul, Nat.mul_comm]] at this
theorem window_full (L : List UInt8) (n : Nat) (h : L.length = n) : window L 0 n = L := by
  unfold window; rw [List.drop_zero, List.take_of_length_le (by omega)]
theorem window_zeros (m off n : Nat) (h : off + n ≤ m) : window (zeros m) off n = zeros n := by
  unfold window zeros; rw [List.drop_replicate, List.take_replicate, Nat.min_eq_left (by omega)]
theorem readDigest_zeros : readDigest (zeros 16) = 0 := by
  rw [show zeros 16 = bytesLE 16 0 from bytesLE_zero16.symm, Correctness.readDigest_bytesLE]
theorem readLE_bytesLE_32 (v : BitVec 32) : BitVec.ofNat 32 (readLE (bytesLE 4 v)) = v := by
  rw [Correctness.readLE_bytesLE]; exact BitVec.ofNat_toNat 32 v
theorem window_take (L : List UInt8) (m off n : Nat) (h : off + n ≤ m) : window (L.take m) off n = window L off n := by
  unfold window; rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]
theorem getD_of_window (L : List UInt8) (i : Nat) (x : UInt8) (h : window L i 1 = [x]) : L.getD i 0 = x := by
  unfold window at h
  rcases hl : L.drop i with _ | ⟨y, rest⟩
  · rw [hl] at h; simp at h
  · rw [hl] at h
    simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at h
    have hi : i < L.length := by
      by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at hl; simp at hl
    rw [List.getD_eq_getElem _ _ hi]
    have e := congrArg (fun l => l[0]?) hl
    simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero, List.getElem?_eq_getElem hi] at e
    rw [Option.some.inj e, h]
section regions
variable (N : HashOutput) (w : Witness)
theorem win_header (off n : Nat) (h : off + n ≤ 64) :
    window (witList N w) off n = window (headerBytes w) off n := by
  unfold witList
  rw [window_append_left _ _ _ _ (by simp [headerBytes_length, leafBytes_length, streamBytes_length]; omega),
    window_append_left _ _ _ _ (by simp [headerBytes_length, leafBytes_length]; omega),
    window_append_left _ _ _ _ (by simp [headerBytes_length]; omega)]
theorem win_leaf (off n : Nat) (h1 : 64 ≤ off) (h : off + n ≤ 1088) :
    window (witList N w) off n = window (leafBytes w.signature) (off - 64) n := by
  unfold witList
  rw [window_append_left _ _ _ _ (by simp [headerBytes_length, leafBytes_length, streamBytes_length]; omega),
    window_append_left _ _ _ _ (by simp [headerBytes_length, leafBytes_length]; omega),
    window_append_right _ _ _ _ (by simp [headerBytes_length]; omega), headerBytes_length]
theorem win_stream (off n : Nat) (h1 : 1088 ≤ off) (h : off + n ≤ 11288) :
    window (witList N w) off n = window (streamBytes (selections N) w.signature.proof) (off - 1088) n := by
  unfold witList
  rw [window_append_left _ _ _ _ (by simp [headerBytes_length, leafBytes_length, streamBytes_length]; omega),
    window_append_right _ _ _ _ (by simp [headerBytes_length, leafBytes_length]; omega)]
  simp [headerBytes_length, leafBytes_length]
theorem win_layers (off n : Nat) (h1 : 11288 ≤ off) :
    window (witList N w) off n = window ((List.finRange 4).flatMap fun lay =>
      layerStorage lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)) (off - 11288) n := by
  unfold witList
  rw [window_append_right _ _ _ _ (by simp [headerBytes_length, leafBytes_length, streamBytes_length]; omega)]
  simp [headerBytes_length, leafBytes_length, streamBytes_length]
end regions
theorem wrho_witEnc (N : HashOutput) (w : Witness) : wrho (witEnc N w) = w.signature.rho := by
  unfold wrho rhoOff
  rw [wdig_witEnc, show ((witList N w).drop 0).take 16 = window (witList N w) 0 16 from rfl, win_header _ _ _ _ (by omega)]
  unfold headerBytes
  rw [window_append_left _ _ _ _ (by simp [bytesLE_length, List.length_flatMap, zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length]),
    window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _),
    Correctness.readDigest_bytesLE]
theorem wdc_witEnc (N : HashOutput) (w : Witness) : wdc (witEnc N w) = w.digestCounter := by
  unfold wdc dcOff
  rw [wle32_witEnc, show ((witList N w).drop 16).take 4 = window (witList N w) 16 4 from rfl,
    win_header _ _ _ _ (by omega)]
  unfold headerBytes
  rw [window_append_left _ _ _ _ (by simp [bytesLE_length, List.length_flatMap, zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length]),
    window_append_right _ _ _ _ (by simp [bytesLE_length]), bytesLE_length, Nat.sub_self,
    window_full _ _ (bytesLE_length _ _), readLE_bytesLE_32]
theorem wctr_witEnc (N : HashOutput) (w : Witness) (lay : Layer) : wctr (witEnc N w) lay = w.counters lay := by
  unfold wctr counterOff
  rw [wle32_witEnc, show ((witList N w).drop (20 + 4 * lay.val)).take 4 = window (witList N w) (20 + 4 * lay.val) 4
    from rfl, win_header _ _ _ _ (by omega)]
  unfold headerBytes
  rw [window_append_left _ _ _ _ (by simp [bytesLE_length, List.length_flatMap, zeros]; omega),
    window_append_right _ _ _ _ (by simp [bytesLE_length]),
    show 20 + 4 * lay.val - (bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter).length = 4 * lay.val + 0 by
      simp [bytesLE_length],
    window_flatMap_const _ _ 4 (fun _ => bytesLE_length _ _) lay.val (by simp) 0 4 le_rfl,
    window_full _ _ (bytesLE_length _ _)]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
  exact readLE_bytesLE_32 _
theorem wsecret_witEnc (N : HashOutput) (w : Witness) (s : Nat) (hs : s < 21) :
    wsecret (witEnc N w) s = w.signature.secrets ⟨s, hs⟩ := by
  unfold wsecret leafBlock
  rw [wdig_witEnc, show ((witList N w).drop (64 + 48 * s + 32)).take 16 = window (witList N w) (64 + 48 * s + 32) 16
    from rfl, win_leaf _ _ _ _ (by omega) (by omega)]
  unfold leafBytes
  rw [window_append_left _ _ _ _ (by simp [List.length_flatMap, zeros, bytesLE_length]; omega),
    show 64 + 48 * s + 32 - 64 = 48 * s + 32 by omega,
    window_flatMap_const _ _ 48 (fun _ => by simp [zeros, bytesLE_length]) s (by simpa using hs) 32 16 le_rfl,
    window_append_right _ _ _ _ (by simp [zeros]), show 32 - (zeros 32).length = 0 by simp [zeros],
    window_full _ _ (bytesLE_length _ _)]
  simp only [List.getElem_finRange, Fin.cast_mk]
  exact Correctness.readDigest_bytesLE _
theorem wleafPad_witEnc (N : HashOutput) (w : Witness) (s : Nat) (hs : s < 22) : wleafPad (witEnc N w) s = 0 := by
  unfold wleafPad leafBlock
  rw [wdig_witEnc, show ((witList N w).drop (64 + 48 * s)).take 16 = window (witList N w) (64 + 48 * s) 16
    from rfl, win_leaf _ _ _ _ (by omega) (by omega), show 64 + 48 * s - 64 = 48 * s by omega]
  unfold leafBytes
  by_cases h21 : s < 21
  · rw [window_append_left _ _ _ _ (by simp [List.length_flatMap, zeros, bytesLE_length]; omega),
      show 48 * s = 48 * s + 0 by omega,
      window_flatMap_const _ _ 48 (fun _ => by simp [zeros, bytesLE_length]) s (by simpa using h21) 0 16 (by omega),
      window_append_left _ _ _ _ (by simp [zeros]), window_zeros _ _ _ (by omega), readDigest_zeros]
  · obtain rfl : s = 21 := by omega
    rw [window_append_right _ _ _ _ (by simp [List.length_flatMap, zeros, bytesLE_length])]
    simp only [List.length_flatMap, zeros, bytesLE_length, List.length_append, List.length_replicate]
    simp only [List.map_const', List.length_finRange, List.sum_replicate, smul_eq_mul, Nat.reduceMul, Nat.sub_self]
    rw [window_full _ _ (by simp), show List.replicate 16 (0 : UInt8) = zeros 16 from rfl, readDigest_zeros]
theorem foldBytes_length (E : Nat) (sib : Digest) : (foldBytes E sib).length = 80 := by
  unfold foldBytes; split <;> simp [zeros, bytesLE_length]
theorem segBytes_length (chosen : List Selection) (proof : Fin 115 → Digest) (seg : Segment) :
    (segBytes chosen proof seg).length = 8 + 80 * seg.a := by
  unfold segBytes
  simp only [List.length_append, List.length_singleton, zeros, List.length_replicate, List.length_flatMap,
    foldBytes_length, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  omega
theorem stream_flat_length (chosen : List Selection) (proof : Fin 115 → Digest) :
    ((schedule chosen).flatMap (segBytes chosen proof)).length = ((schedule chosen).map fun s => 8 + 80 * s.a).sum := by
  rw [List.length_flatMap]; congr 1; exact List.map_congr_left (fun s _ => segBytes_length _ _ _)
theorem segPtr_le_end (chosen : List Selection) (_hc : ChosenOk chosen) {n : Nat} (_hn : n ≤ 35) :
    segPtr (schedule chosen) n ≤ segPtr (schedule chosen) 35 := by
  unfold segPtr
  have := List.sum_take_add_sum_drop ((schedule chosen).map fun s => 8 + 80 * s.a) n
  rw [← List.map_take] at this
  rw [show (schedule chosen).take 35 = schedule chosen from List.take_of_length_le (by rw [schedule_length])]
  omega
theorem win_seg (N : HashOutput) (w : Witness) (hc : ChosenOk (selections N)) (hle : slotBase (selections N) 7 ≤ 115)
    {n : Nat} (hn : n < 35) (j m : Nat) (hjm : j + m ≤ 8 + 80 * ((schedule (selections N)).getD n default).a) :
    window (witList N w) (segPtr (schedule (selections N)) n + j) m =
      window (segBytes (selections N) w.signature.proof ((schedule (selections N)).getD n default)) j m := by
  have hend := segPtr_end (selections N) hc
  have hsucc := segPtr_succ (schedule (selections N)) (m := n) (by rw [schedule_length]; exact hn)
  have hmono := segPtr_le_end (selections N) hc (show n + 1 ≤ 35 by omega)
  unfold segNext at hsucc
  have hb : 1088 ≤ segPtr (schedule (selections N)) n := by unfold segPtr streamBase; omega
  have hflat := stream_flat_length (selections N) w.signature.proof
  have hsum : segPtr (schedule (selections N)) 35 = 1088 + ((schedule (selections N)).map fun s => 8 + 80 * s.a).sum := by
    unfold segPtr streamBase; rw [List.take_of_length_le (by rw [schedule_length])]
  rw [win_stream _ _ _ _ (by omega) (by unfold streamBase at hend; omega)]
  unfold streamBytes
  rw [window_take _ _ _ _ (by unfold streamBase at hend; omega),
    window_append_left _ _ _ _ (by rw [hflat]; omega)]
  have hpre : segPtr (schedule (selections N)) n + j - 1088 =
      (((schedule (selections N)).take n).map fun s => (segBytes (selections N) w.signature.proof s).length).sum + j := by
    unfold segPtr streamBase
    rw [List.map_congr_left (fun s _ => segBytes_length _ _ s)]
    omega
  rw [hpre, window_flatMap _ _ n (by rw [schedule_length]; exact hn) j m
    (by rw [segBytes_length, ← List.getD_eq_getElem _ default (by rw [schedule_length]; exact hn)]; exact hjm)]
  rw [List.getD_eq_getElem _ default (by rw [schedule_length]; exact hn)]
theorem segBytes_header (chosen : List Selection) (proof : Fin 115 → Digest) (seg : Segment) :
    window (segBytes chosen proof seg) 0 1 = [UInt8.ofNat seg.byte0] := by
  unfold segBytes window; simp
theorem segBytes_fold (chosen : List Selection) (proof : Fin 115 → Digest) (seg : Segment) {r : Nat}
    (hr : r < seg.a) (j : Nat) (hj : j + 16 ≤ 80) :
    window (segBytes chosen proof seg) (8 + 80 * r + j) 16 =
      window (foldBytes (seg.heap r) (proof ⟨foldSlot chosen seg r % 115, Nat.mod_lt _ (by decide)⟩)) j 16 := by
  unfold segBytes
  have hl : ([UInt8.ofNat seg.byte0] ++ zeros 7).length = 8 := by simp [zeros]
  rw [window_append_right _ _ _ _ (by rw [hl]; omega), hl, show 8 + 80 * r + j - 8 = 80 * r + j by omega]
  rw [window_flatMap_const _ _ 80 (fun _ => foldBytes_length _ _) r (by simpa using hr) j 16 hj]
  simp only [List.getElem_range]
theorem foldBytes_sib (E : Nat) (sib : Digest) : window (foldBytes E sib) (sibOff (E % 2)) 16 = bytesLE 16 sib := by
  unfold foldBytes sibOff
  rcases Nat.mod_two_eq_zero_or_one E with h | h
  · simp only [h, show (0 : Nat) ≠ 1 by decide, if_false]
    rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]), window_append_right _ _ _ _ (by simp [zeros]),
      show 48 - (zeros 48).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _)]
  · simp only [h, if_true]
    rw [window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _)]
theorem foldBytes_pad (E : Nat) (sib : Digest) : window (foldBytes E sib) 32 16 = zeros 16 := by
  unfold foldBytes
  split
  · rw [window_append_right _ _ _ _ (by simp [bytesLE_length]), window_zeros _ _ _ (by simp [bytesLE_length])]
  · rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]), window_append_left _ _ _ _ (by simp [zeros]),
      window_zeros _ _ _ (by omega)]
theorem layer_prefix (N : HashOutput) (w : Witness) (lay : Layer) :
    (((List.finRange 4).take lay.val).map fun l =>
        (layerStorage l (route (N.toNat % 2 ^ 31) l).1 (w.signature.layers l)).length).sum = layerBase lay - 11288 := by
  simp only [layerStorage_length]
  fin_cases lay <;> simp [List.finRange, layerBase, height, chainCount]
theorem win_layer (N : HashOutput) (w : Witness) (lay : Layer) (j m : Nat)
    (hjm : j + m ≤ 64 * (height lay + chainCount lay)) :
    window (witList N w) (layerBase lay + j) m =
      window (layerBytes lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)) j m := by
  have hb : 11288 ≤ layerBase lay := by fin_cases lay <;> simp [layerBase]
  have hlen : ((List.finRange 4)[lay.val]'(by simp)) = lay := by simp
  have key := window_flatMap (List.finRange 4) (fun l => layerStorage l (route (N.toNat % 2 ^ 31) l).1
    (w.signature.layers l)) lay.val (by simp) j m (by rw [hlen, layerStorage_length]; omega)
  rw [layer_prefix N w lay, hlen] at key
  rw [win_layers _ _ _ _ (by omega), show layerBase lay + j - 11288 = (layerBase lay - 11288) + j by omega, key]
  unfold layerStorage
  exact window_append_left _ _ _ _ (by rw [layerBytes_length]; exact hjm)
theorem layerBytes_merkle (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (j : Fin (height lay)) (o : Nat)
    (ho : o + 16 ≤ 64) :
    window (layerBytes lay leaf ls) (64 * (height lay - 1 - j.val) + o) 16 =
      window (if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
        else zeros 48 ++ bytesLE 16 (ls.path j)) o 16 := by
  unfold layerBytes
  rw [window_append_left _ _ _ _ (by
    rw [List.length_flatMap]
    have : ∀ j : Fin (height lay), (if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
        else zeros 48 ++ bytesLE 16 (ls.path j)).length = 64 := by intro j; split <;> simp [zeros, bytesLE_length]
    simp only [this, List.map_const', List.length_reverse, List.length_finRange, List.sum_replicate, smul_eq_mul]
    have := j.isLt; omega)]
  rw [window_flatMap_const _ _ 64 (fun j => by split <;> simp [zeros, bytesLE_length]) (height lay - 1 - j.val)
    (by simp; omega) o 16 ho]
  have hj : ((List.finRange (height lay)).reverse[height lay - 1 - j.val]'(by simp; omega)) = j := by
    rw [List.getElem_reverse]; ext; simp; omega
  rw [hj]
theorem layerBytes_chain (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (i : Fin (chainCount lay)) (o : Nat)
    (ho : o + 16 ≤ 64) :
    window (layerBytes lay leaf ls) (64 * height lay + 64 * (chainCount lay - 1 - i.val) + o) 16 =
      window (zeros 48 ++ bytesLE 16 (ls.values i)) o 16 := by
  unfold layerBytes
  have hM : ((List.finRange (height lay)).reverse.flatMap fun j =>
      if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (ls.path j)).length = 64 * height lay := by
    rw [List.length_flatMap]
    have : ∀ j : Fin (height lay), (if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
        else zeros 48 ++ bytesLE 16 (ls.path j)).length = 64 := by intro j; split <;> simp [zeros, bytesLE_length]
    simp only [this, List.map_const', List.length_reverse, List.length_finRange, List.sum_replicate, smul_eq_mul]
    ring
  rw [window_append_right _ _ _ _ (by rw [hM]; omega), hM,
    show 64 * height lay + 64 * (chainCount lay - 1 - i.val) + o - 64 * height lay =
      64 * (chainCount lay - 1 - i.val) + o by omega]
  rw [window_flatMap_const _ _ 64 (fun j => by simp [zeros, bytesLE_length]) (chainCount lay - 1 - i.val)
    (by simp; omega) o 16 ho]
  have hi : ((List.finRange (chainCount lay)).reverse[chainCount lay - 1 - i.val]'(by simp; omega)) = i := by
    rw [List.getElem_reverse]; ext; simp; omega
  rw [hi]
section fields
variable (N : HashOutput) (w : Witness)
theorem wvalue_witEnc (lay : Layer) (i : Fin (chainCount lay)) :
    wvalue (witEnc N w) lay i.val = (w.signature.layers lay).values i := by
  have hi := i.isLt
  unfold wvalue chainBlock
  rw [wdig_witEnc, show ((witList N w).drop (layerBase lay + 64 * height lay + 64 * (chainCount lay - 1 - i.val) + 48)).take 16
    = window (witList N w) (layerBase lay + (64 * height lay + 64 * (chainCount lay - 1 - i.val) + 48)) 16 by
      unfold window; congr 2; omega, win_layer _ _ _ _ _ (by omega), layerBytes_chain _ _ _ _ _ (by omega),
    window_append_right _ _ _ _ (by simp [zeros]), show 48 - (zeros 48).length = 0 by simp [zeros],
    window_full _ _ (bytesLE_length _ _), Correctness.readDigest_bytesLE]
theorem wchainPads_witEnc (lay : Layer) (i : Fin (chainCount lay)) : wchainPads (witEnc N w) lay i.val = (0, 0) := by
  have hi := i.isLt
  unfold wchainPads chainBlock
  rw [wdig_witEnc, wdig_witEnc]
  rw [show ((witList N w).drop (layerBase lay + 64 * height lay + 64 * (chainCount lay - 1 - i.val))).take 16
    = window (witList N w) (layerBase lay + (64 * height lay + 64 * (chainCount lay - 1 - i.val) + 0)) 16 by
      unfold window; congr 2; omega,
    show ((witList N w).drop (layerBase lay + 64 * height lay + 64 * (chainCount lay - 1 - i.val) + 32)).take 16
    = window (witList N w) (layerBase lay + (64 * height lay + 64 * (chainCount lay - 1 - i.val) + 32)) 16 by
      unfold window; congr 2; omega,
    win_layer _ _ _ _ _ (by omega), win_layer _ _ _ _ _ (by omega), layerBytes_chain _ _ _ _ _ (by omega),
    layerBytes_chain _ _ _ _ _ (by omega), window_append_left _ _ _ _ (by simp [zeros]),
    window_append_left _ _ _ _ (by simp [zeros]), window_zeros _ _ _ (by omega), window_zeros _ _ _ (by omega),
    readDigest_zeros]
theorem wpath_witEnc (lay : Layer) (j : Fin (height lay)) :
    wpath (witEnc N w) lay (route (N.toNat % 2 ^ 31) lay).1 j.val = (w.signature.layers lay).path j := by
  have hj := j.isLt
  unfold wpath merkleBlock
  have hs : sibOff ((route (N.toNat % 2 ^ 31) lay).1 / 2 ^ j.val % 2) ≤ 48 := by unfold sibOff; split <;> omega
  rw [wdig_witEnc, show ((witList N w).drop (layerBase lay + 64 * (height lay - 1 - j.val) +
      sibOff ((route (N.toNat % 2 ^ 31) lay).1 / 2 ^ j.val % 2))).take 16
    = window (witList N w) (layerBase lay + (64 * (height lay - 1 - j.val) +
      sibOff ((route (N.toNat % 2 ^ 31) lay).1 / 2 ^ j.val % 2))) 16 by unfold window; congr 2; omega,
    win_layer _ _ _ _ _ (by omega), layerBytes_merkle _ _ _ _ _ (by omega)]
  unfold sibOff
  split
  · rw [window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _),
      Correctness.readDigest_bytesLE]
  · rw [window_append_right _ _ _ _ (by simp [zeros]), show 48 - (zeros 48).length = 0 by simp [zeros],
      window_full _ _ (bytesLE_length _ _), Correctness.readDigest_bytesLE]
theorem wmerklePad_witEnc (lay : Layer) (j : Fin (height lay)) : wmerklePad (witEnc N w) lay j.val = 0 := by
  have hj := j.isLt
  unfold wmerklePad merkleBlock
  rw [wdig_witEnc, show ((witList N w).drop (layerBase lay + 64 * (height lay - 1 - j.val) + 32)).take 16
    = window (witList N w) (layerBase lay + (64 * (height lay - 1 - j.val) + 32)) 16 by unfold window; congr 2,
    win_layer _ _ _ _ _ (by omega), layerBytes_merkle _ _ _ _ _ (by omega)]
  split
  · rw [window_append_right _ _ _ _ (by simp [bytesLE_length]), window_zeros _ _ _ (by simp [bytesLE_length]),
      readDigest_zeros]
  · rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]), window_zeros _ _ _ (by omega), readDigest_zeros]
end fields
theorem schedule_a_le (chosen : List Selection) (hc : ChosenOk chosen) {n : Nat} (hn : n < 35) :
    ((schedule chosen).getD n default).lo + ((schedule chosen).getD n default).a ≤ 11 := by
  rw [schedule_getD chosen hn]; exact (foldFacts _ _ (hc _ (by omega))).top _ (by omega)
theorem byte0_lt (seg : Segment) (h : seg.a ≤ 11) : seg.byte0 < 64 := by
  unfold Segment.byte0 Segment.t
  have := Nat.mod_lt (seg.heap 0) (show 0 < 2 by decide)
  split <;> omega
theorem Segment.matches_byte0 (seg : Segment) (h : seg.a ≤ 11) : seg.Matches seg.byte0 := by
  unfold Segment.Matches Segment.byte0
  have ht : seg.t < 2 := Nat.mod_lt _ (by decide)
  refine ⟨?_, ?_, ?_⟩
  · split <;> omega
  · cases seg.merge <;> simp <;> omega
  · intro _; split <;> omega
theorem wbyte_seg_witEnc (N : HashOutput) (w : Witness) (hc : ChosenOk (selections N))
    (hle : slotBase (selections N) 7 ≤ 115) {n : Nat} (hn : n < 35) :
    (wbyte (witEnc N w) (segPtr (schedule (selections N)) n)).toNat = ((schedule (selections N)).getD n default).byte0 := by
  rw [wbyte_witEnc]
  have hw := win_seg N w hc hle hn 0 1 (by omega)
  rw [Nat.add_zero, segBytes_header] at hw
  rw [getD_of_window _ _ _ hw, UInt8.toNat_ofNat', Nat.mod_eq_of_lt
    (by have := byte0_lt _ (show ((schedule (selections N)).getD n default).a ≤ 11 by
      have := schedule_a_le _ hc hn; omega); omega)]
theorem streamMatches_witEnc (N : HashOutput) (w : Witness) (hc : ChosenOk (selections N))
    (hle : slotBase (selections N) 7 ≤ 115) : StreamMatches (selections N) (witEnc N w) := by
  intro n hn
  rw [schedule_length] at hn
  rw [wbyte_seg_witEnc N w hc hle hn]
  exact Segment.matches_byte0 _ (by have := schedule_a_le _ hc hn; omega)
theorem wfold_witEnc (N : HashOutput) (w : Witness) (hc : ChosenOk (selections N))
    (hle : slotBase (selections N) 7 ≤ 115) {n r : Nat} (hn : n < 35)
    (hr : r < ((schedule (selections N)).getD n default).a) :
    wdig (witEnc N w) (foldBlock (segPtr (schedule (selections N)) n) r +
        sibOff (((schedule (selections N)).getD n default).heap r % 2)) =
      w.signature.proof ⟨foldSlot (selections N) ((schedule (selections N)).getD n default) r % 115,
        Nat.mod_lt _ (by decide)⟩ ∧
    wdig (witEnc N w) (foldBlock (segPtr (schedule (selections N)) n) r + 32) = 0 := by
  have hs : sibOff (((schedule (selections N)).getD n default).heap r % 2) ≤ 48 := by unfold sibOff; split <;> omega
  unfold foldBlock
  constructor
  · rw [wdig_witEnc, show ((witList N w).drop (segPtr (schedule (selections N)) n + 8 + 80 * r +
        sibOff (((schedule (selections N)).getD n default).heap r % 2))).take 16 =
      window (witList N w) (segPtr (schedule (selections N)) n + (8 + 80 * r +
        sibOff (((schedule (selections N)).getD n default).heap r % 2))) 16 by unfold window; congr 2; omega,
      win_seg N w hc hle hn _ _ (by omega), segBytes_fold _ _ _ hr _ (by omega), foldBytes_sib,
      Correctness.readDigest_bytesLE]
  · rw [wdig_witEnc, show ((witList N w).drop (segPtr (schedule (selections N)) n + 8 + 80 * r + 32)).take 16 =
      window (witList N w) (segPtr (schedule (selections N)) n + (8 + 80 * r + 32)) 16 by unfold window; congr 2; omega,
      win_seg N w hc hle hn _ _ (by omega), segBytes_fold _ _ _ hr _ (by omega), foldBytes_pad, readDigest_zeros]
theorem foldPositions_nodup (segs : List Segment) : (foldPositions segs).Nodup := by
  unfold foldPositions
  refine List.nodup_flatMap.mpr ⟨fun n _ => (List.nodup_range).map (fun a b h => by simpa using h), ?_⟩
  refine (List.nodup_range).pairwise_of_forall_ne (fun a _ b _ hab => ?_)
  simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_range, not_exists, not_and]
  rintro p ⟨r, _, rfl⟩ r' _ h
  simp only [Prod.mk.injEq] at h
  exact hab h.1.symm
theorem foldPositions_length (segs : List Segment) : (foldPositions segs).length = (segs.map Segment.a).sum := by
  unfold foldPositions
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_range]
  rw [← sum_range_getD segs default Segment.a]
theorem foldSlot_surj (chosen : List Selection) (hc : ChosenOk chosen) {k : Nat} (hk : k < slotBase chosen 7) :
    ∃ p ∈ foldPositions (schedule chosen), foldSlot chosen ((schedule chosen).getD p.1 default) p.2 = k := by
  classical
  have key := Finset.surj_on_of_inj_on_of_card_le (s := (foldPositions (schedule chosen)).toFinset)
    (t := Finset.range (slotBase chosen 7))
    (fun p _ => foldSlot chosen ((schedule chosen).getD p.1 default) p.2)
    (fun p hp => by
      have hm := mem_foldPositions.mp (List.mem_toFinset.mp hp)
      rw [schedule_length] at hm
      obtain ⟨e, l⟩ := foldSlot_split chosen hc hm.1 hm.2
      have hb1 := slotBase_mono chosen (show p.1 / 5 + 1 ≤ 7 by omega)
      rw [slotBase_succ] at hb1
      rw [Finset.mem_range, e]; omega)
    (fun p q hp hq h => by
      have hm := mem_foldPositions.mp (List.mem_toFinset.mp hp)
      have hm' := mem_foldPositions.mp (List.mem_toFinset.mp hq)
      rw [schedule_length] at hm hm'
      obtain ⟨h1, h2⟩ := foldSlot_inj chosen hc hm.1 hm'.1 hm.2 hm'.2 h
      exact Prod.ext h1 h2)
    (by
      rw [Finset.card_range, List.toFinset_card_of_nodup (foldPositions_nodup _), foldPositions_length,
        schedule_folds chosen hc])
  obtain ⟨p, hp, he⟩ := key k (Finset.mem_range.mpr hk)
  exact ⟨p, List.mem_toFinset.mp hp, he.symm⟩
theorem witDecP_proof_witEnc (N : HashOutput) (w : Witness) (hc : ChosenOk (selections N))
    (hle : slotBase (selections N) 7 ≤ 115)
    (htail : ∀ k : Fin 115, slotBase (selections N) 7 ≤ k.val → w.signature.proof k = 0) (k : Fin 115) :
    (witDecP N (witEnc N w)).signature.proof k = w.signature.proof k := by
  show (match slotOffset (selections N) k with | some off => wdig (witEnc N w) off | none => 0) = _
  unfold slotOffset
  rcases hp : streamPlan (selections N) k with _ | ⟨n, r⟩
  · simp only [Option.map_none]
    by_contra hne
    have hk : k.val < slotBase (selections N) 7 := by
      by_contra hk; exact hne (htail k (by omega)).symm
    obtain ⟨⟨n, r⟩, hmem, he⟩ := foldSlot_surj (selections N) hc hk
    unfold streamPlan at hp
    rw [List.find?_eq_none] at hp
    exact hp _ hmem (by simpa using he)
  · simp only [Option.map_some]
    unfold streamPlan at hp
    have hmem := mem_foldPositions.mp (List.mem_of_find?_eq_some hp)
    have hsl := List.find?_some hp
    simp only [decide_eq_true_eq] at hsl hmem
    rw [schedule_length] at hmem
    rw [(wfold_witEnc N w hc hle hmem.1 hmem.2).1]
    congr 1; ext; simp only [hsl, Nat.mod_eq_of_lt k.isLt]
theorem LayerSignature.ext' {lay : Layer} {x y : LayerSignature lay} (hv : x.values = y.values)
    (hp : x.path = y.path) : x = y := by
  cases x; cases y; simp_all
theorem witDecP_witEnc (N : HashOutput) (w : Witness) (hc : ChosenOk (selections N))
    (hle : slotBase (selections N) 7 ≤ 115)
    (htail : ∀ k : Fin 115, slotBase (selections N) 7 ≤ k.val → w.signature.proof k = 0) :
    witDecP N (witEnc N w) = w := by
  obtain ⟨⟨rho, secrets, proof, layers⟩, dc, ctr⟩ := w
  unfold witDecP
  simp only [Witness.mk.injEq, Signature.mk.injEq]
  refine ⟨⟨wrho_witEnc N _, funext fun s => wsecret_witEnc N _ s.val s.isLt,
    funext fun k => witDecP_proof_witEnc N _ hc hle htail k, funext fun lay => ?_⟩, wdc_witEnc N _,
    funext fun lay => wctr_witEnc N _ lay⟩
  exact LayerSignature.ext' (funext fun i => wvalue_witEnc N _ lay i) (funext fun j => wpath_witEnc N _ lay j)
theorem padDecP_witEnc (N : HashOutput) (w : Witness) (hc : ChosenOk (selections N))
    (hle : slotBase (selections N) 7 ≤ 115) : padDecP N (witEnc N w) = 0 := by
  unfold padDecP
  show Pads.mk _ _ _ _ = Pads.mk _ _ _ _
  congr 1
  · funext s; exact wleafPad_witEnc N w s.val s.isLt
  · funext k
    show (match slotBlock (selections N) k with | some blk => wdig (witEnc N w) (blk + 32) | none => 0) = 0
    unfold slotBlock
    rcases hp : streamPlan (selections N) k with _ | ⟨n, r⟩
    · rfl
    · simp only [Option.map_some]
      unfold streamPlan at hp
      have hmem := mem_foldPositions.mp (List.mem_of_find?_eq_some hp)
      simp only at hmem
      rw [schedule_length] at hmem
      exact (wfold_witEnc N w hc hle hmem.1 hmem.2).2
  · funext lay i; exact wchainPads_witEnc N w lay i
  · funext lay j; exact wmerklePad_witEnc N w lay j
theorem shaped_witEnc (N : HashOutput) (w : Witness) (hsel : selectionsOk (selections N) = true)
    (hadm : admissible (selections N) = true) : Shaped N (witEnc N w) :=
  ⟨hsel, hadm, streamMatches_witEnc N w (chosenOk_of N hsel) (slotBase_seven_le N (chosenOk_of N hsel) hadm)⟩
end SigGolfCandidate.T3M
