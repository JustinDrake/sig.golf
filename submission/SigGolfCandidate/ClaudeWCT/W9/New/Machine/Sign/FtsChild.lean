import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsPieces

section

set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest header pad64 privateInput zero16)
open SphincsSecurity (bytesLE bytesLE_length)
theorem readWords_of_getD (t : MachineState) (A : Nat) :
    ∀ (m : Nat) (l : List Word), l.length = m →
      (∀ j < m, t.getMem (BitVec.ofNat 64 (A + 8 * j)) = l.getD j 0) → t.readWords (BitVec.ofNat 64 A) m = l
  | 0, l, hl, _ => by rw [List.length_eq_zero_iff] at hl; subst hl; rfl
  | m + 1, l, hl, h => by
    obtain ⟨l', d, rfl⟩ : ∃ l' d, l = l' ++ [d] := ⟨l.dropLast, l.getLast (by
      intro he; subst he; simp at hl), (List.dropLast_append_getLast _).symm⟩
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
    rw [readWords_add, readWords_of_getD t A m l' hl (fun j hj => by
      rw [h j (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hl ▸ hj)]),
      readWords_one, h m (by omega)]
    simp [List.getD_eq_getElem?_getD, hl]
theorem hashInput_of_words (t : MachineState) (l : List UInt8) (n A : Nat) (hl : l.length = 64 * (n + 1))
    (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 64 * (n + 1) < 2 ^ 64)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (n + 1)))
    (hw : ∀ j < 8 * (n + 1), t.getMem (BitVec.ofNat 64 (A + 8 * j)) = (wordsOf l).getD j 0) :
    hashInput t = toQ l :=
  hashInput_toQ t l n A hl h10 hA (by omega) h11 (by omega)
    (readWords_of_getD t A _ _ (length_wordsOf _ _ (by rw [hl]; ring)) hw)
theorem header_words (tag lay tree pos idx : Nat) (ht : ¬ SigGolfCandidate.T3.packedNodeTag tag) (htag : tag < 256)
    (hlay : lay < 256) (htree : tree < 2 ^ 32) (hpos : pos < 2 ^ 32) (hidx : idx < 2 ^ 32) :
    wordsOf (bytesLE 16 (header tag lay tree pos idx)) =
      [BitVec.ofNat 64 (1 + 256 * tag + 65536 * lay + 2 ^ 32 * pos), BitVec.ofNat 64 (tree + 2 ^ 32 * idx)] := by
  rw [wordsOf_header, if_neg ht, if_neg ht, hdr0_eq tag lay tree pos htag hlay htree hpos, hdr1_eq tree idx htree hidx]
theorem wordsOf_priv (sk : BitVec 256) (c index q : Nat) (hc : c < 256) (hidx : index < 2 ^ 32) (hq : q < 2 ^ 32) :
    wordsOf (privateInput sk (.inl (header 8 c index 0 q))) =
      [sk.extractLsb' 0 64, sk.extractLsb' 64 64, BitVec.ofNat 64 (hdr8 c), BitVec.ofNat 64 (index + 2 ^ 32 * q),
        sk.extractLsb' 128 64, sk.extractLsb' 192 64, 0, 0] := by
  rw [wordsOf_privateInput_tweak, header_lo, header_hi, if_neg (by decide), if_neg (by decide),
    hdr0_eq 8 c index 0 (by norm_num) hc hidx (by norm_num), hdr1_eq index q hidx hq]
  simp only [hdr8]; congr 3
theorem chainInput_len (index c j i st : Nat) (v : Digest) : (WCT9.chainInput index c j i st v).length = 64 := by
  simp only [WCT9.chainInput, zero16, List.length_append, bytesLE_length, List.length_replicate]
theorem wordsOf_chain (index c j i st : Nat) (v : Digest) (hc : c < 256) (hidx : index < 2 ^ 32)
    (hpos : st + 256 * i < 2 ^ 32) (hj : j < 2 ^ 32) :
    wordsOf (pad64 (WCT9.chainInput index c j i st v)) =
      [0, 0, BitVec.ofNat 64 (hdr5 c + 2 ^ 32 * st + 2 ^ 40 * i), BitVec.ofNat 64 (index + 2 ^ 32 * j), 0, 0,
        v.extractLsb' 0 64, v.extractLsb' 64 64] := by
  rw [pad64_of_aligned _ (by rw [chainInput_len]), WCT9.chainInput_eq_header,
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_append _ _ (by simp [zero16, bytesLE_length]),
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_zero16,
    header_words 5 c index (st + 256 * i) j (by decide) (by norm_num) hc hidx hpos hj, wordsOf_bytesLE16]
  simp only [hdr5, List.cons_append, List.nil_append]
  congr 4; ring
def leafIn (index c j : Nat) (ends : List Digest) : List UInt8 :=
  bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (WCT9.wctHeader 6 c index 0 j) ++ (ends.drop 1).flatMap (bytesLE 16)
theorem leafHash_eq (index c j : Nat) (ends : List Digest) :
    WCT9.leafHash index c j ends = SigGolfCandidate.T3.shortHash (leafIn index c j ends) := rfl
theorem leafIn_len (index c j : Nat) (ends : List Digest) (h : ends.length = 7) : (leafIn index c j ends).length = 128 := by
  have : ((ends.drop 1).flatMap (bytesLE 16)).length = 96 := by
    rw [List.length_flatMap]; simp [bytesLE_length, h]
  simp only [leafIn, List.length_append, bytesLE_length, this]
theorem wordsOf_leaf (index c j : Nat) (ends : List Digest) (h : ends.length = 7) (hc : c < 256)
    (hidx : index < 2 ^ 32) (hj : j < 2 ^ 32) :
    wordsOf (pad64 (leafIn index c j ends)) =
      wordsOf (bytesLE 16 (ends.getD 0 0)) ++ [BitVec.ofNat 64 (hdr6 c), BitVec.ofNat 64 (index + 2 ^ 32 * j)] ++
        (ends.drop 1).flatMap fun d => [d.extractLsb' 0 64, d.extractLsb' 64 64] := by
  rw [pad64_of_aligned _ (by rw [leafIn_len _ _ _ _ h]), leafIn,
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_append _ _ (by simp [bytesLE_length]),
    WCT9.leaf_header_eq, header_words 6 c index 0 j (by decide) (by norm_num) hc hidx (by norm_num) hj,
    wordsOf_flatMap16]
  simp only [hdr6]; congr 4
def nodeIn (c index h : Nat) (L R : Digest) : List UInt8 :=
  bytesLE 16 L ++ bytesLE 16 (header 11 c index 0 h) ++ zero16 ++ bytesLE 16 R
theorem nodeHash_eq (c index h : Nat) (L R : Digest) :
    SigGolfCandidate.T3.nodeHash 11 c index h L R = SigGolfCandidate.T3.shortHash (nodeIn c index h L R) := rfl
theorem nodeIn_len (c index h : Nat) (L R : Digest) : (nodeIn c index h L R).length = 64 := by
  simp only [nodeIn, zero16, List.length_append, bytesLE_length, List.length_replicate]
theorem wordsOf_node (c index h : Nat) (L R : Digest) (hc : c < 256) (hidx : index < 2 ^ 32) (hh : h < 2 ^ 32) :
    wordsOf (pad64 (nodeIn c index h L R)) =
      [L.extractLsb' 0 64, L.extractLsb' 64 64, BitVec.ofNat 64 (hdr11 c), BitVec.ofNat 64 (index + 2 ^ 32 * h), 0, 0,
        R.extractLsb' 0 64, R.extractLsb' 64 64] := by
  rw [pad64_of_aligned _ (by rw [nodeIn_len]), nodeIn,
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_append _ _ (by simp [zero16, bytesLE_length]),
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_zero16,
    header_words 11 c index 0 h (by decide) (by norm_num) hc hidx (by norm_num) hh, wordsOf_bytesLE16, wordsOf_bytesLE16]
  simp only [hdr11, List.cons_append, List.nil_append]
  congr 3
def forestIn (index : Nat) (roots : List Digest) : List UInt8 :=
  bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 15 0 index 0 0) ++ (roots.drop 1).flatMap (bytesLE 16)
theorem forestPk_eq (index : Nat) (roots : List Digest) :
    WCT9.forestPk index roots = SigGolfCandidate.T3.shortHash (forestIn index roots) := rfl
theorem forestIn_len (index : Nat) (roots : List Digest) (h : roots.length = 9) : (forestIn index roots).length = 160 := by
  have : ((roots.drop 1).flatMap (bytesLE 16)).length = 128 := by
    rw [List.length_flatMap]; simp [bytesLE_length, h]
  simp only [forestIn, List.length_append, bytesLE_length, this]
theorem pad64_forest (index : Nat) (roots : List Digest) (h : roots.length = 9) :
    pad64 (forestIn index roots) = forestIn index roots ++ List.replicate 32 0 := by
  rw [pad64, forestIn_len _ _ h]
theorem wordsOf_forest (index : Nat) (roots : List Digest) (h : roots.length = 9) (hidx : index < 2 ^ 32) :
    wordsOf (pad64 (forestIn index roots)) =
      wordsOf (bytesLE 16 (roots.getD 0 0)) ++ [BitVec.ofNat 64 3841, BitVec.ofNat 64 index] ++
        ((roots.drop 1).flatMap fun d => [d.extractLsb' 0 64, d.extractLsb' 64 64]) ++ [0, 0, 0, 0] := by
  rw [pad64_forest _ _ h, wordsOf_append _ _ (by rw [forestIn_len _ _ h]), forestIn,
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_append _ _ (by simp [bytesLE_length]),
    header_words 15 0 index 0 0 (by decide) (by norm_num) (by norm_num) hidx (by norm_num) (by norm_num),
    wordsOf_flatMap16, show List.replicate 32 (0 : UInt8) = List.replicate (8 * 4) 0 from rfl,
    wordsOf_replicate_zero]
  rfl
end ClaudeWCT.W9.Machine.Sign
end

section

set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash)
open SphincsSecurity (bytesLE bytesLE_length)
def chainRest (index c j i d : Nat) : Nat → List Digest → M (Digest × Digest)
  | 0, L => pure (L.getD (3 - d) 0, L.getD 3 0)
  | r + 1, L => shortHash (WCT9.chainInput index c j i (2 - r) (L.getD (2 - r) 0)) >>= fun v =>
      chainRest index c j i d r (L ++ [v])
theorem chain3_eq (index c j i d : Nat) (hd : d ≤ 3) (seed : Digest) :
    (WCT9.chain index c j i 0 (3 - d) seed >>= fun value =>
      WCT9.chain index c j i (3 - d) d value >>= fun last => pure (value, last)) =
      chainRest index c j i d 3 [seed] := by
  interval_cases d <;>
    simp only [WCT9.chain, chainRest, show List.range' 0 3 = [0, 1, 2] from rfl,
      show List.range' 0 2 = [0, 1] from rfl, show List.range' 0 1 = [0] from rfl,
      show List.range' 0 0 = [] from rfl, show List.range' 3 0 = [] from rfl, show List.range' 2 1 = [2] from rfl,
      show List.range' 1 2 = [1, 2] from rfl, List.foldlM_cons, List.foldlM_nil, bind_assoc, pure_bind,
      Nat.sub_self, Nat.sub_zero] <;> rfl
def chainW (c i : Nat) (A : Nat) : Prop :=
  (CHAINW + 16 ≤ A ∧ A < CHAINW + 32) ∨ (CHAINW + 48 ≤ A ∧ A < CHAINW + 80) ∨ A = LEAFW + leafOff i ∨
    A = LEAFW + leafOff i + 8 ∨ A = slotV c i ∨ A = slotV c i + 8
def chainRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x26, .x28, .x29]
structure ChkSt (c i j index sel w d r : Nat) (L : List Digest) (s0 t : MachineState) : Prop where
  pc : t.pc = pcOf (chkI c i (3 - r))
  x5 : t.getReg .x5 = 0
  x18 : t.getReg .x18 = BitVec.ofNat 64 j
  x22 : t.getReg .x22 = BitVec.ofNat 64 index
  x24 : t.getReg .x24 = BitVec.ofNat 64 sel
  x25 : t.getReg .x25 = BitVec.ofNat 64 w
  x26 : t.getReg .x26 = BitVec.ofNat 64 (3 - d)
  len : L.length = 4 - r
  val : DigAt t (CHAINW + 48) (L.getD (3 - r) 0)
  h16 : t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i (3 - r - 1))
  h24 : t.getMem (BitVec.ofNat 64 (CHAINW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * j)
  z0 : t.getMem (BitVec.ofNat 64 CHAINW) = 0
  z8 : t.getMem (BitVec.ofNat 64 (CHAINW + 8)) = 0
  z32 : t.getMem (BitVec.ofNat 64 (CHAINW + 32)) = 0
  z40 : t.getMem (BitVec.ofNat 64 (CHAINW + 40)) = 0
  op : j = sel → 3 - d < 3 - r → DigAt t (slotV c i) (L.getD (3 - d) 0)
  regs : RegsExcept s0 t chainRegs
  frame : Frame s0 t (chainW c i)
  nosel : j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 7 →
    t.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A)
def ChainPost (c i j sel : Nat) (s0 : MachineState) (r : Digest × Digest) (t : MachineState) : Prop :=
  t.pc = pcOf (lcEnd c i) ∧ DigAt t (LEAFW + leafOff i) r.2 ∧ (j = sel → DigAt t (slotV c i) r.1) ∧
    RegsExcept s0 t chainRegs ∧ Frame s0 t (chainW c i) ∧
    (j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 7 →
      t.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A))
theorem chkI_pos : ∀ c, c < 9 → ∀ i, i < 7 → ∀ st, st < 4 → 1 ≤ chkI c i st := by decide +kernel
theorem blocks64 (l : List UInt8) (hl : l.length = 64) : (toQ (pad64 l)).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [hl]), blocks_toQ ⟨by rw [hl]; norm_num, by rw [hl]⟩, hl]
theorem pcOf_pred4 (n : Nat) (hn : 1 ≤ n) : pcOf (n - 1) + 4 = pcOf n := by
  rw [pcOf_add4, Nat.sub_add_cancel hn]
theorem DigAt.frame' {s t : MachineState} {W : Nat → Prop} {A : Nat} {d : Digest} (h : DigAt s A d)
    (hf : Frame s t W) (hA : A + 8 < 2 ^ 64) (h0 : ¬ W A) (h1 : ¬ W (A + 8)) : DigAt t A d :=
  h.frame hf hA h0 h1
section chain
variable {im : Image} {sk : BitVec 256}
theorem chain_from (hcode : NewCodeAt im) {c i j index sel w d : Nat} (hc : c < 9) (hi : i < 7) (hj : j < 128)
    (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64) (hd : d ≤ 3) {s0 : MachineState} :
    ∀ r, r ≤ 3 → ∀ (L : List Digest) (t : MachineState), ChkSt c i j index sel w d r L s0 t →
      TBSim im sk t (11 + 28 * r + 8) (chainRest index c j i d r L) (ChainPost c i j sel s0) := by
  intro r
  induction r with
  | zero =>
    intro _ L t h
    obtain ⟨t1, k1, s1, hk1, p1, r1, f1, o1, n1⟩ :=
      step_Chk hcode hc hi (by norm_num : 3 < 4) t h.pc h.x18 h.x24 h.x26 (by omega) (by omega) (by omega) h.val
    obtain ⟨t2, s2, p2, l2, r2, f2⟩ := step_Lc hcode hc hi t1 p1 (h.val.frame f1 (by ao) (by ao) (by ao))
    have hlo : leafOff i ≤ 112 := by unfold leafOff; split_ifs <;> omega
    refine (TBSim.pure_steps' (s1.trans s2) ⟨p2, l2, fun hjs => ?_, ?_, ?_, ?_⟩).mono (by omega) (fun _ _ h => h)
    · by_cases hd0 : d = 0
      · subst hd0
        have := o1 hjs rfl
        exact this.frame f2 (by ao) (by ao) (by ao)
      · have := h.op hjs (by omega)
        exact (this.frame (n1 (fun h' => hd0 (by omega))) (by ao) (fun h => h) (fun h => h)).frame f2
          (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
    · exact ((h.regs.trans r1).trans r2).mono (by simp [chainRegs])
    · refine ((h.frame.trans f1).trans f2).mono (fun A _ hA => ?_)
      unfold chainW
      rcases hA with (hA | hA) | hA <;> [exact hA; (rcases hA with rfl | rfl <;> simp); (rcases hA with rfl | rfl <;> simp)]
    · intro hjs A hA h1 h2
      rw [f2.get hA (by intro h'; unfold slotV at h1 h2; rcases h' with rfl | rfl <;> aoh),
        n1 (fun h' => hjs h'.1) A hA (fun h => h), h.nosel hjs A hA h1 h2]
  | succ r ih =>
    intro hr L t h
    have hpos := chkI_pos c hc i hi (3 - r) (by omega)
    obtain ⟨t1, k1, s1, hk1, p1, r1, f1, o1, n1⟩ :=
      step_Chk hcode hc hi (by omega : 2 - r < 4) t (by rw [h.pc]; congr 2; omega) h.x18 h.x24 h.x26
        (by omega) (by omega) (by omega) h.val
    have h16 : t1.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i (3 - (r + 1) - 1)) := by
      rw [f1.get (by ao) (by unfold slotV; ao)]; exact h.h16
    obtain ⟨t2, s2, e2, p2, x10, x11, x12, m16, r2, f2⟩ :=
      step_Stp hcode hc hi (by omega : 1 ≤ 3 - r) (by omega : 3 - r < 4) t1
        (by rw [p1]; congr 2; omega) (by omega : 3 - (r + 1) - 1 < 4) h16
    have g12 : ∀ A, A ≠ CHAINW + 16 → A ≠ slotV c i → A ≠ slotV c i + 8 → A < 2 ^ 64 →
        t2.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A h1 h2 h3 hA => by
      rw [f2.get hA (by simpa using h1), f1.get hA (by simp [h2, h3])]
    have hx5 : t2.getReg .x5 = 0 := by
      rw [r2.get (by simp), r1.get (by simp)]; exact h.x5
    have hv := h.val
    have hq : hashInput t2 = toQ (pad64 (WCT9.chainInput index c j i (2 - r) (L.getD (2 - r) 0))) := by
      refine hashInput_of_words t2 _ 0 CHAINW (by rw [pad64_of_aligned _ (by rw [chainInput_len]), chainInput_len])
        x10 (by ao) (by ao) x11 ?_
      rw [wordsOf_chain index c j i (2 - r) _ (by omega) (by omega) (by omega) (by omega)]
      intro k hk
      interval_cases k
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.z0
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.z8
      · rw [show CHAINW + 8 * 2 = CHAINW + 16 by ao, m16, chainW0, show 3 - r - 1 = 2 - r by omega]; rfl
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.h24
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.z32
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.z40
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]
        rw [show 3 - (r + 1) = 2 - r by omega] at hv; exact hv.1
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]
        rw [show 3 - (r + 1) = 2 - r by omega] at hv; exact hv.2
    have hbl := blocks64 _ (chainInput_len index c j i (2 - r) (L.getD (2 - r) 0))
    refine (TBSim.steps (s1.trans s2) (TBSim.shortHash_bind' (W := 11 + 28 * r + 8) e2 hx5
      (hashArgs_const t2 CHAINW 64 (CHAINW + 48) x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao)) hq
      (fun a => ih (by omega) (L ++ [a.extractLsb' 0 128]) (writeHash t2 a) ?_))).mono
      (by rw [hbl]; omega) (fun _ _ h => h)
    have fw := Frame.writeHash t2 a (CHAINW + 48) x12 (by ao)
    have g : ∀ A, A ≠ CHAINW + 16 → A ≠ slotV c i → A ≠ slotV c i + 8 → ¬ (CHAINW + 48 ≤ A ∧ A < CHAINW + 80) →
        A < 2 ^ 64 → (writeHash t2 a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
      intro A h1 h2 h3 h4 hA
      rw [fw.get hA (by intro h; exact h4 ⟨h.1, by omega⟩), g12 A h1 h2 h3 hA]
    have hlen : L.length = 3 - r := by have := h.len; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pc_writeHash, p2, pcOf_pred4 _ hpos]
    · rw [getReg_writeHash]; exact hx5
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x18
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x22
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x24
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x25
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x26
    · simp [hlen]; omega
    · have := DigAt.writeHash_lo t2 a (CHAINW + 48) x12 (by ao)
      refine this.congr ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), show 3 - r - L.length = 0 by omega]
      rfl
    · rw [fw.get (by ao) (by intro h; ao), m16]
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.h24
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.z0
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.z8
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.z32
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.z40
    · intro hjs hlt
      have e : (L ++ [a.extractLsb' 0 128]).getD (3 - d) 0 = L.getD (3 - d) 0 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rw [e]
      have hslot : DigAt t2 (slotV c i) (L.getD (3 - d) 0) := by
        by_cases hlt' : 3 - d < 3 - (r + 1)
        · exact ((h.op hjs hlt').frame (n1 (fun h' => by omega)) (by unfold slotV; ao) (fun h => h)
            (fun h => h)).frame f2 (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
        · have heq : 3 - d = 2 - r := by omega
          have := o1 hjs heq
          rw [heq]
          rw [show 3 - (r + 1) = 2 - r by omega] at this
          exact this.frame f2 (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
      exact hslot.frame fw (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
    · exact (((h.regs.trans r1).trans r2).trans
        (fun x _ => getReg_writeHash t2 a x : RegsExcept t2 (writeHash t2 a) [])).mono (by simp [chainRegs])
    · refine (((h.frame.trans f1).trans f2).trans fw).mono (fun A _ hA => ?_)
      unfold chainW
      rcases hA with ((hA | hA) | hA) | hA
      · exact hA
      · rcases hA with rfl | rfl <;> simp
      · subst hA; left; constructor <;> omega
      · right; left; constructor <;> omega
    · intro hjs A hA h1 h2
      have hs : slotV c 0 = SIG + 16 + 224 * c := by unfold slotV; omega
      rw [fw.get hA (by intro h'; unfold slotV at h1 h2; aoh), f2.get hA (by intro h'; unfold slotV at h1 h2; aoh),
        n1 (fun h' => hjs h'.1) A hA (fun h => h), h.nosel hjs A hA h1 h2]
structure ChainPre (c i j index sel w : Nat) (seed : Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf (preI c i)
  x5 : t.getReg .x5 = 0
  x18 : t.getReg .x18 = BitVec.ofNat 64 j
  x22 : t.getReg .x22 = BitVec.ofNat 64 index
  x24 : t.getReg .x24 = BitVec.ofNat 64 sel
  x25 : t.getReg .x25 = BitVec.ofNat 64 w
  seed : DigAt t (PAIRW + 16 * (i % 2)) seed
  z0 : t.getMem (BitVec.ofNat 64 CHAINW) = 0
  z8 : t.getMem (BitVec.ofNat 64 (CHAINW + 8)) = 0
  z32 : t.getMem (BitVec.ofNat 64 (CHAINW + 32)) = 0
  z40 : t.getMem (BitVec.ofNat 64 (CHAINW + 40)) = 0
def chainC : Nat := 20 + (11 + 28 * 3 + 8)
theorem chain_unit (hcode : NewCodeAt im) {c i j index sel w : Nat} (hc : c < 9) (hi : i < 7) (hj : j < 128)
    (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64) {seed : Digest} {s : MachineState}
    (h : ChainPre c i j index sel w seed s) :
    TBSim im sk s chainC (chainRest index c j i (w / 4 ^ i % 4) 3 [seed]) (ChainPost c i j sel s) := by
  obtain ⟨t1, s1, p1, x26, v1, m16, m24, r1, f1⟩ :=
    step_Pre hcode hc hi s h.pc h.x18 h.x22 (by omega) h.x25 hw h.seed
  have hd : w / 4 ^ i % 4 ≤ 3 := by have := Nat.mod_lt (w / 4 ^ i) (show 0 < 4 by norm_num); omega
  have g : ∀ A, A ≠ CHAINW + 16 → A ≠ CHAINW + 24 → A ≠ CHAINW + 56 → A ≠ CHAINW + 48 → A < 2 ^ 64 →
      t1.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A h1 h2 h3 h4 hA =>
    f1.get hA (by simp [h1, h2, h3, h4])
  have hst : ChkSt c i j index sel w (w / 4 ^ i % 4) 3 [seed] s t1 :=
    { pc := p1
      x5 := by rw [r1.get (by simp)]; exact h.x5
      x18 := by rw [r1.get (by simp)]; exact h.x18
      x22 := by rw [r1.get (by simp)]; exact h.x22
      x24 := by rw [r1.get (by simp)]; exact h.x24
      x25 := by rw [r1.get (by simp)]; exact h.x25
      x26 := x26
      len := rfl
      val := v1
      h16 := by rw [m16]; rfl
      h24 := m24
      z0 := by rw [g _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact h.z0
      z8 := by rw [g _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact h.z8
      z32 := by rw [g _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact h.z32
      z40 := by rw [g _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact h.z40
      op := fun _ h => absurd h (by omega)
      regs := r1.mono (by simp [chainRegs])
      frame := f1.mono (fun A _ hA => by
        unfold chainW
        rcases hA with rfl | rfl | rfl | rfl
        · left; constructor <;> omega
        · left; constructor <;> omega
        · right; left; constructor <;> omega
        · right; left; constructor <;> omega)
      nosel := fun _ A hA h1 h2 => f1.get hA (by unfold slotV at h1 h2; intro h'; aoh) }
  refine (TBSim.steps s1 (chain_from hcode hc hi hj hsel hidx hw hd 3 le_rfl [seed] t1 hst)).mono ?_ (fun _ _ h => h)
  unfold chainC; split_ifs <;> omega
end chain
end ClaudeWCT.W9.Machine.Sign
end

section

set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash privatePair privateInput)
open SphincsSecurity (bytesLE bytesLE_length)
def pairBody (index c j : Nat) (word : WCT9.Rank) (p : Fin 4) (state : List Digest × List Digest) :
    M (List Digest × List Digest) := do
  let seeds ← privatePair 8 c index 0 (4 * j + p.val)
  (List.finRange 2).foldlM (WCT9.childHalf index c j word p seeds) state
theorem childRows_eq (index c j : Nat) (word : WCT9.Rank) :
    WCT9.childRows index c j word = (do
      let s1 ← pairBody index c j word 0 ([], [])
      let s2 ← pairBody index c j word 1 s1
      let s3 ← pairBody index c j word 2 s2
      pairBody index c j word 3 s3) := by
  simp only [WCT9.childRows, pairBody, show List.finRange 4 = [0, 1, 2, 3] from rfl, List.foldlM_cons,
    List.foldlM_nil, bind_assoc, bind_pure]
theorem childHalf_eq (index c j : Nat) (word : WCT9.Rank) (p : Fin 4) (seeds : Digest × Digest)
    (state : List Digest × List Digest) (h : Fin 2) (hh : 2 * p.val + h.val < 7) :
    WCT9.childHalf index c j word p seeds state h =
      (chainRest index c j (2 * p.val + h.val) (WCT9.digit word ⟨2 * p.val + h.val, hh⟩) 3
        [if h.val = 0 then seeds.1 else seeds.2] >>= fun r => pure (state.1 ++ [r.2], state.2 ++ [r.1])) := by
  have hd := WCT9.digit_le_three word ⟨2 * p.val + h.val, hh⟩
  rw [← chain3_eq _ _ _ _ _ hd]
  simp only [WCT9.childHalf, dif_pos hh, bind_assoc, pure_bind]
theorem childHalf_none (index c j : Nat) (word : WCT9.Rank) (p : Fin 4) (seeds : Digest × Digest)
    (state : List Digest × List Digest) (h : Fin 2) (hh : ¬ 2 * p.val + h.val < 7) :
    WCT9.childHalf index c j word p seeds state h = pure state := by
  simp only [WCT9.childHalf, dif_neg hh]
def bodyRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x26, .x28, .x29]
def bodyW (c : Nat) (A : Nat) : Prop :=
  (PRIVW + 16 ≤ A ∧ A < PRIVW + 32) ∨ (PAIRW ≤ A ∧ A < PAIRW + 32) ∨ (CHAINW + 16 ≤ A ∧ A < CHAINW + 32) ∨
    (CHAINW + 48 ≤ A ∧ A < CHAINW + 80) ∨ (LEAFW ≤ A ∧ A < LEAFW + 128) ∨ (slotV c 0 ≤ A ∧ A < slotV c 7)
structure BodySt (sk : BitVec 256) (j index sel w : Nat) (t : MachineState) : Prop where
  x5 : t.getReg .x5 = 0
  x18 : t.getReg .x18 = BitVec.ofNat 64 j
  x22 : t.getReg .x22 = BitVec.ofNat 64 index
  x24 : t.getReg .x24 = BitVec.ofNat 64 sel
  x25 : t.getReg .x25 = BitVec.ofNat 64 w
  p0 : t.getMem (BitVec.ofNat 64 PRIVW) = sk.extractLsb' 0 64
  p8 : t.getMem (BitVec.ofNat 64 (PRIVW + 8)) = sk.extractLsb' 64 64
  p32 : t.getMem (BitVec.ofNat 64 (PRIVW + 32)) = sk.extractLsb' 128 64
  p40 : t.getMem (BitVec.ofNat 64 (PRIVW + 40)) = sk.extractLsb' 192 64
  p48 : t.getMem (BitVec.ofNat 64 (PRIVW + 48)) = 0
  p56 : t.getMem (BitVec.ofNat 64 (PRIVW + 56)) = 0
  z0 : t.getMem (BitVec.ofNat 64 CHAINW) = 0
  z8 : t.getMem (BitVec.ofNat 64 (CHAINW + 8)) = 0
  z32 : t.getMem (BitVec.ofNat 64 (CHAINW + 32)) = 0
  z40 : t.getMem (BitVec.ofNat 64 (CHAINW + 40)) = 0
theorem BodySt.of {sk : BitVec 256} {j index sel w : Nat} {s t : MachineState} {W : Nat → Prop} {l : List Reg}
    (h : BodySt sk j index sel w s) (hr : RegsExcept s t l)
    (hl : .x5 ∉ l ∧ .x18 ∉ l ∧ .x22 ∉ l ∧ .x24 ∉ l ∧ .x25 ∉ l) (hf : Frame s t W)
    (hW : ¬ W PRIVW ∧ ¬ W (PRIVW + 8) ∧ ¬ W (PRIVW + 32) ∧ ¬ W (PRIVW + 40) ∧ ¬ W (PRIVW + 48) ∧
      ¬ W (PRIVW + 56) ∧ ¬ W CHAINW ∧ ¬ W (CHAINW + 8) ∧ ¬ W (CHAINW + 32) ∧ ¬ W (CHAINW + 40)) :
    BodySt sk j index sel w t := by
  obtain ⟨l5, l18, l22, l24, l25⟩ := hl
  obtain ⟨w0, w8, w32, w40, w48, w56, c0, c8, c32, c40⟩ := hW
  exact ⟨by rw [hr.get l5]; exact h.x5, by rw [hr.get l18]; exact h.x18, by rw [hr.get l22]; exact h.x22,
    by rw [hr.get l24]; exact h.x24, by rw [hr.get l25]; exact h.x25,
    by rw [hf.get (by ao) w0]; exact h.p0, by rw [hf.get (by ao) w8]; exact h.p8,
    by rw [hf.get (by ao) w32]; exact h.p32, by rw [hf.get (by ao) w40]; exact h.p40,
    by rw [hf.get (by ao) w48]; exact h.p48, by rw [hf.get (by ao) w56]; exact h.p56,
    by rw [hf.get (by ao) c0]; exact h.z0, by rw [hf.get (by ao) c8]; exact h.z8,
    by rw [hf.get (by ao) c32]; exact h.z32, by rw [hf.get (by ao) c40]; exact h.z40⟩
structure RowsAt (c j sel n : Nat) (rows : List Digest × List Digest) (t : MachineState) : Prop where
  len1 : rows.1.length = n
  len2 : rows.2.length = n
  leaf : ∀ i < n, DigAt t (LEAFW + leafOff i) (rows.1.getD i 0)
  sig : j = sel → ∀ i < n, DigAt t (slotV c i) (rows.2.getD i 0)
theorem leafOff_lt (i : Nat) (hi : i < 7) : leafOff i + 16 ≤ 128 := by unfold leafOff; split_ifs <;> omega
theorem leafOff_ne (i i' : Nat) (hi : i < 7) (hi' : i' < 7) (hne : i ≠ i') :
    leafOff i ≠ leafOff i' ∧ leafOff i ≠ leafOff i' + 8 ∧ leafOff i + 8 ≠ leafOff i' ∧ leafOff i + 8 ≠ leafOff i' + 8 := by
  unfold leafOff; split_ifs <;> omega
theorem hashInput_priv (t : MachineState) (sk : BitVec 256) {c index q : Nat} (hc : c < 9) (hidx : index < 2 ^ 32)
    (hq : q < 2 ^ 32) (h10 : t.getReg .x10 = BitVec.ofNat 64 PRIVW) (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (p0 : t.getMem (BitVec.ofNat 64 PRIVW) = sk.extractLsb' 0 64)
    (p8 : t.getMem (BitVec.ofNat 64 (PRIVW + 8)) = sk.extractLsb' 64 64)
    (p16 : t.getMem (BitVec.ofNat 64 (PRIVW + 16)) = BitVec.ofNat 64 (hdr8 c))
    (p24 : t.getMem (BitVec.ofNat 64 (PRIVW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * q))
    (p32 : t.getMem (BitVec.ofNat 64 (PRIVW + 32)) = sk.extractLsb' 128 64)
    (p40 : t.getMem (BitVec.ofNat 64 (PRIVW + 40)) = sk.extractLsb' 192 64)
    (p48 : t.getMem (BitVec.ofNat 64 (PRIVW + 48)) = 0) (p56 : t.getMem (BitVec.ofNat 64 (PRIVW + 56)) = 0) :
    hashInput t = toQ (privateInput sk (.inl (header 8 c index 0 q))) := by
  refine hashInput_of_words t _ 0 PRIVW (by rw [privateInput_tweak_length]) h10 (by ao) (by ao) h11 ?_
  rw [wordsOf_priv sk c index q (by omega) hidx hq]
  intro k hk
  interval_cases k
  · exact p0
  · exact p8
  · exact p16
  · exact p24
  · exact p32
  · exact p40
  · exact p48
  · exact p56
theorem slotV_lt (c i : Nat) (hi : i < 7) : slotV c i + 16 ≤ slotV c 7 := by unfold slotV; omega
theorem chainW_bodyW {c i A : Nat} (hi : i < 7) (h : chainW c i A) : bodyW c A := by
  have := leafOff_lt i hi
  have := slotV_lt c i hi
  unfold chainW at h; unfold bodyW
  rcases h with h | h | h | h | h | h
  · right; right; left; exact h
  · right; right; right; left; exact h
  · right; right; right; right; left; subst h; constructor <;> omega
  · right; right; right; right; left; subst h; constructor <;> omega
  · right; right; right; right; right; subst h; unfold slotV at *; constructor <;> omega
  · right; right; right; right; right; subst h; unfold slotV at *; constructor <;> omega
theorem BodySt.of_body {sk : BitVec 256} {j index sel w c : Nat} {s t : MachineState} {W : Nat → Prop} {l : List Reg}
    (hc : c < 9) (h : BodySt sk j index sel w s) (hr : RegsExcept s t l) (hl : ∀ r ∈ l, r ∈ bodyRegs) (hf : Frame s t W)
    (hW : ∀ A, W A → bodyW c A) : BodySt sk j index sel w t := by
  have nb : ∀ A, (A = PRIVW ∨ A = PRIVW + 8 ∨ A = PRIVW + 32 ∨ A = PRIVW + 40 ∨ A = PRIVW + 48 ∨ A = PRIVW + 56 ∨
      A = CHAINW ∨ A = CHAINW + 8 ∨ A = CHAINW + 32 ∨ A = CHAINW + 40) → ¬ W A := by
    intro A hA hw
    have := hW A hw
    unfold bodyW slotV at this
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [PRIVW, PAIRW, CHAINW, LEAFW, SIG] at this <;> omega
  refine h.of hr ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_⟩ hf
    ⟨nb _ (by simp), nb _ (by simp), nb _ (by simp), nb _ (by simp), nb _ (by simp), nb _ (by simp),
      nb _ (by simp), nb _ (by simp), nb _ (by simp), nb _ (by simp)⟩ <;>
    · have := hl _ m; simp [bodyRegs] at this
theorem RowsAt.frame {c j sel n : Nat} {rows : List Digest × List Digest} {s t : MachineState} {W : Nat → Prop}
    (h : RowsAt c j sel n rows s) (hc : c < 9) (hn : n ≤ 7) (hf : Frame s t W)
    (hW : ∀ i < n, ¬ W (LEAFW + leafOff i) ∧ ¬ W (LEAFW + leafOff i + 8) ∧ ¬ W (slotV c i) ∧ ¬ W (slotV c i + 8)) :
    RowsAt c j sel n rows t := by
  refine ⟨h.len1, h.len2, fun i hi => ?_, fun hjs i hi => ?_⟩
  · have := leafOff_lt i (by omega)
    exact (h.leaf i hi).frame hf (by ao) (hW i hi).1 (hW i hi).2.1
  · exact (h.sig hjs i hi).frame hf (by unfold slotV; ao) (hW i hi).2.2.1 (hW i hi).2.2.2
theorem RowsAt.snoc {c j sel n : Nat} {rows : List Digest × List Digest} {t : MachineState} {x y : Digest}
    (h : RowsAt c j sel n rows t) (hl : DigAt t (LEAFW + leafOff n) x) (hs : j = sel → DigAt t (slotV c n) y) :
    RowsAt c j sel (n + 1) (rows.1 ++ [x], rows.2 ++ [y]) t := by
  refine ⟨by simp [h.len1], by simp [h.len2], fun i hi => ?_, fun hjs i hi => ?_⟩
  · by_cases hin : i < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [h.len1]; exact hin), ← List.getD_eq_getElem?_getD]
      exact h.leaf i hin
    · have : i = n := by omega
      subst this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h.len1]), h.len1, Nat.sub_self]; exact hl
  · by_cases hin : i < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [h.len2]; exact hin), ← List.getD_eq_getElem?_getD]
      exact h.sig hjs i hin
    · have : i = n := by omega
      subst this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h.len2]), h.len2, Nat.sub_self]; exact hs hjs
theorem chainW_other {c i i' : Nat} (hc : c < 9) (hi : i < 7) (hi' : i' < 7) (hne : i' ≠ i) :
    ¬ chainW c i (LEAFW + leafOff i') ∧ ¬ chainW c i (LEAFW + leafOff i' + 8) ∧ ¬ chainW c i (slotV c i') ∧
      ¬ chainW c i (slotV c i' + 8) := by
  have h1 := leafOff_lt i hi
  have h2 := leafOff_lt i' hi'
  have h3 := leafOff_ne i' i hi' hi hne
  unfold chainW slotV
  refine ⟨?_, ?_, ?_, ?_⟩ <;> aoh
theorem preI_pI : ∀ c, c < 9 → ∀ p, p < 4 → preI c (2 * p) = pI c p + 20 := by decide +kernel
theorem pI_pos : ∀ c, c < 9 → ∀ p, p < 4 → 1 ≤ pI c p := by decide +kernel
def pairEnd (c p : Nat) : Nat := if p = 3 then lI c else pI c (p + 1)
def pairC : Nat := 19 + (8 + (chainC + chainC))
theorem childHalf_eq' (index c j : Nat) (word : WCT9.Rank) (p : Fin 4) (seeds : Digest × Digest)
    (state : List Digest × List Digest) (h : Fin 2) (i : Nat) (hi : 2 * p.val + h.val = i) (hi7 : i < 7) (d : Nat)
    (hd : WCT9.digit word ⟨i, hi7⟩ = d) (seed : Digest) (hseed : (if h.val = 0 then seeds.1 else seeds.2) = seed) :
    WCT9.childHalf index c j word p seeds state h =
      (chainRest index c j i d 3 [seed] >>= fun r => pure (state.1 ++ [r.2], state.2 ++ [r.1])) := by
  subst hi; subst hd; subst hseed
  exact childHalf_eq index c j word p seeds state h hi7
theorem halves_eq (index c j : Nat) (word : WCT9.Rank) (w : Nat)
    (hword : ∀ i : Fin 7, w / 4 ^ i.val % 4 = WCT9.digit word i) (p : Nat) (hp : p < 4) (seeds : Digest × Digest)
    (rows : List Digest × List Digest) :
    (List.finRange 2).foldlM (WCT9.childHalf index c j word ⟨p, hp⟩ seeds) rows =
      if p < 3 then
        (chainRest index c j (2 * p) (w / 4 ^ (2 * p) % 4) 3 [seeds.1] >>= fun r =>
          chainRest index c j (2 * p + 1) (w / 4 ^ (2 * p + 1) % 4) 3 [seeds.2] >>= fun r' =>
            pure (rows.1 ++ [r.2] ++ [r'.2], rows.2 ++ [r.1] ++ [r'.1]))
      else
        (chainRest index c j (2 * p) (w / 4 ^ (2 * p) % 4) 3 [seeds.1] >>= fun r =>
          pure (rows.1 ++ [r.2], rows.2 ++ [r.1])) := by
  rw [show List.finRange 2 = [0, 1] from rfl]
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
  rw [childHalf_eq' index c j word ⟨p, hp⟩ seeds rows 0 (2 * p) rfl (by omega) _ (hword ⟨2 * p, by omega⟩).symm
    seeds.1 rfl]
  simp only [bind_assoc, pure_bind]
  by_cases hp3 : p < 3
  · rw [if_pos hp3]
    refine bind_congr fun r => ?_
    rw [childHalf_eq' index c j word ⟨p, hp⟩ seeds _ 1 (2 * p + 1) rfl (by omega) _
      (hword ⟨2 * p + 1, by omega⟩).symm seeds.2 rfl]
  · rw [if_neg hp3]
    refine bind_congr fun r => ?_
    rw [childHalf_none index c j word ⟨p, hp⟩ seeds _ 1 (by simp; omega)]
section pair
variable {im : Image} {sk : BitVec 256}
theorem pair_unit (hcode : NewCodeAt im) {c p j index sel w : Nat} {word : WCT9.Rank} (hc : c < 9) (hp : p < 4)
    (hj : j < 128) (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64)
    (hword : ∀ i : Fin 7, w / 4 ^ i.val % 4 = WCT9.digit word i)
    {rows : List Digest × List Digest} {s : MachineState} (hpc : s.pc = pcOf (pI c p))
    (hb : BodySt sk j index sel w s) (hr : RowsAt c j sel (2 * p) rows s) :
    TBSim im sk s pairC (pairBody index c j word ⟨p, hp⟩ rows) (fun rows' t =>
      t.pc = pcOf (pairEnd c p) ∧ BodySt sk j index sel w t ∧ RowsAt c j sel (min (2 * p + 2) 7) rows' t ∧
        RegsExcept s t bodyRegs ∧ Frame s t (bodyW c) ∧
        (j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 7 →
          t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A))) := by
  obtain ⟨t1, s1, e1, p1, x10, x11, x12, m16, m24, r1, f1⟩ :=
    step_P hcode hc hp s hpc hb.x18 hb.x22 (by omega)
  have hb1 : BodySt sk j index sel w t1 := hb.of_body hc r1 (by simp [bodyRegs]) f1 (fun A hA => by
    unfold bodyW; rcases hA with rfl | rfl <;> (left; constructor <;> ao))
  have hq := hashInput_priv t1 sk hc (by omega : index < 2 ^ 32) (by omega : 4 * j + p < 2 ^ 32) x10 x11 hb1.p0 hb1.p8
    m16 m24 hb1.p32 hb1.p40 hb1.p48 hb1.p56
  unfold pairBody
  refine (TBSim.steps s1 (TBSim.privatePair_bind' (W := chainC + chainC) e1 hb1.x5
    (hashArgs_const t1 PRIVW 64 PAIRW x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao)) hq
    (fun a => ?_))).mono (by unfold pairC; omega) (fun _ _ h => h)
  set u := writeHash t1 a with hu
  have fu := Frame.writeHash t1 a PAIRW x12 (by ao)
  have sd0 : DigAt u PAIRW (a.extractLsb' 0 128) := DigAt.writeHash_lo t1 a PAIRW x12 (by ao)
  have sd1 : DigAt u (PAIRW + 16) (a.extractLsb' 128 128) := DigAt.writeHash_hi t1 a PAIRW x12 (by ao)
  have hbu : BodySt sk j index sel w u := hb1.of_body hc (fun x _ => getReg_writeHash t1 a x : RegsExcept t1 u [])
    (by simp) fu (fun A hA => by unfold bodyW; right; left; exact hA)
  have hupc : u.pc = pcOf (preI c (2 * p)) := by
    rw [hu, pc_writeHash, p1, preI_pI c hc p hp, pcOf_add4]
  have fsu : Frame s u (bodyW c) := (f1.trans fu).mono (fun A _ hA => by
    unfold bodyW
    rcases hA with (rfl | rfl) | hA
    · left; constructor <;> ao
    · left; constructor <;> ao
    · right; left; exact hA)
  have rsu : RegsExcept s u bodyRegs := (r1.trans (fun x _ => getReg_writeHash t1 a x : RegsExcept t1 u [])).mono
    (by simp [bodyRegs])
  have hru : RowsAt c j sel (2 * p) rows u := hr.frame hc (by omega) (f1.trans fu) (fun i hi => by
    have := leafOff_lt i (by omega)
    unfold slotV
    refine ⟨?_, ?_, ?_, ?_⟩ <;> aoh)
  have hpre1 : ChainPre c (2 * p) j index sel w (a.extractLsb' 0 128) u :=
    ⟨hupc, hbu.x5, hbu.x18, hbu.x22, hbu.x24, hbu.x25, by rw [show 2 * p % 2 = 0 by omega]; simpa using sd0,
      hbu.z0, hbu.z8, hbu.z32, hbu.z40⟩
  rw [halves_eq index c j word w hword p hp]
  split_ifs with hp3
  · refine (TBSim.bind (W₂ := chainC) (chain_unit hcode hc (by omega) hj hsel hidx hw hpre1)
      (fun r t ht => ?_)).mono (by omega) (fun _ _ h => h)
    obtain ⟨tpc, tleaf, tsig, tregs, tframe, tnos⟩ := ht
    have hnu : j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 7 →
        u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun _ A hA h1 h2 =>
      (f1.trans fu).get hA (by unfold slotV at h1 h2; intro h'; rcases h' with (h' | h') | h' <;> aoh)
    have hbt : BodySt sk j index sel w t := hbu.of_body hc tregs (by simp [chainRegs, bodyRegs]) tframe
      (fun A hA => chainW_bodyW (by omega) hA)
    have sdt : DigAt t (PAIRW + 16 * ((2 * p + 1) % 2)) (a.extractLsb' 128 128) := by
      rw [show (2 * p + 1) % 2 = 1 by omega, Nat.mul_one]
      refine sd1.frame tframe (by ao) ?_ ?_ <;> (unfold chainW slotV; have := leafOff_lt (2 * p) (by omega); aoh)
    have hpre2 : ChainPre c (2 * p + 1) j index sel w (a.extractLsb' 128 128) t :=
      ⟨by rw [tpc]; unfold lcEnd; rw [if_neg (by omega), if_pos (by omega)], hbt.x5, hbt.x18, hbt.x22, hbt.x24,
        hbt.x25, sdt, hbt.z0, hbt.z8, hbt.z32, hbt.z40⟩
    have hrt : RowsAt c j sel (2 * p + 1) (rows.1 ++ [r.2], rows.2 ++ [r.1]) t :=
      (hru.frame hc (by omega) tframe (fun i hi => chainW_other hc (by omega) (by omega) (by omega))).snoc tleaf tsig
    refine (TBSim.bind (W₂ := 0) (chain_unit hcode hc (by omega) hj hsel hidx hw hpre2) (fun r' t' ht' => ?_)).mono
      (by omega) (fun _ _ h => h)
    obtain ⟨tpc', tleaf', tsig', tregs', tframe', tnos'⟩ := ht'
    refine TBSim.pure ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [tpc']; unfold lcEnd pairEnd
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show (2 * p + 1 + 1) / 2 = p + 1 by omega]
    · exact hbt.of_body hc tregs' (by simp [chainRegs, bodyRegs]) tframe' (fun A hA => chainW_bodyW (by omega) hA)
    · rw [show min (2 * p + 2) 7 = 2 * p + 1 + 1 by omega]
      exact (hrt.frame hc (by omega) tframe' (fun i hi => chainW_other hc (by omega) (by omega) (by omega))).snoc
        tleaf' tsig'
    · exact ((rsu.trans tregs).trans tregs').mono (by simp [chainRegs, bodyRegs])
    · exact ((fsu.trans tframe).trans tframe').mono (fun A _ hA => by
        rcases hA with (hA | hA) | hA
        · exact hA
        · exact chainW_bodyW (by omega) hA
        · exact chainW_bodyW (by omega) hA)
    · intro hjs A hA h1 h2; rw [tnos' hjs A hA h1 h2, tnos hjs A hA h1 h2, hnu hjs A hA h1 h2]
  · have hp3' : p = 3 := by omega
    subst hp3'
    refine (TBSim.bind (W₂ := 0) (chain_unit hcode hc (by omega) hj hsel hidx hw hpre1) (fun r t ht => ?_)).mono
      (by omega) (fun _ _ h => h)
    obtain ⟨tpc, tleaf, tsig, tregs, tframe, tnos⟩ := ht
    have hnu : j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 7 →
        u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun _ A hA h1 h2 =>
      (f1.trans fu).get hA (by unfold slotV at h1 h2; intro h'; rcases h' with (h' | h') | h' <;> aoh)
    refine TBSim.pure ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [tpc]; unfold lcEnd pairEnd; rw [if_pos (by omega), if_pos rfl]
    · exact hbu.of_body hc tregs (by simp [chainRegs, bodyRegs]) tframe (fun A hA => chainW_bodyW (by omega) hA)
    · exact (hru.frame hc (by omega) tframe (fun i hi => chainW_other hc (by omega) (by omega) (by omega))).snoc
        tleaf tsig
    · exact (rsu.trans tregs).mono (by simp [chainRegs, bodyRegs])
    · exact (fsu.trans tframe).mono (fun A _ hA => by
        rcases hA with hA | hA
        · exact hA
        · exact chainW_bodyW (by omega) hA)
    · intro hjs A hA h1 h2; rw [tnos hjs A hA h1 h2, hnu hjs A hA h1 h2]
end pair
end ClaudeWCT.W9.Machine.Sign
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash privatePair privateInput)
open SphincsSecurity (bytesLE bytesLE_length)
theorem hashInput_leaf (t : MachineState) {c j index : Nat} (ends : List Digest) (hlen : ends.length = 7) (hc : c < 9)
    (hidx : index < 2 ^ 32) (hj : j < 2 ^ 32) (h10 : t.getReg .x10 = BitVec.ofNat 64 LEAFW)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 128) (he : ∀ i < 7, DigAt t (LEAFW + leafOff i) (ends.getD i 0))
    (m16 : t.getMem (BitVec.ofNat 64 (LEAFW + 16)) = BitVec.ofNat 64 (hdr6 c))
    (m24 : t.getMem (BitVec.ofNat 64 (LEAFW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * j)) :
    hashInput t = toQ (pad64 (leafIn index c j ends)) := by
  refine hashInput_of_words t _ 1 LEAFW (by rw [pad64_of_aligned _ (by rw [leafIn_len _ _ _ _ hlen]),
    leafIn_len _ _ _ _ hlen]) h10 (by ao) (by ao) h11 ?_
  rw [wordsOf_leaf index c j ends hlen (by omega) hidx hj]
  match ends, hlen with
  | [e0, e1, e2, e3, e4, e5, e6], _ =>
    have d0 := he 0 (by norm_num); have d1 := he 1 (by norm_num); have d2 := he 2 (by norm_num)
    have d3 := he 3 (by norm_num); have d4 := he 4 (by norm_num); have d5 := he 5 (by norm_num)
    have d6 := he 6 (by norm_num)
    simp only [leafOff, List.getD_cons_zero, List.getD_cons_succ] at d0 d1 d2 d3 d4 d5 d6
    simp only [if_true, show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 0 by decide,
      show (4 : Nat) ≠ 0 by decide, show (5 : Nat) ≠ 0 by decide, show (6 : Nat) ≠ 0 by decide, if_false,
      Nat.add_zero] at d0 d1 d2 d3 d4 d5 d6
    intro k hk
    interval_cases k <;> simp only [List.getD_cons_zero, List.drop_succ_cons, List.drop_zero, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, wordsOf_bytesLE16, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero]
    · exact d0.1
    · exact d0.2
    · exact m16
    · exact m24
    · exact d1.1
    · exact d1.2
    · exact d2.1
    · exact d2.2
    · exact d3.1
    · exact d3.2
    · exact d4.1
    · exact d4.2
    · exact d5.1
    · exact d5.2
    · exact d6.1
    · exact d6.2
theorem leafI_pI : ∀ c, c < 9 → leafI c = pI c 0 := by decide +kernel
theorem tI_pos : ∀ c, c < 9 → 1 ≤ tI c := by decide +kernel
def childW (c j : Nat) (A : Nat) : Prop :=
  bodyW c A ∨ (HEAPW + 16 * (128 + j) ≤ A ∧ A < HEAPW + 16 * (128 + j) + 32)
def childC : Nat := 4 * pairC + (16 + (16 + 0))
section child
variable {im : Image} {sk : BitVec 256}
theorem child_unit (hcode : NewCodeAt im) {c j index sel w : Nat} {word : WCT9.Rank} (hc : c < 9) (hj : j < 128)
    (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64)
    (hword : ∀ i : Fin 7, w / 4 ^ i.val % 4 = WCT9.digit word i) {s : MachineState}
    (hpc : s.pc = pcOf (leafI c)) (hb : BodySt sk j index sel w s) :
    TBSim im sk s childC (WCT9.buildChild index c j word) (fun rv t =>
      t.pc = pcOf (tI c) ∧ BodySt sk j index sel w t ∧ DigAt t (HEAPW + 16 * (128 + j)) rv.1 ∧
        (j = sel → rv.2.length = 7 ∧ ∀ i < 7, DigAt t (slotV c i) (rv.2.getD i 0)) ∧
        RegsExcept s t bodyRegs ∧ Frame s t (childW c j) ∧
        (j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 7 →
          t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A))) := by
  rw [WCT9.buildChild_factor, childRows_eq]
  simp only [bind_assoc]
  have h0 : RowsAt c j sel (2 * 0) ([], []) s := ⟨rfl, rfl, fun i hi => absurd hi (by omega), fun _ i hi => absurd hi (by omega)⟩
  have fw : ∀ {t1 t2 : MachineState}, Frame s t1 (bodyW c) → Frame t1 t2 (bodyW c) → Frame s t2 (bodyW c) :=
    fun f1 f2 => (f1.trans f2).mono (fun A _ hA => by rcases hA with hA | hA <;> exact hA)
  have rw' : ∀ {t1 t2 : MachineState}, RegsExcept s t1 bodyRegs → RegsExcept t1 t2 bodyRegs →
      RegsExcept s t2 bodyRegs := fun r1 r2 => (r1.trans r2).mono (by simp)
  refine (TBSim.bind (W₂ := 3 * pairC + (16 + (16 + 0)))
    (pair_unit hcode hc (by norm_num : 0 < 4) hj hsel hidx hw hword (by rw [hpc, leafI_pI c hc]) hb h0)
    (fun r1 t1 ht1 => ?_)).mono (by unfold childC; omega) (fun _ _ h => h)
  obtain ⟨p1, b1, rr1, g1, f1, n1⟩ := ht1
  refine (TBSim.bind (W₂ := 2 * pairC + (16 + (16 + 0)))
    (pair_unit hcode hc (by norm_num : 1 < 4) hj hsel hidx hw hword (by rw [p1]; rfl) b1 rr1)
    (fun r2 t2 ht2 => ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p2, b2, rr2, g2, f2, n2⟩ := ht2
  refine (TBSim.bind (W₂ := pairC + (16 + (16 + 0)))
    (pair_unit hcode hc (by norm_num : 2 < 4) hj hsel hidx hw hword (by rw [p2]; rfl) b2 rr2)
    (fun r3 t3 ht3 => ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p3, b3, rr3, g3, f3, n3⟩ := ht3
  refine (TBSim.bind (W₂ := 16 + (16 + 0))
    (pair_unit hcode hc (by norm_num : 3 < 4) hj hsel hidx hw hword (by rw [p3]; rfl) b3 rr3)
    (fun rows t4 ht4 => ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p4, b4, rr4, g4, f4, n4⟩ := ht4
  have f14 : Frame s t4 (bodyW c) := fw (fw (fw f1 f2) f3) f4
  have g14 : RegsExcept s t4 bodyRegs := rw' (rw' (rw' g1 g2) g3) g4
  obtain ⟨t5, s5, e5, p5, x10, x11, x12, m16, m24, r5, f5⟩ :=
    step_L hcode hc t4 (by rw [p4]; rfl) b4.x18 b4.x22 (by omega)
  have hrows : RowsAt c j sel 7 rows t5 := rr4.frame hc (by norm_num) f5 (fun i hi => by
    have := leafOff_lt i (by omega)
    have := leafOff_ne i 1 (by omega) (by norm_num)
    unfold slotV leafOff at *
    refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs at * <;> aoh)
  have hq := hashInput_leaf t5 rows.1 hrows.len1 hc (by omega) (by omega) x10 x11 hrows.leaf m16 m24
  have hb5 : BodySt sk j index sel w t5 := b4.of_body hc r5 (by simp [bodyRegs]) f5 (fun A hA => by
    unfold bodyW; rcases hA with rfl | rfl <;> (right; right; right; right; left; constructor <;> ao))
  have hbl : (toQ (pad64 (leafIn index c j rows.1))).blocks = 2 := by
    rw [pad64_of_aligned _ (by rw [leafIn_len _ _ _ _ hrows.len1]),
      blocks_toQ ⟨by rw [leafIn_len _ _ _ _ hrows.len1]; norm_num, by rw [leafIn_len _ _ _ _ hrows.len1]⟩,
      leafIn_len _ _ _ _ hrows.len1]
  rw [leafHash_eq]
  refine (TBSim.steps s5 (TBSim.shortHash_bind' (W := 0) (f := fun root => pure (root, rows.2)) e5 hb5.x5
    (hashArgs_const t5 LEAFW 128 (HEAPW + 16 * (j + 128)) x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao))
    hq (fun a => TBSim.pure ?_))).mono (by rw [hbl]; split <;> omega) (fun _ _ h => h)
  have fh := Frame.writeHash t5 a (HEAPW + 16 * (j + 128)) x12 (by ao)
  refine ⟨?_, ?_, ?_, fun hjs => ⟨by rw [hrows.len2], fun i hi => ?_⟩, ?_, ?_, ?_⟩
  · rw [pc_writeHash, p5, pcOf_pred4 _ (tI_pos c hc)]
  · exact hb5.of (fun x _ => getReg_writeHash t5 a x : RegsExcept t5 (writeHash t5 a) []) (by simp) fh
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ao)
  · rw [show 128 + j = j + 128 by omega]; exact DigAt.writeHash_lo t5 a _ x12 (by ao)
  · exact (hrows.sig hjs i hi).frame fh (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
  · exact (g14.trans (r5.trans (fun x _ => getReg_writeHash t5 a x : RegsExcept t5 (writeHash t5 a) []))).mono
      (by simp [bodyRegs])
  · refine ((f14.trans f5).trans fh).mono (fun A _ hA => ?_)
    unfold childW
    rcases hA with (hA | hA) | hA
    · left; exact hA
    · left; unfold bodyW; rcases hA with rfl | rfl <;> (right; right; right; right; left; constructor <;> ao)
    · right; constructor <;> omega
  · intro hjs A hA h1 h2
    rw [fh.get hA (by unfold slotV at h1 h2; intro h'; aoh), f5.get hA (by unfold slotV at h1 h2; intro h'; aoh),
      n4 hjs A hA h1 h2, n3 hjs A hA h1 h2, n2 hjs A hA h1 h2, n1 hjs A hA h1 h2]
end child
end ClaudeWCT.W9.Machine.Sign
end
