import SigGolfCandidate.T3M.Verify.ChainGood
import SigGolfCandidate.T3M.Verify.Decode
import SigGolfCandidate.T3M.Verify.Words
import SigGolfCandidate.T3M.Verify.LayerSem
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3 OracleComp
theorem mapM_congr' {α β : Type} {f g : α → M β} : ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h x (by simp), mapM_congr' l (fun y hy => h y (by simp [hy]))]
theorem finRange_mapM {β : Type} (n : Nat) (g : Nat → M β) :
    (List.finRange n).mapM (fun i => g i.val) = (List.range n).mapM g := by
  have e : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem (by simp)
    intro i h1 h2; simp
  rw [← e, List.mapM_map]; rfl
theorem foldlM_app_mapM (f : Nat → M Digest) : ∀ (n a : Nat) (acc : List Digest),
    (List.range' a n).foldlM (fun e i => do let v ← f i; pure (e ++ [v])) acc =
      (fun l => acc ++ l) <$> (List.range' a n).mapM f
  | 0, a, acc => by simp
  | n + 1, a, acc => by
    rw [List.range'_succ, List.foldlM_cons, List.mapM_cons]
    simp only [bind_assoc, pure_bind, foldlM_app_mapM f n (a + 1), map_bind, bind_map_left, map_pure]
    congr 1; funext v
    rw [← bind_pure_comp]
    congr 1; funext l; simp
namespace QCtx
theorem sum_range'_eq (f g : Nat → Nat) (a n : Nat) (h : ∀ i, a ≤ i → i < a + n → f i = g i) :
    ((List.range' a n).map f).sum = ((List.range' a n).map g).sum := by
  congr 1
  apply List.map_congr_left
  intro i hi
  have := List.mem_range'_1.mp hi
  exact h i this.1 this.2
end QCtx
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
namespace LCtx
def lowP (c : LCtx) : M (List Digest) := (List.range' 0 42).foldlM c.chainF [] >>= fun e => c.chainF e 42
def lowCost (c : LCtx) : Nat := c.chainsCost 0 42 + chainCost 42 c.ck
theorem lower_good (c : LCtx) (hc : c.ok) (hi0 : c.i0 = 0) (hko : c.koff = 0) (hck : c.ck < 8) {s0 : MachineState}
    (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2) (h0 : c.Orig0 s0)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t, c.ChainOut s0 43 ends t → Verify.GoodQ t N C Q A (K ends))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    Verify.GoodQ s (N + 1720) (C + c.lowCost) Q (A + c.lowCost) (Verify.ccM c.lowP K) := by
  unfold lowP
  rw [Verify.ccM_bind]
  have H := c.chains_good hc hk h0 (fun _ => hko) (fun e => Verify.ccM (c.chainF e 42) K)
    (N + 40) (C + chainCost 42 c.ck) (A + chainCost 42 c.ck) Q
    (fun ends t ht => c.ck_good hc hk h0 (fun _ => hko) hck K N C A Q hK ends t ht) 42 0 (by omega) (by omega) [] s hs
  refine H.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
  · unfold lowCost; omega
  · unfold lowCost; omega
def coreChain (c : LCtx) (D : List Nat) (i : Nat) : M Digest :=
  chainP c.lay c.tree c.leaf i (D.getD i 0) (maxDigit c.lay i - D.getD i 0) (wchainPads c.w c.lay i).1
    (wchainPads c.w c.lay i).2 (wchainHeaderPad c.w c.lay i) (wvalue c.w c.lay i)
theorem chainCount_lower (lay : Layer) (h : lay ≠ 0) : chainCount lay = 43 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals rfl
theorem fit_chain (c : LCtx) (hlay : c.lay ≠ 0) (hko : c.koff = 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0) (hS6 : c.S6 = 0x800 + chainBlock c.lay 42 + 1024) (i : Nat) (hi : i < 43) :
    chainP c.lay c.tree c.leaf (i + c.koff) (c.dig i) (7 - c.dig i) (c.pad0 i) (c.pad1 i) (c.padHeader i) (c.val i) =
      c.coreChain D i := by
  unfold coreChain
  have hw : maxDigit c.lay i = 7 := by simp [maxDigit, hlay]
  rw [← hD i hi, hw, hko, Nat.add_zero]
  have hn := chainCount_lower c.lay hlay
  have e : c.blk i - 0x800 = chainBlock c.lay i := by
    unfold blk chainBlock at *; rw [hS6]; rw [hn] at *; simp only at *; omega
  unfold pad0 pad1 padHeader val wchainPads wchainHeaderPad wvalue
  rw [e, wdig_hi, show chainBlock c.lay i + 16 + 8 = chainBlock c.lay i + 24 by omega]
theorem lowP_eq (c : LCtx) (hlay : c.lay ≠ 0) (hko : c.koff = 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0) (hS6 : c.S6 = 0x800 + chainBlock c.lay 42 + 1024) :
    c.lowP = (List.finRange 43).mapM fun i => c.coreChain D i.val := by
  rw [finRange_mapM, List.range_eq_range', show (43 : Nat) = 42 + 1 from rfl, List.range'_append_1.symm,
    List.mapM_append]
  unfold lowP
  have hF : (List.range' 0 42).foldlM c.chainF [] = (fun l => [] ++ l) <$> (List.range' 0 42).mapM
      (fun i => chainP c.lay c.tree c.leaf (i + c.koff) (c.dig i) (7 - c.dig i) (c.pad0 i) (c.pad1 i) (c.padHeader i) (c.val i)) :=
    foldlM_app_mapM _ 42 0 []
  rw [hF, mapM_congr' (List.range' 0 42) (fun i hi => c.fit_chain hlay hko D hD hS6 i (by
    have := List.mem_range'_1.mp hi; omega))]
  have h42 := c.fit_chain hlay hko D hD hS6 42 (by omega)
  unfold chainF
  rw [h42]
  simp [List.range'_one]
theorem decode_lower_sum (lay : Layer) (hlay : lay ≠ 0) (value : Digest) (ds : List Nat)
    (h : decode lay value = some ds) : ds.length = 43 ∧ ds.sum = target lay := by
  unfold decode at h
  split at h
  · cases h
  · simp only [if_neg hlay] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      have hl : (dataDigits lay value).length = 42 := by simp [dataDigits, dataCount, hlay]
      refine ⟨by simp [hl], ?_⟩
      rw [List.sum_append, List.sum_cons, List.sum_nil]
      omega
    · cases h
theorem sum_dig (c : LCtx) (D : List Nat) (hD : ∀ i < 43, c.dig i = D.getD i 0) (hl : D.length = 43) :
    ((List.range' 0 43).map c.dig).sum = D.sum := by
  have hE : D = (List.range' 0 43).map fun i => D.getD i 0 := by
    apply List.ext_getElem (by simp [hl])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range']
    rw [show 0 + 1 * i = i by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  conv_rhs => rw [hE]
  exact QCtx.sum_range'_eq _ _ 0 43 (fun i _ hi => hD i (by omega))
theorem lowCost_accept (c : LCtx) (hck : c.ck < 8) (D : List Nat) (hD : ∀ i < 43, c.dig i = D.getD i 0)
    (hl : D.length = 43) (T : Nat) (hT : D.sum = T) : c.lowCost + c.zSum 0 43 + 9 * T = 2950 := by
  have := c.chainsCost_lower hck T (by rw [c.sum_dig D hD hl, hT])
  unfold lowCost
  omega
end LCtx
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
def leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) : HashInput :=
  SphincsSecurity.bytesLE 16 (ends.getD 0 0) ++ SphincsSecurity.bytesLE 16 (header 2 lay.val tree 0 leaf) ++
    (ends.drop 1).flatMap (SphincsSecurity.bytesLE 16)
theorem leafHash_eq (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    leafHash lay tree leaf ends = shortHash (leafInput lay tree leaf ends) := rfl
def dw (e : Digest) : List (BitVec 64) := [e.extractLsb' 0 64, e.extractLsb' 64 64]
theorem flatMap_length16 : ∀ (L : List Digest), (L.flatMap (SphincsSecurity.bytesLE 16)).length = 16 * L.length
  | [] => rfl
  | e :: L => by
    rw [List.flatMap_cons, List.length_append, flatMap_length16 L, SphincsSecurity.bytesLE_length]; simp; ring
theorem leafInput_length (lay : Layer) (tree leaf : Nat) (ends : List Digest) (h : 1 ≤ ends.length) :
    (leafInput lay tree leaf ends).length = 16 * (ends.length + 1) := by
  unfold leafInput
  rw [List.length_append, List.length_append, flatMap_length16, SphincsSecurity.bytesLE_length,
    SphincsSecurity.bytesLE_length, List.length_drop]
  omega
theorem wordsOf_leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    wordsOf (leafInput lay tree leaf ends) =
      dw (ends.getD 0 0) ++ [BitVec.ofNat 64 (hdr0 2 lay.val tree 0), BitVec.ofNat 64 (hdr1 tree leaf)] ++
        (ends.drop 1).flatMap dw := by
  unfold leafInput
  rw [wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]), wordsOf_bytesLE16, wordsOf_header,
    wordsOf_flatMap16]
  rfl
theorem readWords_digs (t : MachineState) : ∀ (L : List Digest) (A : Nat),
    (∀ j < L.length, DigAt t (A + 16 * j) (L.getD j 0)) →
      t.readWords (BitVec.ofNat 64 A) (2 * L.length) = L.flatMap dw
  | [], _, _ => rfl
  | e :: L, A, h => by
    rw [List.length_cons, show 2 * (L.length + 1) = 2 + 2 * L.length by ring, readWords_add, readWords_two,
      show A + 8 * 2 = A + 16 by ring, readWords_digs t L (A + 16) (fun j hj => by
        have := h (j + 1) (by simp; omega)
        rwa [show A + 16 * (j + 1) = A + 16 + 16 * j by ring, List.getD_cons_succ] at this),
      List.flatMap_cons]
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] at h0
    rw [h0.1, h0.2]; rfl
theorem getD_drop1 (L : List Digest) (j : Nat) : (L.drop 1).getD j 0 = L.getD (j + 1) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2; omega
theorem lowLeaf_hashInput (t : MachineState) (lay : Layer) (tree leaf : Nat) (ends : List Digest)
    (hn : ends.length = 43) (h10 : t.getReg .x10 = BitVec.ofNat 64 0x300)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 704) (hS : ∀ j < 43, DigAt t (slotL j) (ends.getD j 0))
    (hT0 : t.getMem (BitVec.ofNat 64 0x310) = BitVec.ofNat 64 (hdr0 2 lay.val tree 0))
    (hT1 : t.getMem (BitVec.ofNat 64 0x318) = BitVec.ofNat 64 (hdr1 tree leaf)) :
    hashInput t = toQ (pad64 (leafInput lay tree leaf ends)) ∧ (toQ (pad64 (leafInput lay tree leaf ends))).blocks = 11 := by
  have hl : (leafInput lay tree leaf ends).length = 64 * (10 + 1) := by
    rw [leafInput_length _ _ _ _ (by omega), hn]
  rw [pad64_of_aligned _ (by simp [hl])]
  refine ⟨?_, by rw [blocks_toQ ⟨by simp [hl], by simp [hl]⟩, hl]⟩
  apply hashInput_toQ t _ 10 0x300 hl h10 (by norm_num) (by norm_num) (by simpa using h11) (by norm_num)
  rw [wordsOf_leafInput, show 8 * (10 + 1) = 2 + (2 + 2 * (ends.drop 1).length) by simp [hn],
    readWords_add, readWords_add, readWords_two, readWords_two]
  have e0 := hS 0 (by omega)
  rw [show slotL 0 = 0x300 from rfl] at e0
  rw [show 0x300 + 8 * 2 = 0x310 by rfl, show 0x310 + 8 = 0x318 by rfl, show 0x310 + 8 * 2 = 0x320 by rfl,
    e0.1, show 0x300 + 8 = (0x300 : Nat) + 8 from rfl, e0.2, hT0, hT1,
    readWords_digs t (ends.drop 1) 0x320 (fun j hj => by
      rw [getD_drop1]
      have := hS (j + 1) (by simp at hj; omega)
      rwa [show slotL (j + 1) = 0x320 + 16 * j by unfold slotL; simp; omega] at this)]
  rfl
theorem topLeaf_hashInput (t : MachineState) (tree leaf : Nat) (ends : List Digest)
    (hn : ends.length = 54) (h10 : t.getReg .x10 = BitVec.ofNat 64 0x200)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 896) (hS : ∀ j < 54, DigAt t (slotT j) (ends.getD j 0))
    (hT0 : t.getMem (BitVec.ofNat 64 0x210) = BitVec.ofNat 64 (hdr0 2 (0 : Layer).val tree 0))
    (hT1 : t.getMem (BitVec.ofNat 64 0x218) = BitVec.ofNat 64 (hdr1 tree leaf))
    (hZ0 : t.getMem (BitVec.ofNat 64 0x570) = 0) (hZ1 : t.getMem (BitVec.ofNat 64 0x578) = 0) :
    hashInput t = toQ (pad64 (leafInput 0 tree leaf ends)) ∧ (toQ (pad64 (leafInput 0 tree leaf ends))).blocks = 14 := by
  have hl0 : (leafInput 0 tree leaf ends).length = 880 := by
    rw [leafInput_length _ _ _ _ (by omega), hn]
  have hl : (pad64 (leafInput 0 tree leaf ends)).length = 64 * (13 + 1) := by
    unfold pad64; rw [List.length_append, List.length_replicate, hl0]
  refine ⟨?_, by rw [blocks_toQ ⟨by simp [hl], by simp [hl]⟩, hl]⟩
  apply hashInput_toQ t _ 13 0x200 hl h10 (by norm_num) (by norm_num) (by simpa using h11) (by norm_num)
  rw [Verify.wordsOf_pad64 _ (by rw [hl0]), hl0, wordsOf_leafInput,
    show 8 * (13 + 1) = 2 + (2 + (2 * (ends.drop 1).length + 2)) by simp [hn],
    readWords_add, readWords_add, readWords_add, readWords_two, readWords_two, readWords_two]
  have e0 := hS 0 (by omega)
  rw [show slotT 0 = 0x200 from rfl] at e0
  have hd : (ends.drop 1).length = 53 := by simp [hn]
  rw [show 0x200 + 8 * 2 = 0x210 by rfl, show 0x210 + 8 = 0x218 by rfl, show 0x210 + 8 * 2 = 0x220 by rfl,
    e0.1, e0.2, hT0, hT1,
    readWords_digs t (ends.drop 1) 0x220 (fun j hj => by
      rw [getD_drop1]
      have := hS (j + 1) (by simp at hj; omega)
      rwa [show slotT (j + 1) = 0x220 + 16 * j by unfold slotT; simp; omega] at this),
    hd, show 0x220 + 8 * (2 * 53) = 0x570 by rfl, show 0x570 + 8 = 0x578 by rfl, hZ0, hZ1]
  simp [List.append_assoc, dw]
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)
def keepLfAll (lay : Nat) : List Reg :=
  if lay = 0 then [.x1, .x2, .x6, .x7, .x8, .x9, .x12, .x13, .x16, .x17, .x19, .x20, .x21, .x22, .x23,
    .x24, .x25, .x26, .x28, .x29, .x30, .x31]
  else [.x1, .x2, .x7, .x8, .x9, .x12, .x13, .x16, .x17, .x19, .x20, .x21, .x22, .x23,
    .x24, .x25, .x26, .x29, .x30, .x31]
def leafCheck (lay p : Nat) : Bool :=
  specB [] [] baseK (runAt (leafK lay) [] (p + retOff lay) [.jmp]) (specLf lay) [] (postLf lay) (keepLfAll lay)
def leafChecks (lay lo n : Nat) : Bool := (List.range' lo n).all fun c => leafCheck lay (trPc lay c)
set_option maxRecDepth 100000 in
theorem leafChecks_3 : leafChecks 3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem leafChecks_2 : leafChecks 2 0 64 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem leafChecks_1 : leafChecks 1 0 64 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem leafChecks_0 : leafChecks 0 0 128 = true := by decide +kernel
theorem leafCheck_at (lay c : Nat) (hlay : lay < 4) (hc : c < nCopy lay) : leafCheck lay (trPc lay c) = true := by
  obtain ⟨n3, n2, n1, n0⟩ := nCopy_eq
  have hall : ∀ n, leafChecks lay 0 n = true → c < n → leafCheck lay (trPc lay c) = true :=
    fun n h h2 => List.all_eq_true.mp h c (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
  interval_cases lay
  · exact hall 128 leafChecks_0 (by omega)
  · exact hall 64 leafChecks_1 (by omega)
  · exact hall 64 leafChecks_2 (by omega)
  · exact hall 1 leafChecks_3 (by omega)
def lfBase (lay : Nat) : Nat := if lay = 0 then 512 else 768
def lfBytes (lay : Nat) : Nat := if lay = 0 then 896 else 704
def lfBlocks (lay : Nat) : Nat := if lay = 0 then 14 else 11
def lfSlot (lay j : Nat) : Nat := if lay = 0 then slotT j else slotL j
def stabBits (lay : Nat) : Nat := if lay = 1 then 7 else 6
def lfSteps (lay : Nat) : Nat := if lay = 0 then 13 else 12
def lfKeepK (lay : Nat) : List (Reg × Word) :=
  [(.x2, 0x3fe00), (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6),
   (.x31, 7), (.x22, BitVec.ofNat 64 (s6v lay))] ++
  (if lay = 0 then [] else [(.x28, BitVec.ofNat 64 (headerBank 0 0)), (.x20, BitVec.ofNat 64 M1c),
    (.x21, BitVec.ofNat 64 M2c), (.x24, 0x10000)])
def lfK (lay : Nat) : List (Reg × Word) := postLf lay ++ lfKeepK lay
structure LeafOut (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (ends : List Digest) (u : MachineState) :
    Prop where
  pc : u.pc = pcOf (stabIdx lay.val + (route index lay).1 % 2 ^ stabBits lay.val)
  glob : Glob (lfK lay.val) w pk u
  s7 : u.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1)
  t5 : u.getReg .x30 = BitVec.ofNat 64 (route index lay).2
  len : ends.length = chainCount lay
  ends : ∀ j < chainCount lay, DigAt u (lfSlot lay.val j) (ends.getD j 0)
  T0 : u.getMem (BitVec.ofNat 64 (lfBase lay.val + 16)) = BitVec.ofNat 64 (hdr0 2 lay.val (route index lay).2 0)
  T1 : u.getMem (BitVec.ofNat 64 (lfBase lay.val + 24)) =
    BitVec.ofNat 64 (hdr1 (route index lay).2 (route index lay).1)
  zero : lay = 0 → u.getMem (BitVec.ofNat 64 0x570) = 0 ∧ u.getMem (BitVec.ofNat 64 0x578) = 0
  orig : Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerBase lay + 64 * height lay) u
theorem LeafOut.hashInput {w : WBytes} {pk : Digest} {index : Nat} {lay : Layer} {ends : List Digest}
    {u : MachineState} (h : LeafOut w pk index lay ends u) :
    hashInput u = toQ (pad64 (leafInput lay (route index lay).2 (route index lay).1 ends)) ∧
      (toQ (pad64 (leafInput lay (route index lay).2 (route index lay).1 ends))).blocks = lfBlocks lay.val := by
  have h10 := h.glob.1 (.x10, BitVec.ofNat 64 (lfBase lay.val)) (by simp [lfK, postLf, lfBase])
  have h11 := h.glob.1 (.x11, BitVec.ofNat 64 (lfBytes lay.val)) (by simp [lfK, postLf, lfBytes])
  have hT0 := h.T0
  have hT1 := h.T1
  have hS := h.ends
  have hn := h.len
  by_cases h0 : lay = 0
  · subst h0
    have r := topLeaf_hashInput u _ _ ends hn h10 h11 hS hT0 hT1 (h.zero rfl).1 (h.zero rfl).2
    exact ⟨r.1, r.2⟩
  · have hc := LCtx.chainCount_lower lay h0
    have hv : lay.val ≠ 0 := fun hv => h0 (Fin.ext hv)
    simp only [lfBase, lfBytes, lfSlot, lfBlocks, if_neg hv] at h10 h11 hT0 hT1 hS ⊢
    rw [hc] at hn hS
    exact lowLeaf_hashInput u lay _ _ ends hn h10 h11 hS hT0 hT1
theorem glob_frame {gk gk' : List (Reg × Word)} {w : WBytes} {pk : Digest} {s t : MachineState}
    {W : Nat → Prop} (hG : Glob gk w pk s) (hf : Frame s t W)
    (hW : ∀ A, W A → 0x140 ≤ A ∧ (A < 0x800 ∨ 0x840 ≤ A) ∧ A < 2 ^ 23) (hk : ∀ p ∈ gk', t.getReg p.1 = p.2) :
    Glob gk' w pk t := by
  obtain ⟨-, hH, hP, hZ, hh, hD⟩ := hG
  have hn : ∀ A, A < 0x140 → ¬ W A := fun A hA h => by have := hW A h; omega
  refine ⟨hk, fun j hj => ?_, ⟨?_, ?_⟩, fun a ha => ?_, ?_, ?_⟩
  · rw [hf.get (by unfold WIT; omega) (fun h => by have := hW _ h; unfold WIT at this; omega)]; exact hH j hj
  · exact (hf.get (A := 0xA0) (by norm_num) (hn _ (by norm_num))).trans hP.1
  · exact (hf.get (A := 0xA8) (by norm_num) (hn _ (by norm_num))).trans hP.2
  · have ha' : a < 0x140 := by simp only [pSlots, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
    rw [hf.get (by omega) (hn _ ha')]; exact hZ a ha
  · unfold PHalf CTRW at *; rw [hf.get (by norm_num) (hn _ (by norm_num))]; exact hh
  · exact hD.congr (fun A hA hB => hf.get (by omega) (fun hw => by
      have := hW A hw
      unfold Verify.TAB at hA
      omega))
theorem land4 (n k : Nat) : n &&& (4 * (2 ^ k - 1)) = 4 * (n / 4 % 2 ^ k) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, show (4 : Nat) = 2 ^ 2 by norm_num, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h2 : 2 ≤ j
  · simp only [h2, decide_true, Bool.true_and, show j - 2 + 2 = j by omega]
    by_cases hj : j - 2 < k
    · simp [hj]
    · simp [hj]
  · simp [h2]
theorem stabMask_eq (lay : Nat) : stabMask lay = 4 * (2 ^ stabBits lay - 1) := by
  unfold stabMask stabBits; split <;> rfl
theorem tgtLfOld_eval (lay : Nat) (t : MachineState) (h leaf : Nat) (hn : stabBits lay ≤ h) (hh : h ≤ 12)
    (hl : leaf < 2 ^ h) (hs : stabIdx lay < 2 ^ 32)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 (2 ^ h + leaf)) :
    (tgtLfOld lay).eval t = pcOf (stabIdx lay + leaf % 2 ^ stabBits lay) := by
  have hpow : 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
  have hb : stabBits lay ≤ 7 := by unfold stabBits; split <;> omega
  have hpb : 2 ^ stabBits lay ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hb
  have hX : 2 ^ h + leaf < 2 ^ 13 := by omega
  have hmod : (2 ^ h + leaf) % 2 ^ stabBits lay = leaf % 2 ^ stabBits lay := by
    rw [show 2 ^ h = 2 ^ stabBits lay * 2 ^ (h - stabBits lay) by rw [← Nat.pow_add]; congr 1; omega,
      Nat.mul_add_mod]
  have hm : ((t.getReg .x23) <<< ((BitVec.ofNat 64 2).toNat % 64) &&& BitVec.ofNat 64 (stabMask lay)) =
      BitVec.ofNat 64 (4 * (leaf % 2 ^ stabBits lay)) := by
    apply BitVec.eq_of_toNat_eq
    have hmk : stabMask lay < 2 ^ 64 := by unfold stabMask; split <;> norm_num
    rw [toNat_andc _ _ hmk, toNat_sll _ 2 (by norm_num), stabMask_eq, land4, h23, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 2 ^ h + leaf < 2 ^ 64 by omega),
      show (2 ^ h + leaf) * 2 ^ 2 % 2 ^ 64 / 4 = 2 ^ h + leaf by omega, hmod, BitVec.toNat_ofNat]
    have := Nat.mod_lt leaf (show 0 < 2 ^ stabBits lay by positivity)
    omega
  simp only [tgtLfOld, E.eval, BinOp.eval, kw]
  rw [hm, ofNat_add_ofNat, even_andNot1' _ (by omega)]
  congr 1
  omega
theorem stabBits_le (lay : Layer) : stabBits lay.val ≤ hL lay.val := by fin_cases lay <;> decide
theorem stabIdx_lt (lay : Nat) : stabIdx lay < 2 ^ 32 := by
  unfold stabIdx
  rcases lay with _ | _ | _ | _ | n <;> simp
theorem tgtLf_lower_eval (lay : Layer) (hlay : lay ≠ 0) (t : MachineState) (leaf : Nat)
    (hl : leaf < 2 ^ hL lay.val)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + leaf)) :
    (tgtLf lay.val).eval t = pcOf (stabIdx lay.val + leaf % 2 ^ stabBits lay.val) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have he : stabBits lay.val = hL lay.val := by fin_cases lay <;> simp_all [stabBits, hL]
  have hb : 2 ^ hL lay.val ≤ 128 := by fin_cases lay <;> simp_all [hL]
  have hi := stabIdx_lt lay.val
  have hbase : 4 * 2 ^ hL lay.val ≤ 0x1000 + 4 * stabIdx lay.val := by omega
  have hshift : t.getReg .x23 <<< ((BitVec.ofNat 64 2).toNat % 64) =
      BitVec.ofNat 64 (4 * (2 ^ hL lay.val + leaf)) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sll _ 2 (by norm_num), h23]
    simp only [BitVec.toNat_ofNat]
    omega
  simp only [tgtLf, if_neg h0, E.eval, BinOp.eval, kw]
  rw [hshift, ofNat_add_ofNat]
  have hn : 4 * (2 ^ hL lay.val + leaf) + (0x1000 + 4 * stabIdx lay.val - 4 * 2 ^ hL lay.val) =
      0x1000 + 4 * (stabIdx lay.val + leaf) := by omega
  rw [hn, even_andNot1' _ (by omega), he, Nat.mod_eq_of_lt hl]
theorem hw2_hdr0 (lay : Layer) (tree : Nat) (ht : tree < 2 ^ 32) : hw 2 lay.val = hdr0 2 lay.val tree 0 := by
  rw [hdr0_eq _ _ _ _ (by norm_num) (by have := lay.isLt; omega) ht (by norm_num)]
  unfold hw; ring
theorem geomL (lay : Layer) (h : lay ≠ 0) :
    s6v lay.val = 2048 + layerBase lay + 64 * height lay + 1024 ∧ layerBase lay + 64 * height lay ≤ layerEnd lay.val ∧
      11288 ≤ layerBase lay ∧ layerEnd lay.val < 25241 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide
theorem geomT : s6v 0 = 15064 ∧ layerBase 0 = 11288 ∧ height 0 = 12 ∧ layerEnd 0 = 15768 := by
  decide
theorem leafL_step (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (c : Nat)
    (hc : c < nCopy lay.val) (hidx : index < 2 ^ 31) (a : BitVec 256) (s0 : MachineState)
    (hk : ∀ p ∈ (lctxOf w index lay a (trPc lay.val c)).known, s0.getReg p.1 = p.2)
    (hG : Glob (chainK lay.val) w pk s0) (hO : Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd lay.val) s0)
    (h23 : s0.getReg .x23 = BitVec.ofNat 64 (2 ^ hL lay.val + (route index lay).1))
    (h30 : s0.getReg .x30 = BitVec.ofNat 64 (route index lay).2)
    (ends : List Digest) (t : MachineState)
    (ht : (lctxOf w index lay a (trPc lay.val c)).ChainOut s0 43 ends t) :
    ∃ u, Steps image t 12 12 u ∧ LeafOut w pk index lay ends u := by
  set L := lctxOf w index lay a (trPc lay.val c) with hLd
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := ht
  have hkL : ∀ q ∈ chainK lay.val, s0.getReg q.1 = q.2 := hG.1
  have hknown : KnownOK (leafK lay.val) t := by
    intro p hp
    simp only [leafK, baseK, if_neg h0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ((rfl | rfl) | rfl) | rfl
    · rw [hR .x5 (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK, baseK])
    · rw [hR .x18 (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK, baseK])
    · rw [hR .x27 (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK])
    · rw [hR .x6 (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK])
  obtain ⟨u, hu⟩ := spec_run (leafCheck_at lay.val c lay.isLt hc) t (by rw [hpc]; rfl) hknown
    (by intro b hb; simp [specLf, h0] at hb) (by simp)
  have hst := hu.steps
  rw [show (specLf lay.val).steps = 12 by simp [specLf, h0], show (specLf lay.val).cycles = 12 by simp [specLf, h0]]
    at hst
  refine ⟨u, hst, ?_⟩
  have hku : KnownOK (postLf lay.val) u := hu.known
  have hkeep := hu.keep
  have hmem : ∀ A, u.getMem A = memEval t [(⟨none, BitVec.ofNat 64 792⟩, .reg .x4),
      (⟨none, BitVec.ofNat 64 784⟩, kw (hw 2 lay.val))] A := by
    intro A; rw [hu.mem]; simp [specLf, h0]
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ 792 → A ≠ 784 → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2
    rw [hmem]
    apply memEval_frame_ofNat t _ A hA
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp <;> omega
  have htr := tree_lt index lay hidx
  have hlf := leaf_lt index lay
  obtain ⟨hg1, hg2, hg3, hg4⟩ := geomL lay hlay
  have hS6 : L.S6 = s6v lay.val := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd h hlay, ?_⟩
  ·
    rw [hu.spc (tgtLf lay.val) (by simp [specLf, h0])]
    have := hL_le lay
    exact tgtLf_lower_eval lay hlay t _ hlf
      (by rw [hR .x23 (by simp [chainRegs]), h23])
  ·
    have hGt : Glob baseK w pk t := glob_frame hG hF (fun A hA => by
        unfold LCtx.Wr LCtx.blk at hA; rw [hS6] at hA
        have : slotL L.i0 = 768 := rfl
        rw [this] at hA
        rcases hA with hA | hA <;> omega)
      (fun p hp => hknown p (by simp [leafK, hp]))
    have hGu := hu.glob _ w pk hGt (RelOK.nil t)
    refine ⟨fun p hp => ?_, hGu.2.1, hGu.2.2.1, hGu.2.2.2.1, hGu.2.2.2.2⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hku p hp
    · have h22 : s0.getReg .x22 = BitVec.ofNat 64 (s6v lay.val) :=
        hk (.x22, BitVec.ofNat 64 L.S6) (by simp [LCtx.known])
      have m28 : ((.x28 : Reg), BitVec.ofNat 64 (headerBank 0 0)) ∈ postLf lay.val := by
        simp [postLf, h0]
      have m6 : ((.x6 : Reg), (1 : Word)) ∈ postLf lay.val := by
        simp [postLf, leafK, h0]
      simp only [lfKeepK, if_neg h0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
      all_goals first
        | exact hku _ m28
        | exact hku _ m6
        | rw [hkeep _ (by simp [keepLfAll, h0]), hR _ (by simp [chainRegs])]; exact h22
        | rw [hkeep _ (by simp [keepLfAll, h0]), hR _ (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK])
  · rw [hkeep .x23 (by simp [keepLfAll, h0]), hR .x23 (by simp [chainRegs]), h23]
  · rw [hkeep .x30 (by simp [keepLfAll, h0]), hR .x30 (by simp [chainRegs]), h30]
  · rw [hlen, LCtx.chainCount_lower lay hlay]; rfl
  · intro j hj
    rw [LCtx.chainCount_lower lay hlay] at hj
    have e := hS j (by rw [hlen]; exact hj)
    have hj0 : slotL (L.i0 + j) = slotL j := by rw [show L.i0 = 0 from rfl, Nat.zero_add]
    rw [hj0] at e
    simp only [lfSlot, if_neg h0]
    have hsl : slotL j = 768 ∨ 800 ≤ slotL j := by unfold slotL; split <;> omega
    have hsl' : slotL j < 2 ^ 32 := by unfold slotL; split <;> omega
    exact ⟨(hfr (slotL j) (by omega) (by omega) (by omega)).trans e.1,
      (hfr (slotL j + 8) (by omega) (by omega) (by omega)).trans e.2⟩
  · rw [show lfBase lay.val + 16 = 784 by simp [lfBase, h0], hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    simp only [E.eval, kw]
    rw [hw2_hdr0 lay _ htr]
  · rw [show lfBase lay.val + 24 = 792 by simp [lfBase, h0], hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    simp only [E.eval]
    rw [hR .x4 (by simp [chainRegs]), hk (.x4, BitVec.ofNat 64 L.w1) (by simp [LCtx.known])]
    rfl
  ·
    have hOt : Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerBase lay + 64 * height lay) t :=
      (hO.mono (fun o ho => ⟨ho.1, by omega⟩)).frame (fun j hj hp => hF.get (by unfold WIT WX at *; omega)
        (fun hw => by
          unfold LCtx.Wr at hw; rw [hS6] at hw
          unfold WIT at hw
          rcases hw with hw | hw <;> omega))
    exact (hu.orig_const hOt).mono (fun o ho => ⟨ho, by simp⟩)
structure TopLeafReady (w : WBytes) (pk : Digest) (index c : Nat) (ends : List Digest)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf (trPc 0 c + 19)
  glob : Glob (leafK 0) w pk t
  keep : KnownOK (lfKeepK 0) t
  s7 : t.getReg .x23 = BitVec.ofNat 64 (2 ^ hL 0 + (route index 0).1)
  t5 : t.getReg .x30 = BitVec.ofNat 64 (route index 0).2
  tp : t.getReg .x4 = BitVec.ofNat 64 (hdr1 (route index 0).2 (route index 0).1)
  len : ends.length = 54
  ends : ∀ j < 54, DigAt t (slotT j) (ends.getD j 0)
  orig : Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerBase 0 + 64 * height 0) t
theorem leafT_step (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0) (hidx : index < 2 ^ 31)
    (ends : List Digest) (t : MachineState) (ht : TopLeafReady w pk index c ends t) :
    ∃ u, Steps image t 13 13 u ∧ LeafOut w pk index 0 ends u := by
  obtain ⟨u, hu⟩ := spec_run (leafCheck_at 0 c (by norm_num) hc) t ht.pc ht.glob.1
    (by intro b hb; simp [specLf] at hb) (by simp)
  have hst := hu.steps
  rw [show (specLf 0).steps = 13 by simp [specLf], show (specLf 0).cycles = 13 by simp [specLf]] at hst
  refine ⟨u, hst, ?_⟩
  have hku : KnownOK (postLf 0) u := hu.known
  have hkeep := hu.keep
  have hmem : ∀ A, u.getMem A = memEval t [(⟨none, BitVec.ofNat 64 1400⟩, kw 0), (⟨none, BitVec.ofNat 64 1392⟩, kw 0),
      (⟨none, BitVec.ofNat 64 536⟩, .reg .x4), (⟨none, BitVec.ofNat 64 528⟩, kw (hw 2 0))] A := by
    intro A; rw [hu.mem]; simp [specLf]
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ 1400 → A ≠ 1392 → A ≠ 536 → A ≠ 528 →
      u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    rw [hmem]
    apply memEval_frame_ofNat t _ A hA
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp <;> omega
  have htr := tree_lt index 0 hidx
  have hlf := leaf_lt index 0
  refine ⟨?_, ?_, ?_, ?_, ht.len, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩, ?_⟩
  · rw [hu.spc (tgtLf 0) (by simp [specLf])]
    change (tgtLfOld 0).eval t = _
    exact tgtLfOld_eval 0 t (hL 0) _ (stabBits_le 0) (by decide) hlf (stabIdx_lt _) ht.s7
  · have hGu := hu.glob _ w pk ht.glob (RelOK.nil t)
    refine ⟨fun p hp => ?_, hGu.2.1, hGu.2.2.1, hGu.2.2.2.1, hGu.2.2.2.2⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hku p hp
    · have hkp : p.1 ∈ keepLfAll 0 := by
        change p ∈ lfKeepK 0 at hp
        simp [lfKeepK] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [keepLfAll]
      rw [hkeep _ hkp]
      exact ht.keep p hp
  · rw [hkeep .x23 (by simp [keepLfAll]), ht.s7]
    rfl
  · rw [hkeep .x30 (by simp [keepLfAll]), ht.t5]
  · intro j hj
    have hj' : j < 54 := hj
    have e := ht.ends j hj'
    simp only [lfSlot, if_pos rfl]
    have hsl : slotT j = 512 ∨ (544 ≤ slotT j ∧ slotT j ≤ 1376) := by unfold slotT; split <;> omega
    exact ⟨(hfr (slotT j) (by omega) (by omega) (by omega) (by omega) (by omega)).trans e.1,
      (hfr (slotT j + 8) (by omega) (by omega) (by omega) (by omega) (by omega)).trans e.2⟩
  · rw [show lfBase (0 : Layer).val + 16 = 528 from rfl, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    simp only [E.eval, kw]
    exact hw2_hdr0 0 _ htr |>.symm ▸ rfl
  · rw [show lfBase (0 : Layer).val + 24 = 536 from rfl, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    exact ht.tp
  · rw [show (0x570 : Nat) = 1392 by norm_num, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    rfl
  · rw [show (0x578 : Nat) = 1400 by norm_num, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    rfl
  · exact (hu.orig_const ht.orig).mono (fun o ho => ⟨ho, by simp⟩)
end SigGolfCandidate.T3M
end
