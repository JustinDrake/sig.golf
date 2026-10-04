import SigGolfCandidate.T3M.Expand.LayerChain
import SigGolfCandidate.T3M.Search.Params
import SigGolfCandidate.T3M.Search.Arith
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Signature chain chainInput shortHash pad64 zero16 header chainCount height
  width maxDigit route recoverLayer leafHash nodeHash)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC csN4)
set_option autoImplicit false
theorem chainCount_cases' (lay : Layer) : chainCount lay = 54 ∨ chainCount lay = 43 := by
  fin_cases lay <;> simp [chainCount]
theorem height_le (lay : Layer) : height lay ≤ 12 := by
  fin_cases lay <;> simp [height]
theorem csN4_le (lay : Layer) : csN4 lay ≤ chainCount lay := by
  unfold csN4; split_ifs with h
  · subst h; simp [chainCount]
  · omega
theorem endpoint_eq (lay : Layer) (i : Nat) : maxDigit lay i = endpoint lay i (csN4 lay) := by
  unfold maxDigit endpoint csN4
  split_ifs <;> rfl
theorem leafInput_words' (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : ends.length = chainCount lay) :
    wordsOf (pad64 (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (header 2 lay.val tree 0 leaf) ++
        (ends.drop 1).flatMap (bytesLE 16))) =
      wordsOf (bytesLE 16 (ends.getD 0 0)) ++
        [BitVec.ofNat 64 (hdr0 2 lay.val tree 0), BitVec.ofNat 64 (hdr1 tree leaf)] ++
        wordsOf ((ends.drop 1).flatMap (bytesLE 16)) ++ (if chainCount lay = 54 then [0, 0] else []) := by
  have hn := chainCount_cases' lay
  have hfl : ((ends.drop 1).flatMap (bytesLE 16)).length = 16 * (chainCount lay - 1) := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen]; ring
  unfold pad64
  rw [List.length_append, List.length_append, bytesLE_length, bytesLE_length, hfl,
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length, hfl]; omega),
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_header]
  rcases hn with h | h
  · rw [h, if_pos rfl]
    simp only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMod]
    rw [show (List.replicate 16 0 : List UInt8) = List.replicate (8 * 2) 0 from rfl, wordsOf_replicate_zero]
    rfl
  · rw [h, if_neg (by decide)]
    simp only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMod, List.replicate_zero,
      wordsOf_nil, List.append_nil]
    simp [T3.packedNodeTag]
def leafBlocks' (lay : Layer) : Nat := (16 * (chainCount lay + 1) + 63) / 64
theorem leafInput_length' (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : ends.length = chainCount lay) :
    (pad64 (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (header 2 lay.val tree 0 leaf) ++
        (ends.drop 1).flatMap (bytesLE 16))).length = 64 * leafBlocks' lay := by
  have hn := chainCount_cases' lay
  have hfl : ((ends.drop 1).flatMap (bytesLE 16)).length = 16 * (chainCount lay - 1) := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen]; ring
  rw [pad64_length, List.length_append, List.length_append, bytesLE_length, bytesLE_length, hfl]
  unfold leafBlocks'
  rcases hn with h | h <;> rw [h]
theorem leafBlocks'_cases (lay : Layer) : leafBlocks' lay = 14 ∧ chainCount lay = 54 ∨
    leafBlocks' lay = 11 ∧ chainCount lay = 43 := by
  unfold leafBlocks'; rcases chainCount_cases' lay with h | h <;> rw [h] <;> simp
def sideOff (leaf j : Nat) : Nat := if leaf / 2 ^ j % 2 = 1 then 0 else 48
def RlScratch (A : Nat) : Prop :=
  A = CHAIN + 16 ∨ A = CHAIN + 24 ∨ (CHAIN + 48 ≤ A ∧ A < CHAIN + 80) ∨ (LEAFPK ≤ A ∧ A < LEAFPK + 880) ∨
  A = NODE ∨ A = NODE + 8 ∨ A = NODE + 16 ∨ A = NODE + 24 ∨ A = NODE + 48 ∨ A = NODE + 56 ∨
  (NOUT ≤ A ∧ A < NOUT + 32) ∨ A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56
def RlWit (lay : Layer) (leaf WC WM : Nat) (A : Nat) : Prop :=
  (∃ i < chainCount lay, A = WC - 64 * i + 48 ∨ A = WC - 64 * i + 56) ∨
  (∃ j < height lay, A = WM - 64 * j + sideOff leaf j ∨ A = WM - 64 * j + sideOff leaf j + 8)
def rlRegs : List Reg :=
  [.x6, .x7, .x10, .x11, .x12, .x13, .x19, .x20, .x21, .x22, .x23, .x24, .x28, .x29, .x30]
structure RlPre (s : MachineState) (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (P WC WM ret : Nat) : Prop where
  pc : s.pc = pcOf 997
  x1 : s.getReg .x1 = pcOf ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 (route index lay).2
  x18 : s.getReg .x18 = BitVec.ofNat 64 (route index lay).1
  x15 : s.getReg .x15 = BitVec.ofNat 64 (height lay)
  x26 : s.getReg .x26 = BitVec.ofNat 64 (chainCount lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 lay)
  x16 : s.getReg .x16 = BitVec.ofNat 64 P
  x23 : s.getReg .x23 = BitVec.ofNat 64 WC
  x24 : s.getReg .x24 = BitVec.ofNat 64 WM
  hidx : index < 2 ^ 31
  hP : 0x7000 ≤ P
  hP' : P + 16 * (chainCount lay + height lay) ≤ 0x7000 + 5616
  hP8 : P % 8 = 0
  hWC8 : WC % 8 = 0
  hWM8 : WM % 8 = 0
  hWM : 0x800 + 64 * (height lay - 1) ≤ WM
  hWMC : WM + 64 + 64 * (chainCount lay - 1) ≤ WC
  hWC : WC + 64 ≤ 0x7000
  dbytes : ∀ i < chainCount lay, s.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 (digits.getD i 0)
  hdig : ∀ i < chainCount lay, digits.getD i 0 ≤ maxDigit lay i
  vals : ∀ i (h : i < chainCount lay), DigAt s (P + 16 * i) ((sig.layers lay).values ⟨i, h⟩)
  path : ∀ j (h : j < height lay), DigAt s (P + 16 * chainCount lay + 16 * j) ((sig.layers lay).path ⟨j, h⟩)
  c0 : s.getMem (BitVec.ofNat 64 CHAIN) = 0
  c8 : s.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
  c32 : s.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0
  c40 : s.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0
  n32 : s.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  n40 : s.getMem (BitVec.ofNat 64 (NODE + 40)) = 0
  l944 : s.getMem (BitVec.ofNat 64 (LEAFPK + 880)) = 0
  l952 : s.getMem (BitVec.ofNat 64 (LEAFPK + 888)) = 0
theorem route_lt (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ height lay := by
  unfold route; exact Nat.mod_lt _ (by positivity)
theorem route_tree_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) : (route index lay).2 < 2 ^ 32 := by
  unfold route
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
def lval (sig : Signature) (lay : Layer) (i : Nat) : Digest :=
  if h : i < chainCount lay then (sig.layers lay).values ⟨i, h⟩ else 0
def lpath (sig : Signature) (lay : Layer) (j : Nat) : Digest :=
  if h : j < height lay then (sig.layers lay).path ⟨j, h⟩ else 0
theorem slotOff_lt {i n : Nat} (hi : i < n) : slotOff i + 16 ≤ 16 * (n + 1) := by
  unfold slotOff; split_ifs <;> omega
theorem slotOff_ne {i j : Nat} (h : i ≠ j) : slotOff i + 16 ≤ slotOff j ∨ slotOff j + 16 ≤ slotOff i := by
  unfold slotOff; split_ifs <;> omega
theorem slotOff_hdr (i : Nat) : slotOff i + 16 ≤ 16 ∨ 32 ≤ slotOff i := by
  unfold slotOff; split_ifs <;> omega
section phase
variable {sk : BitVec 256}
theorem rl_chains {s0 t1 : MachineState} {sig : Signature} {index : Nat} {lay : Layer} {digits : List Nat}
    {P WC WM ret : Nat} (hpre : RlPre s0 sig index lay digits P WC WM ret)
    (r1 : RegsExcept s0 t1 [.x6, .x7, .x19, .x28, .x30])
    (f1 : Frame s0 t1 (fun A => A = CHAIN + 24 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24))
    (hI0 : ChainsInv t1 lay (route index lay).2 (route index lay).1 P WC (chainCount lay) (csN4 lay)
      (lval sig lay) [] t1) :
    TBSim image sk t1 (chainCount lay * 351)
      ((List.finRange (chainCount lay)).mapM fun i => chain lay (route index lay).2 (route index lay).1 i.val
        (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0) ((sig.layers lay).values i))
      (fun ends u => ends.length = chainCount lay ∧ ChainsInv t1 lay (route index lay).2 (route index lay).1 P WC
        (chainCount lay) (csN4 lay) (lval sig lay) ends u) := by
  set tree := (route index lay).2 with htree_def
  set leaf := (route index lay).1 with hleaf_def
  have htree : tree < 2 ^ 32 := route_tree_lt index lay hpre.hidx
  have hN := chainCount_cases' lay
  have hH := height_le lay
  have hPb := hpre.hP'
  have hWC := hpre.hWC
  have hWMC := hpre.hWMC
  have hWM := hpre.hWM
  have hP0 := hpre.hP
  refine tb_mapM_finRange (chainCount lay) _ 351 _ (fun i pre t hlen hI => ?_) hI0
  have hi := i.isLt
  have hfr : Frame s0 t (fun A => (A = CHAIN + 24 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) ∨ ChW WC pre.length A) :=
    f1.trans hI.frame
  have g : ∀ r, r ∉ oneRegs → r ∉ [Reg.x6, .x7, .x19, .x28, .x30] → t.getReg r = s0.getReg r :=
    fun r h1 h2 => by rw [hI.regs.get h1, r1.get h2]
  have h26 : t.getReg .x26 = BitVec.ofNat 64 (chainCount lay) := by
    rw [g _ (by decide) (by decide), hpre.x26]
  have h27 : t.getReg .x27 = BitVec.ofNat 64 (csN4 lay) := by rw [g _ (by decide) (by decide), hpre.x27]
  have h16 : t.getReg .x16 = BitVec.ofNat 64 P := by rw [g _ (by decide) (by decide), hpre.x16]
  have h23 : t.getReg .x23 = BitVec.ofNat 64 (WC - 64 * i.val) := by rw [hI.x23, hlen]
  have hv : DigAt t (P + 16 * i.val) ((sig.layers lay).values i) :=
    (hpre.vals i.val hi).frame hfr (by omega)
      (by rintro (h | h); · simp only [CHAIN, LEAFPK] at h; omega
          · exact not_ChW_of (by omega) (by omega) (by simp only [CHAIN]; omega) (by simp only [LEAFPK]; omega) h)
      (by rintro (h | h); · simp only [CHAIN, LEAFPK] at h; omega
          · exact not_ChW_of (by omega) (by omega) (by simp only [CHAIN]; omega) (by simp only [LEAFPK]; omega) h)
  have hdig : t.getByte (BitVec.ofNat 64 (DIGITS + i.val)) = BitVec.ofNat 8 (digits.getD i.val 0) := by
    rw [Frame.getByte hfr (by simp only [DIGITS]; omega)
      (by rintro (h | h); · simp only [CHAIN, LEAFPK, DIGITS] at h; omega
          · exact not_ChW_of (by omega) (by simp only [DIGITS]; omega) (by simp only [CHAIN, DIGITS]; omega)
              (by simp only [LEAFPK, DIGITS]; omega) h)]
    exact hpre.dbytes i.val hi
  have hd : digits.getD i.val 0 ≤ endpoint lay i.val (csN4 lay) := by
    have := hpre.hdig i.val hi; rwa [endpoint_eq] at this
  have hc : ChainCtx lay.val tree leaf i.val t := hlen ▸ hI.ctx
  have hone := rl_one (sk := sk) lay tree leaf i.val (digits.getD i.val 0) P (WC - 64 * i.val) (chainCount lay)
    (csN4 lay) (by
      have hidx := hpre.hidx
      dsimp [tree, leaf]
      fin_cases lay <;> norm_num [route, height] at * <;> omega)
    (route_lt index lay) hi (by omega) (csN4_le lay) hpre.hP (by omega) hpre.hP8
    (by have := hpre.hWC8; omega) (by omega) (by omega) hd ((sig.layers lay).values i) t hI.pc hc h26 h27 h16 h23 hv
    hdig
  rw [endpoint_eq]
  refine hone.mono le_rfl (fun d u hu => ?_)
  obtain ⟨upc, u19, u23, uc, uslot, uval, ur, uf⟩ := hu
  have hl1 : (pre ++ [d]).length = i.val + 1 := by simp [hlen]
  refine ⟨upc, hl1 ▸ uc, ?_, ?_, ?_, (hI.regs.trans ur).mono (fun r hr => by
    rcases List.mem_append.mp hr with h | h <;> exact h), (hI.frame.trans uf).mono (fun A _ h => ?_)⟩
  · rw [u23, hl1, Nat.mul_succ, Nat.sub_sub]
  · intro j hj
    rw [hl1] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have hs := hI.slots j (by omega)
      rw [List.getD_append _ _ _ _ (by omega)]
      have hne := slotOff_ne (show j ≠ i.val by omega)
      have hlt := slotOff_lt (show j < chainCount lay by omega)
      exact hs.frame uf (by simp only [LEAFPK]; omega)
        (by unfold OneW StepW; simp only [LEAFPK, CHAIN]; omega)
        (by unfold OneW StepW; simp only [LEAFPK, CHAIN]; omega)
    · rw [List.getD_append_right _ _ _ _ (by omega), show i.val - pre.length = 0 by omega]
      simpa using uslot
  · intro j hj
    rw [hl1] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have hw := hI.wvals j (by omega)
      exact hw.frame uf (by omega) (by unfold OneW StepW slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega)
        (by unfold OneW StepW slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega)
    · have : lval sig lay i.val = (sig.layers lay).values i := by unfold lval; rw [dif_pos hi]
      rw [this]
      exact uval
  · rw [hl1]
    unfold ChW
    rcases h with h | h
    · rw [hlen] at h
      rcases h with h | ⟨c, hc, h⟩ | ⟨c, hc, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨c, by omega, h⟩)
      · exact Or.inr (Or.inr ⟨c, by omega, h⟩)
    · unfold OneW at h
      rcases h with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨i.val, by omega, Or.inl h⟩)
      · exact Or.inr (Or.inl ⟨i.val, by omega, Or.inr h⟩)
      · exact Or.inr (Or.inr ⟨i.val, by omega, Or.inl h⟩)
      · exact Or.inr (Or.inr ⟨i.val, by omega, Or.inr h⟩)
theorem nodeInput_length' (tag lay tree heap : Nat) (l r : Digest) :
    (bytesLE 16 l ++ bytesLE 16 (header tag lay tree 0 heap) ++ zero16 ++ bytesLE 16 r).length = 64 := by
  simp [bytesLE_length, zero16]
theorem wordsOf_nodeInput' (tag lay tree heap : Nat) (l r : Digest) (hn : T3.packedNodeTag tag := by decide) :
    wordsOf (bytesLE 16 l ++ bytesLE 16 (header tag lay tree 0 heap) ++ zero16 ++ bytesLE 16 r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 (hdr0 tag lay tree tree),
        BitVec.ofNat 64 (T3.nodeWord tag 0 heap), 0, 0, r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_packed_header _ _ _ _ _ hn, wordsOf_zero16,
    wordsOf_bytesLE16]
  rfl
def mkRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x13, .x20, .x22, .x24, .x28, .x29, .x30]
def MkW (leaf WM j : Nat) (A : Nat) : Prop :=
  A = NODE ∨ A = NODE + 8 ∨ A = NODE + 16 ∨ A = NODE + 24 ∨ A = NODE + 48 ∨ A = NODE + 56 ∨
  (NOUT ≤ A ∧ A < NOUT + 32) ∨ (∃ j' < j, A = WM - 64 * j' + sideOff leaf j' ∨ A = WM - 64 * j' + sideOff leaf j' + 8)
structure MkInv (tc : MachineState) (sig : Signature) (lay : Layer) (leaf P WM j : Nat) (value : Digest)
    (u : MachineState) : Prop where
  pc : u.pc = pcOf 1076
  x20 : u.getReg .x20 = BitVec.ofNat 64 j
  x22 : u.getReg .x22 = BitVec.ofNat 64 (P + 16 * chainCount lay + 16 * j)
  x24 : u.getReg .x24 = BitVec.ofNat 64 (WM - 64 * j)
  hj : j ≤ height lay
  val : DigAt u NOUT value
  wit : ∀ j' < j, DigAt u (WM - 64 * j' + sideOff leaf j') (lpath sig lay j')
  regs : RegsExcept tc u mkRegs
  frame : Frame tc u (MkW leaf WM j)
theorem sideOff_le (leaf j : Nat) : sideOff leaf j ≤ 48 := by unfold sideOff; split_ifs <;> omega
theorem not_MkW_of {leaf WM j A : Nat} (hA1 : WM + 64 ≤ A) (hA2 : A < NODE ∨ NODE + 64 ≤ A)
    (hA3 : A < NOUT ∨ NOUT + 32 ≤ A) : ¬ MkW leaf WM j A := by
  unfold MkW
  rintro (h | h | h | h | h | h | h | ⟨j', _, h | h⟩) <;>
    first | (simp only [NODE, NOUT] at h hA2 hA3; omega) | (have := sideOff_le leaf j'; omega)
theorem rl_mk_step {tc : MachineState} {sig : Signature} {lay : Layer} {tree leaf P WM j : Nat}
    {value : Digest} {u : MachineState} (hj : j < height lay) (htree : tree < 2 ^ 32) (hleaf : leaf < 2 ^ height lay)
    (hP0 : 0x7000 ≤ P) (hP' : P + 16 * (chainCount lay + height lay) ≤ 0x7000 + 5616) (hP8 : P % 8 = 0)
    (hWM8 : WM % 8 = 0) (hWM : 0x800 + 64 * (height lay - 1) ≤ WM) (hWM' : WM + 64 ≤ 0x7000)
    (c5 : tc.getReg .x5 = 0) (c8 : tc.getReg .x8 = BitVec.ofNat 64 lay.val)
    (c9 : tc.getReg .x9 = BitVec.ofNat 64 tree) (c18 : tc.getReg .x18 = BitVec.ofNat 64 leaf)
    (c15 : tc.getReg .x15 = BitVec.ofNat 64 (height lay))
    (cpath : DigAt tc (P + 16 * chainCount lay + 16 * j) (lpath sig lay j))
    (cn32 : tc.getMem (BitVec.ofNat 64 (NODE + 32)) = 0) (cn40 : tc.getMem (BitVec.ofNat 64 (NODE + 40)) = 0)
    (hI : MkInv tc sig lay leaf P WM j value u) :
    TBSim image sk u 56 (let other := (sig.layers lay).path ⟨j, hj⟩
        let pair := if leaf / 2 ^ j % 2 = 0 then (value, other) else (other, value)
        nodeHash 3 lay.val tree (2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1)) pair.1 pair.2)
      (fun v' u' => MkInv tc sig lay leaf P WM (j + 1) v' u' ∧
        DigAt u' NODE (if leaf / 2 ^ j % 2 = 0 then value else lpath sig lay j) ∧
        DigAt u' (NODE + 48) (if leaf / 2 ^ j % 2 = 0 then lpath sig lay j else value)) := by
  have hH := height_le lay
  have hlay := lay.isLt
  have hleaf' : leaf < 2 ^ 12 := lt_of_lt_of_le hleaf (Nat.pow_le_pow_right (by norm_num) hH)
  have g : ∀ r, r ∉ mkRegs → u.getReg r = tc.getReg r := fun r h => hI.regs.get h
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1076_spec u hI.pc j (height lay) (by omega) (by omega) hI.x20
    (by rw [g _ (by decide)]; exact c15)
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, r2, f2⟩ := rl1077_spec t1 p1 leaf j (by omega) (by omega)
    (by rw [r1.get (by decide), g _ (by decide)]; exact c18) (by rw [r1.get (by decide)]; exact hI.x20)
  have fu2 : Frame u t2 (fun _ => False) := (f1.trans f2).mono (fun A _ h => by rcases h with h | h <;> exact h)
  have ru2 : RegsExcept u t2 [.x28] := (r1.trans r2).mono (by decide)
  have hpu : DigAt u (P + 16 * chainCount lay + 16 * j) (lpath sig lay j) :=
    cpath.frame hI.frame (by omega) (not_MkW_of (by omega) (by simp only [NODE]; omega) (by simp only [NOUT]; omega))
      (not_MkW_of (by omega) (by simp only [NODE]; omega) (by simp only [NOUT]; omega))
  set P' := P + 16 * chainCount lay + 16 * j with hP'def
  set M := WM - 64 * j with hMdef
  have h22 : t2.getReg .x22 = BitVec.ofNat 64 P' := by rw [ru2.get (by decide)]; exact hI.x22
  have h24 : t2.getReg .x24 = BitVec.ofNat 64 M := by rw [ru2.get (by decide)]; exact hI.x24
  have hval2 : DigAt t2 NOUT value := hI.val.frame fu2 (by decide) (by simp) (by simp)
  have hpu2 : DigAt t2 P' (lpath sig lay j) := hpu.frame fu2 (by omega) (by simp) (by simp)
  have hn32 : t2.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 := by
    rw [fu2.get (by decide) (by simp), hI.frame.get (by decide)
      (by unfold MkW; simp only [NODE, NOUT]; rintro (h | h | h | h | h | h | h | ⟨j', _, h | h⟩) <;>
        first | omega | (have := sideOff_le leaf j'; omega)), cn32]
  have hn40 : t2.getMem (BitVec.ofNat 64 (NODE + 40)) = 0 := by
    rw [fu2.get (by decide) (by simp), hI.frame.get (by decide)
      (by unfold MkW; simp only [NODE, NOUT]; rintro (h | h | h | h | h | h | h | ⟨j', _, h | h⟩) <;>
        first | omega | (have := sideOff_le leaf j'; omega)), cn40]
  obtain ⟨t3, k3, s3, hk3, p3, nl, nr, wsib, r3, f3⟩ : ∃ t3 k3, Steps image t2 k3 k3 t3 ∧ k3 ≤ 19 ∧
      t3.pc = pcOf 1117 ∧
      DigAt t3 NODE (if leaf / 2 ^ j % 2 = 0 then value else lpath sig lay j) ∧
      DigAt t3 (NODE + 48) (if leaf / 2 ^ j % 2 = 0 then lpath sig lay j else value) ∧
      DigAt t3 (M + sideOff leaf j) (lpath sig lay j) ∧
      RegsExcept t2 t3 [.x6, .x7, .x29, .x30] ∧
      Frame t2 t3 (fun A => A = M + sideOff leaf j ∨ A = M + sideOff leaf j + 8 ∨ A = NODE ∨ A = NODE + 8 ∨
        A = NODE + 48 ∨ A = NODE + 56) := by
    by_cases hb : leaf / 2 ^ j % 2 = 0
    · rw [if_pos hb] at p2
      obtain ⟨t3, s3, p3, m48, m56, n0, n8, n48, n56, r3, f3⟩ := rl1099_spec t2 p2 P' M (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) h22 h24
      have hso : sideOff leaf j = 48 := by unfold sideOff; rw [if_neg (by omega)]
      refine ⟨t3, 18, s3, by omega, p3, ?_, ?_, ?_, r3, ?_⟩
      · rw [if_pos hb]; exact ⟨n0.trans hval2.1, n8.trans hval2.2⟩
      · rw [if_pos hb]; exact ⟨n48.trans hpu2.1, n56.trans hpu2.2⟩
      · rw [hso]; exact ⟨m48.trans hpu2.1, by rw [show M + 48 + 8 = M + 56 by omega]; exact m56.trans hpu2.2⟩
      · rw [hso]; exact f3
    · rw [if_neg hb] at p2
      obtain ⟨t3, s3, p3, m0, m8, n0, n8, n48, n56, r3, f3⟩ := rl1080_spec t2 p2 P' M (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) h22 h24
      have hso : sideOff leaf j = 0 := by unfold sideOff; rw [if_pos (by omega)]
      refine ⟨t3, 19, s3, le_refl _, p3, ?_, ?_, ?_, r3, ?_⟩
      · rw [if_neg hb]; exact ⟨n0.trans hpu2.1, n8.trans hpu2.2⟩
      · rw [if_neg hb]; exact ⟨n48.trans hval2.1, n56.trans hval2.2⟩
      · rw [hso]; exact ⟨m0.trans hpu2.1, m8.trans hpu2.2⟩
      · rw [hso]; simpa using f3
  have g3' : RegsExcept tc t3 mkRegs := ((hI.regs.trans ru2).trans r3).mono (by decide)
  have g3 : ∀ r, r ∉ mkRegs → t3.getReg r = tc.getReg r := fun r h => g3'.get h
  obtain ⟨t4, s4, p4, h16, h24', h10, h11, h12, r4, f4⟩ := rl1117_spec t3 p3 lay.val tree leaf (height lay) j
    (by omega) htree (by omega) hj hH (by rw [g3 _ (by decide)]; exact c8) (by rw [g3 _ (by decide)]; exact c9)
    (by rw [g3 _ (by decide)]; exact c18) (by rw [g3 _ (by decide)]; exact c15)
    (by rw [r3.get (by decide), ru2.get (by decide)]; exact hI.x20)
  set heap := 2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1) with hheap
  have hheap' : heap < 2 ^ 32 := by
    have : 2 ^ (height lay - j - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : leaf / 2 ^ (j + 1) ≤ leaf := Nat.div_le_self _ _
    omega
  set L := if leaf / 2 ^ j % 2 = 0 then value else lpath sig lay j with hL
  set R := if leaf / 2 ^ j % 2 = 0 then lpath sig lay j else value with hR
  have f34 : ∀ A, A < 2 ^ 64 → A ≠ NODE + 16 → A ≠ NODE + 24 → t4.getMem (BitVec.ofNat 64 A) = t3.getMem (BitVec.ofNat 64 A) :=
    fun A hA h1 h2 => f4.get hA (by rintro (h | h) <;> contradiction)
  have hq : hashInput t4 = toQ (pad64 (bytesLE 16 L ++ bytesLE 16 (header 3 lay.val tree 0 heap) ++ zero16 ++
      bytesLE 16 R)) := by
    rw [pad64_of_aligned _ (by rw [nodeInput_length'])]
    refine hashInput_toQ t4 _ 0 NODE (nodeInput_length' _ _ _ _ _ _) h10 (by decide) (by decide) h11 (by decide) ?_
    rw [wordsOf_nodeInput' 3 _ _ _ _ _ (by decide), readWords_eight, f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide), h16, h24',
      f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide), nl.1, nl.2,
      show NODE + 48 + 8 = NODE + 56 from rfl, nr.1, nr.2,
      f3.get (by decide) (by simp only [NODE]; have := sideOff_le leaf j; omega), hn32,
      f3.get (by decide) (by simp only [NODE]; have := sideOff_le leaf j; omega), hn40,
      nodeWord_3, hdr0_eq 3 lay.val tree tree (by decide) (by omega) htree htree, hdr1_eq heap 0 hheap' (by decide)]
    congr 3
  have hv : hashArgumentsValid t4 = true :=
    hashArgs_const t4 NODE 64 NOUT h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have r34 : RegsExcept t2 t4 ([.x6, .x7, .x29, .x30] ++ [.x6, .x7, .x10, .x11, .x12, .x13, .x28, .x30]) := r3.trans r4
  have h5 : t4.getReg .x5 = 0 := by rw [r34.get (by decide), ru2.get (by decide), g _ (by decide)]; exact c5
  have hprog : (let other := (sig.layers lay).path ⟨j, hj⟩
      let pair := if leaf / 2 ^ j % 2 = 0 then (value, other) else (other, value)
      nodeHash 3 lay.val tree (2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1)) pair.1 pair.2) =
      (shortHash (bytesLE 16 L ++ bytesLE 16 (header 3 lay.val tree 0 heap) ++ zero16 ++ bytesLE 16 R) >>= pure) := by
    have e : (sig.layers lay).path ⟨j, hj⟩ = lpath sig lay j := by unfold lpath; rw [dif_pos hj]
    rw [bind_pure, e]
    by_cases hb : leaf / 2 ^ j % 2 = 0
    · simp only [hL, hR, hb, ↓reduceIte, hheap]; rfl
    · simp only [hL, hR, hb, ↓reduceIte, hheap]; rfl
  rw [hprog]
  refine (TBSim.steps (s1.trans (s2.trans (s3.trans s4))) (tb_shortHash_bind' (W := 4) (fetch_1138 t4 p4) h5 hv hq
    (fun a => ?_))).mono ?_ (fun _ _ h => h)
  rotate_left
  · rw [pad64_of_aligned _ (by rw [nodeInput_length']), blocks_toQ ⟨by rw [nodeInput_length']; omega,
      by rw [nodeInput_length']⟩, nodeInput_length']; omega
  have p5 : (writeHash t4 a).pc = pcOf 1139 := by rw [pc_writeHash, p4, pcOf_add4]
  obtain ⟨t6, s6, p6, x22', x24', x20', r6, f6⟩ := rl1139_spec (writeHash t4 a) p5 P' M j (by omega) (by omega)
    (by rw [getReg_writeHash, r34.get (by decide)]; exact h22) (by rw [getReg_writeHash, r34.get (by decide)]; exact h24)
    (by rw [getReg_writeHash, r34.get (by decide), ru2.get (by decide)]; exact hI.x20)
  have fw := Frame.writeHash t4 a NOUT h12 (by decide)
  have hd := DigAt.writeHash_lo t4 a NOUT h12 (by decide)
  have f36 : Frame t3 t6 (fun A => (A = NODE + 16 ∨ A = NODE + 24) ∨ (NOUT ≤ A ∧ A < NOUT + 32)) :=
    ((f4.trans fw).trans f6).mono (fun A _ h => by rcases h with (h | h) | h; exact Or.inl h; exact Or.inr h; exact h.elim)
  refine TBSim.steps s6 (TBSim.pure ⟨⟨p6, x20', by rw [x22']; congr 1, by rw [x24', hMdef, Nat.mul_succ, Nat.sub_sub],
    by omega, hd.frame f6 (by decide) (by simp) (by simp), ?_, ?_, ?_⟩,
    nl.frame f36 (by decide) (by simp only [NODE, NOUT]; omega) (by simp only [NODE, NOUT]; omega),
    nr.frame f36 (by decide) (by simp only [NODE, NOUT]; omega) (by simp only [NODE, NOUT]; omega)⟩)
  · intro j' hj'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
    · have hw := hI.wit j' hj'
      have hs1 := sideOff_le leaf j'
      have hs2 := sideOff_le leaf j
      have hne : WM - 64 * j' + sideOff leaf j' + 16 ≤ M + sideOff leaf j ∨ M + 64 ≤ WM - 64 * j' + sideOff leaf j' := by
        unfold sideOff at hs1 hs2 ⊢; split_ifs <;> omega
      refine ((hw.frame fu2 (by omega) (by simp) (by simp)).frame f3 (by omega) ?_ ?_).frame f36 (by omega) ?_ ?_
      · simp only [NODE]; omega
      · simp only [NODE]; omega
      · simp only [NODE, NOUT]; omega
      · simp only [NODE, NOUT]; omega
    · have hs2 := sideOff_le leaf j'
      exact wsib.frame f36 (by omega) (by simp only [NODE, NOUT]; omega) (by simp only [NODE, NOUT]; omega)
  · have rw0 : RegsExcept t4 (writeHash t4 a) [] := fun r _ => getReg_writeHash t4 a r
    exact (((g3'.trans r4).trans rw0).trans r6).mono (by decide)
  · have fall := ((hI.frame.trans fu2).trans f3).trans f36
    refine fall.mono (fun A _ h => ?_)
    unfold MkW at h ⊢
    rcases h with ((h | h) | h) | h
    · rcases h with h | h | h | h | h | h | h | ⟨j', hj', h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j', by omega, h⟩))))))
    · exact h.elim
    · rcases h with h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, by omega, Or.inl h⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, by omega, Or.inr h⟩))))))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · rcases h with (h | h) | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
def rlCost (lay : Layer) : Nat := 13 + chainCount lay * 351 + 10 + 8 * leafBlocks' lay + 18 + height lay * 56
def pairRoot (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) : T3.M (T3.LayerMessage × Digest) :=
  T3.recoverPair sig index lay digits >>= fun pair => T3.rootHash index lay pair >>= fun root => pure (pair, root)
def RlPost (s0 : MachineState) (sig : Signature) (index : Nat) (lay : Layer) (WC WM ret : Nat)
    (pr : T3.LayerMessage × Digest) (t : MachineState) : Prop :=
  t.pc = pcOf ret ∧ DigAt t NOUT pr.2 ∧ DigAt t ENC pr.1.1 ∧ DigAt t (ENC + 48) pr.1.2.2 ∧ pr.1.2.1 = 0 ∧
    (∀ i < chainCount lay, DigAt t (WC - 64 * i + 48) (lval sig lay i)) ∧
    (∀ j < height lay, DigAt t (WM - 64 * j + sideOff (route index lay).1 j) (lpath sig lay j)) ∧
    RegsExcept s0 t rlRegs ∧ Frame s0 t (fun A => RlScratch A ∨ RlWit lay (route index lay).1 WC WM A)
theorem pairRoot_eq (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    pairRoot sig index lay digits =
      ((List.finRange (chainCount lay)).mapM fun i => chain lay (route index lay).2 (route index lay).1 i.val
        (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0) ((sig.layers lay).values i)) >>=
      fun ends => leafHash lay (route index lay).2 (route index lay).1 ends >>= fun value =>
        (List.finRange (height lay - 1)).foldlM (fun value j => do
          let other := (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j)
          let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
          nodeHash 3 lay.val (route index lay).2 (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1))
            pair.1 pair.2) value >>= fun node =>
        T3.rootHash index lay (T3.pairOf (route index lay).1 (height lay)
          ((sig.layers lay).path ⟨height lay - 1, Nat.sub_lt (T3.height_pos lay) Nat.one_pos⟩) 0 node) >>= fun root =>
        pure (T3.pairOf (route index lay).1 (height lay)
          ((sig.layers lay).path ⟨height lay - 1, Nat.sub_lt (T3.height_pos lay) Nat.one_pos⟩) 0 node, root) := by
  unfold pairRoot T3.recoverPair
  rcases hr : route index lay with ⟨leaf, tree⟩
  simp only [bind_assoc, pure_bind]
theorem rootHash_pairOf (index : Nat) (lay : Layer) (other node : Digest) :
    T3.rootHash index lay (T3.pairOf (route index lay).1 (height lay) other 0 node) =
      (let pair := if (route index lay).1 / 2 ^ (height lay - 1) % 2 = 0 then (node, other) else (other, node)
       nodeHash 3 lay.val (route index lay).2 (2 ^ (height lay - (height lay - 1) - 1) +
         (route index lay).1 / 2 ^ (height lay - 1 + 1)) pair.1 pair.2) := by
  unfold T3.rootHash T3.pairOf
  split_ifs <;> rfl
theorem recoverLayer_eq (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    recoverLayer sig index lay digits =
      ((List.finRange (chainCount lay)).mapM fun i => chain lay (route index lay).2 (route index lay).1 i.val
        (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0) ((sig.layers lay).values i)) >>=
      fun ends => leafHash lay (route index lay).2 (route index lay).1 ends >>= fun value =>
        (List.finRange (height lay)).foldlM (fun value j => do
          let other := (sig.layers lay).path j
          let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
          nodeHash 3 lay.val (route index lay).2 (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1))
            pair.1 pair.2) value := rfl
theorem recoverLayer_tbsim {s0 : MachineState} {sig : Signature} {index : Nat} {lay : Layer} {digits : List Nat}
    {P WC WM ret : Nat} (hpre : RlPre s0 sig index lay digits P WC WM ret) :
    TBSim image sk s0 (rlCost lay) (pairRoot sig index lay digits) (RlPost s0 sig index lay WC WM ret) := by
  set tree := (route index lay).2 with htree_def
  set leaf := (route index lay).1 with hleaf_def
  have htree : tree < 2 ^ 32 := route_tree_lt index lay hpre.hidx
  have hleaf : leaf < 2 ^ height lay := route_lt index lay
  have hH := height_le lay
  have hleaf32 : leaf < 2 ^ 32 := lt_of_lt_of_le hleaf (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hN := chainCount_cases' lay
  have hlay := lay.isLt
  have hPb := hpre.hP'
  have hWC := hpre.hWC
  have hWMC := hpre.hWMC
  have hWM := hpre.hWM
  have hP0 := hpre.hP
  obtain ⟨t1, st1, p1, x19, c24, l24, l16, r1, f1⟩ := rl997_spec s0 hpre.pc lay.val tree leaf htree hpre.x8 hpre.x9
    hpre.x18
  have f1g : ∀ A, A < 2 ^ 64 → A ≠ CHAIN + 24 → A ≠ LEAFPK + 16 → A ≠ LEAFPK + 24 →
      t1.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
    fun A hA h1 h2 h3 => f1.get hA (by rintro (h | h | h) <;> contradiction)
  have hI0 : ChainsInv t1 lay tree leaf P WC (chainCount lay) (csN4 lay) (lval sig lay) [] t1 := by
    refine ⟨p1, ⟨?_, ?_, ?_, ?_, x19, ?_, ?_, ?_, ?_⟩, ?_, fun j hj => absurd hj (by simp), fun j hj => absurd hj (by simp),
      RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [r1.get (by decide), hpre.x5]
    · rw [r1.get (by decide), hpre.x8]
    · rw [r1.get (by decide), hpre.x9]
    · rw [r1.get (by decide), hpre.x18]
    · rw [f1g _ (by decide) (by decide) (by decide) (by decide), hpre.c0]
    · rw [f1g _ (by decide) (by decide) (by decide) (by decide), hpre.c8]
    · rw [f1g _ (by decide) (by decide) (by decide) (by decide), hpre.c32]
    · rw [f1g _ (by decide) (by decide) (by decide) (by decide), hpre.c40]
    · rw [r1.get (by decide), hpre.x23]; simp
  rw [pairRoot_eq]
  refine (TBSim.steps st1 (TBSim.bind (W₂ := 10 + 8 * leafBlocks' lay + 18 + height lay * 56)
    (rl_chains (sk := sk) hpre r1 f1 hI0) (fun ends u hu => ?_))).mono (by unfold rlCost; omega) (fun _ _ h => h)
  obtain ⟨hlen, hC⟩ := hu
  have hN58 : chainCount lay ≤ 58 := by omega
  obtain ⟨v1, sv1, pv1, rv1, fv1⟩ := rl1010_spec u hC.pc (chainCount lay) (chainCount lay) (by omega) (by omega)
    (by rw [hC.ctx.x19, hlen]) (by rw [hC.regs.get (by decide), r1.get (by decide)]; exact hpre.x26)
  rw [if_pos (le_refl _)] at pv1
  obtain ⟨v2, sv2, pv2, h10, h11, h12, rv2, fv2⟩ := rl1063_spec v1 pv1 (chainCount lay) (by omega)
    (by rw [rv1.get (by decide), hC.regs.get (by decide), r1.get (by decide)]; exact hpre.x26)
  have fu2 : Frame u v2 (fun _ => False) := (fv1.trans fv2).mono (fun A _ h => by rcases h with h | h <;> exact h)
  have ru2 : RegsExcept u v2 [.x6, .x10, .x11, .x12] := (rv1.trans rv2).mono (by decide)
  have fs2 : Frame s0 v2 (fun A => ((A = CHAIN + 24 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) ∨ ChW WC ends.length A) ∨
      False) := (f1.trans hC.frame).trans fu2
  have hfar : ∀ A, A < 2 ^ 64 → (A = LEAFPK + 880 ∨ A = LEAFPK + 888) →
      v2.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) := by
    intro A hA hA'
    refine fs2.get hA ?_
    rintro ((h | h) | h)
    · simp only [CHAIN, LEAFPK] at h hA'; omega
    · exact not_ChW_hdr (by simp only [LEAFPK]; omega) (Or.inr (Or.inr hA')) (by omega) h
    · exact h
  have hhd16 : v2.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = BitVec.ofNat 64 (513 + 65536 * lay.val) := by
    rw [fu2.get (by decide) (by simp), hC.frame.get (by decide) (not_ChW_hdr (by simp only [LEAFPK]; omega)
      (Or.inl rfl) (by omega)), l16]
  have hhd24 : v2.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = BitVec.ofNat 64 (tree + 2 ^ 32 * leaf) := by
    rw [fu2.get (by decide) (by simp), hC.frame.get (by decide) (not_ChW_hdr (by simp only [LEAFPK]; omega)
      (Or.inr (Or.inl rfl)) (by omega)), l24]
  have hw : v2.readWords (BitVec.ofNat 64 LEAFPK) (8 * leafBlocks' lay) =
      wordsOf (pad64 (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (header 2 lay.val tree 0 leaf) ++
        (ends.drop 1).flatMap (bytesLE 16))) := by
    rw [leafInput_words' lay tree leaf ends hlen]
    have h0 : DigAt v2 LEAFPK (ends.getD 0 0) := by
      have := (hC.slots 0 (by omega)).frame fu2 (by decide) (by simp) (by simp)
      simpa [slotOff] using this
    have hrest : DigsAt v2 (LEAFPK + 32) (ends.drop 1) := by
      intro c hc
      simp only [List.length_drop] at hc
      have := (hC.slots (c + 1) (by omega)).frame fu2 (by unfold slotOff; simp only [LEAFPK]; split_ifs <;> omega)
        (by simp) (by simp)
      simp only [slotOff, if_neg (show c + 1 ≠ 0 by omega)] at this
      rw [show LEAFPK + 32 + 16 * c = LEAFPK + (16 * (c + 1) + 16) by ring]
      simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using this
    have hhd : v2.readWords (BitVec.ofNat 64 (LEAFPK + 16)) 2 =
        [BitVec.ofNat 64 (hdr0 2 lay.val tree 0), BitVec.ofNat 64 (hdr1 tree leaf)] := by
      rw [readWords_two, hhd16, show LEAFPK + 16 + 8 = LEAFPK + 24 from rfl, hhd24,
        hdr0_eq 2 lay.val tree 0 (by decide) (by omega) htree (by decide), hdr1_eq tree leaf htree hleaf32]
      congr 2
    rcases leafBlocks'_cases lay with ⟨hb15, hn'⟩ | ⟨hb11, hn'⟩
    · have hz : v2.readWords (BitVec.ofNat 64 (LEAFPK + 880)) 2 = [0, 0] := by
        rw [readWords_two, hfar _ (by decide) (Or.inl rfl), show LEAFPK + 880 + 8 = LEAFPK + 888 from rfl,
          hfar _ (by decide) (Or.inr rfl), hpre.l944, hpre.l952]
      have hb : 8 * leafBlocks' lay = 2 + (2 + (2 * (ends.drop 1).length + 2)) := by
        simp only [List.length_drop, hlen, hb15, hn']
      rw [hb, readWords_add, readWords_add, readWords_add, h0.words, hhd, hrest.words,
        show LEAFPK + 8 * 2 + 8 * 2 + 8 * (2 * (ends.drop 1).length) = LEAFPK + 880 by
          simp only [List.length_drop, hlen, hn', LEAFPK], hz, if_pos hn']
      simp only [List.append_assoc]
    · have hb : 8 * leafBlocks' lay = 2 + (2 + 2 * (ends.drop 1).length) := by
        simp only [List.length_drop, hlen, hb11, hn']
      rw [hb, readWords_add, readWords_add, h0.words, hhd, hrest.words, if_neg (by omega)]
      simp only [List.append_assoc, List.append_nil]
  have hl := leafInput_length' lay tree leaf ends hlen
  have hB : 1 ≤ leafBlocks' lay := by rcases leafBlocks'_cases lay with h | h <;> omega
  have h11' : v2.getReg .x11 = BitVec.ofNat 64 (64 * leafBlocks' lay) := by
    rw [h11]; unfold leafBlocks'; congr 1; omega
  have hq : hashInput v2 = toQ (pad64 (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (header 2 lay.val tree 0 leaf) ++
      (ends.drop 1).flatMap (bytesLE 16))) := by
    refine hashInput_toQ v2 _ (leafBlocks' lay - 1) LEAFPK (by rw [hl]; congr 1; omega) h10 (by decide) (by decide)
      (by rw [h11']; congr 2; omega) (by rcases leafBlocks'_cases lay with h | h <;> omega)
      (by rw [show 8 * (leafBlocks' lay - 1 + 1) = 8 * leafBlocks' lay by omega]; exact hw)
  have hblk : (toQ (pad64 (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (header 2 lay.val tree 0 leaf) ++
      (ends.drop 1).flatMap (bytesLE 16)))).blocks = leafBlocks' lay := by
    rw [blocks_toQ ⟨by rw [hl]; omega, by rw [hl]; omega⟩, hl]; omega
  have hv : hashArgumentsValid v2 = true :=
    hashArgs_const v2 LEAFPK (64 * leafBlocks' lay) NOUT h10 h11' h12 (by decide)
      (by rcases leafBlocks'_cases lay with h | h <;> omega) (by rcases leafBlocks'_cases lay with h | h <;>
        simp only [LEAFPK] <;> omega) (by decide) (by decide)
  have rs2 : RegsExcept s0 v2 oneRegs := ((r1.trans hC.regs).trans ru2).mono (by decide)
  have h5 : v2.getReg .x5 = 0 := by rw [rs2.get (by decide), hpre.x5]
  unfold leafHash
  refine (TBSim.steps (sv1.trans sv2) (tb_shortHash_bind' (W := 18 + height lay * 56) (fetch_1072 v2 pv2) h5 hv hq
    (fun a => ?_))).mono (by rw [hblk]; omega) (fun _ _ h => h)
  set tc := writeHash v2 a with htc
  have pc3 : tc.pc = pcOf 1073 := by rw [htc, pc_writeHash, pv2, pcOf_add4]
  have rtc : RegsExcept s0 tc oneRegs := fun r hr => by rw [htc, getReg_writeHash]; exact rs2 r hr
  have fwc := Frame.writeHash v2 a NOUT h12 (by decide)
  have ftc : Frame s0 tc (fun A => (((A = CHAIN + 24 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) ∨ ChW WC ends.length A) ∨
      False) ∨ (NOUT ≤ A ∧ A < NOUT + 32)) := fs2.trans fwc
  have hfar' : ∀ A, A < 2 ^ 64 → WC + 64 ≤ A → (A < CHAIN ∨ CHAIN + 80 ≤ A) → (A < LEAFPK ∨ LEAFPK + 960 ≤ A) →
      (A < NOUT ∨ NOUT + 32 ≤ A) → tc.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    refine ftc.get hA ?_
    rintro (((h | h) | h) | h)
    · simp only [CHAIN, LEAFPK] at h h2 h3; omega
    · exact not_ChW_of (by omega) h1 (by simp only [CHAIN] at h2 ⊢; omega) (by simp only [LEAFPK] at h3 ⊢; omega) h
    · exact h
    · simp only [NOUT] at h h4; omega
  obtain ⟨v4, sv4, pv4, x20, x22, rv4, fv4⟩ := rl1073_spec tc pc3 P (chainCount lay) (by omega)
    (by rw [rtc.get (by decide), hpre.x16]) (by rw [rtc.get (by decide), hpre.x26])
  have hM0 : MkInv tc sig lay leaf P WM 0 (a.extractLsb' 0 128) v4 := by
    refine ⟨pv4, x20, by rw [x22]; congr 1, ?_, by omega, ?_, fun j hj => absurd hj (by omega), rv4.mono (by decide),
      fv4.mono (fun _ _ h => h.elim)⟩
    · rw [rv4.get (by decide), rtc.get (by decide), hpre.x24]; congr 1
    · exact (DigAt.writeHash_lo v2 a NOUT h12 (by decide)).frame fv4 (by decide) (by simp) (by simp)
  have c5 : tc.getReg .x5 = 0 := by rw [rtc.get (by decide), hpre.x5]
  have c8 : tc.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [rtc.get (by decide), hpre.x8]
  have c9 : tc.getReg .x9 = BitVec.ofNat 64 tree := by rw [rtc.get (by decide), hpre.x9]
  have c18 : tc.getReg .x18 = BitVec.ofNat 64 leaf := by rw [rtc.get (by decide), hpre.x18]
  have c15 : tc.getReg .x15 = BitVec.ofNat 64 (height lay) := by rw [rtc.get (by decide), hpre.x15]
  have cn32 : tc.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 := by
    rw [hfar' _ (by decide) (by simp only [NODE]; omega) (by simp only [NODE, CHAIN]; omega)
      (by simp only [NODE, LEAFPK]; omega) (by simp only [NODE, NOUT]; omega), hpre.n32]
  have cn40 : tc.getMem (BitVec.ofNat 64 (NODE + 40)) = 0 := by
    rw [hfar' _ (by decide) (by simp only [NODE]; omega) (by simp only [NODE, CHAIN]; omega)
      (by simp only [NODE, LEAFPK]; omega) (by simp only [NODE, NOUT]; omega), hpre.n40]
  have cpath : ∀ j < height lay, DigAt tc (P + 16 * chainCount lay + 16 * j) (lpath sig lay j) := by
    intro j hj
    have hp := hpre.path j hj
    have e : lpath sig lay j = (sig.layers lay).path ⟨j, hj⟩ := by unfold lpath; rw [dif_pos hj]
    rw [e]
    exact ⟨(hfar' _ (by omega) (by omega) (by simp only [CHAIN]; omega) (by simp only [LEAFPK]; omega)
      (by simp only [NOUT]; omega)).trans hp.1, (hfar' _ (by omega) (by omega) (by simp only [CHAIN]; omega)
      (by simp only [LEAFPK]; omega) (by simp only [NOUT]; omega)).trans hp.2⟩
  have hH1 : 1 ≤ height lay := T3.height_pos lay
  have hfold := tb_foldlM_finRange (image := image) (sk := sk) (height lay - 1)
    (fun value j => do
      let other := (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j)
      let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
      nodeHash 3 lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1 pair.2)
    (a.extractLsb' 0 128) 56 (fun j value w => MkInv tc sig lay leaf P WM j value w)
    (fun i acc w hw => (rl_mk_step (j := i.val) (by omega) htree hleaf hpre.hP hpre.hP' hpre.hP8 hpre.hWM8 hpre.hWM
      (by omega) c5 c8 c9 c18 c15 (cpath i.val (by omega)) cn32 cn40 hw).mono (le_refl _) (fun _ _ h => h.1)) hM0
  refine (TBSim.steps sv4 (TBSim.bind (W₂ := 56 + 15) hfold (fun node w hw => ?_))).mono (by omega)
    (fun _ _ h => h)
  have hlast := rl_mk_step (sk := sk) (j := height lay - 1) (by omega) htree hleaf hpre.hP hpre.hP' hpre.hP8 hpre.hWM8 hpre.hWM
    (by omega) c5 c8 c9 c18 c15 (cpath (height lay - 1) (by omega)) cn32 cn40 hw
  rw [show T3.rootHash index lay (T3.pairOf leaf (height lay)
      ((sig.layers lay).path ⟨height lay - 1, Nat.sub_lt (T3.height_pos lay) Nat.one_pos⟩) 0 node) = _ from
    rootHash_pairOf index lay _ node]
  refine (TBSim.bind (W₂ := 15) hlast (fun root x hx => ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨hx, xn0, xn48⟩ := hx
  have e1 : height lay - 1 + 1 = height lay := by omega
  rw [e1] at hx
  obtain ⟨wx1, swx1, pwx1, rwx1, fwx1⟩ := rl1076_spec x hx.pc (height lay) (height lay) (by omega) (by omega)
    hx.x20 (by rw [hx.regs.get (by decide)]; exact c15)
  rw [if_pos (le_refl _)] at pwx1
  have rsw : RegsExcept s0 wx1 rlRegs := ((rtc.trans hx.regs).trans rwx1).mono (by decide)
  obtain ⟨t, st, pt, e0, e8, e48, e56, rt, ft⟩ := rl1143_full wx1 pwx1 ret (by rw [rsw.get (by decide), hpre.x1])
  have fw1 : Frame x wx1 (fun _ => False) := fwx1
  have hlp : lpath sig lay (height lay - 1) =
      (sig.layers lay).path ⟨height lay - 1, Nat.sub_lt (T3.height_pos lay) Nat.one_pos⟩ := by
    unfold lpath; rw [dif_pos (by omega)]
  refine TBSim.steps (swx1.trans st) (TBSim.pure ⟨pt, ?_, ?_, ?_, ?_, ?_, ?_, ((rsw.trans rt).mono (by decide)), ?_⟩)
  · exact (hx.val.frame fw1 (by decide) (by simp) (by simp)).frame ft (by decide) (by simp [ENC, NOUT]) (by simp [ENC, NOUT])
  · show DigAt t ENC (T3.pairOf leaf (height lay) _ 0 node).1
    have e : (T3.pairOf leaf (height lay)
        ((sig.layers lay).path ⟨height lay - 1, Nat.sub_lt (T3.height_pos lay) Nat.one_pos⟩) 0 node).1 =
        if leaf / 2 ^ (height lay - 1) % 2 = 0 then node else lpath sig lay (height lay - 1) := by
      rw [hlp]; unfold T3.pairOf; split_ifs <;> rfl
    rw [e]
    refine ⟨e0.trans ?_, e8.trans ?_⟩
    · rw [fw1.get (by decide) (by simp)]; exact xn0.1
    · rw [fw1.get (by decide) (by simp)]; exact xn0.2
  · show DigAt t (ENC + 48) (T3.pairOf leaf (height lay) _ 0 node).2.2
    have e : (T3.pairOf leaf (height lay)
        ((sig.layers lay).path ⟨height lay - 1, Nat.sub_lt (T3.height_pos lay) Nat.one_pos⟩) 0 node).2.2 =
        if leaf / 2 ^ (height lay - 1) % 2 = 0 then lpath sig lay (height lay - 1) else node := by
      rw [hlp]; unfold T3.pairOf; split_ifs <;> rfl
    rw [e]
    refine ⟨e48.trans ?_, e56.trans ?_⟩
    · rw [fw1.get (by decide) (by simp)]; exact xn48.1
    · rw [fw1.get (by decide) (by simp)]; exact xn48.2
  · show (T3.pairOf leaf (height lay) _ 0 node).2.1 = 0
    unfold T3.pairOf; split_ifs <;> rfl
  · intro i hi
    have hv := hC.wvals i (by omega)
    have hWi : WM + 64 ≤ WC - 64 * i + 48 := by omega
    refine (((hv.frame fu2 (by omega) (by simp) (by simp)).frame fwc (by omega) (by simp only [NOUT]; omega)
      (by simp only [NOUT]; omega)).frame hx.frame (by omega) (not_MkW_of (by omega) (by simp only [NODE]; omega)
      (by simp only [NOUT]; omega)) (not_MkW_of (by omega) (by simp only [NODE]; omega)
      (by simp only [NOUT]; omega))).frame (fw1.trans ft) (by omega) ?_ ?_
    · rintro (h | h | h | h | h) <;> first | exact h | (simp only [ENC] at h; omega)
    · rintro (h | h | h | h | h) <;> first | exact h | (simp only [ENC] at h; omega)
  · intro j hj
    have hs := sideOff_le leaf j
    exact (hx.wit j hj).frame (fw1.trans ft) (by omega)
      (by rintro (h | h | h | h | h) <;> first | exact h | (simp only [ENC] at h; omega))
      (by rintro (h | h | h | h | h) <;> first | exact h | (simp only [ENC] at h; omega))
  · have fall := ((ftc.trans hx.frame).trans fw1).trans ft
    refine fall.mono (fun A _ h => ?_)
    unfold RlScratch RlWit
    rcases h with ((((((hX | hC) | hF) | hN) | hM) | hF2) | hE)
    · rcases hX with h | h | h
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (by simp only [LEAFPK] at h ⊢; omega)))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (by simp only [LEAFPK] at h ⊢; omega)))))
    · unfold ChW StepW at hC
      rcases hC with (h | h) | ⟨c, hc, h⟩ | ⟨c, hc, h⟩
      · exact Or.inl (by rcases h with h | h; exact Or.inl h; exact Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
      · have hlt := slotOff_lt (show c < chainCount lay by omega)
        exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (by simp only [LEAFPK] at h ⊢; omega)))))
      · exact Or.inr (Or.inl ⟨c, by omega, h⟩)
    · exact hF.elim
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl hN)))))))))))
    · unfold MkW at hM
      rcases hM with h | h | h | h | h | h | h | ⟨j', hj', h⟩
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl h)))))))))))
      · exact Or.inr (Or.inr ⟨j', hj', h⟩)
    · exact hF2.elim
    · exact Or.inl (by simp only [ENC] at hE ⊢; omega)
end phase
end SigGolfCandidate.T3M.Expand
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC NOUT csN4 ofNat_and_mask)
set_option autoImplicit false
set_option maxRecDepth 8192
abbrev IDXV : Nat := 0x20550
theorem shr_and_mask (a k m : Nat) (ha : a < 2 ^ 64) (hm : m ≤ 64) :
    BitVec.ofNat 64 a >>> k &&& BitVec.ofNat 64 (2 ^ m - 1) = BitVec.ofNat 64 (a / 2 ^ k % 2 ^ m) := by
  rw [ofNat_shr _ _ ha, ofNat_and_mask _ _ hm]
theorem replaceWord32_lo (x c : Nat) (hc : c < 2 ^ 32) :
    replaceWord32 (BitVec.ofNat 64 x) 0 ((BitVec.ofNat 64 c).truncate 32) =
      BitVec.ofNat 64 (2 ^ 32 * (x / 2 ^ 32) + c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceWord32, Nat.zero_mul, BitVec.shiftLeft_zero, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_ofNat, BitVec.getLsbD_setWidth, BitVec.truncate_eq_setWidth, hi,
    decide_true, Bool.true_and, Nat.testBit_two_pow_mul_add _ hc]
  by_cases h : i < 32
  · have : (0xFFFFFFFF : Nat).testBit i = true := by
      rw [show (0xFFFFFFFF : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp [h]
    simp [this, h]
  · have h1 : (0xFFFFFFFF : Nat).testBit i = false := by
      rw [show (0xFFFFFFFF : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp; omega
    have h3 : c.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h1, h3, h]
    rw [show (4294967296 : Nat) = 2 ^ 32 from rfl, Nat.testBit_div_two_pow, show i - 32 + 32 = i by omega]
theorem replaceWord32_hi (x c : Nat) (hx : x < 2 ^ 32) :
    replaceWord32 (BitVec.ofNat 64 x) 1 ((BitVec.ofNat 64 c).truncate 32) =
      BitVec.ofNat 64 (2 ^ 32 * c + x) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceWord32, Nat.one_mul, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_ofNat, BitVec.getLsbD_setWidth, BitVec.truncate_eq_setWidth, hi,
    decide_true, Bool.true_and, Nat.testBit_two_pow_mul_add _ hx, BitVec.getLsbD_shiftLeft]
  by_cases h : i < 32
  · simp [h]
  · have hx' : x.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    have h1 : (0xFFFFFFFF : Nat).testBit (i - 32) = true := by
      rw [show (0xFFFFFFFF : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp; omega
    simp [h, hx', h1, show i - 32 < 64 by omega, show i - 32 < 32 by omega]
section blocks
variable (s : MachineState)
theorem l249_spec (hpc : s.pc = pcOf 249) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps image s 13 13 t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf 262 ∧
      t.getReg .x8 = BitVec.ofNat 64 3 ∧ t.getReg .x15 = BitVec.ofNat 64 6 ∧
      t.getReg .x26 = BitVec.ofNat 64 43 ∧ t.getReg .x27 = BitVec.ofNat 64 0 ∧
      t.getReg .x17 = BitVec.ofNat 64 196 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 0 % 2 ^ 6) ∧ t.getReg .x9 = BitVec.ofNat 64 (index / 2 ^ 6) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_249 codeAt_249 s hpc (by simp [eblk_249.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_249.res, E.eval]
  · simp [eblk_249.res, rv_simp]
  · simp [eblk_249.res, rv_simp]
  · simp [eblk_249.res, rv_simp]
  · simp [eblk_249.res, rv_simp]
  · simp [eblk_249.res, rv_simp]
  · simp [eblk_249.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_249.res, rv_simp, hidx]
    t3n []
    rw [show (63#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl,
      shr_and_mask _ _ _ (by omega) (by decide)]
    norm_num
  · simp only [Result.toState_getReg, eblk_249.res, rv_simp, hidx]
    t3n []
    rw [ofNat_shr _ _ (by omega)]
    norm_num
  · ex_regs eblk_249.res
  · intro A _ _; simp [eblk_249.res, rv_simp]
theorem l272_spec (hpc : s.pc = pcOf 272) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps image s 13 13 t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf 285 ∧
      t.getReg .x8 = BitVec.ofNat 64 2 ∧ t.getReg .x15 = BitVec.ofNat 64 6 ∧
      t.getReg .x26 = BitVec.ofNat 64 43 ∧ t.getReg .x27 = BitVec.ofNat 64 0 ∧
      t.getReg .x17 = BitVec.ofNat 64 196 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 6 % 2 ^ 6) ∧ t.getReg .x9 = BitVec.ofNat 64 (index / 2 ^ 12) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_272 codeAt_272 s hpc (by simp [eblk_272.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_272.res, E.eval]
  · simp [eblk_272.res, rv_simp]
  · simp [eblk_272.res, rv_simp]
  · simp [eblk_272.res, rv_simp]
  · simp [eblk_272.res, rv_simp]
  · simp [eblk_272.res, rv_simp]
  · simp [eblk_272.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_272.res, rv_simp, hidx]
    t3n []
    rw [show (63#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl,
      shr_and_mask _ _ _ (by omega) (by decide)]
    norm_num
  · simp only [Result.toState_getReg, eblk_272.res, rv_simp, hidx]
    t3n []
    rw [ofNat_shr _ _ (by omega)]
    norm_num
  · ex_regs eblk_272.res
  · intro A _ _; simp [eblk_272.res, rv_simp]
theorem l295_spec (hpc : s.pc = pcOf 295) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps image s 13 13 t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf 308 ∧
      t.getReg .x8 = BitVec.ofNat 64 1 ∧ t.getReg .x15 = BitVec.ofNat 64 7 ∧
      t.getReg .x26 = BitVec.ofNat 64 43 ∧ t.getReg .x27 = BitVec.ofNat 64 0 ∧
      t.getReg .x17 = BitVec.ofNat 64 196 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 12 % 2 ^ 7) ∧ t.getReg .x9 = BitVec.ofNat 64 (index / 2 ^ 19) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_295 codeAt_295 s hpc (by simp [eblk_295.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_295.res, E.eval]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_295.res, rv_simp, hidx]
    t3n []
    rw [show (127#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      shr_and_mask _ _ _ (by omega) (by decide)]
    norm_num
  · simp only [Result.toState_getReg, eblk_295.res, rv_simp, hidx]
    t3n []
    rw [ofNat_shr _ _ (by omega)]
    norm_num
  · ex_regs eblk_295.res
  · intro A _ _; simp [eblk_295.res, rv_simp]
theorem l318_spec (hpc : s.pc = pcOf 318) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf 332 ∧
      t.getReg .x8 = BitVec.ofNat 64 0 ∧ t.getReg .x15 = BitVec.ofNat 64 12 ∧
      t.getReg .x26 = BitVec.ofNat 64 54 ∧ t.getReg .x27 = BitVec.ofNat 64 51 ∧
      t.getReg .x17 = BitVec.ofNat 64 126 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 19 % 2 ^ 12) ∧ t.getReg .x9 = BitVec.ofNat 64 (index / 2 ^ 31) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_318 codeAt_318 s hpc (by simp [eblk_318.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_318.res, E.eval]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_318.res, rv_simp, hidx]
    t3n []
    rw [show (4095#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 12 - 1) from rfl,
      shr_and_mask _ _ _ (by omega) (by decide)]
    norm_num
  · simp only [Result.toState_getReg, eblk_318.res, rv_simp, hidx]
    t3n []
    rw [ofNat_shr _ _ (by omega)]
    norm_num
  · ex_regs eblk_318.res
  · intro A _ _; simp [eblk_318.res, rv_simp]
theorem l262_spec (hpc : s.pc = pcOf 262) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf 272 ∧
      t.getMem (BitVec.ofNat 64 0x820) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x820)) 0 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 0x82e0 ∧ t.getReg .x23 = BitVec.ofNat 64 0x6a58 ∧
      t.getReg .x24 = BitVec.ofNat 64 0x5f98 ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = 0x820) := by
  refine ⟨_, symRun_sound eblk_262 codeAt_262 s hpc (by simp [eblk_262.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_262.res, E.eval]
  · simp [eblk_262.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_262.res]
    t3n [h19]
  · simp [eblk_262.res, rv_simp]
  · simp [eblk_262.res, rv_simp]
  · simp [eblk_262.res, rv_simp]
  · ex_regs eblk_262.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_262.res]
    t3n []
    rw [if_neg (by omega)]
theorem l285_spec (hpc : s.pc = pcOf 285) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf 295 ∧
      t.getMem (BitVec.ofNat 64 0x818) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x818)) 1 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 0x7fd0 ∧ t.getReg .x23 = BitVec.ofNat 64 0x5e18 ∧
      t.getReg .x24 = BitVec.ofNat 64 0x5358 ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = 0x818) := by
  refine ⟨_, symRun_sound eblk_285 codeAt_285 s hpc (by simp [eblk_285.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_285.res, E.eval]
  · simp [eblk_285.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_285.res]
    t3n [h19]
  · simp [eblk_285.res, rv_simp]
  · simp [eblk_285.res, rv_simp]
  · simp [eblk_285.res, rv_simp]
  · ex_regs eblk_285.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_285.res]
    t3n []
    rw [if_neg (by omega)]
theorem l308_spec (hpc : s.pc = pcOf 308) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf 318 ∧
      t.getMem (BitVec.ofNat 64 0x818) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x818)) 0 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 0x7cb0 ∧ t.getReg .x23 = BitVec.ofNat 64 0x51d8 ∧
      t.getReg .x24 = BitVec.ofNat 64 0x4718 ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = 0x818) := by
  refine ⟨_, symRun_sound eblk_308 codeAt_308 s hpc (by simp [eblk_308.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_308.res, E.eval]
  · simp [eblk_308.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_308.res]
    t3n [h19]
  · simp [eblk_308.res, rv_simp]
  · simp [eblk_308.res, rv_simp]
  · simp [eblk_308.res, rv_simp]
  · ex_regs eblk_308.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_308.res]
    t3n []
    rw [if_neg (by omega)]
theorem l332_spec (hpc : s.pc = pcOf 332) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf 342 ∧
      t.getMem (BitVec.ofNat 64 0x810) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x810)) 1 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 0x7890 ∧ t.getReg .x23 = BitVec.ofNat 64 0x4458 ∧
      t.getReg .x24 = BitVec.ofNat 64 0x36d8 ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = 0x810) := by
  refine ⟨_, symRun_sound eblk_332 codeAt_332 s hpc (by simp [eblk_332.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_332.res, E.eval]
  · simp [eblk_332.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_332.res]
    t3n [h19]
  · simp [eblk_332.res, rv_simp]
  · simp [eblk_332.res, rv_simp]
  · simp [eblk_332.res, rv_simp]
  · ex_regs eblk_332.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_332.res]
    t3n []
    rw [if_neg (by omega)]
theorem c342_spec (hpc : s.pc = pcOf 342) :
    ∃ t, Steps image s 6 6 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 NOUT) = s.getMem (BitVec.ofNat 64 0xA0) then pcOf 348 else pcOf 354) ∧
      t.getReg .x28 = BitVec.ofNat 64 NOUT ∧ t.getReg .x29 = BitVec.ofNat 64 0xA0 ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_342 codeAt_342 s hpc (by simp [eblk_342.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_342.res, E.eval, CmpOp.eval, rebase, rv_simp, NOUT]
    split_ifs with h1 h2 h2 <;> simp_all
  · simp [eblk_342.res, rv_simp]
  · simp [eblk_342.res, rv_simp]
  · ex_regs eblk_342.res
  · intro A _ _; simp [eblk_342.res, rv_simp]
theorem c348_spec (hpc : s.pc = pcOf 348) (h28 : s.getReg .x28 = BitVec.ofNat 64 NOUT)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 0xA0) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (NOUT + 8)) = s.getMem (BitVec.ofNat 64 0xA8) then pcOf 351 else pcOf 354) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_348 codeAt_348 s hpc
    (by simp [eblk_348.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, h29, NOUT]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_348.res, E.eval, CmpOp.eval, rebase, rv_simp, NOUT, h28, h29]
    split_ifs with h1 h2 h2 <;> simp_all
  · ex_regs eblk_348.res
  · intro A _ _; simp [eblk_348.res, rv_simp]
theorem c351_spec (hpc : s.pc = pcOf 351) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 353 ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧
      t.getReg .x10 = BitVec.ofNat 64 0 ∧ fetch image t = some (.base .ECALL) ∧
      RegsExcept s t [.x5, .x10] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_351 codeAt_351 s hpc (by simp [eblk_351.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_351.res, E.eval]
  · simp [eblk_351.res, rv_simp]
  · simp [eblk_351.res, rv_simp]
  · rw [codeAt_353.fetch _ (by simp [Result.toState_pc, eblk_351.res, E.eval])]; rfl
  · ex_regs eblk_351.res
  · intro A _ _; simp [eblk_351.res, rv_simp]
end blocks
def lE (lay : Layer) : Nat := ![318, 295, 272, 249] lay
def lK (lay : Layer) : Nat := ![14, 13, 13, 13] lay
def lR1 (lay : Layer) : Nat := ![332, 308, 285, 262] lay
def lR2 (lay : Layer) : Nat := ![342, 318, 295, 272] lay
def lD (lay : Layer) : Nat := ![0x810, 0x818, 0x818, 0x820] lay
def lk (lay : Layer) : Nat := ![1, 0, 1, 0] lay
def lP (lay : Layer) : Nat := ![0x7890, 0x7cb0, 0x7fd0, 0x82e0] lay
def lWC (lay : Layer) : Nat := ![0x4458, 0x51D8, 0x5E18, 0x6A58] lay
def lWM (lay : Layer) : Nat := ![0x36D8, 0x4718, 0x5358, 0x5F98] lay
theorem route_fst (index : Nat) (lay : Layer) :
    (route index lay).1 = index / 2 ^ ((![19, 12, 6, 0] : Layer → Nat) lay) % 2 ^ height lay := rfl
theorem route_snd (index : Nat) (lay : Layer) :
    (route index lay).2 = index / 2 ^ ((![19, 12, 6, 0] : Layer → Nat) lay + height lay) := rfl
theorem lentry_spec (lay : Layer) (s : MachineState) (hpc : s.pc = pcOf (lE lay)) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps image s (lK lay) (lK lay) t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf (lR1 lay) ∧
      t.getReg .x8 = BitVec.ofNat 64 lay.val ∧ t.getReg .x15 = BitVec.ofNat 64 (height lay) ∧
      t.getReg .x26 = BitVec.ofNat 64 (chainCount lay) ∧ t.getReg .x27 = BitVec.ofNat 64 (csN4 lay) ∧
      t.getReg .x17 = BitVec.ofNat 64 (target lay) ∧
      t.getReg .x18 = BitVec.ofNat 64 (route index lay).1 ∧ t.getReg .x9 = BitVec.ofNat 64 (route index lay).2 ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  rw [route_fst, route_snd]
  fin_cases lay
  · exact l318_spec s hpc index hi hidx
  · exact l295_spec s hpc index hi hidx
  · exact l272_spec s hpc index hi hidx
  · exact l249_spec s hpc index hi hidx
theorem lpost_spec (lay : Layer) (s : MachineState) (hpc : s.pc = pcOf (lR1 lay)) (c : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf (lR2 lay) ∧
      t.getMem (BitVec.ofNat 64 (lD lay)) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 (lD lay))) (lk lay) ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 (lP lay) ∧ t.getReg .x23 = BitVec.ofNat 64 (lWC lay) ∧
      t.getReg .x24 = BitVec.ofNat 64 (lWM lay) ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = lD lay) := by
  fin_cases lay
  · exact l332_spec s hpc c h19
  · exact l308_spec s hpc c h19
  · exact l285_spec s hpc c h19
  · exact l262_spec s hpc c h19
end SigGolfCandidate.T3M.Expand
end
