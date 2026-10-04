import SigGolfCandidate.T3M.Verify.BCWords
import SigGolfCandidate.T3M.Verify.LayerSem
import SigGolfCandidate.T3M.Verify.LeafSem

section


namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest Layer route counterLimit encodingInput pad64)
open ClaudeWCT.WCT9 (LayerMsg)
def CounterEval : Prop := ∀ (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  (ctrE lay.val).eval s = BitVec.ofNat 64 (ClaudeWCT.W9.T3M.wbcCtr w lay).toNat
theorem counter_eval : CounterEval := fun w pk index lay msg s hs => by
  by_cases h3 : lay.val = 3
  case neg =>
    cases msg with
    | forest root => exact False.elim (h3 hs.msg.1)
    | pair left right =>
      have hm := hs.msg.2.2.2 4 (Or.inl rfl)
      simp only [ctrE, if_neg h3, E.eval, kw, UnOp.eval, hm]
      rw [counterWord]
      fin_cases lay <;> rfl
  case pos =>
    obtain rfl : lay = 3 := Fin.ext h3
    exact T3M.ctrE_eval w 3 s hs.glob.2.1
def CounterBranch : Prop := ∀ (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  ∀ d, Br.holds s (ctrBr lay.val d) ↔
    d = decide ((ClaudeWCT.W9.T3M.wbcCtr w lay).toNat ≥ counterLimit)
theorem counter_branch : CounterBranch := fun w pk index lay msg s hs d => by
  simp only [ctrBr, Br.holds, CmpOp.eval, E.eval, counter_eval w pk index lay msg s hs, kw]
  have h64 : (ClaudeWCT.W9.T3M.wbcCtr w lay).toNat < 18446744073709551616 :=
    lt_of_lt_of_le (ClaudeWCT.W9.T3M.wbcCtr w lay).isLt (by decide)
  simp [BitVec.ult, Nat.mod_eq_of_lt h64, counterLimit, ← decide_not, eq_comm]
theorem encoding_reject (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer)
    (msg : LayerMsg) (s : MachineState) (hs : LayerIn w pk index lay.val msg s)
    (hge : (ClaudeWCT.W9.T3M.wbcCtr w lay).toNat ≥ counterLimit) :
    ∃ u, Steps image s (rejectSteps lay.val) (rejectSteps lay.val) u ∧
      fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1 := by
  obtain ⟨c, hc, hpc⟩ := hs.copy
  have hcc := (T3M.copy_parts lay.val (trPc lay.val c)
    (copyCheck_at lay.val c lay.isLt hc)).2.1
  have hbrs : (rejA lay.val (trPc lay.val c)).brs = [ctrBr lay.val true] := by
    fin_cases lay <;> rfl
  obtain ⟨u, hu⟩ := spec_run hcc s hpc hs.glob.1 (by
    intro b hb
    rw [hbrs, List.mem_singleton] at hb
    subst b
    exact (counter_branch w pk index lay msg s hs true).mpr (by simp [hge]))
    (by simp)
  exact ⟨u, (by fin_cases lay <;> exact hu.steps),
    hu.ecall (by fin_cases lay <;> rfl),
    hu.regs (.x5, kw 1) (by fin_cases lay <;> simp [rejA, T3M.rejA]),
    hu.regs (.x10, kw 1) (by fin_cases lay <;> simp [rejA, T3M.rejA])⟩
def PairInputBlock : Prop := ∀ (w : WBytes) (lay : Layer) (tree leaf : Nat)
  (left right : Digest), ClaudeWCT.WCT9.pairEncodingInputP lay tree leaf left right
    (ClaudeWCT.W9.T3M.wbcCtr w lay) (ClaudeWCT.W9.T3M.wbcPad w lay) =
  blk4 left (T3.header 4 lay.val tree 0 leaf)
    (wdig w (ClaudeWCT.W9.T3M.bcCounterOff lay)) right
theorem pair_input_block : PairInputBlock := fun w lay tree leaf left right => by
  unfold ClaudeWCT.WCT9.pairEncodingInputP blk4
  simp only [List.append_assoc]
  rw [← List.append_assoc (SphincsSecurity.bytesLE 4 (ClaudeWCT.W9.T3M.wbcCtr w lay)), counterPadBytes]
  rw [show ClaudeWCT.W9.T3M.wbcPad w lay ++ ClaudeWCT.W9.T3M.wbcCtr w lay = wdig w (ClaudeWCT.W9.T3M.bcCounterOff lay) from counterPadExtract w _]
def EncodingRun : Prop := ∀ (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  (ClaudeWCT.W9.T3M.wbcCtr w lay).toNat < counterLimit →
  ∃ c, c < nCopy lay.val ∧ ∃ t,
    SpecRes (allowed lay.val) [] baseK (specA lay.val (trPc lay.val c))
      (bK lay.val) keepA s t
def SetupPost : Prop := ∀ (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  ∀ c t, SpecRes (allowed lay.val) [] baseK (specA lay.val (trPc lay.val c))
    (bK lay.val) keepA s t → EncPre w pk index lay.val c t
theorem encoding_run : EncodingRun := fun w pk index lay msg s hs hlt => by
  obtain ⟨c, hc, hpc⟩ := hs.copy
  have hcc := (T3M.copy_parts lay.val (trPc lay.val c)
    (copyCheck_at lay.val c lay.isLt hc)).1
  have hbrs : (specA lay.val (trPc lay.val c)).brs = [ctrBr lay.val false] := by
    fin_cases lay <;> rfl
  obtain ⟨t, ht⟩ := spec_run hcc s hpc hs.glob.1 (by
    intro b hb
    rw [hbrs, List.mem_singleton] at hb
    subst b
    exact (counter_branch w pk index lay msg s hs false).mpr (by simp; omega)) (by simp)
  exact ⟨c, hc, t, ht⟩
theorem setup_post : SetupPost := fun w pk index lay msg s hs c t ht => by
  obtain ⟨hlE, htE, htpE, hs7E⟩ := T3M.route_evals index lay hs.idx s hs.route
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  case refine_6 =>
    exact (ht.orig_const hs.orig).mono (fun o ho => ⟨ho, by
      fin_cases lay <;> simp [allowed, x10In, layerEnd, WIT] at * <;> omega⟩)
  case refine_1 => fin_cases lay <;> exact ht.pc rfl
  case refine_2 => exact ⟨ht.known, (ht.glob _ w pk hs.glob (RelOK.nil s)).2⟩
  case refine_3 =>
    intro L hL
    obtain rfl : L = lay := Fin.ext hL
    exact (ht.regs (.x4, tpE L.val) (by fin_cases L <;> simp [specA, T3M.specA])).trans htpE
  case refine_4 =>
    intro L hL
    obtain rfl : L = lay := Fin.ext hL
    exact (ht.regs (.x23, s7E L.val) (by fin_cases L <;> simp [specA, T3M.specA])).trans hs7E
  case refine_5 =>
    intro L hL h0
    obtain rfl : L = lay := Fin.ext hL
    exact (ht.regs (.x30, treeE L.val) (by fin_cases L <;> simp [specA, T3M.specA] at *)).trans htE
def PairSetupHash : Prop := ∀ (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (left right : Digest) (s : MachineState), LayerIn w pk index lay.val (.pair left right) s →
  ∀ c t, SpecRes (allowed lay.val) [] baseK (specA lay.val (trPc lay.val c))
    (bK lay.val) keepA s t →
  t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
  hashInput t = toQ (T3.pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay
    (route index lay).2 (route index lay).1 (.pair left right)
    (ClaudeWCT.W9.T3M.wbcCtr w lay) (ClaudeWCT.W9.T3M.wbcPad w lay)))
theorem pair_setup_hash : PairSetupHash := fun w pk index lay left right s hs c t ht => by
  have h3 : lay.val ≠ 3 := Nat.ne_of_lt hs.msg.1
  have h10 : t.getReg .x10 = BitVec.ofNat 64 (x10In lay.val) :=
    ht.known (.x10, _) (by rw [bK, if_neg h3]; exact List.mem_append_right _ (List.mem_singleton_self _))
  have h11 : t.getReg .x11 = BitVec.ofNat 64 64 :=
    ht.known (.x11, _) (by fin_cases lay <;> simp [bK, T3M.bK, layK])
  have h12 : t.getReg .x12 = BitVec.ofNat 64 256 :=
    ht.known (.x12, _) (by fin_cases lay <;> simp [bK, T3M.bK])
  refine ⟨ht.known (.x5, 0) (by fin_cases lay <;> simp [bK, T3M.bK, layK, baseK]),
    hashArgs_of t (x10In lay.val) 64 256 h10 h11 h12
      (by fin_cases lay <;> decide) (by decide) (by fin_cases lay <;> decide)
      (by decide) (by decide), ?_⟩
  change hashInput t = toQ (T3.pad64 (ClaudeWCT.WCT9.pairEncodingInputP lay
    (route index lay).2 (route index lay).1 left right
    (ClaudeWCT.W9.T3M.wbcCtr w lay) (ClaudeWCT.W9.T3M.wbcPad w lay)))
  rw [pair_input_block, pad64_blk4]
  apply hashInput_words8 t _ (x10In lay.val) (blk4_length _ _ _ _)
    h10 (by fin_cases lay <;> decide) (by fin_cases lay <;> decide) h11
  rw [wordsOf_blk4]
  simp only [List.cons.injEq, and_true]
  have hm (A : Word) : t.getMem A = memEval s (headerWrites lay.val) A := by
    simpa [specA, h3] using ht.mem A
  have frame (q : Nat) (hq : q < 64) (h16 : q ≠ 16) (h24 : q ≠ 24) :
      t.getMem (BitVec.ofNat 64 (x10In lay.val + q)) =
        s.getMem (BitVec.ofNat 64 (x10In lay.val + q)) := by
    rw [hm]
    apply memEval_frame_ofNat s _ _ (by fin_cases lay <;> simp [x10In] at * <;> omega)
    intro p hp
    simp only [headerWrites, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> fin_cases lay <;> simp [x10In] <;> omega
  refine ⟨(frame 0 (by decide) (by decide) (by decide)).trans hs.msg.2.1.1,
    (frame 8 (by decide) (by decide) (by decide)).trans hs.msg.2.1.2,
    ?_, ?_, ?_, ?_,
    (frame 48 (by decide) (by decide) (by decide)).trans hs.msg.2.2.1.1,
    (frame 56 (by decide) (by decide) (by decide)).trans ?_⟩
  case refine_5 => simpa [Nat.add_assoc] using hs.msg.2.2.1.2
  case refine_3 =>
    rw [frame 32 (by decide) (by decide) (by decide)]
    fin_cases lay <;> exact (hs.msg.2.2.2 4 (Or.inl rfl)).trans (Verify.wdig_lo w _).symm
  case refine_4 =>
    rw [frame 40 (by decide) (by decide) (by decide)]
    fin_cases lay <;> exact (hs.msg.2.2.2 5 (Or.inr rfl)).trans (Verify.wdig_hi w _).symm
  case refine_1 =>
    rw [hm]
    unfold headerWrites
    rw [memEval_cons_ofNat _ _ _ _ _ (by fin_cases lay <;> decide) (by fin_cases lay <;> decide),
      if_neg (by omega),
      memEval_cons_ofNat _ _ _ _ _ (by fin_cases lay <;> decide) (by fin_cases lay <;> decide), if_pos rfl]
    simpa [dlo, header_lo, T3.packedNodeTag, E.eval, kw] using
      congrArg (BitVec.ofNat 64) (T3M.hw4_hdr0 lay _ (T3M.tree_lt index lay hs.idx))
  case refine_2 =>
    rw [hm]
    unfold headerWrites
    rw [memEval_cons_ofNat _ _ _ _ _ (by fin_cases lay <;> decide) (by fin_cases lay <;> decide), if_pos rfl]
    simpa [dhi, header_hi, T3.packedNodeTag] using
      (T3M.route_evals index lay hs.idx s hs.route).2.2.1
def ForestSetupHash : Prop := ∀ (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (root : Digest) (s : MachineState), LayerIn w pk index lay.val (.forest root) s →
  ∀ c t, SpecRes (allowed lay.val) [] baseK (specA lay.val (trPc lay.val c))
    (bK lay.val) keepA s t →
  t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
  hashInput t = toQ (T3.pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay
    (route index lay).2 (route index lay).1 (.forest root)
    (ClaudeWCT.W9.T3M.wbcCtr w lay) (ClaudeWCT.W9.T3M.wbcPad w lay)))
theorem forest_setup_hash : ForestSetupHash := fun w pk index lay root s hs c t ht => by
  obtain rfl : lay = 3 := Fin.ext hs.msg.1
  have hH : WitHdr w s := hs.glob.2.1
  have h10 : t.getReg .x10 = BitVec.ofNat 64 256 := ht.known (.x10, _) (by simp [bK, T3M.bK])
  have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := ht.known (.x11, _) (by simp [bK, T3M.bK, layK])
  have h12 : t.getReg .x12 = BitVec.ofNat 64 256 := ht.known (.x12, _) (by simp [bK, T3M.bK])
  refine ⟨ht.known (.x5, 0) (by simp [bK, T3M.bK, layK, baseK]),
    hashArgs_of t 256 64 256 h10 h11 h12 (by decide) (by decide) (by decide)
      (by decide) (by decide), ?_⟩
  change hashInput t = toQ (pad64 (encodingInput 3 (route index 3).2 (route index 3).1 root (wctr w 3)))
  have hm (A : Word) : t.getMem A = memEval s (T3M.specA 3 (trPc 3 c)).mem A := ht.mem A
  have frame : ∀ A, A < 2 ^ 64 → A ≠ 288 → A ≠ 280 → A ≠ 272 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3
    rw [hm]
    apply memEval_frame_ofNat s _ A hA
    intro p hp
    simp only [T3M.specA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp <;> omega
  have tree_lt' := T3M.tree_lt index (3 : Layer) hs.idx
  have htpE : (tpE 3).eval s = BitVec.ofNat 64 (hdr1 (route index 3).2 (route index 3).1) :=
    (T3M.route_evals index (3 : Layer) hs.idx s hs.route).2.2.1
  have hctr : (T3M.ctrE 3).eval s = BitVec.ofNat 64 (wctr w 3).toNat :=
    T3M.ctrE_eval w (3 : Layer) s hH
  apply hashInput_words8 t _ 256 (by rw [pad64_encodingInput]; simp [encodingInput, SphincsSecurity.bytesLE_length])
    h10 (by norm_num) (by norm_num) h11
  rw [wordsOf_encodingInput]
  have m0 := hs.msg.2
  have hPZ : PZero s := hs.glob.2.2.2.1
  have hPH : PHalf s := hs.glob.2.2.2.2.1
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frame 256 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact m0.1
  · rw [show (256 : Nat) + 8 = 264 by rfl, frame 264 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact m0.2
  · rw [show (256 : Nat) + 16 = 272 by rfl, hm]
    simp only [T3M.specA]
    rw [memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    simp only [E.eval, kw]
    exact congrArg (BitVec.ofNat 64) (T3M.hw4_hdr0 (3 : Layer) _ tree_lt')
  · rw [show (256 : Nat) + 24 = 280 by rfl, hm]
    simp only [T3M.specA]
    rw [memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl, htpE]
  · rw [show (256 : Nat) + 32 = 288 by rfl, hm]
    simp only [T3M.specA]
    rw [memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    simp only [E.eval, BinOp.eval, kw]
    rw [hctr]
    apply BitVec.eq_of_toNat_eq
    rw [merge_w0_toNat]
    have hph : (s.getMem (BitVec.ofNat 64 288)).toNat / 2 ^ 32 = 0 := hPH
    have := ctr_lt w (3 : Layer)
    simp only [BitVec.toNat_ofNat] at hph ⊢
    rw [hph]; omega
  · rw [show (256 : Nat) + 40 = 296 by rfl, frame 296 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact hPZ 0x128 (by simp [pSlots])
  · rw [show (256 : Nat) + 48 = 304 by rfl, frame 304 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact hPZ 0x130 (by simp [pSlots])
  · rw [show (256 : Nat) + 56 = 312 by rfl, frame 312 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact hPZ 0x138 (by simp [pSlots])
theorem encoding_setup : EncodingSetup := fun w pk index lay msg s hs => by
  refine ⟨encoding_reject w pk index lay msg s hs, fun hlt => ?_⟩
  obtain ⟨c, hc, t, ht⟩ := encoding_run w pk index lay msg s hs hlt
  have hh : t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay
        (route index lay).2 (route index lay).1 msg
        (ClaudeWCT.W9.T3M.wbcCtr w lay) (ClaudeWCT.W9.T3M.wbcPad w lay))) := by
    cases msg with
    | forest root => exact forest_setup_hash w pk index lay root s hs c t ht
    | pair left right => exact pair_setup_hash w pk index lay left right s hs c t ht
  exact ⟨t, (by fin_cases lay <;> exact ht.steps), ht.ecall (by fin_cases lay <;> rfl),
    hh.1, hh.2.1, hh.2.2, c, hc, setup_post w pk index lay msg s hs c t ht⟩
def EncodingBlocks : Prop := ∀ (w : WBytes) (lay : Layer) (tree leaf : Nat)
  (msg : LayerMsg), (toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay tree leaf msg
    (ClaudeWCT.W9.T3M.wbcCtr w lay) (ClaudeWCT.W9.T3M.wbcPad w lay)))).blocks = 1
theorem encoding_blocks : EncodingBlocks := fun w lay tree leaf msg => by
  cases msg with
  | forest root => exact blocks_encodingInput lay tree leaf root (ClaudeWCT.W9.T3M.wbcCtr w lay)
  | pair left right =>
    change (toQ (pad64 (ClaudeWCT.WCT9.pairEncodingInputP lay tree leaf left right
      (ClaudeWCT.W9.T3M.wbcCtr w lay) (ClaudeWCT.W9.T3M.wbcPad w lay)))).blocks = 1
    rw [pair_input_block]
    exact blocks_blk4 _ _ _ _
set_option maxRecDepth 100000 in
theorem ld3Check_ok : ld3Check = true := by decide +kernel
end SigGolfCandidate.T3M.BC
end

section


set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 width maxDigit shortHash leafHash)
def chainsP (w : WBytes) (lay : Layer) (tree leaf : Nat) (digits : List Nat) : T3.M (List Digest) :=
  (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wchainHeaderPad w lay i.val) (wvalue w lay i.val)
def merkleP (w : WBytes) (index : Nat) (lay : Layer) (value : Digest) : T3.M Digest :=
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := wpath w lay (route index lay).1 j.val
    let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 3 lay.val (route index lay).2 (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1))
      pair.1 (wmerklePad w lay j.val) pair.2) value
theorem layerP_eq (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerP w index lay digits = chainsP w lay (route index lay).2 (route index lay).1 digits >>= fun ends =>
      leafHash lay (route index lay).2 (route index lay).1 ends >>= merkleP w index lay := by
  unfold layerP chainsP merkleP
  generalize route index lay = p
  obtain ⟨leaf, tree⟩ := p
  rfl
def layerHead {β : Type} (w : WBytes) (index : Nat) (lay : Layer) (M : ClaudeWCT.WCT9.LayerMsg)
    (R : List Digest → T3.M (Option β)) : T3.M (Option β) :=
  if (ClaudeWCT.W9.T3M.wbcCtr w lay).toNat ≥ counterLimit then pure none else
  shortHash (ClaudeWCT.W9.T3M.layerEncodingInputP lay (route index lay).2 (route index lay).1 M
    (ClaudeWCT.W9.T3M.wbcCtr w lay) (ClaudeWCT.W9.T3M.wbcPad w lay)) >>= fun answer =>
    match decode lay answer with
    | none => pure none
    | some digits => chainsP w lay (route index lay).2 (route index lay).1 digits >>= R
def stB (lay : Nat) : Nat := if lay = 0 then 123 else bSt lay
def cyB (lay : Nat) : Nat := if lay = 0 then 75 else bCy lay
def chainCost0 (lay : Nat) : Nat := if lay = 0 then 1086 else 2950 - 9 * tgtL lay
def chainFuel (lay : Nat) : Nat := if lay = 0 then 2321 else 1720
def layerCost (lay Z : Nat) : Nat := stepsA lay + 8 + cyB lay + lfSteps lay + chainCost0 lay - Z
def layerFuel (lay : Nat) : Nat := stepsA lay + 1 + stB lay + chainFuel lay + lfSteps lay
theorem layerCost_vals :
    layerCost 3 0 = 1262 ∧ layerCost 2 0 = 1243 ∧ layerCost 1 0 = 1244 ∧ layerCost 0 0 = 1191 := by decide
theorem layerFuel_vals :
    layerFuel 3 = 1786 ∧ layerFuel 2 = 1776 ∧ layerFuel 1 = 1777 ∧ layerFuel 0 = 2467 := by decide
theorem ckOf_lt (lay : Layer) (hlay : lay ≠ 0) (a : BitVec 256) (ds : List Nat)
    (hds : decode lay (a.extractLsb' 0 128) = some ds) : ckOf lay a < 8 := by
  rw [decode_lower lay hlay] at hds
  split_ifs at hds with h1 h2
  unfold ckOf; rw [tgtL_eq]; exact h2
theorem decode_top_sum (value : Digest) (ds : List Nat) (h : decode 0 value = some ds) :
    ds = dataDigits 0 value ∧ (dataDigits 0 value).sum = 126 := by
  rw [Search.decode_top] at h
  split_ifs at h with hp
  · exact ⟨(Option.some.inj h).symm, hp.2.2⟩
theorem s6v_chainBlock (lay : Layer) (h : lay ≠ 0) : s6v lay.val = 0x800 + chainBlock lay 42 + 1024 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide
theorem chainCount_top : chainCount (0 : Layer) = 54 := by decide
theorem layerCost_low (w : WBytes) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (a : BitVec 256) (p : Nat)
    (ds : List Nat) (hds : decode lay (a.extractLsb' 0 128) = some ds) :
    stepsA lay.val + 8 + bCy lay.val + (lctxOf w index lay a p).lowCost + lfSteps lay.val =
      layerCost lay.val ((lctxOf w index lay a p).zSum 0 43) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hD := lctx_digits w index lay a p hlay ds hds
  have hsum := LCtx.decode_lower_sum lay hlay _ ds hds
  have hck : (lctxOf w index lay a p).ck < 8 := ckOf_lt lay hlay a ds hds
  have hacc := (lctxOf w index lay a p).lowCost_accept hck ds hD hsum.1 (target lay) hsum.2
  rw [← tgtL_eq] at hacc
  simp only [layerCost, cyB, lfSteps, chainCost0, if_neg h0]
  omega
theorem layer_good_low (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (M : ClaudeWCT.WCT9.LayerMsg)
    (s : MachineState) (hs : LayerIn w pk index lay.val M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index lay ends u → GoodQ u N C Q A (ccM (R ends) K)) :
    GoodQ s (N + layerFuel lay.val) (C + layerCost lay.val 0) Q (A + layerCost lay.val 0)
      (ccM (layerHead w index lay M R) K) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hidx := hs.idx
  have hA := BC.encoding_setup w pk index lay M s hs
  have hT : 9 * tgtL lay.val ≤ 2950 := by fin_cases lay <;> decide
  have hfuel : layerFuel lay.val = stepsA lay.val + 1 + bSt lay.val + 1720 + lfSteps lay.val := by
    simp [layerFuel, stB, chainFuel, h0]
  have hcost : layerCost lay.val 0 = stepsA lay.val + 8 + bCy lay.val + lfSteps lay.val + (2950 - 9 * tgtL lay.val) := by
    simp only [layerCost, cyB, chainCost0, if_neg h0]; omega
  have hbS : 27 ≤ bSt lay.val := by unfold bSt; split <;> omega
  have hbC : 30 ≤ bCy lay.val := by unfold bCy; split <;> omega
  have hrej : BC.rejectSteps lay.val ≤ stepsA lay.val + 2 := by
    unfold BC.rejectSteps; split <;> omega
  unfold layerHead
  by_cases hctr : (ClaudeWCT.W9.T3M.wbcCtr w lay).toNat ≥ counterLimit
  · rw [if_pos hctr, ccM_pure, hK0]
    obtain ⟨u, hst, hf, h5, h10⟩ := hA.1 hctr
    exact GoodQ.steps' hst (GoodQ.reject (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  · rw [if_neg hctr]
    obtain ⟨t, hst, hf, h5, hv, hin, c, hc, hpre⟩ := hA.2 (by omega)
    have hblk := BC.encoding_blocks w lay (route index lay).2 (route index lay).1 M
    have H : ∀ a : BitVec 256, GoodQ (writeHash t a) (N + lfSteps lay.val + 1720 + bSt lay.val)
        (C + lfSteps lay.val + (2950 - 9 * tgtL lay.val) + bCy lay.val)
        Q (A + lfSteps lay.val + (2950 - 9 * tgtL lay.val) + bCy lay.val)
        (ccM (match decode lay (a.extractLsb' 0 128) with
          | none => pure none
          | some digits => chainsP w lay (route index lay).2 (route index lay).1 digits >>= R) K) := by
      intro a
      have hB := encB_step w pk index lay hlay c hc hidx t hpre a
      cases hds : decode lay (a.extractLsb' 0 128) with
      | none =>
        dsimp only
        rw [ccM_pure, hK0]
        obtain ⟨v, k, cy, hst', hf', h5', h10', hk, hcy⟩ := hB.1 hds
        exact GoodQ.steps' hst' (GoodQ.reject (Q := Q) (A := 0) hf' h5' h10') (by omega) (by omega)
          (fun hq => ⟨hq, by omega⟩)
      | some ds =>
        dsimp only
        obtain ⟨s0, hst0, hLok, hkn, hO0, hIn, hG0, hOr0, h23, h30⟩ := hB.2 (by rw [hds]; simp)
        set L := lctxOf w index lay a (trPc lay.val c) with hLd
        have hD := lctx_digits w index lay a (trPc lay.val c) hlay ds hds
        have hsum := LCtx.decode_lower_sum lay hlay _ ds hds
        have hck : L.ck < 8 := ckOf_lt lay hlay a ds hds
        have hacc := L.lowCost_accept hck ds hD hsum.1 (target lay) hsum.2
        rw [← tgtL_eq] at hacc
        have hP := L.lowP_eq hlay rfl ds hD (s6v_chainBlock lay hlay)
        have hG := L.lower_good hLok rfl rfl hck hkn hO0 (fun ends => ccM (R ends) K) (N + lfSteps lay.val) (C + lfSteps lay.val) (A + lfSteps lay.val) Q
          (fun ends t ht => by
            obtain ⟨u, hstu, hu⟩ := leafL_step w pk index lay hlay c hc hidx a s0 hkn hG0 hOr0 h23 h30 ends t ht
            exact GoodQ.steps' hstu (hR ends u hu) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩))
          s0 hIn
        have e : chainsP w lay (route index lay).2 (route index lay).1 ds = L.lowP := by
          rw [hP]; unfold chainsP; rw [LCtx.chainCount_lower lay hlay]; rfl
        rw [ccM_bind, e]
        exact GoodQ.steps' hst0 hG (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
    have := GoodQ.shortHash_bind (f := fun answer => match decode lay answer with
      | none => pure none
      | some digits => chainsP w lay (route index lay).2 (route index lay).1 digits >>= R) hf h5 hv hin H
    rw [hblk] at this
    exact GoodQ.steps' hst this (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
theorem layerIn_of_fts (w : WBytes) (pk : Digest) (idx : Nat) (root : Digest) (u : MachineState)
    (hidx : idx < 2 ^ 31) (hglob : Glob baseK w pk u) (hreg : u.getReg .x22 = BitVec.ofNat 64 idx)
    (hpc : u.pc = pcOf 588) (hroot : DigAt u 0x100 root)
    (hwit : Verify.Orig w (fun o => o < 64 ∨ 9288 ≤ o) u) (ha2 : u.getReg .x12 = BitVec.ofNat 64 0x100) :
    ∃ t, Steps image u 6 6 t ∧ LayerIn w pk idx 3 (.forest root) t := by
  obtain ⟨t, ht⟩ := spec_run BC.ld3Check_ok u hpc hglob.1 (by simp [ld3Spec]) (by simp)
  have hm : ∀ A, t.getMem A = u.getMem A := fun A => by rw [ht.mem]; rfl
  have hD : DataOK u := hglob.2.2.2.2.2
  have r19 : t.getReg .x19 = (kw 0x400000).eval u := ht.regs (.x19, kw 0x400000) (by simp [ld3Spec])
  have r21 : t.getReg .x21 = (E.ld (kw (DATA + 8))).eval u := ht.regs (.x21, .ld (kw (DATA + 8))) (by simp [ld3Spec])
  have r20 : t.getReg .x20 = (E.ld (kw (DATA + 16))).eval u :=
    ht.regs (.x20, .ld (kw (DATA + 16))) (by simp [ld3Spec])
  have r27 : t.getReg .x27 = (E.ld (kw (DATA + 24))).eval u :=
    ht.regs (.x27, .ld (kw (DATA + 24))) (by simp [ld3Spec])
  have r2 : t.getReg .x2 = (E.ld (kw (DATA + 32))).eval u := ht.regs (.x2, .ld (kw (DATA + 32))) (by simp [ld3Spec])
  have e19 : t.getReg .x19 = BitVec.ofNat 64 0x400000 := r19
  have e21 : t.getReg .x21 = BitVec.ofNat 64 M2c :=
    r21.trans (hD.word 1 (by omega) M2c (by decide) (DATA + 8) (by omega))
  have e20 : t.getReg .x20 = BitVec.ofNat 64 M1c :=
    r20.trans (hD.word 2 (by omega) M1c (by decide) (DATA + 16) (by omega))
  have e27 : t.getReg .x27 = BitVec.ofNat 64 (hw 4 3) :=
    r27.trans (hD.word 3 (by omega) (hw 4 3) (by decide) (DATA + 24) (by omega))
  have e2 : t.getReg .x2 = BitVec.ofNat 64 0x3fe00 :=
    r2.trans (hD.word 4 (by omega) 0x3fe00 (by decide) (DATA + 32) (by omega))
  have hG0 : Glob baseK w pk t := ht.glob _ _ _ hglob (RelOK.nil u)
  have hpk : preK 3 = baseK ++ [(.x19, BitVec.ofNat 64 0x400000), (.x21, BitVec.ofNat 64 M2c),
      (.x20, BitVec.ofNat 64 M1c), (.x27, BitVec.ofNat 64 (hw 4 3)), (.x2, BitVec.ofNat 64 0x3fe00),
      (.x12, BitVec.ofNat 64 256)] := rfl
  have e12 : t.getReg .x12 = BitVec.ofNat 64 256 := (ht.keep .x12 (by simp)).trans ha2
  have hk : ∀ p ∈ preK 3, t.getReg p.1 = p.2 := by
    intro p hp
    rw [hpk] at hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ht.known p hp
    · exact e19
    · exact e21
    · exact e20
    · exact e27
    · exact e2
    · exact e12
  refine ⟨t, ht.steps, ⟨by norm_num, hidx, ⟨0, by rw [BC.nCopy_eq.1]; norm_num, by rw [ht.pc rfl]; rfl⟩, ⟨hk, hG0.2⟩,
    ?_, ?_, ?_⟩⟩
  · rw [show rReg 3 = .x22 from rfl, show BC.below 3 = 0 from rfl, pow_zero, Nat.div_one,
      ht.keep .x22 (by simp), hreg]
  · exact ⟨rfl, (hm _).trans hroot.1, (hm _).trans hroot.2⟩
  · exact (hwit.mono (fun o ho => Or.inr ho.1)).frame (fun j _ _ => hm _)
theorem tree_next (index : Nat) (L : Layer) (h : L ≠ 0) : (route index L).2 = index / 2 ^ below (L.val - 1) := by
  rw [route_snd]
  fin_cases L
  · exact absurd rfl h
  all_goals rfl
theorem layerEnd_prev (L : Layer) (h : L ≠ 0) : layerEnd (L.val - 1) = layerBase L := by
  fin_cases L
  · exact absurd rfl h
  all_goals decide
end SigGolfCandidate.T3M
end
