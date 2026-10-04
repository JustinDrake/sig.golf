import SigGolfCandidate.W9Machine.WctTraceMem
import SigGolfCandidate.W9Machine.WctChainPieces
import SigGolfCandidate.W9Machine.WctChainContract
import SigGolfCandidate.W9Machine.WctPackedHeader
import SigGolfCandidate.W9Machine.WctWitnessBridge
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctTraceProgram
import SigGolfCandidate.W9Machine.WctChainControl
import SigGolfCandidate.W9Machine.WctRoutineReady

section


namespace W9Machine
set_option maxRecDepth 10000
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def hLoad (i d : Nat) : E := .ld (addC (.reg .x28) (hOff i d))
theorem leafSetup_keeps : Keeps leafSetupRel [.x25, .x10, .x11] := by
  intro r hr
  simp only [leafSetupRel]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp))]
theorem leafSetup_mem (s : MachineState) (B A : Nat)
    (hbase : s.getReg .x8 = BitVec.ofNat 64 B) (hhi : B + 1024 < 2 ^ 64) (hA : A < 2 ^ 64) :
    (leafSetupRel.toState s).getMem (BitVec.ofNat 64 A) =
      if A = B + 904 then s.getReg .x4 else
      if A = B + 896 then (hLoad 7 1).eval s else s.getMem (BitVec.ofNat 64 A) := by
  exact memEval_two s _ _ _ _ (B + 904) (B + 896) A
    (by change s.getReg .x8 + 904 = _; rw [hbase]; exact ofNat_add_ofNat B 904)
    (by change s.getReg .x8 + 896 = _; rw [hbase]; exact ofNat_add_ofNat B 896)
    (by omega) (by omega) hA
theorem leaf_trace_mem (value : ChainWord → Word) (tr : ChainTrace) (s : MachineState) (B : Nat)
    (ht : TraceMem value B tr s) (hbase : s.getReg .x8 = BitVec.ofNat 64 B)
    (hB : B + 1024 < 2 ^ 64) (hh : (hLoad 7 1).eval s = value .leafHeader)
    (hr : s.getReg .x4 = value .route) :
    TraceMem value B (tr.step .leaf) (leafSetupRel.toState s) := by
  intro x hx
  rw [leafSetup_mem s B (B + x) hbase hB (by omega)]
  simp only [ChainTrace.step, ChainTrace.read_put]
  split_ifs <;> first | omega | exact ht x hx
theorem leafSetup_regs (s : MachineState) (B : Nat) (hbase : s.getReg .x8 = BitVec.ofNat 64 B) :
    (leafSetupRel.toState s).getReg .x10 = BitVec.ofNat 64 (B + 880) ∧
    (leafSetupRel.toState s).getReg .x11 = 128 ∧
    (leafSetupRel.toState s).pc = s.getReg .x23 &&& ~~~1#64 := by
  simp only [leafSetupRel, Result.toState_getReg, Result.toState_pc,
    RegFile.get, RegFile.set, addC_eval, E.eval, BinOp.eval, hbase]
  exact ⟨ofNat_add_ofNat B 880, trivial, trivial⟩
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
def wctChainClobbers : List Reg := [.x3, .x10, .x11, .x12, .x14, .x25]
theorem chainPiece_keeps (p : ChainPiece) : Keeps p.result wctChainClobbers := by
  intro r hr
  have hsmall : ∀ ws : List Reg, (∀ x ∈ ws, x ∈ wctChainClobbers) → r ∉ ws := by
    intro ws h hmem; exact hr (h r hmem)
  cases p with
  | mk pc words kind =>
    cases kind with
    | head off dst chain digit =>
      exact headRHRel_keeps _ _ _ _ _ _ r
        (hsmall _ (by simp [wctChainClobbers]))
    | rung digit dst =>
      exact rungRRel_keeps _ _ _ _ r
        (hsmall _ (by simp [wctChainClobbers]))
    | copy off dst =>
      exact copyFHRel_keeps _ _ _ _ r
        (hsmall _ (by simp [wctChainClobbers]))
    | jump target => rfl
    | leaf => exact leafSetup_keeps r (hsmall _ (by simp [wctChainClobbers]))
end W9Machine
end

section


namespace W9Machine
set_option maxRecDepth 10000
open SigGolfCandidate.Legacy.Riscv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
theorem hKey_relative (s : MachineState) (H chain digit : Nat)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (H + 2048))
    (hH : H + 4096 < 2 ^ 64) (hc : chain < 8) (hd : digit < 3) :
    (hKey chain digit).eval s = BitVec.ofNat 64 (H + 64 * chain + 8 * digit) := by
  simp only [hKey, Addr.eval, E.eval, h28, hOff]
  convert ofNat_add_off0 (H + 2048) (64 * chain + 8 * digit) 2048 (by omega) (by omega) using 1 <;> congr 1; omega
theorem headRHRel_obligations (s : MachineState) (B H off dst pc chain digit : Nat)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 B)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (H + 2048))
    (hB : B + 1024 ≤ 2 ^ 24) (hH : H + 1024 ≤ 2 ^ 24)
    (haB : B % 8 = 0) (haH : H % 8 = 0) (hao : off % 8 = 0)
    (ho : off + 64 ≤ 1024) (hc : chain < 8) (hd : digit < 3) :
    ∀ o ∈ (headRHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) pc chain digit).st.obl,
      o.holds s := by
  intro o hm
  simp only [headRHRel, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  change accessValid ((kAt .x8 (BitVec.ofNat 64 off) 16).eval s) 8 = true
  rw [relative_key s .x8 B off 16 h8]
  exact valid_ofNat _ _ (by omega) (by omega)
theorem rungRRel_obligations (s : MachineState) (B off digit pc : Nat) (dst : Option Word)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (B + off))
    (hB : B + 1024 ≤ 2 ^ 24) (haB : B % 8 = 0) (hao : off % 8 = 0)
    (ho : off + 64 ≤ 1024) :
    ∀ o ∈ (rungRRel .x8 digit dst pc).st.obl, o.holds s := by
  intro o hm
  simp only [rungRRel, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · change (s.getReg .x10).toNat % 8 = 0
    rw [h10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : B + off < 2 ^ 64)]
    omega
  · change accessValid ((⟨some (.reg .x10), 17⟩ : Addr).eval s) 1 = true
    have he : (⟨some (.reg .x10), 17⟩ : Addr).eval s = BitVec.ofNat 64 (B + off + 17) := by
      simp only [Addr.eval, E.eval, h10]
      exact ofNat_add_ofNat (B + off) 17
    rw [he]
    exact valid_ofNat _ _ (by omega) (by omega)
theorem copyFHRel_obligations (s : MachineState) (B off dst pc : Nat)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 B) (hB : B + 1024 ≤ 2 ^ 24)
    (haB : B % 8 = 0) (hao : off % 8 = 0) (had : dst % 8 = 0)
    (ho : off + 64 ≤ 1024) (hd : dst + 16 ≤ 1024) :
    ∀ o ∈ (copyFHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) pc).st.obl, o.holds s := by
  intro o hm
  simp only [copyFHRel, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  all_goals
    simp only [Oblig.holds, relative_key s .x8 B _ _ h8]
    exact valid_ofNat _ _ (by omega) (by omega)
end W9Machine
end

section


set_option autoImplicit false
namespace W9Machine.Chain
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem Inv.headerLoad {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128}
    {rank : Fin 728} {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv u index k j tr answers s)
    (t d : Nat) (ht : t < 7) (hd : d < 3) :
    (packedHeader t d).eval s = BitVec.ofNat 64 (V3.chainLow index k.val j.val t d) := by
  exact packedHeader_eval s index k.val j.val t d
    ((hs.keep .x31 (by decide)).trans hu.prefixReg) ht hd
theorem Inv.leafLoad {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128}
    {rank : Fin 728} {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv u index k j tr answers s) :
    (hLoad 7 1).eval s = (SigGolfCandidate.T3.header 6 k.val index 0 j.val).extractLsb' 0 64 := by
  have hk := k.isLt
  have hr := (hs.keep .x28 (by decide)).trans hu.headerReg
  have he := hKey_relative s (table k) 7 1 hr
    (by unfold table headerTable; omega) (by decide) (by decide)
  have hm := hs.frame (table k + 456) (by unfold table headerTable; omega)
    (by unfold writes base coordinateBase table headerTable; omega)
  have hl : (hLoad 7 1).eval s = s.getMem ((hKey 7 1).eval s) := by
    simp only [hLoad, hKey, Addr.eval, E.eval, addC_eval]
  rw [hl, he]
  simpa only [Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] using hm.trans hu.leafHeader
end W9Machine.Chain
end

section

namespace W9Machine.Chain
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem Inv.rung {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv u index k j tr answers s)
    (digit pc old : Nat) (dst : Option Nat) (ans : BitVec 256)
    (hn : 0 < answers.length) (hi : 448 ≤ tr.input ∧ tr.input + 64 ≤ 1024)
    (hdst : 448 ≤ dst.getD tr.output ∧ dst.getD tr.output + 32 ≤ 1024)
    (hc : tr.chain < 7) (ho : old < 3) (hd : digit < 3)
    (hh : tr.read (tr.input + 16) = .header tr.chain old) :
    Inv u index k j (tr.step (.rung digit dst)) (answers ++ [ans])
      (writeHash ((rungRRel .x8 digit (dst.map (BitVec.ofNat 64)) pc).toState s) ans) := by
  have hk := k.isLt
  have hB : base k + 1024 < 2 ^ 64 := by unfold base coordinateBase; omega
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  have hp := hs.pointers hn
  have hstep := packedPos_eval s digit hd
    ((hs.keep .x7 (by decide)).trans hu.stepOne)
    ((hs.keep .x13 (by decide)).trans hu.stepTwo)
  let prepared := (rungRRel .x8 digit (dst.map (BitVec.ofNat 64)) pc).toState s
  have h12 : prepared.getReg .x12 = BitVec.ofNat 64 (base k + dst.getD tr.output) := by
    cases dst with
    | none => exact hp.2
    | some d =>
      simp only [prepared, rungRRel, Option.map, Option.getD_some, Result.toState_getReg,
        RegFile.get, RegFile.set, addC_eval, E.eval, hb]
      exact ofNat_add_ofNat (base k) d
  have hf : Frame s prepared (writes k) :=
    (rungRRel_frame s .x8 digit pc (base k + tr.input) (dst.map (BitVec.ofNat 64))
      hp.1 (by omega) hstep).mono (by intro A hA hw; unfold writes; omega)
  have hhash : Frame prepared (writeHash prepared ans) (writes k) := by
    intro A hA hnot
    rw [writeHash_getMem_ofNat prepared ans (base k + dst.getD tr.output) A h12 hA (by omega)]
    unfold writes at hnot
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  refine ⟨?_, ?_, ?_, ?_, tr.available_step _ hs.available, ?_, ?_⟩
  · intro r hr
    rw [writeHash_getReg]
    exact ((chainPiece_keeps ⟨pc, [], .rung digit dst⟩).reg s hr).trans (hs.keep r hr)
  · exact ((hs.frame.trans hf).trans hhash).mono (by intro A hA hw; rcases hw with (h | h) | h <;> exact h)
  · let th : ChainTrace :=
      { tr.put (tr.input + 16) (.header tr.chain digit) with
        output := dst.getD tr.output,
        valid := tr.valid && (match tr.read (tr.input + 16) with
          | .header chain _ => chain == tr.chain | _ => false) }
    apply hash_trace_append (originalValue u index k j) answers ans th prepared (base k)
      ?_ ?_ hs.count h12 hB hdst.2
    · apply rung_trace_mem _ tr s (base k) digit pc (dst.map (BitVec.ofNat 64))
        hs.memory hp.1 hB hi.2 hstep
      rw [show base k + tr.input + 16 = base k + (tr.input + 16) by omega,
        hs.memory (tr.input + 16) (by omega), hh]
      exact wct_header_step k.val index j.val tr.chain old digit hk hu.indexBound j.isLt hc ho hd
    · exact tr.available_put (tr.input + 16) (.header tr.chain digit) hs.available trivial
  · change (tr.queries ++ [_]).length = (answers ++ [ans]).length
    simp only [List.length_append, List.length_singleton, hs.count]
  · rw [writeHash_getReg]
    exact ((rungRRel_keeps .x8 digit (dst.map (BitVec.ofNat 64)) pc).reg s (by decide)).trans hs.hashLen
  · intro _
    rw [writeHash_getReg, writeHash_getReg]
    exact ⟨((rungRRel_keeps .x8 digit (dst.map (BitVec.ofNat 64)) pc).reg s (by decide)).trans hp.1, h12⟩
end W9Machine.Chain
end

section

namespace W9Machine.Chain
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem Inv.head {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv u index k j tr answers s)
    (off dst pc chain digit : Nat) (ans : BitVec 256)
    (hoff : 448 ≤ off ∧ off + 64 ≤ 1024) (hdst : 448 ≤ dst ∧ dst + 32 ≤ 1024)
    (hc : chain < 7) (hd : digit < 3) :
    Inv u index k j (tr.step (.head off dst chain digit)) (answers ++ [ans])
      (writeHash ((headRHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst)
        pc chain digit).toState s) ans) := by
  have hk := k.isLt
  have hB : base k + 1024 < 2 ^ 64 := by unfold base coordinateBase; omega
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  have hp := headRHRel_addresses .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst)
    pc chain digit s
  rw [hb, ofNat_add_ofNat, ofNat_add_ofNat] at hp
  let prepared := (headRHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) pc chain digit).toState s
  have hf : Frame s prepared (writes k) :=
    (headRHRel_frame s .x8 (base k) off dst pc chain digit hb (by omega)).mono
      (by intro A hA hw; unfold writes; omega)
  have hhash : Frame prepared (writeHash prepared ans) (writes k) := by
    intro A hA hn
    rw [writeHash_getMem_ofNat prepared ans (base k + dst) A hp.2 hA (by omega)]
    unfold writes at hn
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  refine ⟨?_, ?_, ?_, ?_, tr.available_step _ hs.available, ?_, ?_⟩
  · intro r hr
    rw [writeHash_getReg]
    exact ((chainPiece_keeps ⟨pc, [], .head off dst chain digit⟩).reg s hr).trans (hs.keep r hr)
  · exact ((hs.frame.trans hf).trans hhash).mono (by intro A hA hw; rcases hw with (h | h) | h <;> exact h)
  · let th : ChainTrace :=
      { tr.put (off + 16) (.header chain digit) with
        input := off, output := dst, chain := chain }
    apply hash_trace_append (originalValue u index k j) answers ans th prepared (base k)
      ?_ ?_ hs.count hp.2 hB hdst.2
    · exact head_trace_mem _ tr s (base k) off dst pc chain digit hs.memory hb hB hoff.2
        (hs.headerLoad hu chain digit hc hd)
    · exact tr.available_put _ (.header chain digit) hs.available trivial
  · change (tr.queries ++ [_]).length = (answers ++ [ans]).length
    simp only [List.length_append, List.length_singleton, hs.count]
  · rw [writeHash_getReg]
    exact ((headRHRel_keeps .x8 _ _ pc chain digit).reg s (by decide)).trans hs.hashLen
  · intro _
    rw [writeHash_getReg, writeHash_getReg]
    exact hp
end W9Machine.Chain
end

section

namespace W9Machine.Chain
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem Inv.copy {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv u index k j tr answers s)
    (off dst pc : Nat) (hoff : off + 64 ≤ 1024)
    (hdst : 448 ≤ dst ∧ dst + 16 ≤ 1024) :
    Inv u index k j (tr.step (.copy off dst)) answers
      ((copyFHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) pc).toState s) := by
  have hk := k.isLt
  have hB : base k + 1024 < 2 ^ 64 := by unfold base coordinateBase; omega
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  have hf := (copyFHRel_frame s .x8 (base k) off dst pc hb (by omega)).mono
    (show ∀ A, A < 2 ^ 64 → A = base k + dst ∨ A = base k + dst + 8 → writes k A from
      by intro A hA hw; unfold writes; omega)
  refine ⟨?_, ?_, ?_, hs.count, tr.available_step _ hs.available, ?_, ?_⟩
  · intro r hr
    exact ((chainPiece_keeps ⟨pc, [], .copy off dst⟩).reg s hr).trans (hs.keep r hr)
  · exact (hs.frame.trans hf).mono (by intro A hA hw; exact hw.elim id id)
  · exact copy_trace_mem _ tr s (base k) off dst pc hs.memory hb hB hoff hdst.2
  · exact ((copyFHRel_keeps .x8 _ _ pc).reg s (by decide)).trans hs.hashLen
  · intro hn
    exact ⟨((copyFHRel_keeps .x8 _ _ pc).reg s (by decide)).trans (hs.pointers hn).1,
      ((copyFHRel_keeps .x8 _ _ pc).reg s (by decide)).trans (hs.pointers hn).2⟩
theorem Inv.jump {index : Nat} {k : Fin 9} {j : Fin 128}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hs : Inv u index k j tr answers s) (pc target : Nat) :
    Inv u index k j (tr.step (.jump target)) answers
      ((ChainPiece.result ⟨pc, [], .jump target⟩).toState s) := by
  refine ⟨?_, ?_, ?_, hs.count, hs.available, ?_, ?_⟩
  · intro r hr
    exact ((chainPiece_keeps ⟨pc, [], .jump target⟩).reg s hr).trans (hs.keep r hr)
  · intro A hA hn; exact hs.frame A hA hn
  · intro off ho; exact hs.memory off ho
  · exact hs.hashLen
  · exact hs.pointers
end W9Machine.Chain
end

section




namespace W9Machine.Chain
set_option maxRecDepth 10000
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem Inv.hashEffect {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv u index k j tr answers s)
    (p : ChainPiece) (hh : p.isHash = true) (hg : pieceGuard tr p.kind = true)
    (ans : BitVec 256) :
    Inv u index k j (tr.step p.kind) (answers ++ [ans]) (writeHash (p.result.toState s) ans) := by
  cases p with
  | mk pc words kind =>
    cases kind with
    | head off dst chain digit =>
      simp only [pieceGuard, decide_eq_true_eq] at hg
      obtain ⟨hlo, hhi, _, hdlo, hdhi, _, hc, hd⟩ := hg
      exact hs.head hu off dst pc chain digit ans ⟨hlo, hhi⟩ ⟨hdlo, hdhi⟩ hc hd
    | rung digit dst =>
      simp only [pieceGuard, Bool.and_eq_true, decide_eq_true_eq] at hg
      obtain ⟨⟨hn, hilo, hihi, _, hdlo, hdhi, _, hd⟩, hheader⟩ := hg
      cases he : tr.read (tr.input + 16) with
      | header chain old =>
        simp only [he, decide_eq_true_eq] at hheader
        obtain ⟨hechain, hc, ho⟩ := hheader
        subst chain
        exact hs.rung hu digit pc old dst ans (by rw [← hs.count]; exact hn)
          ⟨hilo, hihi⟩ ⟨hdlo, hdhi⟩ hc ho hd he
      | original off => simp [he] at hheader
      | route => simp [he] at hheader
      | answer q i => simp [he] at hheader
      | leafHeader => simp [he] at hheader
    | copy off dst => contradiction
    | jump target => contradiction
    | leaf => contradiction
theorem Inv.plainEffect {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv u index k j tr answers s)
    (p : ChainPiece) (hh : p.isHash = false) (hl : p.kind ≠ .leaf)
    (hg : pieceGuard tr p.kind = true) :
    Inv u index k j (tr.step p.kind) answers (p.result.toState s) := by
  cases p with
  | mk pc words kind =>
    cases kind with
    | head off dst chain digit => contradiction
    | rung digit dst => contradiction
    | copy off dst =>
      simp only [pieceGuard, decide_eq_true_eq] at hg
      exact hs.copy hu off dst pc hg.1 ⟨hg.2.2.1, hg.2.2.2.1⟩
    | jump target => exact hs.jump pc target
    | leaf => exact False.elim (hl rfl)
theorem Inv.plainObligations {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv u index k j tr answers s)
    (p : ChainPiece) (hh : p.isHash = false) (hg : pieceGuard tr p.kind = true) :
    ∀ o ∈ p.result.st.obl, o.holds s := by
  have hk := k.isLt
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  have h28 := (hs.keep .x28 (by decide)).trans hu.headerReg
  have hB : base k + 1024 ≤ 2 ^ 24 := by unfold base coordinateBase; omega
  have hH : table k + 1024 ≤ 2 ^ 24 := by unfold table headerTable; omega
  have haB : base k % 8 = 0 := by unfold base coordinateBase; omega
  have haH : table k % 8 = 0 := by unfold table headerTable; omega
  cases p with
  | mk pc words kind =>
    cases kind with
    | head off dst chain digit => contradiction
    | rung digit dst => contradiction
    | copy off dst =>
      simp only [pieceGuard, decide_eq_true_eq] at hg
      exact copyFHRel_obligations s (base k) off dst pc hb hB haB hg.2.1 hg.2.2.2.2
        hg.1 hg.2.2.2.1
    | jump target => intro o ho; contradiction
    | leaf =>
      intro o ho
      simp only [ChainPiece.result, leafSetupRel, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl
      · change accessValid (s.getReg .x8 + 904) 8 = true
        rw [hb]
        change accessValid (BitVec.ofNat 64 (base k) + BitVec.ofNat 64 904) 8 = true
        rw [ofNat_add_ofNat]
        exact valid_ofNat _ _ (by omega) (by omega)
      · change accessValid (s.getReg .x8 + 896) 8 = true
        rw [hb]
        change accessValid (BitVec.ofNat 64 (base k) + BitVec.ofNat 64 896) 8 = true
        rw [ofNat_add_ofNat]
        exact valid_ofNat _ _ (by omega) (by omega)
      · change accessValid ((hKey 7 1).eval s) 8 = true
        rw [hKey_relative s (table k) 7 1 h28 (by omega) (by decide) (by decide)]
        exact valid_ofNat _ _ (by omega) (by omega)
end W9Machine.Chain
end

section

namespace W9Machine
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (pad64)
def prepareTrace (tr : ChainTrace) : ChainPieceKind → ChainTrace
  | .head off dst chain digit =>
      { tr.put (off + 16) (.header chain digit) with
        input := off, output := dst, chain := chain }
  | .rung digit dst =>
      { tr.put (tr.input + 16) (.header tr.chain digit) with
        output := dst.getD tr.output,
        valid := tr.valid && (match tr.read (tr.input + 16) with
          | .header chain _ => chain == tr.chain | _ => false) }
  | kind => tr.step kind
theorem pieceQuery_prepared (tr : ChainTrace) (p : ChainPiece) (hh : p.isHash = true) :
    pieceQuery tr p = (List.range 8).map fun i =>
      (prepareTrace tr p.kind).read ((prepareTrace tr p.kind).input + 8 * i) := by
  have qhash (t : ChainTrace) : t.hash.queries = t.queries ++
      [(List.range 8).map fun i => t.read (t.input + 8 * i)] := rfl
  cases p with
  | mk pc words kind =>
    cases kind <;> simp only [ChainPiece.isHash, Bool.false_eq_true] at hh
    all_goals first
      | contradiction
      | simp [pieceQuery, ChainTrace.step, qhash, prepareTrace, ChainTrace.put,
          List.getD_eq_getElem?_getD]
    all_goals intro a ha; rfl
theorem preparedQuery (value : ChainWord → Word) (B : Nat) (tr : ChainTrace)
    (p : ChainPiece) (s : MachineState) (hh : p.isHash = true)
    (hm : TraceMem value B (prepareTrace tr p.kind) s)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (B + (prepareTrace tr p.kind).input))
    (h11 : s.getReg .x11 = 64) (hB : B + 1024 < 2 ^ 64)
    (hi : (prepareTrace tr p.kind).input + 64 ≤ 1024)
    (ha : (B + (prepareTrace tr p.kind).input) % 8 = 0) :
    hashInput s = toQ (pad64 (wordBytes ((pieceQuery tr p).map value))) ∧
    (toQ (pad64 (wordBytes ((pieceQuery tr p).map value)))).blocks = 1 := by
  have hl : (wordBytes ((pieceQuery tr p).map value)).length = 64 := by
    rw [wordBytes_length, List.length_map, pieceQuery_prepared tr p hh,
      List.length_map, List.length_range]
  rw [SigGolfCandidate.T3M.pad64_of_aligned _ (by omega)]
  refine ⟨TraceMem.hashInput value B (prepareTrace tr p.kind) s _ hm h10 h11 hB hi ha hl ?_, ?_⟩
  · rw [wordsOf_wordBytes, pieceQuery_prepared tr p hh, List.map_map]
    rfl
  · rw [blocks_toQ ⟨by omega, by omega⟩, hl]
end W9Machine
end

section



namespace W9Machine.Chain
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (pad64)
structure PreparedHash (value : ChainWord → Word) (tr : ChainTrace) (p : ChainPiece)
    (s : MachineState) : Prop where
  obligations : ∀ o ∈ p.result.st.obl, o.holds s
  stop : p.result.stop = .ecall
  mode : (p.result.toState s).getReg .x5 = 0
  valid : hashArgumentsValid (p.result.toState s) = true
  query : hashInput (p.result.toState s) = toQ (pad64 (wordBytes ((pieceQuery tr p).map value)))
  blocks : (toQ (pad64 (wordBytes ((pieceQuery tr p).map value)))).blocks = 1
theorem Inv.hashReady {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv u index k j tr answers s)
    (p : ChainPiece) (hh : p.isHash = true) (hg : pieceGuard tr p.kind = true) :
    PreparedHash (chainValue (originalValue u index k j) answers) tr p s := by
  have hk := k.isLt
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  have h28 := (hs.keep .x28 (by decide)).trans hu.headerReg
  have h5 := (hs.keep .x5 (by decide)).trans hu.hashMode
  have hB : base k + 1024 ≤ 2 ^ 24 := by unfold base coordinateBase; omega
  have hBig : base k + 1024 < 2 ^ 64 := by omega
  have hH : table k + 1024 ≤ 2 ^ 24 := by unfold table headerTable; omega
  have haB : base k % 8 = 0 := by unfold base coordinateBase; omega
  have haH : table k % 8 = 0 := by unfold table headerTable; omega
  cases p with
  | mk pc words kind =>
    cases kind with
    | head off dst chain digit =>
      simp only [pieceGuard, decide_eq_true_eq] at hg
      obtain ⟨hlo, hhi, halign, hdlo, hdhi, hdalign, hchain, hdigit⟩ := hg
      have hp := headRHRel_addresses .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) pc chain digit s
      rw [hb, ofNat_add_ofNat, ofNat_add_ofNat] at hp
      have hlen := ((headRHRel_keeps .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) pc chain digit).reg s (by decide)).trans hs.hashLen
      have hm := head_trace_mem _ tr s (base k) off dst pc chain digit hs.memory hb hBig hhi
        (hs.headerLoad hu chain digit hchain hdigit)
      have hq := preparedQuery _ (base k) tr ⟨pc, words, .head off dst chain digit⟩ _ hh hm
        hp.1 hlen hBig hhi (by change (base k + off) % 8 = 0; omega)
      refine ⟨?_, rfl, ?_, ?_, hq.1, hq.2⟩
      · exact headRHRel_obligations s (base k) (table k) off dst pc chain digit
          hb h28 hB hH haB haH halign hhi (by omega) hdigit
      · exact ((headRHRel_keeps .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) pc chain digit).reg s (by decide)).trans h5
      · exact hashArgs_const _ (base k + off) 64 (base k + dst) hp.1 hlen hp.2
          (by omega) (by decide) (by omega) (by omega) (by omega)
    | rung digit dst =>
      simp only [pieceGuard, Bool.and_eq_true, decide_eq_true_eq] at hg
      obtain ⟨⟨hn, hilo, hihi, hai, hdlo, hdhi, had, hd⟩, hheader⟩ := hg
      have hp := hs.pointers (by rw [← hs.count]; exact hn)
      have hstep := packedPos_eval s digit hd
        ((hs.keep .x7 (by decide)).trans hu.stepOne)
        ((hs.keep .x13 (by decide)).trans hu.stepTwo)
      let prepared := (rungRRel .x8 digit (dst.map (BitVec.ofNat 64)) pc).toState s
      have h10 := ((rungRRel_keeps .x8 digit (dst.map (BitVec.ofNat 64)) pc).reg s (by decide)).trans hp.1
      have hlen := ((rungRRel_keeps .x8 digit (dst.map (BitVec.ofNat 64)) pc).reg s (by decide)).trans hs.hashLen
      have h12 : prepared.getReg .x12 = BitVec.ofNat 64 (base k + dst.getD tr.output) := by
        cases dst with
        | none => exact hp.2
        | some d =>
          simp only [prepared, rungRRel, Option.map, Option.getD_some, Result.toState_getReg,
            RegFile.get, RegFile.set, addC_eval, E.eval, hb]
          exact ofNat_add_ofNat (base k) d
      have hm : TraceMem (chainValue (originalValue u index k j) answers) (base k)
          (prepareTrace tr (.rung digit dst)) prepared := by
        apply rung_trace_mem _ tr s (base k) digit pc (dst.map (BitVec.ofNat 64))
          hs.memory hp.1 hBig hihi hstep
        cases he : tr.read (tr.input + 16) with
        | header chain old =>
          simp only [he, decide_eq_true_eq] at hheader
          obtain ⟨hechain, hc, ho⟩ := hheader
          subst chain
          rw [show base k + tr.input + 16 = base k + (tr.input + 16) by omega,
            hs.memory (tr.input + 16) (by omega), he]
          exact wct_header_step k.val index j.val tr.chain old digit hk hu.indexBound j.isLt hc ho hd
        | original off => simp [he] at hheader
        | route => simp [he] at hheader
        | answer q i => simp [he] at hheader
        | leafHeader => simp [he] at hheader
      have hq := preparedQuery _ (base k) tr ⟨pc, words, .rung digit dst⟩ prepared hh hm
        h10 hlen hBig hihi (by change (base k + tr.input) % 8 = 0; omega)
      refine ⟨?_, rfl, ?_, ?_, hq.1, hq.2⟩
      · exact rungRRel_obligations s (base k) tr.input digit pc (dst.map (BitVec.ofNat 64))
          hp.1 hB haB hai hihi
      · exact ((rungRRel_keeps .x8 digit (dst.map (BitVec.ofNat 64)) pc).reg s (by decide)).trans h5
      · exact hashArgs_const prepared (base k + tr.input) 64 (base k + dst.getD tr.output)
          h10 hlen h12 (by omega) (by decide) (by omega) (by omega) (by omega)
    | copy off dst => contradiction
    | jump target => contradiction
    | leaf => contradiction
end W9Machine.Chain
end

section

set_option autoImplicit false
namespace W9Machine.Chain
set_option maxRecDepth 10000
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
theorem merkleField_of_frame {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9}
    {j : Fin 128} {rank : Fin 728} {u s : MachineState} (hu : Pre L w index k j rank u)
    (hf : Frame u s (writes k)) (off : Nat) (ha : off % 8 = 0) (ho : off + 16 ≤ 448) :
    DigAt s (base k + off) (wdig w (V3.regionOffset k.val + off)) := by
  have hk := k.isLt
  have h0 := hu.origW off (by omega) ha
  have h1 : OrigW w u (base k + off + 8) := by
    simpa only [Nat.add_assoc] using hu.origW (off + 8) (by omega) (by omega)
  have hdig := DigAt_origW h0 h1 (by unfold base coordinateBase; omega)
  have he : base k + off - 0x800 = V3.regionOffset k.val + off := by
    unfold base coordinateBase V3.regionOffset
    omega
  rw [he] at hdig
  exact hdig.frame hf (by unfold base coordinateBase; omega)
    (by unfold writes; omega) (by unfold writes; omega)
theorem merklePad_of_frame {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9}
    {j : Fin 128} {rank : Fin 728} {u s : MachineState} (hu : Pre L w index k j rank u)
    (hf : Frame u s (writes k)) (l : Nat) (hl : l < 7) :
    DigAt s (base k + V3.blockOffset l + 32) (V3.nodePad w k.val l) := by
  have h := merkleField_of_frame hu hf (V3.blockOffset l + 32)
    (by unfold V3.blockOffset; omega) (by unfold V3.blockOffset; omega)
  simpa only [V3.nodePad, Nat.add_assoc] using h
theorem merkleSibling_of_frame {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9}
    {j : Fin 128} {rank : Fin 728} {u s : MachineState} (hu : Pre L w index k j rank u)
    (hf : Frame u s (writes k)) (l : Nat) (hl : l < 7) :
    DigAt s (base k + V3.siblingOffset j.val l) (V3.sibling w k.val j.val l) := by
  apply merkleField_of_frame hu hf
  · unfold V3.siblingOffset V3.blockOffset; split_ifs <;> omega
  · unfold V3.siblingOffset V3.blockOffset; split_ifs <;> omega
theorem Inv.leafPost {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128}
    {rank : Fin 728} {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv u index k j tr answers s)
    (ends : List Digest) (hlen : ends.length = 7)
    (hends : ∀ t, t < 7 → DigAt s (base k + traceLeafSlot t) (ends.getD t 0)) :
    Post L w index k j u ends (leafSetupRel.toState s) := by
  have hk := k.isLt
  have hB : base k + 1024 < 2 ^ 64 := by unfold base coordinateBase; omega
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  let prepared := leafSetupRel.toState s
  have hp := leafSetup_regs s (base k) hb
  have hkeep : ∀ r, r ∉ clobbers → prepared.getReg r = u.getReg r := by
    intro r hr
    exact ((chainPiece_keeps ⟨0, [], .leaf⟩).reg s hr).trans (hs.keep r hr)
  have hfLeaf : Frame s prepared (fun A => A = base k + 896 ∨ A = base k + 904) := by
    intro A hA hn
    rw [leafSetup_mem s (base k) A hb hB hA,
      if_neg (fun h => hn (Or.inr h)), if_neg (fun h => hn (Or.inl h))]
  have hf : Frame u prepared (writes k) := (hs.frame.trans hfLeaf).mono
    (by intro A hA hw; rcases hw with h | h; exact h; unfold writes; omega)
  have hend : ∀ t, t < 7 → DigAt prepared (base k + traceLeafSlot t) (ends.getD t 0) := by
    intro t ht
    apply (hends t ht).frame hfLeaf
    · unfold traceLeafSlot base coordinateBase; split_ifs <;> omega
    · unfold traceLeafSlot; split_ifs <;> omega
    · unfold traceLeafSlot; split_ifs <;> omega
  have hheader : DigAt prepared (base k + 896) (SigGolfCandidate.T3.header 6 k.val index 0 j.val) := by
    constructor
    · rw [leafSetup_mem s (base k) (base k + 896) hb hB (by omega),
        if_neg (by omega), if_pos rfl]
      exact hs.leafLoad hu
    · rw [leafSetup_mem s (base k) (base k + 896 + 8) hb hB (by omega),
        if_pos (by omega), header_hi,
        if_neg (by decide : ¬ SigGolfCandidate.T3.packedNodeTag 6)]
      have hi := hu.indexBound
      have hj := j.isLt
      simpa only [hdr1, Nat.mod_eq_of_lt (by omega : index < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : j.val < 2 ^ 32), Nat.mul_comm] using
          (hs.keep .x4 (by decide)).trans hu.route
  refine { length := hlen, keep := hkeep, frame := hf, child := ?_ }
  refine {
    indexBound := hu.indexBound, length := hlen, pc := ?_,
    hashMode := (hkeep .x5 (by decide)).trans hu.hashMode,
    baseReg := (hkeep .x8 (by decide)).trans hu.baseReg,
    hashInput := hp.1, hashLen := hp.2.1,
    nodeHeader := (hkeep .x27 (by decide)).trans hu.nodeHeader,
    indexReg := (hkeep .x22 (by decide)).trans hu.indexReg,
    forestPointer := (hkeep .x9 (by decide)).trans hu.forestPointer,
    returnPC := (hkeep .x1 (by decide)).trans hu.returnPC,
    heaps := ?_, leafAt := ?_,
    padAt := fun l hl => merklePad_of_frame hu hf l (by omega),
    sibAt := fun l hl => merkleSibling_of_frame hu hf l hl }
  · rw [hp.2.2, hs.keep .x23 (by decide), hu.childPC, pcOf_and_not1]
  · intro h hlo hhi
    have hn : Child.heapReg h ∉ clobbers := by interval_cases h <;> decide
    exact (hkeep _ hn).trans (hu.heaps h hlo hhi)
  · intro i hi
    by_cases h0 : i = 0
    · subst i; simpa [V3.leafFields, traceLeafSlot] using hend 0 (by decide)
    · by_cases h1 : i = 1
      · subst i; simpa [V3.leafFields, Nat.add_assoc] using hheader
      · have he : base k + 880 + 16 * i = base k + traceLeafSlot (i - 1) := by
          unfold traceLeafSlot
          rw [if_neg (by omega)]
          omega
        simpa only [V3.leafFields, if_neg h0, if_neg h1, he] using hend (i - 1) (by omega)
end W9Machine.Chain
end

section




namespace W9Machine.Chain
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem runPlan_good {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u : MachineState} (hu : Pre L w index k j rank u)
    (ps : List ChainPiece) (tr : ChainTrace) (answers : List (BitVec 256)) (s : MachineState)
    (hs : Inv u index k j tr answers s) (hg : planGuard ps tr = true) (hl : PlanLinked ps)
    (hpc : ∀ p, ps.head? = some p → s.pc = pcOf p.pc)
    (N C A : Nat) (Q : Prop) (K : List (BitVec 256) → OracleComp HashSpec Obs)
    (hK : ∀ answers' s', Inv u index k j (terminalTrace ps tr) answers' s' →
      GoodQFor Frozen.image (leafSetupRel.toState s') N C Q A (K answers')) :
    GoodQFor Frozen.image s (N + planFuel ps) (C + planCycles ps) Q (A + planCycles ps)
      (ccM (traceProgram (originalValue u index k j) (planQueries ps tr) answers) K) := by
  induction ps generalizing tr answers s with
  | nil => simp [planGuard] at hg
  | cons p ps ih =>
    obtain ⟨hlink, hcheck⟩ := hl p (by simp)
    have hguard := hg
    simp only [planGuard, Bool.and_eq_true, decide_eq_true_eq] at hguard
    obtain ⟨⟨hguard, hw⟩, hrest⟩ := hguard
    by_cases hleaf : p.kind = .leaf
    · have hnil : ps = [] := by simpa [hleaf] using hrest
      subst ps
      have hh : p.isHash = false := by simp [ChainPiece.isHash, hleaf]
      have he : p.result = leafSetupRel := by simp [ChainPiece.result, hleaf]
      have ht := chainPiece_steps p hlink hcheck s (hpc p rfl) (hs.plainObligations hu p hh hguard)
      rw [he] at ht
      have hc := GoodQFor.steps ht (hK answers s (by simpa [terminalTrace, hleaf] using hs))
      simpa only [planFuel, planCycles, planQueries, hh, Bool.false_eq_true, if_false,
        traceProgram, ccM_pure, ChainPiece.totalCycles, he, leafSetupRel,
        Nat.zero_add, Nat.add_zero] using hc
    · have htail : ((ps.head?.map ChainPiece.pc == some p.nextPc) &&
          planGuard ps (tr.step p.kind)) = true := by
        cases he : p.kind <;> simp_all
      simp only [Bool.and_eq_true, beq_iff_eq] at htail
      obtain ⟨hnext, hgtail⟩ := htail
      have hltail : PlanLinked ps := fun q hq => hl q (List.mem_cons_of_mem p hq)
      have hktail : ∀ answers' s', Inv u index k j (terminalTrace ps (tr.step p.kind)) answers' s' →
          GoodQFor Frozen.image (leafSetupRel.toState s') N C Q A (K answers') := by
        intro answers' s' h
        exact hK answers' s' (by simpa only [terminalTrace, if_neg hleaf] using h)
      have hnpc (ans : BitVec 256) : ∀ q, ps.head? = some q →
          (if p.isHash then writeHash (p.result.toState s) ans else p.result.toState s).pc = pcOf q.pc := by
        intro q hq
        have he : q.pc = p.nextPc := by simpa only [hq, Option.map_some, Option.some.injEq] using hnext
        exact (chain_next_pc p s ans hleaf hw).trans (congrArg pcOf he.symm)
      by_cases hh : p.isHash = true
      · have hr := hs.hashReady hu p hh hguard
        have hc := fun ans => ih (tr.step p.kind) (answers ++ [ans]) _
          (hs.hashEffect hu p hh hguard ans) hgtail hltail
          (by simpa only [if_pos hh] using hnpc ans) hktail
        have hq := GoodQFor.publicHash_bind
          (chainPiece_ecall p hlink hcheck s hr.obligations hr.stop)
          hr.mode hr.valid hr.query hc
        have hrun := GoodQFor.steps (chainPiece_steps p hlink hcheck s (hpc p rfl) hr.obligations) hq
        simpa only [planFuel, planCycles, planQueries, if_pos hh, traceProgram,
          ChainPiece.totalCycles, hr.blocks, Nat.mul_one, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using hrun
      · have hfalse : p.isHash = false := Bool.eq_false_iff.mpr hh
        have hc := ih (tr.step p.kind) answers _ (hs.plainEffect hu p hfalse hleaf hguard)
          hgtail hltail (by simpa only [if_neg hh] using hnpc 0) hktail
        have hrun := GoodQFor.steps
          (chainPiece_steps p hlink hcheck s (hpc p rfl) (hs.plainObligations hu p hfalse hguard)) hc
        simpa only [planFuel, planCycles, planQueries, if_neg hh, ChainPiece.totalCycles,
          Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrun
end W9Machine.Chain
end

section



namespace W9Machine.Chain
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem good_of_ready (source : SourceEquivalent) (endpoints : EndpointsCorrect)
    (rank : Fin 728) (r : ChainRoutine) (hr : RoutineReady rank r) : Good Frozen.layout rank := by
  intro w index k j u N C A Q K hu hK
  have hpc : ∀ p, r.pieces.head? = some p → u.pc = pcOf p.pc := by
    intro p hp
    have he := hr.entry
    rw [hp] at he
    have he' : p.pc = chainEntries.getD rank.val 0 := Option.some.inj he
    exact hu.pc.trans (congrArg pcOf he'.symm)
  have hk : ∀ answers s, Inv u index k j (terminalTrace r.pieces {}) answers s →
      GoodQFor Frozen.image (leafSetupRel.toState s) N C Q A
        (K (sourceEnds w k rank answers)) := by
    intro answers s hs
    exact hK _ _ (hs.leafPost hu _ (by simp [sourceEnds])
      (endpoints Frozen.layout w index k j rank u s _ answers hu hs hr.endpoints))
  have hrun := runPlan_good hu r.pieces {} [] u (inv_initial Frozen.layout w index k j rank u hu)
    hr.guard hr.linked hpc N C A Q (fun answers => K (sourceEnds w k rank answers)) hk
  have hcost := hr.cycles
  have hfuel := planFuel_le_cycles r.pieces
  have hbig := hrun.mono (A' := A + 84) (by omega : N + planFuel r.pieces ≤ N + 89)
    (by omega : C + planCycles r.pieces ≤ C + 89) (fun h => ⟨h, by omega⟩)
  apply hbig.congr
  rw [hr.queries]
  have he := congrArg (fun p => ccM p K) (source Frozen.layout w index k j rank u hu)
  simpa only [ccM_bind, ccM_pure] using he
theorem allGood_of_ready (source : SourceEquivalent) (endpoints : EndpointsCorrect)
    (ready : ∀ rank : Fin 728, ∃ r, RoutineReady rank r) : AllGood Frozen.layout := by
  intro rank
  obtain ⟨r, hr⟩ := ready rank
  exact good_of_ready source endpoints rank r hr
end W9Machine.Chain
end
