import SigGolfCandidate.W9Machine.WctTraceMem
import SigGolfCandidate.W9Machine.WctRungSem
import SigGolfCandidate.W9Machine.WctCopySem
import SigGolfCandidate.T3M.Verify.ChainSem
import SigGolfCandidate.W9Machine.WctPlanFrame
import SigGolfCandidate.W9Machine.WctChainSource
import SigGolfCandidate.W9Machine.WctChainContract
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctChainControl

section

namespace W9Machine
theorem ChainTrace.read_hash (tr : ChainTrace) (x : Nat) :
    tr.hash.read x =
      if x = tr.output + 24 then .answer tr.queries.length 3 else
      if x = tr.output + 16 then .answer tr.queries.length 2 else
      if x = tr.output + 8 then .answer tr.queries.length 1 else
      if x = tr.output then .answer tr.queries.length 0 else tr.read x := by
  change ((((tr.put tr.output (.answer tr.queries.length 0)).put (tr.output + 8)
    (.answer tr.queries.length 1)).put (tr.output + 16) (.answer tr.queries.length 2)).put
    (tr.output + 24) (.answer tr.queries.length 3)).read x = _
  simp only [ChainTrace.read_put]
end W9Machine
end

section



namespace W9Machine
set_option maxRecDepth 10000
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
open SigGolfCandidate.Legacy.Riscv
theorem copy_trace_mem (value : ChainWord → Word) (tr : ChainTrace) (s : MachineState)
    (B off dst p : Nat) (ht : TraceMem value B tr s)
    (hbase : s.getReg .x8 = BitVec.ofNat 64 B) (hB : B + 1024 < 2 ^ 64)
    (hoff : off + 64 ≤ 1024) (hdst : dst + 16 ≤ 1024) :
    TraceMem value B ((tr.put dst (tr.read (off + 48))).put (dst + 8) (tr.read (off + 56)))
      ((copyFHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p).toState s) := by
  intro x hx
  rw [copyFHRel_mem s .x8 B off dst p (B + x) hbase (by omega) (by omega)]
  simp only [ChainTrace.read_put]
  split_ifs <;> first
  | simpa only [Nat.add_assoc] using ht (off + 56) (by omega)
  | simpa only [Nat.add_assoc] using ht (off + 48) (by omega)
  | exact ht x hx
  | omega
theorem rung_trace_mem (value : ChainWord → Word) (tr : ChainTrace) (s : MachineState)
    (B digit p : Nat) (dst : Option Word) (ht : TraceMem value B tr s)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (B + tr.input)) (hB : B + 1024 < 2 ^ 64)
    (hi : tr.input + 64 ≤ 1024) (hstep : (posE digit).eval s = BitVec.ofNat 64 digit)
    (hh : StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (B + tr.input + 16))) 4
      (BitVec.ofNat 64 digit) = value (.header tr.chain digit)) :
    TraceMem value B (tr.put (tr.input + 16) (.header tr.chain digit))
      ((rungRRel .x8 digit dst p).toState s) := by
  intro x hx
  rw [rungRRel_mem s .x8 digit p (B + tr.input) (B + x) dst h10 (by omega) (by omega) hstep]
  simp only [ChainTrace.read_put]
  split_ifs <;> first | exact hh | exact ht x hx | omega
theorem hash_trace_mem (value : ChainWord → Word) (tr : ChainTrace) (s : MachineState)
    (B : Nat) (ans : BitVec 256) (ht : TraceMem value B tr s)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (B + tr.output)) (hB : B + 1024 < 2 ^ 64)
    (ho : tr.output + 32 ≤ 1024)
    (ha : ∀ i, i < 4 → value (.answer tr.queries.length i) = ans.extractLsb' (64 * i) 64) :
    TraceMem value B tr.hash (writeHash s ans) := by
  intro x hx
  rw [writeHash_getMem_ofNat s ans (B + tr.output) (B + x) h12 (by omega) (by omega)]
  rw [ChainTrace.read_hash]
  split_ifs <;> first
  | exact (ha 3 (by decide)).symm
  | exact (ha 2 (by decide)).symm
  | exact (ha 1 (by decide)).symm
  | exact (ha 0 (by decide)).symm
  | exact ht x hx
  | omega
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
open SigGolfCandidate.Legacy.Riscv
def ChainWord.available (n : Nat) : ChainWord → Prop
  | .answer q _ => q < n
  | _ => True
def ChainTrace.Available (tr : ChainTrace) : Prop :=
  ∀ off, (tr.read off).available tr.queries.length
def chainValue (base : ChainWord → Word) (answers : List (BitVec 256)) : ChainWord → Word
  | .answer q i => (answers.getD q 0).extractLsb' (64 * i) 64
  | w => base w
theorem ChainWord.available_mono (w : ChainWord) (n m : Nat) (h : w.available n) (hn : n ≤ m) :
    w.available m := by
  cases w <;> simp_all [available]; omega
theorem ChainTrace.available_put (tr : ChainTrace) (off : Nat) (w : ChainWord)
    (h : tr.Available) (hw : w.available tr.queries.length) : (tr.put off w).Available := by
  intro x
  change ((tr.put off w).read x).available tr.queries.length
  rw [read_put]
  split_ifs
  · exact hw
  · exact h x
theorem ChainTrace.available_hash (tr : ChainTrace) (h : tr.Available) : tr.hash.Available := by
  intro x
  have hl : tr.hash.queries.length = tr.queries.length + 1 := by
    change (tr.queries ++ [_]).length = _
    simp only [List.length_append, List.length_singleton]
  rw [hl, read_hash]
  split_ifs
  all_goals first
    | exact Nat.lt_succ_self _
    | exact ChainWord.available_mono _ _ _ (h x) (by omega)
theorem chainValue_append (base : ChainWord → Word) (answers : List (BitVec 256))
    (ans : BitVec 256) (w : ChainWord) (h : w.available answers.length) :
    chainValue base (answers ++ [ans]) w = chainValue base answers w := by
  cases w with
  | answer q i =>
    simp only [ChainWord.available] at h
    simp only [chainValue, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  | original off => rfl
  | header t d => rfl
  | route => rfl
  | leafHeader => rfl
theorem traceMem_append (base : ChainWord → Word) (answers : List (BitVec 256))
    (ans : BitVec 256) (tr : ChainTrace) (s : MachineState) (B : Nat)
    (ht : TraceMem (chainValue base answers) B tr s) (ha : tr.Available)
    (hn : tr.queries.length = answers.length) :
    TraceMem (chainValue base (answers ++ [ans])) B tr s := by
  intro off ho
  rw [chainValue_append base answers ans (tr.read off) (hn ▸ ha off)]
  exact ht off ho
theorem hash_trace_append (base : ChainWord → Word) (answers : List (BitVec 256))
    (ans : BitVec 256) (tr : ChainTrace) (s : MachineState) (B : Nat)
    (ht : TraceMem (chainValue base answers) B tr s) (ha : tr.Available)
    (hn : tr.queries.length = answers.length)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (B + tr.output))
    (hB : B + 1024 < 2 ^ 64) (ho : tr.output + 32 ≤ 1024) :
    TraceMem (chainValue base (answers ++ [ans])) B tr.hash (writeHash s ans) := by
  apply hash_trace_mem _ tr s B ans (traceMem_append base answers ans tr s B ht ha hn) h12 hB ho
  intro i hi
  simp [chainValue, hn, List.getD_eq_getElem?_getD]
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
open SigGolfCandidate.Legacy.Riscv
theorem ChainTrace.available_step (tr : ChainTrace) (kind : ChainPieceKind) (h : tr.Available) :
    (tr.step kind).Available := by
  cases kind with
  | head off dst chain digit =>
    apply ChainTrace.available_hash
    exact ChainTrace.available_put _ _ _
      (tr.available_put (off + 16) (.header chain digit) h trivial) trivial
  | rung digit dst =>
    apply ChainTrace.available_hash
    exact tr.available_put (tr.input + 16) (.header tr.chain digit) h trivial
  | copy off dst =>
    exact ChainTrace.available_put _ _ _
      (tr.available_put dst (tr.read (off + 48)) h (h _)) (h _)
  | jump target => exact h
  | leaf => exact ChainTrace.available_put _ _ _ (tr.available_put 896 .leafHeader h trivial) trivial
theorem chainTrace_available (r : ChainRoutine) : (chainTrace r).Available := by
  have hfold : ∀ (ps : List ChainPiece) (tr : ChainTrace), tr.Available →
      (ps.foldl (fun s p => s.step p.kind) tr).Available := by
    intro ps
    induction ps with
    | nil => intro tr h; exact h
    | cons p ps ih => intro tr h; exact ih _ (tr.available_step p.kind h)
  exact hfold r.pieces {} (fun _ => trivial)
theorem TraceMem.hashInput (value : ChainWord → Word) (B : Nat) (tr : ChainTrace)
    (s : MachineState) (input : List UInt8) (ht : TraceMem value B tr s)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (B + tr.input))
    (h11 : s.getReg .x11 = 64) (hB : B + 1024 < 2 ^ 64)
    (hi : tr.input + 64 ≤ 1024) (halign : (B + tr.input) % 8 = 0)
    (hlen : input.length = 64)
    (hwords : wordsOf input = ((List.range 8).map fun i => value (tr.read (tr.input + 8 * i)))) :
    SigGolfCandidate.Legacy.Riscv.hashInput s = toQ input := by
  apply hashInput_words8 s input (B + tr.input) hlen h10 halign (by omega) h11
  rw [hwords]
  simp only [List.range_succ, List.range_zero, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, Nat.reduceMul,
    Nat.mul_zero, Nat.add_zero]
  have hread : ∀ x, x < 64 → s.getMem (BitVec.ofNat 64 (B + tr.input + x)) =
      value (tr.read (tr.input + x)) := by
    intro x hx
    simpa only [Nat.add_assoc] using ht (tr.input + x) (by omega)
  rw [ht tr.input (by omega), hread 8 (by decide), hread 16 (by decide), hread 24 (by decide),
    hread 32 (by decide), hread 40 (by decide), hread 48 (by decide), hread 56 (by decide)]
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
theorem wctStepByte (w : Word) (L J m : Nat) (hL : L < 2 ^ 32) (hm : m < 256) (hJ : J < 2 ^ 24)
    (h1 : w.toNat % 2 ^ 32 = L) (h2 : w.toNat / 2 ^ 40 = J) :
    StoreKind.merge .b w 4 (BitVec.ofNat 64 m) = BitVec.ofNat 64 (L + 2 ^ 32 * m + 2 ^ 40 * J) := by
  apply BitVec.eq_of_toNat_eq
  simp only [StoreKind.merge]
  rw [replaceByte_toNat _ _ (by omega)]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show L + 2 ^ 32 * m + 2 ^ 40 * J < 2 ^ 64 by omega)]
  generalize w.toNat = x at *
  norm_num at h1 h2 ⊢
  omega
end W9Machine
end

section




namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
open SigGolfCandidate.Legacy.Riscv
def coordinateRegion (B A : Nat) : Prop := B ≤ A ∧ A < B + 1024
def PieceLocal (p : ChainPiece) (B : Nat) (s : MachineState) : Prop :=
  match p.kind with
  | .head off _ _ _ => off + 64 ≤ 1024
  | .rung d _ => ∃ off, s.getReg .x10 = BitVec.ofNat 64 (B + off) ∧ off + 64 ≤ 1024 ∧
      (posE d).eval s = BitVec.ofNat 64 d
  | .copy _ dst => dst + 16 ≤ 1024
  | .jump _ | .leaf => True
theorem chainPiece_frame (p : ChainPiece) (B : Nat) (s : MachineState)
    (hbase : s.getReg .x8 = BitVec.ofNat 64 B) (hB : B + 1024 < 2 ^ 64)
    (hl : PieceLocal p B s) : Frame s (p.result.toState s) (coordinateRegion B) := by
  cases p with
  | mk pc words kind =>
    cases kind with
    | head off dst chain digit =>
      simp only [PieceLocal] at hl
      exact (headRHRel_frame s .x8 B off dst pc chain digit hbase (by omega)).mono
        (by intro A hA hw; simp only [coordinateRegion]; omega)
    | rung digit dst =>
      obtain ⟨off, h10, hoff, hs⟩ := hl
      exact (rungRRel_frame s .x8 digit pc (B + off) (dst.map (BitVec.ofNat 64))
        h10 (by omega) hs).mono (by intro A hA hw; simp only [coordinateRegion]; omega)
    | copy off dst =>
      exact (copyFHRel_frame s .x8 B off dst pc hbase (by simp only [PieceLocal] at hl; omega)).mono
        (by intro A hA hw; simp only [coordinateRegion]; simp only [PieceLocal] at hl; omega)
    | jump target => intro A hA hn; rfl
    | leaf =>
      intro A hA hn
      change (leafSetupRel.toState s).getMem (BitVec.ofNat 64 A) = _
      rw [leafSetup_mem s B A hbase hB hA, if_neg (by unfold coordinateRegion at hn; omega),
        if_neg (by unfold coordinateRegion at hn; omega)]
theorem hash_coordinate_frame (B dst : Nat) (s : MachineState) (ans : BitVec 256)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (B + dst))
    (hB : B + 1024 < 2 ^ 64) (hd : dst + 32 ≤ 1024) :
    Frame s (writeHash s ans) (coordinateRegion B) := by
  intro A hA hn
  rw [writeHash_getMem_ofNat s ans (B + dst) A h12 hA (by omega)]
  unfold coordinateRegion at hn
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem wct_header_step (k index t old digit : Nat) (hk : k < 9) (hi : index < 2 ^ 31)
    (ht : t < 7) (ho : old < 3) (hd : digit < 3) :
    StoreKind.merge .b (BitVec.ofNat 64 (hdr0 5 k index (old + 256 * t))) 4
      (BitVec.ofNat 64 digit) = BitVec.ofNat 64 (hdr0 5 k index (digit + 256 * t)) := by
  have heq : ∀ d, d < 3 → hdr0 5 k index (d + 256 * t) =
      (1281 + 65536 * k) + 2 ^ 32 * d + 2 ^ 40 * t := by
    intro d hd
    unfold hdr0
    rw [Nat.mod_eq_of_lt (by omega : k < 256), Nat.div_eq_of_lt (by omega : index < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : d + 256 * t < 2 ^ 32)]
    norm_num
    omega
  rw [heq old ho, heq digit hd]
  apply wctStepByte _ (1281 + 65536 * k) t digit (by omega) (by omega) (by omega)
  · rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 1281 + 65536 * k + 2 ^ 32 * old + 2 ^ 40 * t < 2 ^ 64)]
    omega
  · rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 1281 + 65536 * k + 2 ^ 32 * old + 2 ^ 40 * t < 2 ^ 64)]
    omega
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
  rcases hm with rfl | rfl | rfl
  · change accessValid ((kAt .x8 (BitVec.ofNat 64 off) 24).eval s) 8 = true
    rw [relative_key s .x8 B off 24 h8]
    exact valid_ofNat _ _ (by omega) (by omega)
  · change accessValid ((kAt .x8 (BitVec.ofNat 64 off) 16).eval s) 8 = true
    rw [relative_key s .x8 B off 16 h8]
    exact valid_ofNat _ _ (by omega) (by omega)
  · change accessValid ((hKey chain digit).eval s) 8 = true
    rw [hKey_relative s H chain digit h28 (by omega) hc hd]
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
  · change accessValid ((⟨some (.reg .x10), 20⟩ : Addr).eval s) 1 = true
    have he : (⟨some (.reg .x10), 20⟩ : Addr).eval s = BitVec.ofNat 64 (B + off + 20) := by
      simp only [Addr.eval, E.eval, h10]
      exact ofNat_add_ofNat (B + off) 20
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



namespace W9Machine.Chain
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def originalValue (u : MachineState) (index : Nat) (k : Fin 9) (j : Fin 128) : ChainWord → Word
  | .original off => u.getMem (BitVec.ofNat 64 (base k + off))
  | .header t d => BitVec.ofNat 64 (hdr0 5 k.val index (d + 256 * t))
  | .route => BitVec.ofNat 64 (hdr1 index j.val)
  | .leafHeader => BitVec.ofNat 64 (hdr0 6 k.val index 0)
  | .answer _ _ => 0
structure Inv (u : MachineState) (index : Nat) (k : Fin 9) (j : Fin 128)
    (tr : ChainTrace) (answers : List (BitVec 256)) (s : MachineState) : Prop where
  keep : ∀ r, r ∉ wctChainClobbers → s.getReg r = u.getReg r
  frame : Frame u s (writes k)
  memory : TraceMem (chainValue (originalValue u index k j) answers) (base k) tr s
  count : tr.queries.length = answers.length
  available : tr.Available
  hashLen : s.getReg .x11 = 64
  pointers : 0 < answers.length →
    s.getReg .x10 = BitVec.ofNat 64 (base k + tr.input) ∧
    s.getReg .x12 = BitVec.ofNat 64 (base k + tr.output)
theorem inv_initial (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 728)
    (u : MachineState) (hu : Pre w index k j rank u) : Inv u index k j {} [] u := by
  refine ⟨fun _ _ => rfl, Frame.refl _ _, ?_, rfl, fun _ => trivial, hu.hashLen, ?_⟩
  · intro off ho; rfl
  · intro h; simp at h
theorem Inv.headerLoad {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre w index k j rank u) (hs : Inv u index k j tr answers s)
    (t d : Nat) (ht : t < 7) (hd : d < 3) :
    (hLoad t d).eval s = BitVec.ofNat 64 (hdr0 5 k.val index (d + 256 * t)) := by
  have hk := k.isLt
  have hr := (hs.keep .x28 (by decide)).trans hu.headerReg
  have he := hKey_relative s (table k) t d hr (by unfold table; omega) (by omega) hd
  have hm := hs.frame (table k + 64 * t + 8 * d) (by unfold table; omega)
    (by unfold writes base table; omega)
  have hl : (hLoad t d).eval s = s.getMem ((hKey t d).eval s) := by
    simp only [hLoad, hKey, Addr.eval, E.eval, addC_eval]
  rw [hl, he, hm]
  exact hu.headers t ht d hd
theorem Inv.leafLoad {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre w index k j rank u) (hs : Inv u index k j tr answers s) :
    (hLoad 7 1).eval s = BitVec.ofNat 64 (hdr0 6 k.val index 0) := by
  have hk := k.isLt
  have hr := (hs.keep .x28 (by decide)).trans hu.headerReg
  have he := hKey_relative s (table k) 7 1 hr (by unfold table; omega) (by decide) (by decide)
  have hm := hs.frame (table k + 456) (by unfold table; omega)
    (by unfold writes base table; omega)
  have hl : (hLoad 7 1).eval s = s.getMem ((hKey 7 1).eval s) := by
    simp only [hLoad, hKey, Addr.eval, E.eval, addC_eval]
  rw [hl, he]
  simpa only [Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] using hm.trans hu.leafHeader
theorem Inv.merkleField {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre w index k j rank u) (hs : Inv u index k j tr answers s)
    (off : Nat) (ha : off % 8 = 0) (ho : off + 16 ≤ 448) :
    DigAt s (base k + off) (wdig w (ClaudeWCT.W9.T3M.regionBase k.val + off)) := by
  have hk := k.isLt
  have h0 := hu.witness off (by omega) ha
  have h1 : OrigW w u (base k + off + 8) := by
    simpa only [Nat.add_assoc] using hu.witness (off + 8) (by omega) (by omega)
  have hdig := DigAt_origW h0 h1 (by unfold base; omega)
  have he : base k + off - 0x800 = ClaudeWCT.W9.T3M.regionBase k.val + off := by
    unfold base ClaudeWCT.W9.T3M.regionBase
    omega
  rw [he] at hdig
  exact hdig.frame hs.frame (by unfold base; omega)
    (by unfold writes; omega) (by unfold writes; omega)
end W9Machine.Chain
end

section

namespace W9Machine.Chain
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem Inv.rung {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre w index k j rank u) (hs : Inv u index k j tr answers s)
    (digit pc old : Nat) (dst : Option Nat) (ans : BitVec 256)
    (hn : 0 < answers.length) (hi : 448 ≤ tr.input ∧ tr.input + 64 ≤ 1024)
    (hdst : 448 ≤ dst.getD tr.output ∧ dst.getD tr.output + 32 ≤ 1024)
    (hc : tr.chain < 7) (ho : old < 3) (hd : digit < 3)
    (hh : tr.read (tr.input + 16) = .header tr.chain old) :
    Inv u index k j (tr.step (.rung digit dst)) (answers ++ [ans])
      (writeHash ((rungRRel .x8 digit (dst.map (BitVec.ofNat 64)) pc).toState s) ans) := by
  have hk := k.isLt
  have hB : base k + 1024 < 2 ^ 64 := by unfold base; omega
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  have hp := hs.pointers hn
  have hstep := wct_step_register s digit hd
    ((hs.keep .x6 (by decide)).trans hu.stepOne)
    ((hs.keep .x7 (by decide)).trans hu.stepTwo)
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
      exact wct_header_step k.val index tr.chain old digit hk hu.indexBound hc ho hd
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
theorem Inv.head {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre w index k j rank u) (hs : Inv u index k j tr answers s)
    (off dst pc chain digit : Nat) (ans : BitVec 256)
    (hoff : 448 ≤ off ∧ off + 64 ≤ 1024) (hdst : 448 ≤ dst ∧ dst + 32 ≤ 1024)
    (hc : chain < 7) (hd : digit < 3) :
    Inv u index k j (tr.step (.head off dst chain digit)) (answers ++ [ans])
      (writeHash ((headRHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst)
        pc chain digit).toState s) ans) := by
  have hk := k.isLt
  have hB : base k + 1024 < 2 ^ 64 := by unfold base; omega
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  have hr := (hs.keep .x4 (by decide)).trans hu.route
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
      { (tr.put (off + 16) (.header chain digit)).put (off + 24) .route with
        input := off, output := dst, chain := chain }
    apply hash_trace_append (originalValue u index k j) answers ans th prepared (base k)
      ?_ ?_ hs.count hp.2 hB hdst.2
    · exact head_trace_mem _ tr s (base k) off dst pc chain digit hs.memory hb hB hoff.2
        (hs.headerLoad hu chain digit hc hd) hr
    · exact ChainTrace.available_put _ _ _
        (tr.available_put _ (.header chain digit) hs.available trivial) trivial
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
theorem Inv.copy {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre w index k j rank u) (hs : Inv u index k j tr answers s)
    (off dst pc : Nat) (hoff : off + 64 ≤ 1024)
    (hdst : 448 ≤ dst ∧ dst + 16 ≤ 1024) :
    Inv u index k j (tr.step (.copy off dst)) answers
      ((copyFHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) pc).toState s) := by
  have hk := k.isLt
  have hB : base k + 1024 < 2 ^ 64 := by unfold base; omega
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
theorem Inv.hashEffect {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre w index k j rank u) (hs : Inv u index k j tr answers s)
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
theorem Inv.plainEffect {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre w index k j rank u) (hs : Inv u index k j tr answers s)
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
theorem Inv.plainObligations {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre w index k j rank u) (hs : Inv u index k j tr answers s)
    (p : ChainPiece) (hh : p.isHash = false) (hg : pieceGuard tr p.kind = true) :
    ∀ o ∈ p.result.st.obl, o.holds s := by
  have hk := k.isLt
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  have h28 := (hs.keep .x28 (by decide)).trans hu.headerReg
  have hB : base k + 1024 ≤ 2 ^ 24 := by unfold base; omega
  have hH : table k + 1024 ≤ 2 ^ 24 := by unfold table; omega
  have haB : base k % 8 = 0 := by unfold base; omega
  have haH : table k % 8 = 0 := by unfold table; omega
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
      exact headRHRel_obligations s (base k) (table k) 880 0 pc 7 1 hb h28 hB hH haB haH
        (by decide) (by decide) (by decide) (by decide)
end W9Machine.Chain
end

section

namespace W9Machine
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M publicHash)
open SphincsSecurity (bytesLE)
def wordBytes (ws : List Word) : List UInt8 := ws.flatMap (bytesLE 8)
def pieceQuery (tr : ChainTrace) (p : ChainPiece) : List ChainWord :=
  (tr.step p.kind).queries.getD tr.queries.length []
def planQueries : List ChainPiece → ChainTrace → List (List ChainWord)
  | [], _ => []
  | p :: ps, tr =>
      if p.isHash then pieceQuery tr p :: planQueries ps (tr.step p.kind)
      else planQueries ps (tr.step p.kind)
def traceProgram (base : ChainWord → Word) : List (List ChainWord) → List (BitVec 256) →
    M (List (BitVec 256))
  | [], answers => pure answers
  | q :: qs, answers => do
      let ans ← publicHash (wordBytes (q.map (chainValue base answers)))
      traceProgram base qs (answers ++ [ans])
theorem wordBytes_length (ws : List Word) : (wordBytes ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wordBytes, List.flatMap_cons, List.length_append, SphincsSecurity.bytesLE_length,
      List.length_cons] at *
    omega
theorem wordsOf_wordBytes (ws : List Word) : wordsOf (wordBytes ws) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change wordsOf (bytesLE 8 w ++ wordBytes ws) = w :: ws
    rw [wordsOf_append8 _ _ (SphincsSecurity.bytesLE_length _ _), readLE_bytesLE]
    simpa using congrArg (w :: ·) ih
theorem wordBytes_wordsOf (input : List UInt8) (n : Nat) (hn : input.length = 8 * n) :
    wordBytes (wordsOf input) = input := by
  have hl : (wordBytes (wordsOf input)).length = 8 * n := by
    rw [wordBytes_length, length_wordsOf n input hn]
  apply readLE_inj (hl.trans hn.symm)
  rw [← wordsToNat_wordsOf n _ hl, wordsOf_wordBytes, wordsToNat_wordsOf n input hn]
theorem ChainTrace.step_queries (tr : ChainTrace) (p : ChainPiece) :
    (tr.step p.kind).queries = tr.queries ++ if p.isHash then [pieceQuery tr p] else [] := by
  have qhash (t : ChainTrace) : t.hash.queries = t.queries ++
      [(List.range 8).map fun i => t.read (t.input + 8 * i)] := rfl
  cases p with
  | mk pc words kind =>
    cases kind <;> simp [pieceQuery, ChainTrace.step, ChainPiece.isHash, qhash,
      ChainTrace.put, List.getD_eq_getElem?_getD]
theorem planQueries_spec (ps : List ChainPiece) (tr : ChainTrace) :
    (ps.foldl (fun t p => t.step p.kind) tr).queries = tr.queries ++ planQueries ps tr := by
  induction ps generalizing tr with
  | nil => simp only [List.foldl_nil, planQueries, List.append_nil]
  | cons p ps ih =>
    rw [List.foldl_cons, ih, tr.step_queries p]
    simp only [planQueries]
    split_ifs <;> simp only [List.append_nil, List.append_assoc, List.singleton_append]
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (pad64)
def prepareTrace (tr : ChainTrace) : ChainPieceKind → ChainTrace
  | .head off dst chain digit =>
      { (tr.put (off + 16) (.header chain digit)).put (off + 24) .route with
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
theorem Inv.hashReady {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre w index k j rank u) (hs : Inv u index k j tr answers s)
    (p : ChainPiece) (hh : p.isHash = true) (hg : pieceGuard tr p.kind = true) :
    PreparedHash (chainValue (originalValue u index k j) answers) tr p s := by
  have hk := k.isLt
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  have h28 := (hs.keep .x28 (by decide)).trans hu.headerReg
  have h5 := (hs.keep .x5 (by decide)).trans hu.hashMode
  have hB : base k + 1024 ≤ 2 ^ 24 := by unfold base; omega
  have hBig : base k + 1024 < 2 ^ 64 := by omega
  have hH : table k + 1024 ≤ 2 ^ 24 := by unfold table; omega
  have haB : base k % 8 = 0 := by unfold base; omega
  have haH : table k % 8 = 0 := by unfold table; omega
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
        (hs.headerLoad hu chain digit hchain hdigit) ((hs.keep .x4 (by decide)).trans hu.route)
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
      have hstep := wct_step_register s digit hd
        ((hs.keep .x6 (by decide)).trans hu.stepOne)
        ((hs.keep .x7 (by decide)).trans hu.stepTwo)
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
          exact wct_header_step k.val index tr.chain old digit hk hu.indexBound hc ho hd
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

namespace W9Machine.Chain
set_option maxRecDepth 10000
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT.W9.Machine.Merkle
theorem merkleField_of_frame {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128}
    {rank : Fin 728} {u s : MachineState} (hu : Pre w index k j rank u)
    (hf : Frame u s (writes k)) (off : Nat) (ha : off % 8 = 0) (ho : off + 16 ≤ 448) :
    DigAt s (base k + off) (wdig w (ClaudeWCT.W9.T3M.regionBase k.val + off)) := by
  have hk := k.isLt
  have h0 := hu.witness off (by omega) ha
  have h1 : OrigW w u (base k + off + 8) := by
    simpa only [Nat.add_assoc] using hu.witness (off + 8) (by omega) (by omega)
  have hdig := DigAt_origW h0 h1 (by unfold base; omega)
  have he : base k + off - 0x800 = ClaudeWCT.W9.T3M.regionBase k.val + off := by
    unfold base ClaudeWCT.W9.T3M.regionBase
    omega
  rw [he] at hdig
  exact hdig.frame hf (by unfold base; omega)
    (by unfold writes; omega) (by unfold writes; omega)
theorem merklePad_of_frame {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128}
    {rank : Fin 728} {u s : MachineState} (hu : Pre w index k j rank u)
    (hf : Frame u s (writes k)) (l : Nat) (hl : l < 7) :
    DigAt s (base k + padO l) (ClaudeWCT.W9.T3M.wmpad w k.val l) := by
  have h := merkleField_of_frame hu hf (padO l)
    (by unfold padO blkO; omega) (by unfold padO blkO; omega)
  simpa only [ClaudeWCT.W9.T3M.wmpad, ClaudeWCT.W9.T3M.wctMerkleBlock,
    padO, blkO, Nat.add_assoc] using h
theorem merkleSibling_of_frame {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128}
    {rank : Fin 728} {u s : MachineState} (hu : Pre w index k j rank u)
    (hf : Frame u s (writes k)) (l : Nat) (hl : l < 7) :
    DigAt s (base k + sibO l j.val) (ClaudeWCT.W9.T3M.wsib w k.val j.val l) := by
  have hb : bitAt j.val l < 2 := Nat.mod_lt _ (by decide)
  have h := merkleField_of_frame hu hf (sibO l j.val)
    (by unfold sibO blkO; omega) (by unfold sibO blkO; omega)
  have he : sibOff (j.val / 2 ^ l % 2) = 48 * (1 - bitAt j.val l) := by
    unfold sibOff bitAt at *
    split_ifs <;> omega
  simpa only [ClaudeWCT.W9.T3M.wsib, ClaudeWCT.W9.T3M.wctMerkleBlock,
    he, sibO, blkO, Nat.add_assoc] using h
theorem Inv.leafPost {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre w index k j rank u) (hs : Inv u index k j tr answers s)
    (ends : List Digest) (hlen : ends.length = 7)
    (hends : ∀ t, t < 7 → DigAt s (base k + traceLeafSlot t) (ends.getD t 0)) :
    Post w index k j u ends (leafSetupRel.toState s) := by
  have hk := k.isLt
  have hB : base k + 1024 < 2 ^ 64 := by unfold base; omega
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  let prepared := leafSetupRel.toState s
  have hp := leafSetup_regs s (base k) hb
  have hkeep : ∀ r, r ∉ wctChainClobbers → prepared.getReg r = u.getReg r := by
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
    · unfold traceLeafSlot base; split_ifs <;> omega
    · unfold traceLeafSlot; split_ifs <;> omega
    · unfold traceLeafSlot; split_ifs <;> omega
  have hheader : DigAt prepared (base k + 896) (ClaudeWCT.WCT9.wctHeader 6 k.val index 0 j.val) := by
    rw [ClaudeWCT.WCT9.leaf_header_eq]
    constructor
    · rw [leafSetup_mem s (base k) (base k + 896) hb hB (by omega),
        if_neg (by omega), if_pos rfl, header_lo,
        if_neg (by decide : ¬ SigGolfCandidate.T3.packedNodeTag 6)]
      exact hs.leafLoad hu
    · rw [leafSetup_mem s (base k) (base k + 896 + 8) hb hB (by omega),
        if_pos (by omega), header_hi,
        if_neg (by decide : ¬ SigGolfCandidate.T3.packedNodeTag 6)]
      exact (hs.keep .x4 (by decide)).trans hu.route
  refine {
    length := hlen, keep := hkeep, frame := hf,
    rootPad := merklePad_of_frame hu hf 6 (by decide),
    rootSibling := merkleSibling_of_frame hu hf 6 (by decide), child := ?_ }
  refine {
    pc := ?_, base8 := by unfold base; omega,
    baseHi := by unfold base MEMORY_BYTES; omega,
    t0 := (hkeep .x5 (by decide)).trans hu.hashMode,
    s0 := (hkeep .x8 (by decide)).trans hu.baseReg,
    a0 := hp.1, a1 := hp.2.1,
    w0 := (hkeep .x27 (by decide)).trans hu.nodeHeader,
    s6 := (hkeep .x22 (by decide)).trans hu.indexReg,
    heaps := ?_, leafAt := ?_,
    padAt := fun l hl => merklePad_of_frame hu hf l (by omega),
    sibAt := fun l hl => merkleSibling_of_frame hu hf l (by omega) }
  · rw [hp.2.2, hs.keep .x23 (by decide), hu.childPC, pcOf_and_not1]
  · intro h hlo hhi
    have hn : heapReg h ∉ wctChainClobbers := by
      interval_cases h <;> decide
    exact (hkeep _ hn).trans (hu.heaps h hlo hhi)
  · intro i hi
    by_cases h0 : i = 0
    · subst i; simpa [leafFields, leafO, traceLeafSlot] using hend 0 (by decide)
    · by_cases h1 : i = 1
      · subst i; simpa [leafFields, leafO, Nat.add_assoc] using hheader
      · have he : base k + leafO + 16 * i = base k + traceLeafSlot (i - 1) := by
          unfold leafO traceLeafSlot
          rw [if_neg (by omega)]
          omega
        simpa only [leafFields, if_neg h0, if_neg h1, he] using hend (i - 1) (by omega)
end W9Machine.Chain
end

section




namespace W9Machine.Chain
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem runPlan_good {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u : MachineState} (hu : Pre w index k j rank u)
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
open SigGolfCandidate.T3 (Digest M)
def sourceEnds (w : WBytes) (k : Fin 9) (rank : Fin 728)
    (answers : List (BitVec 256)) : List Digest :=
  (List.finRange 7).map fun t =>
    let digits := ClaudeWCT.WCT9.codeword rank
    if digits.getD t.val 0 = 0 then ClaudeWCT.W9.T3M.wleaf w k.val t.val
    else (answers.getD ((digits.take (t.val + 1)).sum - 1) 0).extractLsb' 0 128
def SourceEquivalent : Prop :=
  ∀ (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 728)
    (u : MachineState), Pre w index k j rank u →
    (do
      let answers ← traceProgram (originalValue u index k j)
        (expectedQueries (ClaudeWCT.WCT9.codeword rank)) []
      pure (sourceEnds w k rank answers) : M (List Digest)) = program w index k j rank
def EndpointsCorrect : Prop :=
  ∀ (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 728)
    (u s : MachineState) (tr : ChainTrace) (answers : List (BitVec 256)),
    Pre w index k j rank u → Inv u index k j tr answers s →
    (∀ t, t < 7 → ∀ word, word < 2 →
      tr.read (traceLeafSlot t + 8 * word) =
        expectedEndpoint (ClaudeWCT.WCT9.codeword rank) t word) →
    ∀ t, t < 7 →
      DigAt s (base k + traceLeafSlot t) ((sourceEnds w k rank answers).getD t 0)
end W9Machine.Chain
end
