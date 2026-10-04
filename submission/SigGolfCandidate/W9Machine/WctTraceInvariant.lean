import SigGolfCandidate.W9Machine.WctRelativeMem
import SigGolfCandidate.W9Machine.WctTraceMem

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
open SigGolfCandidate.T3 (Digest pad64)
theorem rungRRel_mem (s : MachineState) (rb : Reg) (digit p A X : Nat) (dst : Option Word)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hhi : A + 64 < 2 ^ 64)
    (hX : X < 2 ^ 64) (hstep : (packedPos digit).eval s = BitVec.ofNat 64 digit) :
    ((rungRRel rb digit dst p).toState s).getMem (BitVec.ofNat 64 X) =
      if X = A + 16 then StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (A + 16))) 1
        (BitVec.ofNat 64 digit) else s.getMem (BitVec.ofNat 64 X) := by
  have hk : (⟨some (.reg .x10), 16⟩ : Addr).eval s = BitVec.ofNat 64 (A + 16) := by
    simp only [Addr.eval, E.eval, h10]
    exact ofNat_add_ofNat A 16
  have hm := memEval_one s ⟨some (.reg .x10), 16⟩
    (.bin (.st .b 1) (.ld (addC (.reg .x10) 16)) (packedPos digit)) (A + 16) X
    hk (by omega) hX
  have ha : BitVec.ofNat 64 A + (16 : Word) = BitVec.ofNat 64 (A + 16) :=
    ofNat_add_ofNat A 16
  simpa only [Result.toState_getMem, rungRRel, E.eval, BinOp.eval, addC_eval, h10,
    hstep, ha] using hm
theorem rungRRel_frame (s : MachineState) (rb : Reg) (digit p A : Nat) (dst : Option Word)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hhi : A + 64 < 2 ^ 64)
    (hstep : (packedPos digit).eval s = BitVec.ofNat 64 digit) :
    Frame s ((rungRRel rb digit dst p).toState s) (fun X => X = A + 16) := by
  intro X hX hn
  rw [rungRRel_mem s rb digit p A X dst h10 hhi hX hstep, if_neg hn]
theorem rungRRel_hashInput (s : MachineState) (rb : Reg) (digit p A : Nat) (dst : Option Word)
    (pad0 hdr pad1 value : Digest) (h10 : s.getReg .x10 = BitVec.ofNat 64 A)
    (halign : A % 8 = 0) (hhi : A + 64 < 2 ^ 64)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 64)
    (hstep : (packedPos digit).eval s = BitVec.ofNat 64 digit)
    (hlo : StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (A + 16))) 1
      (BitVec.ofNat 64 digit) = hdr.extractLsb' 0 64)
    (hhigh : s.getMem (BitVec.ofNat 64 (A + 24)) = hdr.extractLsb' 64 64)
    (hp0 : DigAt s A pad0) (hp1 : DigAt s (A + 32) pad1) (hv : DigAt s (A + 48) value) :
    SigGolfCandidate.Legacy.Riscv.hashInput ((rungRRel rb digit dst p).toState s) =
      toQ (pad64 (blk4 pad0 hdr pad1 value)) := by
  have hf := rungRRel_frame s rb digit p A dst h10 hhi hstep
  refine W9Machine.hashInput_blk4 _ A pad0 hdr pad1 value
    (((rungRRel_keeps rb digit dst p).reg s (by decide)).trans h10)
    (((rungRRel_keeps rb digit dst p).reg s (by decide)).trans h11)
    halign hhi (hp0.frame hf (by omega) (by omega) (by omega)) ?_
    (hp1.frame hf (by omega) (by omega) (by omega))
    (hv.frame hf (by omega) (by omega) (by omega))
  constructor
  · rw [rungRRel_mem s rb digit p A (A + 16) dst h10 hhi (by omega) hstep, if_pos rfl]
    exact hlo
  · rw [rungRRel_mem s rb digit p A (A + 16 + 8) dst h10 hhi (by omega) hstep, if_neg (by omega)]
    simpa only [Nat.add_assoc] using hhigh
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
open SigGolfCandidate.T3 (Digest)
theorem copyFHRel_mem (s : MachineState) (rb : Reg) (B off dst p A : Nat)
    (hbase : s.getReg rb = BitVec.ofNat 64 B) (hhi : B + dst + 16 < 2 ^ 64)
    (hA : A < 2 ^ 64) :
    ((copyFHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p).toState s).getMem
      (BitVec.ofNat 64 A) =
      if A = B + dst + 8 then s.getMem (BitVec.ofNat 64 (B + off + 56)) else
      if A = B + dst then s.getMem (BitVec.ofNat 64 (B + off + 48)) else
      s.getMem (BitVec.ofNat 64 A) := by
  have hm := memEval_two s (kAt rb (BitVec.ofNat 64 dst) 8)
    (kAt rb (BitVec.ofNat 64 dst) 0) (lAt rb (BitVec.ofNat 64 off) 56)
    (lAt rb (BitVec.ofNat 64 off) 48) (B + dst + 8) (B + dst + 0) A
    (relative_key s rb B dst 8 hbase) (relative_key s rb B dst 0 hbase)
    (by omega) (by omega) hA
  simpa only [Result.toState_getMem, copyFHRel, lAt, E.eval, addC_eval, hbase,
    ofNat_add_ofNat, Nat.add_zero, Nat.add_assoc] using hm
theorem copyFHRel_frame (s : MachineState) (rb : Reg) (B off dst p : Nat)
    (hbase : s.getReg rb = BitVec.ofNat 64 B) (hhi : B + dst + 16 < 2 ^ 64) :
    Frame s ((copyFHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p).toState s)
      (fun A => A = B + dst ∨ A = B + dst + 8) := by
  intro A hA hn
  rw [copyFHRel_mem s rb B off dst p A hbase hhi hA,
    if_neg (fun h => hn (Or.inr h)), if_neg (fun h => hn (Or.inl h))]
theorem copyFHRel_digest (s : MachineState) (rb : Reg) (B off dst p : Nat) (value : Digest)
    (hbase : s.getReg rb = BitVec.ofNat 64 B) (hhi : B + dst + 16 < 2 ^ 64)
    (hv : DigAt s (B + off + 48) value) :
    DigAt ((copyFHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p).toState s)
      (B + dst) value := by
  constructor
  · rw [copyFHRel_mem s rb B off dst p (B + dst) hbase hhi (by omega),
      if_neg (by omega), if_pos rfl]
    exact hv.1
  · rw [copyFHRel_mem s rb B off dst p (B + dst + 8) hbase hhi (by omega), if_pos rfl]
    simpa only [Nat.add_assoc] using hv.2
end W9Machine
end

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
    (hi : tr.input + 64 ≤ 1024) (hstep : (packedPos digit).eval s = BitVec.ofNat 64 digit)
    (hh : StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (B + tr.input + 16))) 1
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
    exact tr.available_put (off + 16) (.header chain digit) h trivial
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
