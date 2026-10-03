import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.T3M.Verify.Exec
import SigGolfCandidate.ClaudeWCT.WCT9.Forest
import SigGolfCandidate.ClaudeWCT.W9.T3M.SigCodec
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Data

namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M Pieces Layer signLayers chainCount height privateMac privateNonce)
abbrev SK : Nat := 0x80
abbrev SIG : Nat := 0x7000
abbrev DIG : Nat := 0x20120
abbrev NBUF : Nat := 0x20160
abbrev FOUT : Nat := 0x203A0
abbrev IDXV : Nat := 0x20550
abbrev TBL : Nat := 0xfef000
abbrev PRIVW : Nat := 0x50000
abbrev PAIRW : Nat := 0x50040
abbrev CHAINW : Nat := 0x50100
abbrev LEAFW : Nat := 0x50200
abbrev NODEW : Nat := 0x50300
abbrev FORW : Nat := 0x50400
abbrev NOUTW : Nat := 0x50500
abbrev HEAPW : Nat := 0x51000
abbrev SCREND : Nat := 0x52010
def hook153 : BitVec 32 := 0x6050106f
def hook540 : BitVec 32 := 0x25c0a06f
def NewCodeAt (im : Image) : Prop := signNew <+: im.code.drop 2074
def HooksAt (im : Image) : Prop :=
  im.code[153]? = some hook153 ∧ im.code[540]? = some hook540 ∧ im.code[545]? = some 0x00000073
def SignCodeAt (im : Image) : Prop := NewCodeAt im ∧ HooksAt im
def TableAt (t : MachineState) : Prop :=
  ∀ k < 8192, t.getMem (BitVec.ofNat 64 (TBL + 8 * k)) = bytesToWordLE ((tblBytes.drop (8 * k)).take 8)
def OutAt (t : MachineState) (A : Nat) (N : BitVec 256) : Prop :=
  ∀ k < 4, t.getMem (BitVec.ofNat 64 (A + 8 * k)) = N.extractLsb' (64 * k) 64
structure SearchPre (rho : Digest) (m : Message) (s : MachineState) : Prop where
  pc : s.pc = pcOf 153
  x5 : s.getReg .x5 = 0
  x19 : s.getReg .x19 = BitVec.ofNat 64 0
  rho : DigAt s DIG rho
  msg : ∀ k < 4, s.getMem (BitVec.ofNat 64 (DIG + 32 + 8 * k)) = m.extractLsb' (64 * k) 64
structure FailedS (t : MachineState) : Prop where
  pc : t.pc = pcOf 2214
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 1
def searchRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x22, .x24, .x25, .x28]
def SearchW (A : Nat) : Prop := A = DIG + 16 ∨ A = DIG + 24 ∨ (NBUF ≤ A ∧ A < NBUF + 32) ∨ A = IDXV
def SearchPost (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => FailedS t
  | some (c, N), t => t.pc = pcOf 2215 ∧ t.getReg .x5 = 0 ∧ WCT9.admissible N = true ∧ OutAt t NBUF N ∧
      t.getReg .x22 = BitVec.ofNat 64 (N.toNat % 2 ^ 31) ∧
      t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 (N.toNat % 2 ^ 31) ∧
      c.toNat < WCT9.digestAttemptLimit ∧ RegsExcept s t searchRegs ∧ Frame s t SearchW
def trialC : Nat := 150
def searchC : Nat := WCT9.digestAttemptLimit * trialC + 200
def SearchGood (im : Image) : Prop :=
  NewCodeAt im → HooksAt im → ∀ (sk : BitVec 256) (rho : Digest) (m : Message) (s : MachineState),
    SearchPre rho m s →
      TBSim im sk s searchC (WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit) (SearchPost s)
def ScrZero (A : Nat) : Prop :=
  A = PRIVW + 48 ∨ A = PRIVW + 56 ∨ A = CHAINW ∨ A = CHAINW + 8 ∨ A = CHAINW + 32 ∨ A = CHAINW + 40 ∨
    A = NODEW + 32 ∨ A = NODEW + 40 ∨ A = FORW + 160 ∨ A = FORW + 168 ∨ A = FORW + 176 ∨ A = FORW + 184
structure FtsPre (sk : BitVec 256) (N : HashOutput) (s : MachineState) : Prop where
  pc : s.pc = pcOf 2215
  x5 : s.getReg .x5 = 0
  x22 : s.getReg .x22 = BitVec.ofNat 64 (N.toNat % 2 ^ 31)
  adm : WCT9.admissible N = true
  nbuf : OutAt s NBUF N
  sk : ∀ k < 4, s.getMem (BitVec.ofNat 64 (SK + 8 * k)) = sk.extractLsb' (64 * k) 64
  zero : ∀ A, ScrZero A → s.getMem (BitVec.ofNat 64 A) = 0
  table : TableAt s
def ftsRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x18, .x24, .x25, .x26, .x28, .x29]
def FtsW (A : Nat) : Prop := (PRIVW ≤ A ∧ A < SCREND) ∨ (SIG + 16 ≤ A ∧ A < SIG + 2032) ∨ (FOUT ≤ A ∧ A < FOUT + 32)
def OpeningAt (t : MachineState) (k : Nat) (op : WCT9.Opening) : Prop :=
  (∀ i : Fin 7, DigAt t (SIG + 16 + 224 * k + 16 * i.val) (op.values i)) ∧
    ∀ l : Fin 7, DigAt t (SIG + 128 + 224 * k + 16 * l.val) (op.path l)
def FtsPost (s : MachineState) : List WCT9.Opening × Digest → MachineState → Prop
  | (ops, root), t => t.pc = pcOf 370 ∧ t.getReg .x5 = 0 ∧ DigAt t FOUT root ∧ ops.length = 9 ∧
      (∀ k < 9, OpeningAt t k (ops.getD k ⟨fun _ => 0, fun _ => 0⟩)) ∧ RegsExcept s t ftsRegs ∧ Frame s t FtsW
def ftsC : Nat := 2000000
def FtsGood (im : Image) : Prop :=
  NewCodeAt im → ∀ (sk : BitVec 256) (N : HashOutput) (s : MachineState), FtsPre sk N s →
    TBSim im sk s ftsC (WCT9.signForest (N.toNat % 2 ^ 31) N) (FtsPost s)
def CompactPost (s t : MachineState) : Prop :=
  t.pc = pcOf 10946 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
    (∀ k < 428, t.getMem (BitVec.ofNat 64 (SIG + 2032 + 8 * k)) = s.getMem (BitVec.ofNat 64 (SIG + 2192 + 8 * k))) ∧
    Frame s t (fun A => SIG + 2032 ≤ A ∧ A < SIG + 5456)
def compactK : Nat := 1 + 6 + 214 * 7 + 2
def CompactGood (im : Image) : Prop :=
  NewCodeAt im → HooksAt im → ∀ s : MachineState, s.pc = pcOf 540 →
    ∃ t, Steps im s compactK compactK t ∧ CompactPost s t
structure FailedT (t : MachineState) : Prop where
  pc : t.pc = pcOf 545
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 1
structure HookPre (sk : BitVec 256) (m : Message) (rho : Digest) (t : MachineState) : Prop where
  search : SearchPre rho m t
  sigRho : DigAt t SIG rho
  sk : ∀ k < 4, t.getMem (BitVec.ofNat 64 (SK + 8 * k)) = sk.extractLsb' (64 * k) 64
  zero : ∀ A, ScrZero A → t.getMem (BitVec.ofNat 64 A) = 0
  table : TableAt t
def frontC : Nat := 2490014
def FrontSpec (im : Image) (sk : BitVec 256) (cache : Bytes 131072) (m : Message) (s0 : MachineState)
    (Inv : MachineState → Prop) : Prop :=
  ∀ {α : Type} (W : Nat) (Q : Option α → MachineState → Prop) (K : Digest → M (Option α)),
    (∀ t, FailedT t → Q none t) →
    (∀ rho t, HookPre sk m rho t → Inv t → TBSim im sk t W (K rho) Q) →
    TBSim im sk s0 (frontC + W) (do
      let tag ← privateMac (cacheDec cache).region
      if tag ≠ (cacheDec cache).tag then pure none else privateNonce m >>= K) Q
structure LayPre (index : Nat) (root : Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf 370
  x5 : t.getReg .x5 = 0
  hidx : index < 2 ^ 31
  idx : t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  root : DigAt t FOUT root
def t3LayIdx (lay : Layer) : Nat := (![137, 203, 253, 302] : Layer → Nat) lay
def PieceAt (u : MachineState) (lay : Layer) (p : Pieces) : Prop :=
  (∀ i < chainCount lay, DigAt u (SIG + 16 * (t3LayIdx lay + i)) (p.1.getD i 0)) ∧
    ∀ j < height lay, DigAt u (SIG + 16 * (t3LayIdx lay + chainCount lay + j)) (p.2.getD j 0)
def LayPost (t : MachineState) : Option (List Pieces) → MachineState → Prop
  | none, u => FailedT u
  | some ps, u => u.pc = pcOf 540 ∧ ps.length = 4 ∧ (∀ lay : Layer, PieceAt u lay (ps.getD lay.val ([], []))) ∧
      Frame t u (fun A => ¬ (SIG ≤ A ∧ A < SIG + 2192))
def layC : Nat := 26 + 2877375919
def LayersSpec (im : Image) (sk : BitVec 256) (cache : Bytes 131072) (Inv : MachineState → Prop) : Prop :=
  ∀ (index : Nat) (root : Digest) (t : MachineState), LayPre index root t → Inv t →
    TBSim im sk t layC (signLayers (cacheDec cache) index 4 root) (LayPost t)
def newRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x18, .x19, .x22, .x24, .x25, .x26, .x28, .x29]
def NewW (A : Nat) : Prop := SearchW A ∨ FtsW A
def InvStable (Inv : MachineState → Prop) : Prop :=
  ∀ t u, Inv t → Frame t u NewW → RegsExcept t u newRegs → Inv u
def wsub (imgs : Phase → Image) : Submission :=
  ⟨⟨5456, 25240, 131072⟩, ⟨0x40, 0x80, 0xA0, 0x80000, 0x7000, 0x800⟩, imgs⟩
structure Unchanged (imgs : Phase → Image) (Inv : BitVec 256 → Bytes 131072 → Message → MachineState → Prop) :
    Prop where
  front : ∀ sk cache m, ∃ s0, initialState (wsub imgs) .sign (sk, cache, m) = some s0 ∧
    FrontSpec (imgs .sign) sk cache m s0 (Inv sk cache m)
  stable : ∀ sk cache m, InvStable (Inv sk cache m)
  layers : ∀ sk cache m, LayersSpec (imgs .sign) sk cache (Inv sk cache m)
def SignRefinesW (imgs : Phase → Image) : Prop :=
  ∀ (sk : SecretKey) (cache : Bytes 131072) (m : Message),
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> (wsub imgs).run .sign (sk, cache, m) =
      (fun p => (p.1.map W9.T3M.sigB, p.2.1, p.2.2)) <$> countBoth (mrealize sk (WCT9.Rev3.sign (cacheDec cache) m))
def SignTerminatesW (imgs : Phase → Image) : Prop :=
  ∀ (hash : Hash) (sk : SecretKey) (cache : Bytes 131072) (m : Message),
    ((wsub imgs).runWith hash .sign (sk, cache, m)).finished = true ∧
      ((wsub imgs).runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT
def SignMain : Prop :=
  ∀ (imgs : Phase → Image) (Inv : BitVec 256 → Bytes 131072 → Message → MachineState → Prop),
    SignCodeAt (imgs .sign) → Unchanged imgs Inv → SignRefinesW imgs ∧ SignTerminatesW imgs
end ClaudeWCT.W9.Machine.Sign
