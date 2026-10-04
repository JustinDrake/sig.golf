import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Fetch
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Honest
import SigGolfCandidate.ClaudeWCT.W9.T3M.SigCodec
import SigGolfCandidate.T3M.Expand.LayersBlocks
import SigGolfCandidate.T3M.Expand.Blocks

namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC FailedAt KernAt)
open SigGolfCandidate.T3M.Expand (IDXV)
def hookWord : BitVec 32 := 0x3880106f
def HB0 : Nat := 0xffde00
def regBase (k : Nat) : Nat := 0x840 + 1024 * k
def HdrBankOK (s : MachineState) : Prop :=
  ∀ k, k < 9 →
    s.getMem (BitVec.ofNat 64 (HB0 + 512 * k + 448)) = BitVec.ofNat 64 (hdr0 3 (4 + k) 0 0) ∧
    s.getMem (BitVec.ofNat 64 (HB0 + 512 * k + 456)) = BitVec.ofNat 64 (hdr0 6 k 0 0)
def regionWord (N : HashOutput) (sig : WCT9.Signature) (k i : Nat) : Word :=
  (wordsOf (ClaudeWCT.W9.T3M.regionBytes (WCT9.child N ⟨k % 9, Nat.mod_lt _ (by decide)⟩).val
    (sig.openings ⟨k % 9, Nat.mod_lt _ (by decide)⟩))).getD i 0
def Placed (N : HashOutput) (sig : WCT9.Signature) (s : MachineState) : Prop :=
  ∀ k i, k < 9 → i < 128 → s.getMem (BitVec.ofNat 64 (regBase k + 8 * i)) = regionWord N sig k i
def newProg (m : Message) (sig : WCT9.Signature) : M (Option (BitVec 32 × HashOutput × Digest)) := do
  let some (counter, N) ← WCT9.digestSearch sig.rho m 0 WCT9.digestAttemptLimit | pure none
  let root ← WCT9.recoverFts sig (N.toNat % 2 ^ 31) N
  pure (some (counter, N, root))
structure Pre30 (m : Message) (sig : WCT9.Signature) (s : MachineState) : Prop where
  pc : s.pc = pcOf 30
  x5 : s.getReg .x5 = 0
  x19 : s.getReg .x19 = BitVec.ofNat 64 0
  rho : DigAt s DIG sig.rho
  msg : ∀ k, k < 4 → s.getMem (BitVec.ofNat 64 (DIG + 32 + 8 * k)) = m.extractLsb' (64 * k) 64
  sigAt : ∀ k, k < 341 → DigAt s (0x7000 + 16 * k) ((ClaudeWCT.W9.T3M.sigDigests sig).getD k 0)
  zeroW : ∀ A, 0x840 ≤ A → A < 0x3148 → s.getMem (BitVec.ofNat 64 A) = 0
  bank : HdrBankOK s
def NewW (A : Nat) : Prop :=
  A = DIG + 16 ∨ A = DIG + 24 ∨ (NBUF ≤ A ∧ A < NBUF + 32) ∨ A = IDXV ∨ A = 0x810 ∨ (0x60 ≤ A ∧ A < 0x80) ∨
    (0x100 ≤ A ∧ A < 0x120) ∨ (0x400 ≤ A ∧ A < 0x550) ∨ (0x840 ≤ A ∧ A < 0x3148) ∨ A = ENC ∨ A = ENC + 8 ∨
    (0x7000 + 2192 ≤ A ∧ A < 0x7000 + 5616)
structure Post249 (sig : WCT9.Signature) (s0 : MachineState) (counter : BitVec 32) (N : HashOutput) (root : Digest)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf 249
  x5 : t.getReg .x5 = 0
  sp : t.getReg .x2 = BitVec.ofNat 64 0x22000
  idx : t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 (N.toNat % 2 ^ 31)
  enc : DigAt t ENC root
  dc : (t.getMem (BitVec.ofNat 64 0x810)).extractLsb' 0 32 = counter
  placed : Placed N sig t
  gap : ∀ A, 0x2c40 ≤ A → A < 0x3148 → t.getMem (BitVec.ofNat 64 A) = 0
  layers : ∀ i, i < 214 → DigAt t (0x7000 + 2192 + 16 * i) ((ClaudeWCT.W9.T3M.sigDigests sig).getD (127 + i) 0)
  frame : Frame s0 t NewW
def NewPost (sig : WCT9.Signature) (s0 : MachineState) :
    Option (BitVec 32 × HashOutput × Digest) → MachineState → Prop
  | none, t => FailedAt 1418 t
  | some (counter, N, root), t => Post249 sig s0 counter N root t
def newCost : Nat := 2 ^ 21 * 200 + 100000
def HookAt (im : Image) : Prop := CodeAt im (pcOf 30) [hookWord]
def NewCodeSpec (im : Image) : Prop :=
  ∀ (sk : BitVec 256) (m : Message) (sig : WCT9.Signature) (s : MachineState), Pre30 m sig s →
    TBSim im sk s newCost (newProg m sig) (NewPost sig s)
def w9Sub (imgs : Phase → Image) : Submission where
  sizes := ⟨5456, 24264, 131072⟩
  layout := ⟨0x40, 0x80, 0xA0, 0x80000, 0x7000, 0x800⟩
  image := imgs
def FrontAt (im : Image) : Prop := CodeAt im (pcOf 0) (SigGolfCandidate.T3M.Expand.seg_0 ++ [hookWord])
def compareCode : List (BitVec 32) :=
  SigGolfCandidate.T3M.Expand.seg_342 ++ SigGolfCandidate.T3M.Expand.seg_348 ++
    SigGolfCandidate.T3M.Expand.seg_351 ++ SigGolfCandidate.T3M.Expand.seg_353
def ExpandDataOK (im : Image) : Prop := im.data = hdrBankBytes ++ SigGolfCandidate.T3M.Images.expandLegacyData
def ExpandRefinesW (imgs : Phase → Image) : Prop :=
  ∀ (m : Message) (pk : PublicKey) (s : Bytes 5456),
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> (w9Sub imgs).run .expand (m, pk, s) =
      (fun p => (p.1.map (fun x => ClaudeWCT.W9.T3M.witEnc x.1 x.2), p.2.1, p.2.2)) <$>
        countBoth (mrealize 0 (ClaudeWCT.W9.T3M.expandN m pk (ClaudeWCT.W9.T3M.sigDec s)))
def ExpandTerminatesW (imgs : Phase → Image) : Prop :=
  ∀ (hash : Hash) (m : Message) (pk : PublicKey) (s : Bytes 5456),
    ((w9Sub imgs).runWith hash .expand (m, pk, s)).finished = true ∧
      ((w9Sub imgs).runWith hash .expand (m, pk, s)).cycles < CYCLE_LIMIT
end ClaudeWCT.W9.Machine.Expand
