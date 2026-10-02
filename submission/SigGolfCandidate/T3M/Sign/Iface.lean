import SigGolfCandidate.T3M.Sign.BaseInv
import SigGolfCandidate.T3M.SigCodec

/-!
# Sign: the interface between the middle (instance F) and layer 0 / the output (instance M)

* `Halted0 u` : `HALT(0)` reached (word 542, `t0 = 1`, `a0 = 0`);
* `L0Pre sk cache index root t` : the `layer_0` entry (word 427) as left by layer 1's `build_tree`: `Base`,
  the hypertree index at `IDXV`, the layer-1 root (the message of layer 0) at `ENC`, the counter doubleword;
* `L0Spec sk cache` : what F consumes from M: from `L0Pre` the machine refines `signLayers cache index 1 root`
  (layer 0: `counterSearch`, `signTop`) within `L0Cost` cycles; on success it halts with the top piece in the
  signature (values at `SIG + 2192`, path at `SIG + 3120`) and leaves the rest of the signature untouched (`L0W`);
* `PayPost` : what F delivers to M for `payloadRest`: `Failed`, or `Halted0` with all 355 signature digests
  (`sigDigests`, E's `SigCodec`) at `SIG`.
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Signature Pieces signLayers counterLimit)

/-- `HALT(0)` at the final `ECALL` (word 542). -/
structure Halted0 (u : MachineState) : Prop where
  pc : u.pc = pcOf 542
  x5 : u.getReg .x5 = 1
  x10 : u.getReg .x10 = 0

/-- The `layer_0` entry (word 427). -/
structure L0Pre (sk : SecretKey) (cache : Bytes 32768) (index : Nat) (root : Digest) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf 427
  base : Base sk cache t
  hidx : index < 2 ^ 31
  idx : t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  enc : DigAt t ENC root
  c32 : (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32

/-- Layer 0 may write anything but the signature outside its own piece. -/
def L0W (A : Nat) : Prop := ¬ (SIG ≤ A ∧ A < SIG + 2192) ∧ ¬ (SIG + 3312 ≤ A ∧ A < SIG + 5680)

/-- The exit of layer 0: `fail`, or `HALT(0)` with the top piece `(values, path)` in the signature. -/
def L0Post (t : MachineState) : Option (List Pieces) → MachineState → Prop
  | none, u => Failed u
  | some ps, u => ∃ vals path : List Digest, ps = [(vals, path)] ∧ Halted0 u ∧
      (∀ i < 58, DigAt u (SIG + 2192 + 16 * i) (vals.getD i 0)) ∧
      (∀ j < 12, DigAt u (SIG + 3120 + 16 * j) (path.getD j 0)) ∧ Frame t u L0W

/-- All-oracle cycle bound of layer 0 (its counter search: `≤ 205` cycles per trial, plus `signTop`). -/
def L0Cost : Nat := counterLimit * 205 + 200000

/-- **Interface (M)**: layer 0 refines `signLayers cache index 1 root`. -/
def L0Spec (sk : SecretKey) (cache : Bytes 32768) : Prop :=
  ∀ (index : Nat) (root : Digest) (t : MachineState), L0Pre sk cache index root t →
    TBSim image sk t L0Cost (signLayers (cacheDec cache) index 1 root) (L0Post t)

/-- **Interface (F)**: the exit of `payloadRest`: `fail`, or `HALT(0)` with the whole signature at `SIG`. -/
def PayPost : Option Signature → MachineState → Prop
  | none, u => Failed u
  | some sig, u => Halted0 u ∧ ∀ k < 355, DigAt u (SIG + 16 * k) ((sigDigests sig).getD k 0)

end SigGolfCandidate.T3M.Sign
