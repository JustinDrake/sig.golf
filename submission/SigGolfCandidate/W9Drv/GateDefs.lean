import SigGolfCandidate.W9Machine.WctChainContract
import SigGolfCandidate.W9Machine.WctJudg

namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
open ClaudeWCT.W9.Machine.Merkle
def dispatchPc (n : Nat) : Nat := [68,83,100,117,134,151,168,185,202,219].getD n 219
abbrev idxOf (a : HashOutput) : Nat := a.toNat % 2 ^ 31
def DigestAt (a : HashOutput) (u : MachineState) : Prop :=
  ∀ k, k < 4 → u.getMem (BitVec.ofNat 64 (0x60 + 8 * k)) = a.extractLsb' (64 * k) 64
structure HeaderBank (index : Nat) (u : MachineState) : Prop where
  chain : ∀ k : Fin 9, ∀ t, t < 7 → ∀ d, d < 3 →
    u.getMem (BitVec.ofNat 64 (W9Machine.Chain.table k + 64 * t + 8 * d)) =
      BitVec.ofNat 64 (hdr0 5 k.val index (d + 256 * t))
  node : ∀ k : Fin 9,
    u.getMem (BitVec.ofNat 64 (W9Machine.Chain.table k + 448)) = BitVec.ofNat 64 (w0n k.val index)
  leaf : ∀ k : Fin 9,
    u.getMem (BitVec.ofNat 64 (W9Machine.Chain.table k + 456)) =
      BitVec.ofNat 64 (hdr0 6 k.val index 0)
structure GatePre (pk : Digest) (w : WBytes) (a : HashOutput) (u : MachineState) : Prop where
  pc : u.pc = pcOf 23
  glob : Glob baseK w pk u
  digest : DigestAt a u
  bank : HeaderBank (idxOf a) u
  wit : WitAll w u
structure CoordPre (pk : Digest) (w : WBytes) (a : HashOutput) (n : Nat) (roots : List Digest)
    (u : MachineState) : Prop where
  le : n ≤ 9
  length : roots.length = n
  pc : u.pc = pcOf (dispatchPc n)
  glob : Glob baseK w pk u
  digest : DigestAt a u
  bank : HeaderBank (idxOf a) u
  index : u.getReg .x22 = BitVec.ofNat 64 (idxOf a)
  heaps : ∀ h, 1 ≤ h → h ≤ 7 → u.getReg (heapReg h) = BitVec.ofNat 64 (idxOf a + 2 ^ 32 * h)
  stepOne : u.getReg .x6 = 1
  stepTwo : u.getReg .x7 = 2
  mask : u.getReg .x2 = BitVec.ofNat 64 0xfffc
  jt : u.getReg .x24 = BitVec.ofNat 64 0xd6800
  childBlock : u.getReg .x29 = BitVec.ofNat 64 0xce800
  baseReg : u.getReg .x8 = BitVec.ofNat 64 (2112 + 1024 * (n - 1))
  headerReg : u.getReg .x28 = BitVec.ofNat 64 (0xfee600 + 2048 + 512 * (n - 1))
  roots : ∀ i, i < n → DigAt u (W9Machine.forestSlot i) (roots.getD i 0)
  coords : ∀ k : Fin 9, n ≤ k.val → ∀ off, off < 1024 → off % 8 = 0 →
    OrigW w u (W9Machine.Chain.base k + off)
  layer : Orig w (fun o => o < 64 ∨ 11288 ≤ o) u
end W9Drv
