import SigGolfCandidate.W9Machine.WctJudg
import SigGolfCandidate.W9Machine.WctChildContract
import SigGolfCandidate.T3M.Verify.Compose

namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
abbrev idxOf (a : HashOutput) : Nat := a.toNat % 2 ^ 31
def DigestAt (a : HashOutput) (u : MachineState) : Prop :=
  ∀ k, k < 4 → u.getMem (BitVec.ofNat 64 (0x60 + 8 * k)) = a.extractLsb' (64 * k) 64
structure HeaderBank (u : MachineState) : Prop where
  node : ∀ k : Fin 9,
    u.getMem (BitVec.ofNat 64 (0xfee600 + 512 * k.val + 448)) =
      BitVec.ofNat 64 (1 + 3 * 256 + (4 + k.val) * 65536)
  leaf : ∀ k : Fin 9,
    u.getMem (BitVec.ofNat 64 (0xfee600 + 512 * k.val + 456)) =
      BitVec.ofNat 64 (1 + 6 * 256 + k.val * 65536)
structure GatePre (pk : Digest) (w : WBytes) (a : HashOutput) (u : MachineState) : Prop where
  pc : u.pc = pcOf 27
  glob : Glob baseK w pk u
  digest : DigestAt a u
  bank : HeaderBank u
  wit : WitAll w u
def dispatchPc (n : Nat) : Nat := [57,73,91,109,127,145,163,181,199,217].getD n 217
def cachedWord (n : Nat) : Nat := [0,0,1,1,1,2,2,2,3,3].getD n 3
structure CoordPre (pk : Digest) (w : WBytes) (a : HashOutput) (n : Nat)
    (pairs : List (Digest × Digest)) (u : MachineState) : Prop where
  le : n ≤ 9
  length : pairs.length = n
  pc : u.pc = pcOf (dispatchPc n)
  glob : Glob baseK w pk u
  digest : DigestAt a u
  bank : HeaderBank u
  index : u.getReg .x22 = BitVec.ofNat 64 (idxOf a)
  heaps : ∀ h, 2 ≤ h → h ≤ 7 → u.getReg (Child.heapReg h) = BitVec.ofNat 64 h
  stepOne : u.getReg .x7 = 1
  stepTwo : u.getReg .x13 = 2
  hashLen : u.getReg .x11 = 64
  coordStep : u.getReg .x6 = 65536
  prefixReg : u.getReg .x15 = BitVec.ofNat 64 (idxOf a * 2^27 + 65536 * (n-1))
  nodeIndex : u.getReg .x17 = BitVec.ofNat 64 (idxOf a * 2^32)
  cached : n ≠ 0 → u.getReg .x16 = a.extractLsb' (64 * cachedWord n) 64
  mask : u.getReg .x2 = BitVec.ofNat 64 0xfffc
  jt : u.getReg .x24 = BitVec.ofNat 64 0xd6800
  childBlock : u.getReg .x29 = BitVec.ofNat 64 0xce800
  baseReg : u.getReg .x8 = BitVec.ofNat 64 (2112 + 1024 * (n-1))
  headerReg : u.getReg .x28 = BitVec.ofNat 64 (0xfee600 + 2048 + 512 * (n-1))
  pairs : ∀ i, i < n → DigAt u (1056 + 32*i) (pairs.getD i (0,0)).1 ∧
    DigAt u (1056 + 32*i + 16) (pairs.getD i (0,0)).2
  coords : ∀ k : Fin 9, n ≤ k.val → ∀ off, off < 1024 → off % 8 = 0 →
    OrigW w u (coordinateBase k + off)
  layer : Orig w (fun o => o < 64 ∨ 10568 ≤ o) u
end W9Drv
