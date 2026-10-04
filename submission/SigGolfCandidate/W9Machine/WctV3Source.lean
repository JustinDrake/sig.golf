import SigGolfCandidate.W9Machine.WctLayout
import SigGolfCandidate.ClaudeWCT.WCT9.Basic

set_option autoImplicit false
namespace W9Machine.V3
open OracleComp SigGolfCandidate.T3 SigGolfCandidate.T3M
open SphincsSecurity (bytesLE)
def chainPrefix (index coord child : Nat) : Nat :=
  (index <<< 27) ||| (coord <<< 16) ||| (child <<< 20)
def chainLow (index coord child chain step : Nat) : Nat :=
  0x80 ||| (chain <<< 2) ||| (step <<< 8) ||| chainPrefix index coord child
abbrev HeaderPad := BitVec 64
def chainInput (index coord child chain step : Nat) (a : Digest) (b : HeaderPad)
    (c value : Digest) : HashInput :=
  bytesLE 16 a ++ bytesLE 8 (chainLow index coord child chain step) ++ bytesLE 8 b ++
    bytesLE 16 c ++ bytesLE 16 value
def chainP (index coord child chain start count : Nat) (a : Digest) (b : HeaderPad)
    (c value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun v step => shortHash (chainInput index coord child chain step a b c v)) value
def regionOffset (coord : Nat) : Nat := 64 + 1024 * coord
def chainOffset (coord chain : Nat) : Nat := regionOffset coord + (832 - 64 * chain)
def leafSlot (chain : Nat) : Nat := if chain = 0 then 880 else 896 + 16 * chain
def chainPadA (w : WBytes) (coord chain : Nat) : Digest := wdig w (chainOffset coord chain)
def chainPadB (w : WBytes) (coord chain : Nat) : HeaderPad :=
  w.extractLsb' (8 * (chainOffset coord chain + 24)) 64
def chainPadC (w : WBytes) (coord chain : Nat) : Digest :=
  wdig w (chainOffset coord chain + 32)
def reveal (w : WBytes) (coord chain deficit : Nat) : Digest :=
  if deficit = 0 then wdig w (regionOffset coord + leafSlot chain)
  else wdig w (chainOffset coord chain + 48)
def chainProgram (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 728) : M (List Digest) :=
  (List.finRange 7).mapM fun t =>
    let d := ClaudeWCT.WCT9.digit rank t
    chainP index k.val j.val t.val (3 - d) d
      (chainPadA w k.val t.val) (chainPadB w k.val t.val)
      (chainPadC w k.val t.val) (reveal w k.val t.val d)
def nodeLow (coord index : Nat) : Nat :=
  1 ||| (3 <<< 8) ||| ((4 + coord) <<< 16) ||| (index <<< 32)
def nodeInput (coord index heap : Nat) (left pad right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 8 (nodeLow coord index) ++ bytesLE 8 heap ++
    bytesLE 16 pad ++ bytesLE 16 right
def blockOffset (level : Nat) : Nat := 64 * (6 - level)
def siblingOffset (child level : Nat) : Nat :=
  blockOffset level + if child / 2 ^ level % 2 = 0 then 48 else 0
def nodePad (w : WBytes) (coord level : Nat) : Digest :=
  wdig w (regionOffset coord + blockOffset level + 32)
def sibling (w : WBytes) (coord child level : Nat) : Digest :=
  wdig w (regionOffset coord + siblingOffset child level)
def leafFields (coord index child : Nat) (ends : List Digest) (slot : Nat) : Digest :=
  if slot = 0 then ends.getD 0 0
  else if slot = 1 then header 6 coord index 0 child else ends.getD (slot - 1) 0
def leafInput (coord index child : Nat) (ends : List Digest) : HashInput :=
  (List.range 8).flatMap fun slot => bytesLE 16 (leafFields coord index child ends slot)
structure RootPair where
  left : Digest
  right : Digest
def orderPair (child : Nat) (computed other : Digest) : RootPair :=
  if child / 64 % 2 = 0 then ⟨computed, other⟩ else ⟨other, computed⟩
def childProgram (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (ends : List Digest) : M RootPair := do
  let leaf ← shortHash (leafInput k.val index j.val ends)
  let computed ← (List.range 6).foldlM (fun value level =>
    let other := sibling w k.val j.val level
    let left := if j.val / 2 ^ level % 2 = 0 then value else other
    let right := if j.val / 2 ^ level % 2 = 0 then other else value
    shortHash (nodeInput k.val index ((128 + j.val) / 2 ^ (level + 1))
      left (nodePad w k.val level) right)) leaf
  pure (orderPair j.val computed (sibling w k.val j.val 6))
end W9Machine.V3
