import SigGolfCandidate.T3.Core

namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3
def wsize : Nat := 24264
abbrev WBytes := BitVec (8 * 24264)
def wbyte (w : WBytes) (i : Nat) : UInt8 := UInt8.ofBitVec (w.extractLsb' (8 * i) 8)
def wdig (w : WBytes) (off : Nat) : Digest := w.extractLsb' (8 * off) 128
def wle32 (w : WBytes) (off : Nat) : BitVec 32 := w.extractLsb' (8 * off) 32
def rhoOff : Nat := 0
def dcOff : Nat := 16
def counterOff (lay : Layer) : Nat := 20 + 4 * lay.val
def leafBlock (s : Nat) : Nat := 64 + 48 * s
def streamBase : Nat := 1088
def streamEnd : Nat := 10568
def foldBlock (ptr r : Nat) : Nat := ptr + 8 + 80 * r
def segNext (ptr a : Nat) : Nat := ptr + 8 + 80 * a
def sibOff (side : Nat) : Nat := if side = 1 then 0 else 48
def layerBase (lay : Layer) : Nat := (![10568, 14792, 17992, 21128] : Layer → Nat) lay
def merkleBlock (lay : Layer) (j : Nat) : Nat := layerBase lay + 64 * (height lay - 1 - j)
def chainBlock (lay : Layer) (i : Nat) : Nat := layerBase lay + 64 * height lay + 64 * (chainCount lay - 1 - i)
def wrho (w : WBytes) : Digest := wdig w rhoOff
def wdc (w : WBytes) : BitVec 32 := wle32 w dcOff
def wctr (w : WBytes) (lay : Layer) : BitVec 32 := wle32 w (counterOff lay)
def wsecret (w : WBytes) (s : Nat) : Digest := wdig w (leafBlock s + 32)
def wleafPad (w : WBytes) (s : Nat) : Digest := wdig w (leafBlock s)
def wvalue (w : WBytes) (lay : Layer) (i : Nat) : Digest := wdig w (chainBlock lay i + 48)
def wchainPads (w : WBytes) (lay : Layer) (i : Nat) : Digest × Digest :=
  (wdig w (chainBlock lay i), wdig w (chainBlock lay i + 32))
def wpath (w : WBytes) (lay : Layer) (leaf j : Nat) : Digest :=
  wdig w (merkleBlock lay j + sibOff (leaf / 2 ^ j % 2))
def wmerklePad (w : WBytes) (lay : Layer) (j : Nat) : Digest := wdig w (merkleBlock lay j + 32)
def selLeaf (sel : Selection) (j : Nat) : Nat := sel.bucket * 128 + sel.leaves.getD j 0
end SigGolfCandidate.T3M
