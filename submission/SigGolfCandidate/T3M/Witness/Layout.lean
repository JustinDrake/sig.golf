import SigGolfCandidate.T3.Core

/-! # T3M witness layout (stream W)

The byte layout of the machine witness, transcribed from `t3m/ref3/layout.py` (layout v3, `W = 25,240`, charge
99), and the byte readers of the padded verifier `verifyP`. Every offset is relative to the witness base (`0x800`
on the machine).

| offset | content |
|---|---|
| `[0,16)` rho, `[16,20)` dc (LE32), `[20,36)` `c_0..c_3` (LE32), `[36,64)` zero | payload / dead |
| `[64,1088)` | 21 FTS leaf blocks `[pad | T | secret | pad']` at stride 48 (`pad'` of block `s` = `pad` of `s+1`) |
| `[1088,11288)` | fold stream: 35 segments (8-byte header, `a` × (64-byte fold block + 16-byte gap)) |
| `[11288,15768)` | layer 0: 12 Merkle blocks (level `j` at `+64 (11-j)`), then 58 chain blocks (chain `i` at `+64 (57-i)`) |
| `[15768,18968)`, `[18968,22104)`, `[22104,25240)` | layers 1, 2, 3 (`h` Merkle + 43 chain blocks each) |

Reads at or beyond `wsize` return zero (`BitVec.extractLsb'` past the width is zero): during verify the machine's
memory after the witness is zero, as `absverify_t3.wb` assumes. -/
namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3

/-- Witness size in bytes. -/
def wsize : Nat := 25240

/-- The witness as the organizer's `Legacy.Bytes 25240` (= `BitVec (8 * 25240)`, byte `i` = bits `8i..8i+8`). -/
abbrev WBytes := BitVec (8 * 25240)

/-- Witness byte `i` (zero for `i ≥ wsize`). -/
def wbyte (w : WBytes) (i : Nat) : UInt8 := UInt8.ofBitVec (w.extractLsb' (8 * i) 8)

/-- The 16 witness bytes at `off`, little endian (bytes past the witness read as zero). -/
def wdig (w : WBytes) (off : Nat) : Digest := w.extractLsb' (8 * off) 128

/-- The little-endian 32-bit word at `off`. -/
def wle32 (w : WBytes) (off : Nat) : BitVec 32 := w.extractLsb' (8 * off) 32

/-! ## Offsets -/

/-- `rho` at `[0,16)`. -/
def rhoOff : Nat := 0
/-- The digest counter (LE32) at `[16,20)`. -/
def dcOff : Nat := 16
/-- Layer `lay`'s counter (LE32) at `20 + 4 lay`. -/
def counterOff (lay : Layer) : Nat := 20 + 4 * lay.val

/-- Leaf block of slot `s = 3 coord + j` (`j` = position in the sorted triple): `[pad | T | secret | pad']`. -/
def leafBlock (s : Nat) : Nat := 64 + 48 * s

/-- First segment header of the fold stream. -/
def streamBase : Nat := 1088
/-- The pointer cap checked after coordinate 6 (`35 · 8 + 121 · 80` bytes after `streamBase`). -/
def streamEnd : Nat := 11048
/-- Fold block `r` of the segment whose header is at `ptr`: `[L | T | pad | R]` then a 16-byte gap. -/
def foldBlock (ptr r : Nat) : Nat := ptr + 8 + 80 * r
/-- The next header after a segment at `ptr` with `a` folds. -/
def segNext (ptr a : Nat) : Nat := ptr + 8 + 80 * a
/-- Offset of the pre-placed sibling inside a fold or Merkle block: `L` (0) when the current node is a right child
(`side = 1`), else `R` (48). -/
def sibOff (side : Nat) : Nat := if side = 1 then 0 else 48

/-- Start of layer `lay`'s region (memory order 0, 1, 2, 3). -/
def layerBase (lay : Layer) : Nat := (![11288, 15768, 18968, 22104] : Layer → Nat) lay
/-- Merkle block of level `j` (0 = the fold with the leaf pk) of layer `lay`: `[L | T | pad | R]`. -/
def merkleBlock (lay : Layer) (j : Nat) : Nat := layerBase lay + 64 * (height lay - 1 - j)
/-- Chain block of chain `i` of layer `lay`: `[pad0 | T | pad1 | value]`. -/
def chainBlock (lay : Layer) (i : Nat) : Nat := layerBase lay + 64 * height lay + 64 * (chainCount lay - 1 - i)

/-! ## Field readers (shared by `verifyP` and the decoders) -/

/-- `rho`. -/
def wrho (w : WBytes) : Digest := wdig w rhoOff
/-- The digest counter. -/
def wdc (w : WBytes) : BitVec 32 := wle32 w dcOff
/-- Layer `lay`'s counter. -/
def wctr (w : WBytes) (lay : Layer) : BitVec 32 := wle32 w (counterOff lay)
/-- Opened FTS secret of slot `s`. -/
def wsecret (w : WBytes) (s : Nat) : Digest := wdig w (leafBlock s + 32)
/-- Leaf pad `P_s` (`[0,16)` of leaf block `s`; `P_{s+1}` is also bytes `48..64` of block `s`). -/
def wleafPad (w : WBytes) (s : Nat) : Digest := wdig w (leafBlock s)
/-- Chain value of chain `i` of layer `lay` (`+48` of its block). -/
def wvalue (w : WBytes) (lay : Layer) (i : Nat) : Digest := wdig w (chainBlock lay i + 48)
/-- The two chain pads (`+0`, `+32`). -/
def wchainPads (w : WBytes) (lay : Layer) (i : Nat) : Digest × Digest :=
  (wdig w (chainBlock lay i), wdig w (chainBlock lay i + 32))
/-- Merkle sibling of level `j` for the leaf index `leaf` (at `L` iff bit `j` of `leaf` is 1). -/
def wpath (w : WBytes) (lay : Layer) (leaf j : Nat) : Digest :=
  wdig w (merkleBlock lay j + sibOff (leaf / 2 ^ j % 2))
/-- Merkle pad of level `j` (`+32`). -/
def wmerklePad (w : WBytes) (lay : Layer) (j : Nat) : Digest := wdig w (merkleBlock lay j + 32)

/-- Global leaf `g = 128 bucket + x_j` of position `j` of a selection (its heap index is `2048 + g`). -/
def selLeaf (sel : Selection) (j : Nat) : Nat := sel.bucket * 128 + sel.leaves.getD j 0

end SigGolfCandidate.T3M
