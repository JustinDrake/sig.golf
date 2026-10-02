import SigGolfCandidate.T3M.FullCache.MacLanes
import SigGolfCandidate.T3.FullCache.Polynomial

namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SphincsSecurity
open SiggolfT3Mac4
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

def KeysAt (s : MachineState) (a b : BitVec 256) : Prop :=
  ∀ j : Fin 8, s.getMem (BitVec.ofNat 64 (KEYS+8*j.val)) =
    if j.val < 4 then a.extractLsb' (64*j.val) 64 else b.extractLsb' (64*(j.val-4)) 64

def keyPair (a b : BitVec 256) : MacKey := fun i => if i = 0 then a else b

theorem extract64_mod61 (a : BitVec 256) (off : Nat) :
    (a.extractLsb' off 64).toNat % 2^61 = (a.extractLsb' off 61).toNat := by
  simp only [BitVec.extractLsb'_toNat]
  exact Nat.mod_mod_of_dvd _ (by norm_num)

theorem laneWord_eq_tag (s : MachineState) (a b : BitVec 256) (region : List UInt8)
    (hk : KeysAt s a b) (j : Fin 4) : laneWord s j region = macTag (keyPair a b) region j := by
  have h0 := hk 0; have h1 := hk 1; have h2 := hk 2; have h3 := hk 3
  have h4 := hk 4; have h5 := hk 5; have h6 := hk 6; have h7 := hk 7
  change s.getMem 458752#64 = a.extractLsb' 0 64 at h0
  change s.getMem 458760#64 = a.extractLsb' 64 64 at h1
  change s.getMem 458768#64 = a.extractLsb' 128 64 at h2
  change s.getMem 458776#64 = a.extractLsb' 192 64 at h3
  change s.getMem 458784#64 = b.extractLsb' 0 64 at h4
  change s.getMem 458792#64 = b.extractLsb' 64 64 at h5
  change s.getMem 458800#64 = b.extractLsb' 128 64 at h6
  change s.getMem 458808#64 = b.extractLsb' 192 64 at h7
  fin_cases j <;>
    simp [laneWord, macTag, macKeyWord, macPadWord, keyPair, KEYS, h0,h1,h2,h3,h4,h5,h6,h7,
      extract64_mod61]

theorem encodeTag_word (tag : MacTag) (j : Fin 4) :
    (encodeTag tag).extractLsb' (64*j.val) 64 = tag j := by
  obtain ⟨h0,h1,h2,h3⟩ := extract_answerOfWords (tag 0) (tag 1) (tag 2) (tag 3)
  fin_cases j <;> simp only [encodeTag] <;> assumption

end SigGolfCandidate.T3M.FullCache
