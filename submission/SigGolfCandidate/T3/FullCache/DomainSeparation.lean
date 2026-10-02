import SigGolfCandidate.T3.Proofs
import SigGolfCandidate.T3.FullCache.KeySplit

namespace SiggolfT3Mac4.Source
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Header packing preserves the domain-tag byte for every address. -/
theorem header_tag_nat (tag lay tree position index : Nat) :
    ((SigGolfCandidate.T3.header tag lay tree position index).toNat / 256) % 256 = tag % 256 := by
  rw [SigGolfCandidate.T3.header_toNat]
  have ht := Nat.mod_lt tag (by decide : 0 < 256)
  have hl := Nat.mod_lt lay (by decide : 0 < 256)
  have hth := Nat.mod_lt (tree/2^32) (by decide : 0 < 256)
  have hp := Nat.mod_lt position (by decide : 0 < 2^32)
  have htl := Nat.mod_lt tree (by decide : 0 < 2^32)
  have hi := Nat.mod_lt index (by decide : 0 < 2^32)
  split_ifs <;> norm_num only [Nat.reducePow] at * <;> omega

theorem non_mac_tweak (tag lay tree position index : Nat) (htag : tag % 256 ≠ 14)
    (i : Fin 2) :
    (.inl (SigGolfCandidate.T3.header tag lay tree position index) : T3Coordinate) ≠ keyCoordinate i := by
  intro h
  have h' : SigGolfCandidate.T3.header tag lay tree position index =
      SigGolfCandidate.T3.header 14 0 0 0 i.val := Sum.inl.inj h
  have he := congrArg (fun t : BitVec 128 => (t.toNat / 256) % 256) h'
  rw [header_tag_nat,header_tag_nat] at he
  exact htag he

/-- Entire paired mask family, including all indices needed by the full cache. -/
theorem mask_coordinate_other (level pair : Nat) :
    (.inl (SigGolfCandidate.T3.header 13 0 0 level pair) : T3Coordinate) ≠ keyCoordinate 0 ∧
    (.inl (SigGolfCandidate.T3.header 13 0 0 level pair) : T3Coordinate) ≠ keyCoordinate 1 :=
  ⟨non_mac_tweak 13 0 0 level pair (by decide) 0,
   non_mac_tweak 13 0 0 level pair (by decide) 1⟩

/-- Entire WOTS seed family, with no leaf/chain restriction. Reserved unused
coordinates for a cross-leaf packing proof therefore remain independent too. -/
theorem wots_coordinate_other (lay tree pair leaf : Nat) :
    (.inl (SigGolfCandidate.T3.header 0 lay tree pair leaf) : T3Coordinate) ≠ keyCoordinate 0 ∧
    (.inl (SigGolfCandidate.T3.header 0 lay tree pair leaf) : T3Coordinate) ≠ keyCoordinate 1 :=
  ⟨non_mac_tweak 0 lay tree pair leaf (by decide) 0,
   non_mac_tweak 0 lay tree pair leaf (by decide) 1⟩

theorem bpors_coordinate_other (coord index pair : Nat) :
    (.inl (SigGolfCandidate.T3.header 8 coord index 0 pair) : T3Coordinate) ≠ keyCoordinate 0 ∧
    (.inl (SigGolfCandidate.T3.header 8 coord index 0 pair) : T3Coordinate) ≠ keyCoordinate 1 :=
  ⟨non_mac_tweak 8 coord index 0 pair (by decide) 0,
   non_mac_tweak 8 coord index 0 pair (by decide) 1⟩

theorem nonce_coordinate_other (message : SigGolfCandidate.T3.Message) :
    (.inr (.inl message) : T3Coordinate) ≠ keyCoordinate 0 ∧
    (.inr (.inl message) : T3Coordinate) ≠ keyCoordinate 1 := by
  constructor <;> intro h <;> cases h

end SiggolfT3Mac4.Source
