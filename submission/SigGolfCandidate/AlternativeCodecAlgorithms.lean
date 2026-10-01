import SigGolfCandidate.AlternativeVerifyAlgorithms

set_option profiler true
set_option profiler.threshold 1000
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace SigGolfCandidate.Base4Candidate.Reference
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal
open SigGolfCandidate.Ref (Val zeros byte le32 slice answerBytes)

def serialize (sig : Signature) : List Byte :=
  sig.randomness ++ (sig.forest.map fun op => op.secret ++ op.siblings.flatten).flatten ++
    (sig.layers.map fun op => op.values.flatten ++ op.siblings.flatten).flatten

/-- Compact layer offsets; the signature never transmits search counters. -/
def layerOffset (lay : Nat) : Nat := [2736, 3920, 5024, 6128].getD lay 0

def parseForest (bs : List Byte) : List Opening :=
  (List.range 17).map fun tree =>
    ⟨slice bs (16 + 160 * tree) 16,
      (List.range 9).map fun level => slice bs (32 + 160 * tree + 16 * level) 16⟩

def parse (bs : List Byte) : Option Signature :=
  if bs.length = 7232 then
    some ⟨slice bs 0 16, parseForest bs,
      (List.range 4).map fun lay =>
        ⟨(List.range 62).map (fun i => slice bs (layerOffset lay + 16 * i) 16),
          (List.range (height lay)).map
            (fun level => slice bs (layerOffset lay + 992 + 16 * level) 16)⟩⟩
  else none

/-- Witness: forest initialPart, four counters, all paths, 48 spare bytes, then 248
in-place chain blocks. The 19200-byte witness costs 75 cycles. -/
def witnessPathOffset (lay : Nat) : Nat := [2752, 2944, 3056, 3168].getD lay 0
def witnessChainOffset (lay i : Nat) : Nat := 3328 + 64 * (62 * lay + i)

def serializeWitness (w : Witness) : List Byte :=
  w.signature.randomness ++
    (w.signature.forest.map fun op => op.secret ++ op.siblings.flatten).flatten ++
    (w.counters.map le32).flatten ++
    (w.signature.layers.map fun op => op.siblings.flatten).flatten ++ zeros 48 ++
    ((List.range 4).map fun lay =>
      ((List.range 62).map fun i =>
        zeros 16 ++ w.padding.getD (62 * lay + i) (zeros 32) ++
          (w.signature.layers.getD lay default).values.getD i []).flatten).flatten

def parseWitness (bs : List Byte) : Option Witness :=
  if bs.length = 19200 then
    some ⟨⟨slice bs 0 16, parseForest bs,
      (List.range 4).map fun lay =>
        ⟨(List.range 62).map
            (fun i => slice bs (witnessChainOffset lay i + 48) 16),
          (List.range (height lay)).map
            (fun level => slice bs (witnessPathOffset lay + 16 * level) 16)⟩⟩,
      (List.range 4).map (fun lay => SigGolfCandidate.Ref.leNat (slice bs (2736 + 4 * lay) 4)),
      ((List.range 4).map fun lay =>
        (List.range 62).map fun i => slice bs (witnessChainOffset lay i + 16) 32).flatten⟩
  else none

def signBytes (sk cache m : List Byte) : OracleComp HashSpec (Option (List Byte)) := do
  let sig ← sign sk cache m
  pure (sig.map serialize)

def expandBytes (pk m sigBytes : List Byte) : OracleComp HashSpec (Option (List Byte)) := do
  match parse sigBytes with
  | none => pure none
  | some sig =>
    let w ← expand pk m sig
    pure (w.map serializeWitness)

def verifyBytes (pk m witnessBytes : List Byte) : OracleComp HashSpec Bool :=
  match parseWitness witnessBytes with
  | none => pure false
  | some w => verify pk m w

/-! These are search-tail arithmetic lemmas. The adaptive random-oracle proof
must supply their rejection-share premises; independence is not assumed here. -/
theorem digest_tail_arithmetic (x : ENNReal)
    (hx : x + (4097 : ENNReal)⁻¹ ≤ 1) :
    x ^ (2 ^ 21) ≤ (2⁻¹ : ENNReal) ^ 511 := by
  have hx1 : x ≤ 1 := le_trans le_self_add hx
  have hh := SphincsSecurity.Completeness.pow_le_half_ennreal 4097 (by decide) x hx
  calc
    x ^ (2 ^ 21) ≤ x ^ (4097 * 511) :=
      pow_le_pow_right_of_le_one' hx1 (by decide)
    _ = (x ^ 4097) ^ 511 := by rw [pow_mul]
    _ ≤ (2⁻¹ : ENNReal) ^ 511 := pow_le_pow_left' hh _

theorem counter_tail_arithmetic (x : ENNReal)
    (hx : x + (2268 : ENNReal)⁻¹ ≤ 1) :
    x ^ (2 ^ 22) ≤ (2⁻¹ : ENNReal) ^ 1024 := by
  have hx1 : x ≤ 1 := le_trans le_self_add hx
  have hh := SphincsSecurity.Completeness.pow_le_half_ennreal 2268 (by decide) x hx
  calc
    x ^ (2 ^ 22) ≤ x ^ (2268 * 1024) :=
      pow_le_pow_right_of_le_one' hx1 (by decide)
    _ = (x ^ 2268) ^ 1024 := by rw [pow_mul]
    _ ≤ (2⁻¹ : ENNReal) ^ 1024 := pow_le_pow_left' hh _

/-- The proposed finite searches leave room for a union over every message. -/
theorem all_message_tail_arithmetic :
    (2 : ENNReal) ^ 256 * ((2⁻¹ : ENNReal) ^ 511 +
      4 * (2⁻¹ : ENNReal) ^ 1024) ≤ ((2 : ENNReal) ^ 128)⁻¹ := by
  rw [← ENNReal.inv_pow, ← ENNReal.inv_pow]
  norm_num

end SigGolfCandidate.Base4Candidate.Reference
