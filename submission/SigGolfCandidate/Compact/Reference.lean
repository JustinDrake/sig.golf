import SigGolfCandidate.Ref

/-!
# Counter reconstruction during expansion

The compact prefix contains the randomizer, PORS opening, and five layer bodies.
Expansion recovers each first successful encoding counter from public inputs,
starting with the PORS root and proceeding from layer four to layer zero.
This module specifies the proposed expansion; it is not yet connected to a RISC-V image
or to the competition certificate.
-/

namespace SigGolfCandidate.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

def signatureBytes : Nat := CounterPack.tailOffset

theorem signatureBytes_eq : signatureBytes = 6048 := by decide

/-- Recover counters in layer order, using the unchanged chain values and paths. -/
def recoverLayers (w : List Byte) (idx : Nat) :
    Nat → Val → OracleComp HashSpec (Option (List Nat))
  | 0, _ => pure (some [])
  | lay + 1, message => do
    let (e, tau) := route idx lay
    match ← searchCounter lay tau e message 0 cMax with
    | none => pure none
    | some (counter, digits) =>
      let leaf ← verifyLeaf w lay tau e digits
      let root ← foldPath (nodeInput lay tau) e leaf (witPath w lay)
      match ← recoverLayers w idx lay root with
      | none => pure none
      | some rest => pure (some (rest ++ [counter]))

/-- Construct a witness with zero counters to access its unchanged layer bodies. -/
def recoverTail (message shortSig : List Byte) : OracleComp HashSpec (Option (List Nat)) := do
  let padded := shortSig ++ zeros CounterPack.tailBytes
  let digest ← Ref.digest (sigRho padded) message
  match expandOf padded digest with
  | none => pure none
  | some witness =>
    match ← porsRoot (idxOf digest) (leavesOf digest) witness with
    | none => pure none
    | some root => recoverLayers witness (idxOf digest) nLayers root

/-- Reconstruct an old-format signature, retaining the entire submitted prefix. -/
def recoverList (message shortSig : List Byte) : OracleComp HashSpec (Option (List Byte)) :=
  (fun counters => counters.map (fun cs => shortSig ++ CounterPack.packTail cs)) <$>
    recoverTail message shortSig

/-- The new expansion composes reconstruction with the existing expander.
The second digest query is intentional: the security reduction can perform reconstruction
inside the adversary and leave the original final expansion unchanged, including its cost. -/
def expandList (message shortSig : List Byte) : OracleComp HashSpec (Option (List Byte)) := do
  match ← recoverList message shortSig with
  | none => pure none
  | some signature => Ref.expandList message signature

theorem recoverList_prefix (message shortSig signature : List Byte)
    (h : some signature ∈ support (recoverList message shortSig)) :
    signature.take shortSig.length = shortSig ∧
      signature.length = shortSig.length + CounterPack.tailBytes := by
  simp only [recoverList, support_map] at h
  obtain ⟨result, _, hr⟩ := h
  cases result with
  | none => simp at hr
  | some counters =>
    simp only [Option.map_some, Option.some.injEq] at hr
    subst signature
    simp [CounterPack.length_packTail]

theorem recoverList_sizes (message : List Byte) (shortSig : Bytes 6048)
    (signature : List Byte)
    (h : some signature ∈ support (recoverList message (toList shortSig))) :
    signature.take 6048 = toList shortSig ∧ signature.length = 6062 := by
  have hp := recoverList_prefix message (toList shortSig) signature h
  rw [length_toList] at hp
  exact hp

/-- Projection preserves the freshness needed for signature strong unforgeability.
This is a transcript lemma, not the security reduction for the proposed scheme. -/
theorem recoverList_fresh (log : List (List Byte × List Byte))
    (message : List Byte) (shortSig : Bytes 6048) (signature : List Byte)
    (h : some signature ∈ support (recoverList message (toList shortSig)))
    (hfresh : (message, toList shortSig) ∉
      log.map (fun entry => (entry.1, entry.2.take 6048))) :
    (message, signature) ∉ log := by
  intro hmem
  apply hfresh
  refine List.mem_map.mpr ⟨(message, signature), hmem, ?_⟩
  have hp := (recoverList_sizes message shortSig signature h).1
  exact congrArg (fun s : List Byte => (message, s)) hp

end SigGolfCandidate.Compact
