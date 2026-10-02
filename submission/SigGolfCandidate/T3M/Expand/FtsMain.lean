import SigGolfCandidate.T3M.Expand.FtsCoord
import SigGolfCandidate.T3M.Expand.Wit

/-!
# `expand`: the FTS phase (stream E)

**`ftsSpec`**: `FtsSpec sk` for every key, i.e. from `FtsPre` (word 65 after `ds_done`) the machine refines Core's
`ftsFold` (the seven coordinates, `fts_coord_step`) within `ftsCost` cycles and ends in `FtsPost` (the roots in the
forest block, the secrets `leafBytes` and the honest stream `streamBytes` in the witness), or `FailedAt 354`.
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Signature Selection)
open SigGolfCandidate.T3M.Search (NODE NOUT SEL FailedAt)
open SphincsSecurity (bytesLE bytesLE_length)

set_option autoImplicit false

/-! ## The witness leaf blocks -/

theorem readWords_blocksN (t : MachineState) (m : Nat) : ∀ (bs : List (List Word)) (A : Nat),
    (∀ b ∈ bs, b.length = m) → (∀ k < bs.length, t.readWords (BitVec.ofNat 64 (A + 8 * m * k)) m = bs.getD k []) →
    t.readWords (BitVec.ofNat 64 A) (m * bs.length) = bs.flatten
  | [], _, _, _ => by simp
  | b :: bs, A, hl, h => by
    rw [List.length_cons, show m * (bs.length + 1) = m + m * bs.length by ring, readWords_add, List.flatten_cons]
    congr 1
    · simpa using h 0 (by simp)
    · refine readWords_blocksN t m bs (A + 8 * m) (fun x hx => hl x (by simp [hx])) (fun k hk => ?_)
      have := h (k + 1) (by simp; omega)
      rw [show A + 8 * m * (k + 1) = A + 8 * m + 8 * m * k by ring] at this
      simpa using this

/-- The six doublewords of witness leaf block `s`. -/
def leafBlk (d : Digest) : List Word := [0, 0, 0, 0, d.extractLsb' 0 64, d.extractLsb' 64 64]

theorem wordsOf_leafBytes (sig : Signature) :
    wordsOf (leafBytes sig) = ((List.finRange 21).map fun s => leafBlk (sig.secrets s)).flatten ++ [0, 0] := by
  unfold leafBytes
  rw [wordsOf_append _ _ (by
      rw [length_flatMap_const _ 48 (fun s => by simp [bytesLE_length, T3M.zeros])]; simp),
    wordsOf_flatMap8 _ (fun s => by simp [bytesLE_length, T3M.zeros]),
    flatMap_eq_flatten _ (fun s => leafBlk (sig.secrets s)) (fun s => by
      rw [wordsOf_append _ _ (by rfl), wordsOf_bytesLE16,
        show T3M.zeros 32 = List.replicate (8 * 4) 0 from rfl, wordsOf_replicate_zero]
      rfl)]
  rfl

/-- **The leaf blocks** from the secrets and zero doublewords. -/
theorem leaf_readWords (t : MachineState) (sig : Signature)
    (hsec : ∀ k (h : k < 21), DigAt t (0x860 + 48 * k) (sig.secrets ⟨k, h⟩))
    (hz : ∀ A, 0x840 ≤ A → A < 0xC40 → (∀ k < 21, A ≠ 0x860 + 48 * k ∧ A ≠ 0x860 + 48 * k + 8) →
      t.getMem (BitVec.ofNat 64 A) = 0) :
    t.readWords (BitVec.ofNat 64 0x840) 128 = wordsOf (leafBytes sig) := by
  rw [wordsOf_leafBytes, show (128 : Nat) = 6 * ((List.finRange 21).map fun s => leafBlk (sig.secrets s)).length + 2
    by simp, readWords_add]
  congr 1
  · refine readWords_blocksN t 6 _ 0x840 (fun b hb => ?_) (fun k hk => ?_)
    · simp only [List.mem_map] at hb
      obtain ⟨s, _, rfl⟩ := hb
      rfl
    · have hk' : k < 21 := by simpa using hk
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      simp only [List.getElem_map, List.getElem_finRange, Option.getD_some, Fin.cast_mk]
      have hs := hsec k hk'
      rw [readWords_map _ _ 6, show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl]
      simp only [List.map_cons, List.map_nil, leafBlk]
      rw [hz _ (by omega) (by omega) (fun k' _ => ⟨by omega, by omega⟩),
        hz _ (by omega) (by omega) (fun k' _ => ⟨by omega, by omega⟩),
        hz _ (by omega) (by omega) (fun k' _ => ⟨by omega, by omega⟩),
        hz _ (by omega) (by omega) (fun k' _ => ⟨by omega, by omega⟩),
        show 2112 + 8 * 6 * k + 8 * 4 = 0x860 + 48 * k by ring, hs.1,
        show 2112 + 8 * 6 * k + 8 * 5 = 0x860 + 48 * k + 8 by ring, hs.2]
  · simp only [List.length_map, List.length_finRange]
    rw [readWords_two, hz _ (by omega) (by omega) (fun k' _ => ⟨by omega, by omega⟩),
      hz _ (by omega) (by omega) (fun k' _ => ⟨by omega, by omega⟩)]

/-! ## The seven coordinates -/

theorem coordInv_zero {sig : Signature} {N : HashOutput} {s : MachineState} (hpre : FtsPre sig N s) :
    CoordInv s sig N 0 [] 0 s := by
  refine ⟨hpre.pc, hpre.x8, hpre.x18, ?_, hpre.x2, by omega, rfl, rfl, fun c' hc' => absurd hc' (by omega), ?_,
    fun k _ hk => absurd hk (by omega), fun A h1 h2 _ => hpre.wz A h1 (by omega), RegsExcept.refl _ _,
    Frame.refl _ _⟩
  · rw [hpre.x22]; rfl
  · intro k hk
    rw [hpre.wz _ (by omega) (by omega)]
    simp only [emAt, emSegs, List.range_zero, List.flatMap_nil, img, List.nil_append, List.append_nil]
    rcases k with _ | k <;> rfl

/-- **The FTS phase** (`fts_coord` .. `fts_done`): `FtsSpec` holds for every key. -/
theorem ftsSpec (sk : BitVec 256) : FtsSpec sk := by
  intro sig N s hpre
  have hC : ChosenOk (T3.selections N) := chosenOk_of N (selectionsOk_of_admissible N hpre.adm)
  have h7 : slotBase (T3.selections N) 7 ≤ 118 := slotBase_seven_le N hC hpre.adm
  have hbody : ∀ j < 7, ∀ (acc : Option (List Digest × Nat)) (u : MachineState),
      (match acc with
        | none => FailedAt 354 u
        | some (roots, used) => CoordInv s sig N j roots used u) →
      TBSim image sk u coordCost (ftsStep sig (N.toNat % 2 ^ 31) (T3.selections N) acc (0 + j))
        (fun acc' u' => match acc' with
          | none => FailedAt 354 u'
          | some (roots, used) => CoordInv s sig N (j + 1) roots used u') := by
    intro j hj acc u hu
    rcases acc with _ | ⟨roots, used⟩
    · exact (TBSim.pure (a := none) hu).mono (by omega) (fun _ _ h => h)
    · rw [Nat.zero_add]; exact fts_coord_step hpre hj hu
  have hfold := TBSim.foldlM_range' (image := image) (sk := sk) 0 7
    (ftsStep sig (N.toNat % 2 ^ 31) (T3.selections N)) (some ([], 0)) _ coordCost hbody (coordInv_zero hpre)
  unfold ftsFold
  rw [List.range_eq_range', ← bind_pure ((List.range' 0 7).foldlM _ _)]
  refine (TBSim.bind (W₂ := 2) hfold (fun st u hu => ?_)).mono (by unfold ftsCost coordCost; omega)
    (fun _ _ h => h)
  rcases st with _ | ⟨roots, used⟩
  · exact (TBSim.pure (Q := FtsPost s sig N) (a := none) hu).mono (by omega) (fun _ _ h => h)
  simp only [] at hu
  obtain ⟨u1, s1, p1, r1, f1⟩ := f65_spec u hu.pc 7 le_rfl hu.x8
  rw [if_pos le_rfl] at p1
  refine (TBSim.steps s1 (TBSim.pure ?_)).mono (by omega) (fun _ _ h => h)
  have hst : Stat sig N u := (stat_of_pre hpre).frame hu.regs (by decide) (by decide) hu.frame
    (fun A h => not_FtsW'_stat h)
  refine ⟨p1, by rw [r1.get (by decide)]; exact hst.x5, by rw [r1.get (by decide)]; exact hst.x9,
    by rw [r1.get (by decide)]; exact hu.x18, by rw [hu.hused]; exact h7, hu.hlen,
    fun c hc => (hu.roots c hc).frame f1 (by simp only [FOREST]; unfold slotOff; split_ifs <;> omega)
      (fun h => h) (fun h => h), ?_, ?_, (hu.regs.trans r1).mono (by decide), ?_⟩
  · have hS : ∀ k (h : k < 21), DigAt u1 (0x860 + 48 * k) (sig.secrets ⟨k, h⟩) := fun k h =>
      (hu.sec k h (by omega)).frame f1 (by omega) (fun h => h) (fun h => h)
    exact leaf_readWords u1 sig hS (fun A h1 h2 hA => by
      rw [f1.get (by omega) (fun h => h)]; exact hu.wz A h1 h2 hA)
  · exact stream_readWords _ _ hC h7 u1 0 (hu.stream.frame f1 (fun _ _ h => h))
  · refine (hu.frame.trans f1).mono (fun A _ h => ?_)
    rcases h with h | h
    · unfold FtsW' at h; unfold FtsW; simp only [FLEAF] at h ⊢; omega
    · exact h.elim

end SigGolfCandidate.T3M.Expand
