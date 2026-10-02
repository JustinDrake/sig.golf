import SigGolfCandidate.T3M.Sign.Layers
import SigGolfCandidate.T3M.Sign.FtsCoord

/-!
# Sign: `payloadRest` (FTS, forest pk, layers) refines Core

From `ds_done` (172, `AfterDs`): the seven FTS coordinates (`fts_entry`, `fts_fold`), the forest pk (357..369:
the header, one 2-block `shortHash`), the layer-3 setup (370..395), the layers (`layers_tbsim`). On success the
machine halts with the 364 digests of Core's signature at `SIG` (`PayPost`): `rho`, the opened secrets and the
proof slots (unused slots stay zero) from the FTS phase, the layer pieces from the layers.
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest HashOutput Pieces Signature Cache signLayers forestPk piecesSignature selections
  admissible height chainCount header pad64 shortHash)
open SigGolfCandidate.T3M (chosenOk_of selectionsOk_of_admissible slotBase_seven_le slotBase ChosenOk)
open SphincsSecurity (bytesLE bytesLE_length)

/-! ## Core -/

theorem payloadRest_eq (cache : Cache) (rho : Digest) (N : HashOutput) :
    payloadRest cache rho N = (do
      let state ← (List.range 7).foldlM (ftsBody (selections N) (N.toNat % 2 ^ 31)) ([], [], [])
      let root ← forestPk (N.toNat % 2 ^ 31) state.2.2
      let some layers ← signLayers cache (N.toNat % 2 ^ 31) 4 root | pure none
      pure (some ⟨rho, fun i => state.1.getD i.val 0, fun i => state.2.1.getD i.val 0,
        fun lay => piecesSignature lay (layers.getD lay.val ([], []))⟩)) := rfl

/-- The forest-pk input `root0 | T11 | root1 .. root6` (128 bytes, no padding). -/
def forestIn (index : Nat) (roots : List Digest) : List UInt8 :=
  bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 11 0 index 0 0) ++ (roots.drop 1).flatMap (bytesLE 16)

theorem forestIn_length (index : Nat) {roots : List Digest} (hlen : roots.length = 7) :
    (forestIn index roots).length = 128 := by
  have hfl : ((roots.drop 1).flatMap (bytesLE 16)).length = 96 := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen]
  simp only [forestIn, List.length_append, bytesLE_length, hfl]

theorem forestIn_words (index : Nat) {roots : List Digest} (hlen : roots.length = 7) :
    wordsOf (pad64 (forestIn index roots)) =
      wordsOf (bytesLE 16 (roots.getD 0 0)) ++
        [BitVec.ofNat 64 (hdr0 11 0 index 0), BitVec.ofNat 64 (hdr1 index 0)] ++
        wordsOf ((roots.drop 1).flatMap (bytesLE 16)) := by
  rw [pad64_of_aligned _ (by rw [forestIn_length index hlen])]
  unfold forestIn
  rw [wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_header]
  rfl

/-! ## The signature -/

/-- `PayPost` from the digests at their places. -/
theorem payPost_of {w : MachineState} {sig : Signature} (hh : Halted0 w) (hrho : DigAt w SIG sig.rho)
    (hsec : ∀ i (hi : i < 21), DigAt w (SIG + 16 + 16 * i) (sig.secrets ⟨i, hi⟩))
    (hpr : ∀ j (hj : j < 124), DigAt w (SIG + 352 + 16 * j) (sig.proof ⟨j, hj⟩))
    (hval : ∀ (lay : Layer) i (hi : i < chainCount lay),
      DigAt w (SIG + 16 * (layIdx lay + i)) ((sig.layers lay).values ⟨i, hi⟩))
    (hpath : ∀ (lay : Layer) j (hj : j < height lay),
      DigAt w (SIG + 16 * (layIdx lay + chainCount lay + j)) ((sig.layers lay).path ⟨j, hj⟩)) :
    PayPost (some sig) w := by
  refine ⟨hh, fun k hk => ?_⟩
  have hlayer : ∀ lay : Layer, layIdx lay ≤ k → k < layIdx lay + chainCount lay + height lay →
      DigAt w (SIG + 16 * k) ((sigDigests sig).getD k 0) := fun lay h1 h2 => by
    by_cases hv : k < layIdx lay + chainCount lay
    · have e := sigDigests_value sig lay (k - layIdx lay) (by omega)
      rw [show layIdx lay + (k - layIdx lay) = k by omega] at e
      rw [e]
      have := hval lay (k - layIdx lay) (by omega)
      rwa [show layIdx lay + (k - layIdx lay) = k by omega] at this
    · have e := sigDigests_path sig lay (k - layIdx lay - chainCount lay) (by omega)
      rw [show layIdx lay + (chainCount lay + (k - layIdx lay - chainCount lay)) = k by omega] at e
      rw [e]
      have := hpath lay (k - layIdx lay - chainCount lay) (by omega)
      rwa [show layIdx lay + chainCount lay + (k - layIdx lay - chainCount lay) = k by omega] at this
  have i0 : layIdx 0 = 146 := rfl
  have i1 : layIdx 1 = 216 := rfl
  have i2 : layIdx 2 = 266 := rfl
  have i3 : layIdx 3 = 315 := rfl
  have c0 : chainCount 0 = 58 := rfl
  have c1 : chainCount 1 = 43 := rfl
  have c2 : chainCount 2 = 43 := rfl
  have c3 : chainCount 3 = 43 := rfl
  have e0 : height 0 = 12 := rfl
  have e1 : height 1 = 7 := rfl
  have e2 : height 2 = 6 := rfl
  have e3 : height 3 = 6 := rfl
  rcases Nat.lt_or_ge k 1 with h0 | h0
  · obtain rfl : k = 0 := by omega
    rw [sigDigests_rho]
    simpa using hrho
  rcases Nat.lt_or_ge k 22 with h1 | h1
  · have e := sigDigests_secret sig (k - 1) (by omega)
    rw [show 1 + (k - 1) = k by omega] at e
    rw [e]
    have := hsec (k - 1) (by omega)
    rwa [show SIG + 16 + 16 * (k - 1) = SIG + 16 * k by omega] at this
  rcases Nat.lt_or_ge k 146 with h2 | h2
  · have e := sigDigests_proof sig (k - 22) (by omega)
    rw [show 22 + (k - 22) = k by omega] at e
    rw [e]
    have := hpr (k - 22) (by omega)
    rwa [show SIG + 352 + 16 * (k - 22) = SIG + 16 * k by omega] at this
  rcases Nat.lt_or_ge k 216 with h3 | h3
  · exact hlayer 0 (by omega) (by omega)
  rcases Nat.lt_or_ge k 266 with h4 | h4
  · exact hlayer 1 (by omega) (by omega)
  rcases Nat.lt_or_ge k 315 with h5 | h5
  · exact hlayer 2 (by omega) (by omega)
  · exact hlayer 3 (by omega) (by omega)

/-! ## `payloadRest` -/

/-- Cycles of `payloadRest` from `ds_done`. -/
def midC : Nat := 14 + (7 * ftsCoordC + (2 + (12 + (8 * 2 + (26 + layersC)))))

section payload
variable {sk : SecretKey} {cache : Bytes 32768}

/-- **`payloadRest`**: from `ds_done` the machine refines Core's `payloadRest` within `midC` cycles and ends in
`PayPost`. -/
theorem payloadRest_tbsim (hK : CounterSearchSpec sk) (hL0 : L0Spec sk cache) {m : Message} {rho : Digest}
    {N : HashOutput} {t : MachineState} (h : AfterDs sk cache m rho N t) :
    TBSim image sk t midC (payloadRest (cacheDec cache) rho N) PayPost := by
  obtain ⟨s0, st0, hci, hidxv, -, f0⟩ := fts_entry h
  have hadm := h.adm
  have hchosen : ChosenOk (selections N) := chosenOk_of N (selectionsOk_of_admissible N hadm)
  have hsb7 : slotBase (selections N) 7 ≤ 124 := slotBase_seven_le N hchosen hadm
  have hSIG : SIG = 28672 := rfl
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  rw [payloadRest_eq]
  refine TBSim.steps st0 (TBSim.bind (W₂ := 2 + (12 + (8 * 2 + (26 + layersC)))) (fts_fold hadm hci)
    (fun st u hu => ?_))
  -- the coordinate loop exits, the forest header
  obtain ⟨u1, st1, u1pc, u1r, u1f⟩ := blk186_spec u hu.pc 7 (by norm_num) hu.x8
  rw [if_neg (by norm_num)] at u1pc
  obtain ⟨u2, st2, u2pc, u2x10, u2x11, u2x12, u2m16, u2m24, u2r, u2f⟩ := blk357_spec u1 u1pc _
    (by rw [u1r.get (by simp)]; exact hu.x9)
  have f12 : Frame u u2 (fun A => A = FOREST + 16 ∨ A = FOREST + 24) := (u1f.trans u2f).mono (fun A _ h => by
    rcases h with h | h
    · exact h.elim
    · exact h)
  have hx5 : u2.getReg .x5 = 0 := by rw [u2r.get (by decide), u1r.get (by decide), hu.base.x5]
  have hlen7 : st.2.2.length = 7 := hu.len3
  have hl1 : st.1.length = 3 * 7 := hu.len1
  have hl2 : st.2.1.length = slotBase (selections N) 7 := hu.len2
  have hroots : ∀ j < 7, DigAt u2 (FOREST + rootOff j) (st.2.2.getD j 0) := fun j hj =>
    (hu.roots j hj).frame f12 (by unfold rootOff; split_ifs <;> sgo)
      (by unfold rootOff; split_ifs <;> sgo) (by unfold rootOff; split_ifs <;> sgo)
  have hv : hashArgumentsValid u2 = true :=
    hashArgs_const u2 FOREST 128 FOUT u2x10 u2x11 u2x12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hq : hashInput u2 = toQ (pad64 (forestIn (N.toNat % 2 ^ 31) st.2.2)) := by
    refine hashInput_toQ u2 _ 1 FOREST (by rw [pad64_of_aligned _ (by rw [forestIn_length _ hlen7]),
      forestIn_length _ hlen7]) u2x10 (by decide) (by decide) u2x11 (by decide) ?_
    have h0 : DigAt u2 FOREST (st.2.2.getD 0 0) := by simpa [rootOff] using hroots 0 (by decide)
    have hd : DigsAt u2 (FOREST + 32) (st.2.2.drop 1) := fun i hi => by
      rw [List.length_drop, hlen7] at hi
      have := hroots (i + 1) (by omega)
      rw [show FOREST + rootOff (i + 1) = FOREST + 32 + 16 * i by unfold rootOff; rw [if_neg (by omega)]; ring]
        at this
      simpa [List.getD_eq_getElem?_getD] using this
    have hw := hd.words
    rw [List.length_drop, hlen7] at hw
    rw [forestIn_words _ hlen7, show 8 * (1 + 1) = 2 + (2 + 2 * (7 - 1)) from rfl, readWords_add, readWords_add,
      h0.words, show FOREST + 8 * 2 = FOREST + 16 from rfl, readWords_two, u2m16,
      show FOREST + 16 + 8 = FOREST + 24 from rfl, u2m24, show FOREST + 16 + 8 * 2 = FOREST + 32 from rfl, hw]
    have e0 : hdr0 11 0 (N.toNat % 2 ^ 31) 0 = 2817 := by
      simp [hdr0]; omega
    have e1 : hdr1 (N.toNat % 2 ^ 31) 0 = N.toNat % 2 ^ 31 := by
      unfold hdr1; omega
    rw [e0, e1]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hblk : (toQ (pad64 (forestIn (N.toNat % 2 ^ 31) st.2.2))).blocks = 2 := by
    rw [pad64_of_aligned _ (by rw [forestIn_length _ hlen7]), blocks_toQ ⟨by rw [forestIn_length _ hlen7]; omega,
      by rw [forestIn_length _ hlen7]⟩, forestIn_length _ hlen7]
  refine TBSim.steps st1 (TBSim.steps st2 (TBSim.of_eq (TBSim.shortHash_bind (W := 26 + layersC)
    (fetch_369 u2 u2pc) hx5 hv hq (fun a => ?_)) rfl (by rw [hblk])))
  -- the forest pk to `ENC`, layer 3's setup
  have hwf := Frame.writeHash u2 a FOUT u2x12 (by decide)
  have hfo := DigAt.writeHash_lo u2 a FOUT u2x12 (by decide)
  have hidxu : u.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 (N.toNat % 2 ^ 31) := by
    rw [hu.frame.get (by sgo) (by unfold CoordW FtsScr FlW; sgo)]; exact hidxv
  obtain ⟨t3, st3, t3pc, t3x1, t3m0, t3m8, t3x2, t3x31, t3x26, t3x27, t3x8, t3x15, t3x16, t3x17, t3x18, t3x14,
    t3x9, t3r, t3f⟩ := blk370_spec (writeHash u2 a) (by rw [pc_writeHash, u2pc, pcOf_add4]) _ hidx
      (by rw [hwf.get (by sgo) (by sgo), f12.get (by sgo) (by sgo)]; exact hidxu)
  have fu3 : Frame u t3 (fun A => (A = FOREST + 16 ∨ A = FOREST + 24) ∨ (FOUT ≤ A ∧ A < FOUT + 32) ∨
      A = ENC ∨ A = ENC + 8) := ((f12.trans hwf).trans t3f).mono (fun A _ h => by
    rcases h with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h))
  have hr3 : RegsExcept u t3 ([.x6] ++ [.x6, .x7, .x10, .x11, .x12, .x28] ++ [] ++
      [.x1, .x2, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x26, .x27, .x28, .x29, .x30, .x31]) :=
    ((u1r.trans u2r).trans (fun r _ => getReg_writeHash u2 a r)).trans t3r
  have hentry : LayEntry sk cache 3 (N.toNat % 2 ^ 31) (a.extractLsb' 0 128) t3 :=
    { pc := t3pc
      x1 := t3x1
      x2 := t3x2
      x8 := t3x8
      x9 := by rw [t3x9, route_3]
      x14 := by rw [t3x14, route_3]
      x15 := t3x15
      x16 := t3x16
      x17 := t3x17
      x18 := by rw [t3x18, route_3]
      x26 := t3x26
      x27 := t3x27
      x31 := t3x31
      base := hu.base.frame fu3 hr3 (by decide) (fun A _ hb hw => by
        unfold BaseA NeverW at hb
        sgo)
      hlay := by decide
      hidx := hidx
      idx := by rw [fu3.get (by sgo) (by sgo)]; exact hidxu
      enc := ⟨by rw [t3m0]; exact hfo.1, by rw [t3m8]; exact hfo.2⟩
      c32 := by
        rw [fu3.get (by sgo) (by sgo), hu.frame.get (by sgo) (by unfold CoordW FtsScr FlW; sgo),
          f0.get (by sgo) (by sgo), h.frame.get (by sgo) (by unfold FrontW; sgo),
          sinit_zero sk cache m _ (by sgo) (by sgo)]
        decide }
  refine TBSim.steps st3 (TBSim.bind (W₂ := 0) (layers_tbsim hK hL0 hentry) (fun r w hw => ?_))
  rcases r with _ | layers
  · exact TBSim.pure hw
  obtain ⟨wh, -, wpieces, wf⟩ := hw
  -- the FTS part of the signature survives the forest and the layers
  have fuw : Frame u w (fun A => ((A = FOREST + 16 ∨ A = FOREST + 24) ∨ (FOUT ≤ A ∧ A < FOUT + 32) ∨
      A = ENC ∨ A = ENC + 8) ∨ LayW 4 A) := fu3.trans wf
  have nW : ∀ A, SIG ≤ A → A < SIG + 2336 → ¬ (((A = FOREST + 16 ∨ A = FOREST + 24) ∨
      (FOUT ≤ A ∧ A < FOUT + 32) ∨ A = ENC ∨ A = ENC + 8) ∨ LayW 4 A) := fun A h1 h2 hA => by
    rcases hA with hA | hA
    · sgo
    · exact hA.1 ⟨h1, h2⟩
  have keep : ∀ A d, SIG ≤ A → A + 16 ≤ SIG + 2336 → DigAt u A d → DigAt w A d := fun A d h1 h2 hd =>
    hd.frame fuw (by sgo) (nW _ h1 (by omega)) (nW _ (by omega) (by omega))
  refine TBSim.pure (payPost_of wh ?_ (fun i hi => ?_) (fun j hj => ?_) (fun lay i hi => (wpieces lay lay.isLt).1 i hi)
    (fun lay j hj => (wpieces lay lay.isLt).2 j hj))
  · -- rho
    refine keep _ _ le_rfl (by sgo) ?_
    have := h.rho.frame f0 (by sgo) (by sgo) (by sgo)
    exact this.frame hu.frame (by sgo) (by unfold CoordW FtsScr FlW; sgo) (by unfold CoordW FtsScr FlW; sgo)
  · -- the opened secrets
    refine keep _ _ (by omega) (by omega) ?_
    exact hu.opened i (by rw [hu.len1]; exact hi)
  · -- the proof slots: Core's proof values, zero beyond them
    refine keep _ _ (by omega) (by omega) ?_
    by_cases hjl : j < st.2.1.length
    · exact hu.proofs j hjl
    · show DigAt u (SIG + 352 + 16 * j) (st.2.1.getD j 0)
      rw [List.getD_eq_default _ _ (by omega)]
      have z : ∀ A, SIG + 352 + 16 * st.2.1.length ≤ A → A < SIG + 2336 → u.getMem (BitVec.ofNat 64 A) = 0 :=
        fun A h1 h2 => by
          rw [hu.frame.get (by sgo) (by unfold CoordW FtsScr FlW; sgo), f0.get (by sgo) (by sgo),
            h.frame.get (by sgo) (by unfold FrontW; sgo), sinit_zero sk cache m _ (by sgo) (by sgo)]
      exact ⟨by rw [z _ (by omega) (by omega)]; rfl, by rw [z _ (by omega) (by omega)]; rfl⟩

end payload

end SigGolfCandidate.T3M.Sign
