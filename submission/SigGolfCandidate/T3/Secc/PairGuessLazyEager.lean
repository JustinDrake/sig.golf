import SigGolfCandidate.T3.Secc.PairGuessLazyGhost

/-!
# B-PAIR (CC-2, 6/7): eager → lazy

* `eager_lazy`: averaging the eager environment `envE D Nn` over uniform tables `D`, `Nn` gives the lazy
  environment `envL`, for any lazy-world program, slot and start state (a fresh row/nonce is a fresh uniform draw:
  `uniform_update`; the run ignores the table at cached rows: `forced_congr`);
* `forced_avg_law` / `forced_avg_eq_lazy`: under `omegaLaw`, `ω`'s own digest rows and nonce halves are such
  uniform tables independent of the rest of `ω` (`omegaLaw_patch`), and `worldGameL ω` reads only the rest
  (`worldGameL_congr`), so the `ω`-averaged eager forced world is the `ω`-averaged lazy forced world.
-/

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## Uniform tables -/

section Uniform

theorem evalSPMF_uniform {X : Type} [Fintype X] [Nonempty X] (I : SampleableType X) :
    𝒮[(@uniformSample X I : ProbComp X)] = (liftM (PMF.uniformOfFintype X) : SPMF X) := by
  apply SPMF.ext
  intro x
  rw [SPMF.liftM_apply, PMF.uniformOfFintype_apply, ← SPMF.probOutput_eq_apply, probOutput_evalSPMF]
  exact @probOutput_uniformSample X I _ x

/-- **Re-sampling one coordinate** of a uniform table: if `g a` ignores the table at `i`, reading `T i` is a fresh
uniform draw. -/
theorem uniform_update {ι β γ : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β] (i : ι)
    (g : β → (ι → β) → SPMF γ) (hg : ∀ a T c, g a (Function.update T i c) = g a T) :
    ((liftM (PMF.uniformOfFintype (ι → β)) : SPMF (ι → β)) >>= fun T => g (T i) T) =
      ((liftM (PMF.uniformOfFintype β) : SPMF β) >>= fun a =>
        (liftM (PMF.uniformOfFintype (ι → β)) : SPMF (ι → β)) >>= fun T => g a T) := by
  let IT : SampleableType (ι → β) := SampleableType.ofFintype _
  let Ia : SampleableType β := SampleableType.ofFintype _
  let IP : SampleableType ((ι → β) × β) := SampleableType.ofFintype _
  let f : (ι → β) × β → (ι → β) × β := fun p => (Function.update p.1 i p.2, p.1 i)
  have hinv : ∀ p, f (f p) = p := by
    rintro ⟨T, a⟩
    simp only [f, Function.update_self, Function.update_idem, Function.update_eq_self]
  have hf : Function.Bijective f := ⟨fun p q h => by rw [← hinv p, ← hinv q, h], fun p => ⟨f p, hinv p⟩⟩
  have hb := @evalSPMF_map_bijective_uniform_cross ((ι → β) × β) IP ((ι → β) × β) IP _ f hf
  have hp := @FullGame.uniform_product (ι → β) β _ _ IT Ia IP
  rw [← evalSPMF_uniform IT, ← evalSPMF_uniform Ia]
  calc (𝒮[(@uniformSample _ IT : ProbComp (ι → β))] >>= fun T => g (T i) T)
      = (𝒮[(@uniformSample _ IT : ProbComp (ι → β))] >>= fun T =>
          𝒮[(@uniformSample _ Ia : ProbComp β)] >>= fun _ => g (T i) T) := by
        simp only [evalSPMF_uniform Ia, RetainedObservation.lift_bind_const]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (ι → β)) >>= fun T => (@uniformSample _ Ia : ProbComp β) >>= fun a =>
          pure (T, a)] >>= fun p => g (p.1 i) p.1) := by
        simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((ι → β) × β))] >>= fun p => g (p.1 i) p.1) := by rw [hp]
    _ = (𝒮[f <$> (@uniformSample _ IP : ProbComp ((ι → β) × β))] >>= fun p => g (p.1 i) p.1) := by rw [hb]
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((ι → β) × β))] >>= fun p => g p.2 (Function.update p.1 i p.2)) := by
        rw [evalSPMF_map, bind_map_left]
        simp only [f, Function.update_self]
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((ι → β) × β))] >>= fun p => g p.2 p.1) := by simp only [hg]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (ι → β)) >>= fun T => (@uniformSample _ Ia : ProbComp β) >>= fun a =>
          pure (T, a)] >>= fun p => g p.2 p.1) := by rw [hp]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (ι → β))] >>= fun T =>
          𝒮[(@uniformSample _ Ia : ProbComp β)] >>= fun a => g a T) := by
        simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
    _ = _ := RetainedObservation.bind_comm _ _ _

/-- `T` with the coordinates `e s` overwritten by `D s`. -/
noncomputable def patch {α σ β : Type} (e : σ → α) (T : α → β) (D : σ → β) (a : α) : β :=
  @dite _ (∃ s, e s = a) (Classical.propDecidable _) (fun h => D (Classical.choose h)) (fun _ => T a)

theorem patch_e {α σ β : Type} {e : σ → α} (he : Function.Injective e) (T : α → β) (D : σ → β) (s : σ) :
    patch e T D (e s) = D s := by
  have h : ∃ s', e s' = e s := ⟨s, rfl⟩
  rw [patch, dif_pos h]
  exact congrArg D (he (Classical.choose_spec h))

theorem patch_of {α σ β : Type} (e : σ → α) (T : α → β) (D : σ → β) (a : α) (ha : ∀ s, e s ≠ a) :
    patch e T D a = T a := by
  rw [patch, dif_neg (fun h => ha _ (Classical.choose_spec h))]

/-- **Patching a uniform table** at an injective family of coordinates with an independent uniform table leaves it
uniform. -/
theorem patch_uniform {α σ β γ : Type} [Fintype α] [Fintype σ] [Fintype β] [Nonempty β] [DecidableEq α]
    [DecidableEq σ] {e : σ → α} (he : Function.Injective e) (IT : SampleableType (α → β))
    (ID : SampleableType (σ → β)) (k : (α → β) → SPMF γ) :
    (𝒮[(@uniformSample _ IT : ProbComp (α → β))] >>= fun T => 𝒮[(@uniformSample _ ID : ProbComp (σ → β))] >>=
      fun D => k (patch e T D)) = 𝒮[(@uniformSample _ IT : ProbComp (α → β))] >>= k := by
  let IP : SampleableType ((α → β) × (σ → β)) := SampleableType.ofFintype _
  let Φ : (α → β) × (σ → β) → (α → β) × (σ → β) := fun p => (patch e p.1 p.2, p.1 ∘ e)
  have hinv : ∀ p, Φ (Φ p) = p := by
    rintro ⟨T, D⟩
    refine Prod.ext (funext fun a => ?_) (funext fun s => ?_)
    · change patch e (patch e T D) (T ∘ e) a = T a
      by_cases h : ∃ s, e s = a
      · obtain ⟨s, rfl⟩ := h
        rw [patch_e he]
        rfl
      · have h' : ∀ s, e s ≠ a := fun s hs => h ⟨s, hs⟩
        rw [patch_of e _ _ a h', patch_of e _ _ a h']
    · exact patch_e he T D s
  have hΦ : Function.Bijective Φ := ⟨fun p q h => by rw [← hinv p, ← hinv q, h], fun p => ⟨Φ p, hinv p⟩⟩
  have hb := @evalSPMF_map_bijective_uniform_cross ((α → β) × (σ → β)) IP ((α → β) × (σ → β)) IP _ Φ hΦ
  have hp := @FullGame.uniform_product (α → β) (σ → β) _ _ IT ID IP
  calc _ = (𝒮[(@uniformSample _ IT : ProbComp (α → β)) >>= fun T => (@uniformSample _ ID : ProbComp (σ → β)) >>= fun D =>
          pure (T, D)] >>= fun p => k (Φ p).1) := by
        simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
        rfl
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((α → β) × (σ → β)))] >>= fun p => k (Φ p).1) := by rw [hp]
    _ = (𝒮[Φ <$> (@uniformSample _ IP : ProbComp ((α → β) × (σ → β)))] >>= fun p => k p.1) := by
        rw [evalSPMF_map, bind_map_left]
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((α → β) × (σ → β)))] >>= fun p => k p.1) := by rw [hb]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (α → β)) >>= fun T => (@uniformSample _ ID : ProbComp (σ → β)) >>= fun D =>
          pure (T, D)] >>= fun p => k p.1) := by rw [hp]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (α → β))] >>= fun T =>
          𝒮[(@uniformSample _ ID : ProbComp (σ → β))] >>= fun _ => k T) := by
        simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
    _ = _ := by simp only [evalSPMF_uniform ID, RetainedObservation.lift_bind_const]

end Uniform

/-! ## The digest rows and nonce halves of `ω` are independent uniform tables -/

/-- The sampler of digest-row tables. -/
noncomputable instance instSampleableDigestRows : SampleableType (digestInputs → HashOutput) :=
  SampleableType.ofFintype _

/-- The sampler of nonce tables. -/
noncomputable instance instSampleableNonceTables : SampleableType (Message → Digest) := SampleableType.ofFintype _

section OmegaPatch
variable {U : Finset HashInput} (hsub : digestInputs ⊆ U)

/-- The digest rows inside `U`. -/
def digestEmb : digestInputs → U := fun x => ⟨x.1, hsub x.2⟩

theorem digestEmb_injective : Function.Injective (digestEmb hsub) :=
  fun x y h => Subtype.ext (by have h' := congrArg Subtype.val h; exact h')

theorem nonceOther_injective : Function.Injective nonceOther := by
  intro m m' h
  have h1 := congrArg (fun o : CanonGraph.OtherHalf => o.1.1) h
  change (Sum.inr (Sum.inl m) : Coordinate) = Sum.inr (Sum.inl m') at h1
  exact Sum.inl.inj (Sum.inr.inj h1)

/-- `ω` with its digest rows replaced by `D` and its nonce halves by `Nn`. -/
noncomputable def patchOmega (ω : Omega U) (D : digestInputs → HashOutput) (Nn : Message → Digest) : Omega U :=
  ⟨ω.seeds, patch nonceOther ω.other Nn, ω.labels, patch (digestEmb hsub) ω.residual D⟩

theorem digestOf_patch (ω : Omega U) (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    digestOf (patchOmega hsub ω D Nn) = D := by
  funext x
  change finiteHashAnswer ∅ U (patch (digestEmb hsub) ω.residual D) x.1 = D x
  rw [finiteHashAnswer_none ∅ U _ _ (hsub x.2) rfl]
  exact patch_e (digestEmb_injective hsub) _ _ x

theorem nonceOf_patch (ω : Omega U) (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    nonceOf (patchOmega hsub ω D Nn) = Nn :=
  funext fun m => patch_e nonceOther_injective ω.other Nn m

theorem sameRest_patch (ω : Omega U) (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    SameRest ω (patchOmega hsub ω D Nn) := by
  refine ⟨rfl, rfl, fun x hx => (patch_of (digestEmb hsub) ω.residual D x ?_).symm,
    fun h hh => (patch_of nonceOther ω.other Nn h ?_).symm⟩
  · intro y hy
    apply hx
    rw [← hy]
    exact y.2
  · intro m hm
    exact hh m hm.symm

end OmegaPatch

section OmegaLaw
attribute [local instance] instSampleableTypeSeeds_pairGuessFinal instSampleableTypeForallFtsCoordDigest_pairGuessFinal
  CanonGraph.instSampleableTypeSecrets CanonGraph.instSampleableTypeOtherHalves CanonGraph.instSampleableTypeLabels_1

theorem digest_subset (adversary : AdversaryP) : digestInputs ⊆ Wots.referenceInputs adversary :=
  digestInputs_subset_publicUniverse.trans (referenceInputs_universe' adversary)

/-- **`omegaLaw` is invariant under re-drawing the digest rows and nonce halves.** -/
theorem omegaLaw_patch (adversary : AdversaryP) {γ : Type} (k : Omega (Wots.referenceInputs adversary) → SPMF γ) :
    (𝒮[omegaLaw adversary] >>= fun ω => 𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D =>
      𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn => k (patchOmega (digest_subset adversary) ω D Nn)) =
      𝒮[omegaLaw adversary] >>= k := by
  unfold omegaLaw
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  refine bind_congr fun seeds => ?_
  have step1 : ∀ (other : CanonGraph.OtherHalves) (labels : CanonGraph.Labels),
      (𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput)
        (CanonGraph.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _) : ProbComp _)] >>=
        fun residual => 𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D =>
        𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          k (patchOmega (digest_subset adversary) ⟨seeds, other, labels, residual⟩ D Nn)) =
      (𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput)
        (CanonGraph.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _) : ProbComp _)] >>=
        fun residual => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          k ⟨seeds, patch nonceOther other Nn, labels, residual⟩) := by
    intro other labels
    exact patch_uniform (digestEmb_injective (digest_subset adversary)) _ _
      (fun residual => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
        k ⟨seeds, patch nonceOther other Nn, labels, residual⟩)
  simp only [step1]
  have step2 : ∀ other : CanonGraph.OtherHalves,
      (𝒮[($ᵗ CanonGraph.Labels : ProbComp _)] >>= fun labels =>
        𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput)
          (CanonGraph.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _) : ProbComp _)] >>=
        fun residual => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          k ⟨seeds, patch nonceOther other Nn, labels, residual⟩) =
      (𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn => 𝒮[($ᵗ CanonGraph.Labels : ProbComp _)] >>= fun labels =>
        𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput)
          (CanonGraph.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _) : ProbComp _)] >>=
        fun residual => k ⟨seeds, patch nonceOther other Nn, labels, residual⟩) := by
    intro other
    calc _ = (𝒮[($ᵗ CanonGraph.Labels : ProbComp _)] >>= fun labels =>
          𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput)
            (CanonGraph.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _) : ProbComp _)] >>=
          fun residual => k ⟨seeds, patch nonceOther other Nn, labels, residual⟩) :=
          bind_congr fun labels => RetainedObservation.bind_comm _ _ _
      _ = _ := RetainedObservation.bind_comm _ _ _
  simp only [step2]
  exact patch_uniform nonceOther_injective _ _ (fun other => 𝒮[($ᵗ CanonGraph.Labels : ProbComp _)] >>= fun labels =>
    𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput)
      (CanonGraph.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _) : ProbComp _)] >>=
    fun residual => k ⟨seeds, other, labels, residual⟩)

end OmegaLaw

/-! ## One step of the forced run in an environment of value sources -/

section Steps
open SecretGuessObservation (forcedRun forcedImpl lazyImpl runWith afterTrial afterDisclosure forcedTrial)
variable (slot : Nat)

theorem rowStep_some (mem : LazyMem) (x : HashInput) (b : Bool) (src : PMF HashOutput) (a : HashOutput)
    (h : mem.rows x = some a) : rowStep mem x b src = pure (a, mem.replayRow x b) := by
  unfold rowStep
  rw [h]

theorem rowStep_out (mem : LazyMem) (x : HashInput) (b : Bool) (src : PMF HashOutput) (h : mem.rows x = none)
    (hx : x ∉ digestInputs) : rowStep mem x b src = pure (0, mem.replayRow x b) := by
  unfold rowStep
  rw [h, if_neg hx]

theorem rowStep_in (mem : LazyMem) (x : HashInput) (b : Bool) (src : PMF HashOutput) (h : mem.rows x = none)
    (hx : x ∈ digestInputs) : rowStep mem x b src = (fun a => (a, mem.readRow x a b)) <$> src := by
  unfold rowStep
  rw [h, if_pos hx]

theorem nonceStep_some (mem : LazyMem) (m : Message) (src : PMF Digest) (v : Digest) (h : mem.nonces m = some v) :
    nonceStep mem m src = pure (v, mem) := by
  unfold nonceStep
  rw [h]

theorem nonceStep_none (mem : LazyMem) (m : Message) (src : PMF Digest) (h : mem.nonces m = none) :
    nonceStep mem m src = (fun v => (v, mem.drawNonce m v)) <$> src := by
  unfold nonceStep
  rw [h]

variable (rs : HashInput → PMF HashOutput) (ns : Message → PMF Digest)

theorem step_aux (s : WStateL) (input : AuxL) :
    (forcedImpl (envWith rs ns) slot (.inl input)).run s =
      (fun result => (result.1, { s with memory := result.2 })) <$>
        (liftM (auxWith rs ns s input) : SPMF (AuxSpecL.Range input × LazyMem)) := rfl

theorem step_coin (s : WStateL) (n : Nat) :
    (forcedImpl (envWith rs ns) slot (.inl (.coin n))).run s =
      (fun c => (c, s)) <$> (liftM (PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) := by
  rw [step_aux]
  change (fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) = _
  rw [liftM_map, Functor.map_map]

theorem step_expose (s : WStateL) (o : Option HashOutput) :
    (forcedImpl (envWith rs ns) slot (.inl (.expose o))).run s = pure ((), { s with memory := s.memory.expose o }) := by
  rw [step_aux]
  change (fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM (pure ((), s.memory.expose o) : PMF _) : SPMF _) = _
  rw [liftM_pure, map_pure]

theorem step_birth (s : WStateL) (x : HashInput) :
    (forcedImpl (envWith rs ns) slot (.inl (.birth x))).run s =
      (fun result => (result.1, { s with memory := result.2 })) <$>
        (liftM (rowStep s.memory x true (rs x)) : SPMF (HashOutput × LazyMem)) := rfl

theorem step_trial (s : WStateL) (x : HashInput) :
    (forcedImpl (envWith rs ns) slot (.inl (.trial x))).run s =
      (fun result => (result.1, { s with memory := result.2 })) <$>
        (liftM (rowStep s.memory x false (rs x)) : SPMF (HashOutput × LazyMem)) := rfl

theorem step_nonce (s : WStateL) (m : Message) :
    (forcedImpl (envWith rs ns) slot (.inl (.nonce m))).run s =
      (fun result => (result.1, { s with memory := result.2 })) <$>
        (liftM (nonceStep s.memory m (ns m)) : SPMF (Digest × LazyMem)) := rfl

theorem step_guess (s : WStateL) (f : FtsCoord) (c : Digest) :
    (forcedImpl (envWith rs ns) slot (.inr (.inl (f, c)))).run s =
      (fun hit => (hit, { afterTrial (envWith rs ns) s f c hit with memory := s.memory })) <$> forcedTrial slot s f c := rfl

theorem step_disclose (s : WStateL) (f : FtsCoord) :
    (forcedImpl (envWith rs ns) slot (.inr (.inr f))).run s =
      (fun v => (v, { afterDisclosure (envWith rs ns) s f v with memory := s.memory })) <$>
        UniformTableCompletion.cell (s.allowed f) := rfl

/-- The secret steps do not depend on the value sources. -/
theorem afterTrial_sources (rs' : HashInput → PMF HashOutput) (ns' : Message → PMF Digest) (s : WStateL)
    (f : FtsCoord) (c : Digest) (hit : Bool) :
    afterTrial (envWith rs ns) s f c hit = afterTrial (envWith rs' ns') s f c hit := rfl

theorem afterDisclosure_sources (rs' : HashInput → PMF HashOutput) (ns' : Message → PMF Digest) (s : WStateL)
    (f : FtsCoord) (v : Digest) :
    afterDisclosure (envWith rs ns) s f v = afterDisclosure (envWith rs' ns') s f v := rfl

end Steps

/-! ## The eager run ignores its tables at cached rows -/

section Congr
open SecretGuessObservation (forcedRun forcedImpl runWith)

/-- Two eager table pairs agree off the cache of `mem`. -/
def Agree (D D' : digestInputs → HashOutput) (Nn Nn' : Message → Digest) (mem : LazyMem) : Prop :=
  (∀ y : digestInputs, mem.rows y.1 = none → D y = D' y) ∧ ∀ m, mem.nonces m = none → Nn m = Nn' m

theorem rowVal_agree {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (x : HashInput) (hx : mem.rows x = none) : rowVal D x = rowVal D' x := by
  unfold rowVal
  by_cases hd : x ∈ digestInputs
  · rw [dif_pos hd, dif_pos hd]
    exact h.1 ⟨x, hd⟩ hx
  · rw [dif_neg hd, dif_neg hd]

theorem agree_replay {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (x : HashInput) (b : Bool) : Agree D D' Nn Nn' (mem.replayRow x b) := by
  cases b
  · rw [replayRow_false]
    exact h
  · rw [replayRow_true]
    exact h

theorem agree_read {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (x : HashInput) (a : HashOutput) (b : Bool) :
    Agree D D' Nn Nn' (mem.readRow x a b) := by
  have hrows : ∀ y : digestInputs, (mem.rows.cacheQuery x a) y.1 = none → D y = D' y := by
    intro y hy
    by_cases hyx : y.1 = x
    · rw [hyx, QueryCache.cacheQuery_self] at hy
      cases hy
    · rw [QueryCache.cacheQuery_of_ne _ _ hyx] at hy
      exact h.1 y hy
  cases b
  · rw [readRow_false]
    exact ⟨hrows, h.2⟩
  · rw [readRow_true]
    exact ⟨hrows, h.2⟩

theorem agree_draw {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (m : Message) (v : Digest) : Agree D D' Nn Nn' (mem.drawNonce m v) := by
  refine ⟨h.1, fun m' hm' => ?_⟩
  change Function.update mem.nonces m (some v) m' = none at hm'
  by_cases hmm : m' = m
  · rw [hmm, Function.update_self] at hm'
    cases hm'
  · rw [Function.update_of_ne hmm] at hm'
    exact h.2 m' hm'

/-- **Congruence**: the eager forced run depends on its tables only off the cache. -/
theorem forced_congr {α : Type} (D D' : digestInputs → HashOutput) (Nn Nn' : Message → Digest) (slot : Nat)
    (W : OracleComp WSpecL α) (s : WStateL) (h : Agree D D' Nn Nn' s.memory) :
    forcedRun (envE D Nn) slot W s = forcedRun (envE D' Nn') slot W s := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind input next ih =>
      simp only [forcedRun, SecretGuessObservation.runWith_query_bind]
      rcases input with input | (⟨f, c⟩ | f)
      · cases input with
        | coin n =>
            rw [envE, envE, step_coin, step_coin, bind_map_left, bind_map_left]
            exact bind_congr fun c => ih c s h
        | birth x =>
            rw [envE, envE, step_birth, step_birth]
            cases hc : s.memory.rows x with
            | some a =>
                rw [rowStep_some _ _ _ _ a hc, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure, pure_bind, pure_bind]
                exact ih a _ (agree_replay h x true)
            | none =>
                rw [rowVal_agree h x hc]
                by_cases hx : x ∈ digestInputs
                · rw [rowStep_in _ _ _ _ hc hx, liftM_map, liftM_pure, map_pure, map_pure, pure_bind, pure_bind]
                  exact ih (rowVal D' x) { s with memory := s.memory.readRow x (rowVal D' x) true }
                    (agree_read h x _ true)
                · rw [rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure, pure_bind, pure_bind]
                  exact ih _ _ (agree_replay h x true)
        | trial x =>
            rw [envE, envE, step_trial, step_trial]
            cases hc : s.memory.rows x with
            | some a =>
                rw [rowStep_some _ _ _ _ a hc, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure, pure_bind, pure_bind]
                exact ih a _ (agree_replay h x false)
            | none =>
                rw [rowVal_agree h x hc]
                by_cases hx : x ∈ digestInputs
                · rw [rowStep_in _ _ _ _ hc hx, liftM_map, liftM_pure, map_pure, map_pure, pure_bind, pure_bind]
                  exact ih (rowVal D' x) { s with memory := s.memory.readRow x (rowVal D' x) false }
                    (agree_read h x _ false)
                · rw [rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure, pure_bind, pure_bind]
                  exact ih _ _ (agree_replay h x false)
        | nonce m =>
            rw [envE, envE, step_nonce, step_nonce]
            cases hc : s.memory.nonces m with
            | some v =>
                rw [nonceStep_some _ _ _ v hc, nonceStep_some _ _ _ v hc, liftM_pure, map_pure, pure_bind, pure_bind]
                exact ih v _ h
            | none =>
                rw [nonceStep_none _ _ _ hc, nonceStep_none _ _ _ hc, liftM_map, liftM_map, liftM_pure, liftM_pure,
                  map_pure, map_pure, map_pure, map_pure, pure_bind, pure_bind, h.2 m hc]
                exact ih _ _ (agree_draw h m _)
        | expose o =>
            rw [envE, envE, step_expose, step_expose, pure_bind, pure_bind]
            exact ih () _ h
      · rw [envE, envE, step_guess, step_guess, bind_map_left, bind_map_left]
        refine bind_congr fun hit => ?_
        rw [afterTrial_sources _ _ (fun x => pure (rowVal D' x)) (fun m => pure (Nn' m))]
        exact ih hit _ h
      · rw [envE, envE, step_disclose, step_disclose, bind_map_left, bind_map_left]
        refine bind_congr fun v => ?_
        rw [afterDisclosure_sources _ _ (fun x => pure (rowVal D' x)) (fun m => pure (Nn' m))]
        exact ih v _ h

end Congr

/-! ## Eager → lazy -/

section EagerLazy
open SecretGuessObservation (forcedRun forcedImpl runWith)

/-- Uniform digest-row tables. -/
noncomputable def rowsLaw : SPMF (digestInputs → HashOutput) := liftM (PMF.uniformOfFintype (digestInputs → HashOutput))

/-- Uniform nonce tables. -/
noncomputable def noncesLaw : SPMF (Message → Digest) := liftM (PMF.uniformOfFintype (Message → Digest))

theorem avg_indep {α : Type} (slot : Nat) (input : WSpecL.Domain) (next : WSpecL.Range input → OracleComp WSpecL α)
    (s : WStateL)
    (ih : ∀ u s', (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next u) s') =
      forcedRun envL slot (next u) s')
    (X : SPMF (WSpecL.Range input × WStateL)) (hE : ∀ D Nn, (forcedImpl (envE D Nn) slot input).run s = X)
    (hL : (forcedImpl envL slot input).run s = X) :
    (rowsLaw >>= fun D => noncesLaw >>= fun Nn => (forcedImpl (envE D Nn) slot input).run s >>= fun mid =>
        runWith (forcedImpl (envE D Nn) slot) (next mid.1) mid.2) =
      ((forcedImpl envL slot input).run s >>= fun mid => runWith (forcedImpl envL slot) (next mid.1) mid.2) := by
  simp only [hE, hL]
  calc _ = (rowsLaw >>= fun D => X >>= fun mid => noncesLaw >>= fun Nn =>
        runWith (forcedImpl (envE D Nn) slot) (next mid.1) mid.2) :=
        bind_congr fun D => RetainedObservation.bind_comm _ _ _
    _ = (X >>= fun mid => rowsLaw >>= fun D => noncesLaw >>= fun Nn =>
        runWith (forcedImpl (envE D Nn) slot) (next mid.1) mid.2) := RetainedObservation.bind_comm _ _ _
    _ = _ := bind_congr fun mid => ih mid.1 mid.2

/-- A fresh digest-row read (`birth` or `trial`) averages to a fresh uniform draw. -/
theorem avg_fresh_row {α : Type} (slot : Nat) (x : HashInput) (hx : x ∈ digestInputs) (s : WStateL) (b : Bool) (next : HashOutput → OracleComp WSpecL α)
    (ih : ∀ u s', (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next u) s') =
      forcedRun envL slot (next u) s') :
    (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next (rowVal D x))
        { s with memory := s.memory.readRow x (rowVal D x) b }) =
      ((liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) >>= fun a =>
        forcedRun envL slot (next a) { s with memory := s.memory.readRow x a b }) := by
  have hrv : ∀ D : digestInputs → HashOutput, rowVal D x = D ⟨x, hx⟩ := fun D => by rw [rowVal, dif_pos hx]
  simp only [hrv]
  rw [rowsLaw, uniform_update (⟨x, hx⟩ : digestInputs) (fun a D => noncesLaw >>= fun Nn =>
    forcedRun (envE D Nn) slot (next a) { s with memory := s.memory.readRow x a b })]
  · refine bind_congr fun a => ?_
    rw [← rowsLaw]
    exact ih a _
  · intro a T c
    refine bind_congr fun Nn => forced_congr _ _ _ _ slot _ _ ⟨fun y hy => ?_, fun _ _ => rfl⟩
    have hyx : y ≠ ⟨x, hx⟩ := by
      rintro rfl
      have hcached : (s.memory.readRow x a b).rows x = some a := by
        cases b
        · rw [readRow_false]
          exact QueryCache.cacheQuery_self _ _ _
        · rw [readRow_true]
          exact QueryCache.cacheQuery_self _ _ _
      change (s.memory.readRow x a b).rows x = none at hy
      rw [hcached] at hy
      cases hy
    exact Function.update_of_ne hyx _ _

/-- A fresh nonce averages to a fresh uniform draw. -/
theorem avg_fresh_nonce {α : Type} (slot : Nat) (m : Message) (s : WStateL)
    (next : Digest → OracleComp WSpecL α)
    (ih : ∀ u s', (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next u) s') =
      forcedRun envL slot (next u) s') :
    (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next (Nn m))
        { s with memory := s.memory.drawNonce m (Nn m) }) =
      ((liftM (PMF.uniformOfFintype Digest) : SPMF Digest) >>= fun v =>
        forcedRun envL slot (next v) { s with memory := s.memory.drawNonce m v }) := by
  have step : ∀ D : digestInputs → HashOutput,
      (noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next (Nn m)) { s with memory := s.memory.drawNonce m (Nn m) }) =
      ((liftM (PMF.uniformOfFintype Digest) : SPMF Digest) >>= fun v => noncesLaw >>= fun Nn =>
        forcedRun (envE D Nn) slot (next v) { s with memory := s.memory.drawNonce m v }) := by
    intro D
    rw [noncesLaw]
    refine uniform_update m (fun v Nn => forcedRun (envE D Nn) slot (next v) { s with memory := s.memory.drawNonce m v })
      fun v T c => forced_congr _ _ _ _ slot _ _ ⟨fun _ _ => rfl, fun m' hm' => ?_⟩
    have hmm : m' ≠ m := by
      rintro rfl
      change Function.update s.memory.nonces m' (some v) m' = none at hm'
      rw [Function.update_self] at hm'
      cases hm'
    exact Function.update_of_ne hmm _ _
  simp only [step]
  rw [RetainedObservation.bind_comm]
  exact bind_congr fun v => ih v _

/-- **Eager → lazy (core)**: averaging the eager environment over uniform tables is the lazy environment. -/
theorem eager_lazy_core {α : Type} (slot : Nat) (W : OracleComp WSpecL α) (s : WStateL) :
    (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot W s) = forcedRun envL slot W s := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure a =>
      simp only [forcedRun, SecretGuessObservation.runWith_pure, rowsLaw, noncesLaw, RetainedObservation.lift_bind_const]
  | query_bind input next ih =>
      simp only [forcedRun, SecretGuessObservation.runWith_query_bind]
      rcases input with input | (⟨f, c⟩ | f)
      · cases input with
        | coin n =>
            exact avg_indep slot _ next s ih _ (fun D Nn => by rw [envE, step_coin]) (by rw [envL, step_coin])
        | expose o =>
            exact avg_indep slot _ next s ih _ (fun D Nn => by rw [envE, step_expose]) (by rw [envL, step_expose])
        | birth x =>
            cases hc : s.memory.rows x with
            | some a =>
                exact avg_indep slot _ next s ih (pure (a, { s with memory := s.memory.replayRow x true }))
                  (fun D Nn => by rw [envE, step_birth, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure])
                  (by rw [envL, step_birth, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure])
            | none =>
                by_cases hx : x ∈ digestInputs
                · have hE : ∀ D Nn, (forcedImpl (envE D Nn) slot (.inl (.birth x))).run s =
                      pure (rowVal D x, { s with memory := s.memory.readRow x (rowVal D x) true }) := fun D Nn => by
                    rw [envE, step_birth, rowStep_in _ _ _ _ hc hx, liftM_map, liftM_pure, map_pure, map_pure]
                  have hL : (forcedImpl envL slot (.inl (.birth x))).run s =
                      (fun a => (a, { s with memory := s.memory.readRow x a true })) <$>
                        (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) := by
                    rw [envL, step_birth, rowStep_in _ _ _ _ hc hx, liftM_map, Functor.map_map]
                  simp only [hE, hL, pure_bind, bind_map_left]
                  exact avg_fresh_row slot x hx s true next ih
                · exact avg_indep slot _ next s ih (pure ((0 : HashOutput), { s with memory := s.memory.replayRow x true }))
                    (fun D Nn => by rw [envE, step_birth, rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure])
                    (by rw [envL, step_birth, rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure])
        | trial x =>
            cases hc : s.memory.rows x with
            | some a =>
                exact avg_indep slot _ next s ih (pure (a, { s with memory := s.memory.replayRow x false }))
                  (fun D Nn => by rw [envE, step_trial, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure])
                  (by rw [envL, step_trial, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure])
            | none =>
                by_cases hx : x ∈ digestInputs
                · have hE : ∀ D Nn, (forcedImpl (envE D Nn) slot (.inl (.trial x))).run s =
                      pure (rowVal D x, { s with memory := s.memory.readRow x (rowVal D x) false }) := fun D Nn => by
                    rw [envE, step_trial, rowStep_in _ _ _ _ hc hx, liftM_map, liftM_pure, map_pure, map_pure]
                  have hL : (forcedImpl envL slot (.inl (.trial x))).run s =
                      (fun a => (a, { s with memory := s.memory.readRow x a false })) <$>
                        (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) := by
                    rw [envL, step_trial, rowStep_in _ _ _ _ hc hx, liftM_map, Functor.map_map]
                  simp only [hE, hL, pure_bind, bind_map_left]
                  exact avg_fresh_row slot x hx s false next ih
                · exact avg_indep slot _ next s ih (pure ((0 : HashOutput), { s with memory := s.memory.replayRow x false }))
                    (fun D Nn => by rw [envE, step_trial, rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure])
                    (by rw [envL, step_trial, rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure])
        | nonce m =>
            cases hc : s.memory.nonces m with
            | some v =>
                exact avg_indep slot _ next s ih (pure (v, { s with memory := s.memory }))
                  (fun D Nn => by rw [envE, step_nonce, nonceStep_some _ _ _ v hc, liftM_pure, map_pure])
                  (by rw [envL, step_nonce, nonceStep_some _ _ _ v hc, liftM_pure, map_pure])
            | none =>
                have hE : ∀ D Nn, (forcedImpl (envE D Nn) slot (.inl (.nonce m))).run s =
                    pure (Nn m, { s with memory := s.memory.drawNonce m (Nn m) }) := fun D Nn => by
                  rw [envE, step_nonce, nonceStep_none _ _ _ hc, liftM_map, liftM_pure, map_pure, map_pure]
                have hL : (forcedImpl envL slot (.inl (.nonce m))).run s =
                    (fun v => (v, { s with memory := s.memory.drawNonce m v })) <$>
                      (liftM (PMF.uniformOfFintype Digest) : SPMF Digest) := by
                  rw [envL, step_nonce, nonceStep_none _ _ _ hc, liftM_map, Functor.map_map]
                simp only [hE, hL, pure_bind, bind_map_left]
                exact avg_fresh_nonce slot m s next ih
      · refine avg_indep slot _ next s ih _ (fun D Nn => ?_) rfl
        rw [envE, envL, step_guess, step_guess]
        have hfun : (fun hit => (hit, { SecretGuessObservation.afterTrial
              (envWith (fun x => pure (rowVal D x)) (fun m => pure (Nn m))) s f c hit with memory := s.memory })) =
            (fun hit => (hit, { SecretGuessObservation.afterTrial
              (envWith (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)) s f c hit with
                memory := s.memory })) := by
          funext hit
          rw [afterTrial_sources (fun x => pure (rowVal D x)) (fun m => pure (Nn m))
            (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)]
        rw [hfun]
      · refine avg_indep slot _ next s ih _ (fun D Nn => ?_) rfl
        rw [envE, envL, step_disclose, step_disclose]
        have hfun : (fun v => (v, { SecretGuessObservation.afterDisclosure
              (envWith (fun x => pure (rowVal D x)) (fun m => pure (Nn m))) s f v with memory := s.memory })) =
            (fun v => (v, { SecretGuessObservation.afterDisclosure
              (envWith (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)) s f v with
                memory := s.memory })) := by
          funext v
          rw [afterDisclosure_sources (fun x => pure (rowVal D x)) (fun m => pure (Nn m))
            (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)]
        rw [hfun]

/-- **Eager → lazy**: averaging the eager environment `envE D Nn` over uniform `D`, `Nn` gives the lazy
environment, for any lazy-world program and start state. -/
theorem eager_lazy {α : Type} (W : OracleComp WSpecL α) (slot : Nat) (s : WStateL) :
    (𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
      forcedRun (envE D Nn) slot W s) = forcedRun envL slot W s := by
  rw [evalSPMF_uniform, evalSPMF_uniform]
  exact eager_lazy_core slot W s

end EagerLazy

/-! ## The ω-averaged forced worlds -/

section Avg
open SecretGuessObservation (forcedRun)
attribute [local instance] instSampleableTypeSeeds_pairGuessFinal instSampleableTypeForallFtsCoordDigest_pairGuessFinal
  CanonGraph.instSampleableTypeSecrets CanonGraph.instSampleableTypeOtherHalves CanonGraph.instSampleableTypeLabels_1

/-- **The ω-averaged eager forced world is the ω-averaged lazy forced world** (in law). -/
theorem forced_avg_law (adversary : AdversaryP) (slot : Nat) :
    (𝒮[omegaLaw adversary] >>= fun ω => forcedRun (envE (digestOf ω) (nonceOf ω)) slot
        (worldGameL (canon_subset adversary) ω adversary) initL) =
      (𝒮[omegaLaw adversary] >>= fun ω =>
        forcedRun envL slot (worldGameL (canon_subset adversary) ω adversary) initL) := by
  symm
  calc (𝒮[omegaLaw adversary] >>= fun ω =>
        forcedRun envL slot (worldGameL (canon_subset adversary) ω adversary) initL)
      = (𝒮[omegaLaw adversary] >>= fun ω => 𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D =>
          𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          forcedRun (envE D Nn) slot (worldGameL (canon_subset adversary) ω adversary) initL) :=
        bind_congr fun ω => (eager_lazy _ slot initL).symm
    _ = (𝒮[omegaLaw adversary] >>= fun ω => 𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D =>
          𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          (fun ω' : Omega (Wots.referenceInputs adversary) => forcedRun (envE (digestOf ω') (nonceOf ω')) slot
            (worldGameL (canon_subset adversary) ω' adversary) initL)
            (patchOmega (digest_subset adversary) ω D Nn)) := by
        refine bind_congr fun ω => bind_congr fun D => bind_congr fun Nn => ?_
        dsimp only
        rw [digestOf_patch, nonceOf_patch]
        exact congrArg (fun W => forcedRun (envE D Nn) slot W initL)
          (worldGameL_congr (canon_subset adversary) (sameRest_patch (digest_subset adversary) ω D Nn) adversary)
    _ = _ := omegaLaw_patch adversary (fun ω' => forcedRun (envE (digestOf ω') (nonceOf ω')) slot
          (worldGameL (canon_subset adversary) ω' adversary) initL)

/-- **The averaged forced world is the lazy forced world** (any payoff on the final world state). -/
theorem forced_avg_eq_lazy (adversary : AdversaryP) (slot : Nat)
    (payoff : (Bool × QueryLog Requests × List Wots.Entry) × WStateL → ENNReal) :
    ∑' ω, Pr[= ω | omegaLaw adversary] * ∑' r, Pr[= r | forcedRun (envE (digestOf ω) (nonceOf ω)) slot
        (worldGameL (canon_subset adversary) ω adversary) initL] * payoff r =
      ∑' ω, Pr[= ω | omegaLaw adversary] * ∑' r, Pr[= r | forcedRun envL slot
        (worldGameL (canon_subset adversary) ω adversary) initL] * payoff r := by
  have h := congrArg (fun X => expectedValue X payoff) (forced_avg_law adversary slot)
  rw [expectedValue_bind, expectedValue_bind] at h
  simp only [expectedValue_def, probOutput_evalSPMF] at h
  exact h

end Avg

end SigGolfCandidate.T3.Security.BPair
