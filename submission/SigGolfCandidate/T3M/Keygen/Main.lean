import SigGolfCandidate.T3M.Keygen.Payload
import SigGolfCandidate.T3M.Keygen.Halt
import SigGolfCandidate.T3M.FullCache.MacRun
import SigGolfCandidate.T3M.Submission

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest Cache Region keygen keygenPayload cacheBytes readLE)
open SphincsSecurity (bytesLE bytesLE_length)
theorem initialState_keygen (sk : SecretKey) : initialState submission .keygen sk = some (kinit sk) := by
  have hv := submission_keygen_valid
  unfold initialState
  rw [if_pos hv]
  simp only [submission_keygen, Images.keygenImage, Images.keygenData, MachineState.writeBytesAsWords_nil]
  rfl
structure KDone (r : Digest × Cache) (t : MachineState) : Prop where
  pc : t.pc = pcOf 541
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 0
  pk : t.readWords (BitVec.ofNat 64 0xA0) 2 = wordsOf (bytesLE 16 r.1)
  cache : t.readWords (BitVec.ofNat 64 0x80000) 16384 = wordsOf (cacheBytes r.2)
section main
variable {sk : SecretKey} {s1 : MachineState} (hs : KStart sk s1)
include hs
theorem keygen_from_start : TSim image sk s1 31780692 39960212 995328 1048576 keygen KDone := by
  unfold keygen
  refine TSim.bind (k₂ := 1703623) (c₂ := 2489877) (n₂ := 2) (b₂ := 2)
    (payload_tsim hs) (fun r t ht => ?_)
  obtain ⟨pk,region⟩ := r
  have hsk : FullCache.SkAt t sk := by
    intro j; fin_cases j
    · exact ht.k0
    · exact ht.k8
    · exact ht.k16
    · exact ht.k24
  have hmac := FullCache.mac_tsim false sk region t ht.pc ht.x5 hsk ht.region
  refine TSim.bind (k₂ := 2) (c₂ := 2) (n₂ := 0) (b₂ := 0) hmac (fun tag u hu => ?_)
  obtain ⟨v,st,pc,h5,h10,hr,hf⟩ := haltSetup_spec u hu.pc
  refine TSim.pure_steps st ⟨pc,h5,h10,?_,?_⟩
  · have hpk : DigAt u 0xA0 pk := ht.pk.frame hu.frame (by decide)
        (by simp [FullCache.MacW,FullCache.PRIV,FullCache.KEYS,FullCache.OutW,FullCache.macOut])
        (by simp [FullCache.MacW,FullCache.PRIV,FullCache.KEYS,FullCache.OutW,FullCache.macOut])
    exact (hpk.frame hf (by decide) (fun h => h) (fun h => h)).words
  · show v.readWords (BitVec.ofNat 64 0x80000) (4+16380) = wordsOf (bytesLE 32 tag ++ List.ofFn region)
    rw [Frame.readWords hf 0x80000 (4+16380) (by decide) (fun _ _ h => h),readWords_add,
      wordsOf_append _ _ (by simp [bytesLE_length])]
    rw [show u.readWords (BitVec.ofNat 64 0x80000) 4=wordsOf (bytesLE 32 tag) from hu.words]
    rw [Frame.readWords hu.frame (0x80000+8*4) 16380 (by decide) (fun i hi h => by
      simp only [FullCache.MacW,FullCache.PRIV,FullCache.KEYS,FullCache.OutW,FullCache.macOut,Bool.false_eq_true,ite_false] at h
      omega)]
    exact congrArg _ ht.region
end main
theorem keygen_tsim (sk : SecretKey) :
    TSim image sk (kinit sk) 31780718 39960238 995328 1048576 keygen KDone := by
  obtain ⟨s1, st1, hs⟩ := kstart sk
  exact TSim.steps st1 (keygen_from_start hs)
theorem kdone_output {r : Digest × Cache} {t : MachineState} (h : KDone r t) :
    readOutput submission.sizes submission.layout .keygen t = ((r.1 : PublicKey), cacheB r.2) := by
  show (readBuffer t 160 16, readBuffer t 0x80000 131072) = _
  have e1 : readBuffer t 160 (8 * 2) = BitVec.ofNat _ (readLE (bytesLE 16 r.1)) :=
    readBuffer_of_words t 160 2 (bytesLE 16 r.1) (by decide) (by decide) (bytesLE_length _ _) h.pk
  have e2 : readBuffer t 0x80000 (8 * 16384) = BitVec.ofNat _ (readLE (cacheBytes r.2)) :=
    readBuffer_of_words t 0x80000 16384 (cacheBytes r.2) (by decide) (by decide) (cacheBytes_length r.2) h.cache
  rw [readLE_bytesLE] at e1
  refine Prod.ext ?_ e2
  refine e1.trans (BitVec.eq_of_toNat_eq ?_)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt r.1.isLt]
theorem keygen_run (sk : SecretKey) :
    submission.run .keygen sk =
      (fun r => ⟨some ((r.1 : PublicKey), cacheB r.2), true, 39960239, 995328, 1048576⟩) <$>
        mrealize sk keygen :=
  XSim.run_eq submission .keygen sk (initialState_keygen sk) (keygen_tsim sk) (by decide)
    (fun r => ((r.1 : PublicKey), cacheB r.2))
    (fun _ t h => ⟨fetch_541 t h.pc, h.x5, h.x10, kdone_output h⟩)
theorem keygen_countBoth (sk : SecretKey) :
    countBoth (mrealize sk keygen) = (fun a => (a, 995328, 1048576)) <$> mrealize sk keygen :=
  XSim.countBoth_eq (keygen_tsim sk)
theorem keygen_run_counts (sk : SecretKey) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .keygen sk =
      (fun p => (some ((p.1.1 : PublicKey), cacheB p.1.2), p.2.1, p.2.2)) <$>
        countBoth (mrealize sk keygen) := by
  rw [keygen_run, keygen_countBoth, Functor.map_map, Functor.map_map]; rfl
theorem keygen_runWith (hash : Hash) (sk : SecretKey) :
    submission.runWith hash .keygen sk =
      ⟨some (((evalWithAnswerFn hash (mrealize sk keygen)).1 : PublicKey),
        cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2), true, 39960239, 995328, 1048576⟩ := by
  unfold Submission.runWith
  rw [keygen_run, evalWithAnswerFn_map]
end SigGolfCandidate.T3M.Keygen
