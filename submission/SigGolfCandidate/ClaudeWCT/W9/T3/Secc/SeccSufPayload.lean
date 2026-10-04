import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccSufRoute
import SigGolfCandidate.T3.Secc.SeccSufPayload

namespace ClaudeWCT.W9.T3.Security.BSuf
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers treeValue)
open ClaudeWCT.W9.T3M (expandN witEnc expandN_facts wreveal_witEnc wsib_witEnc)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem expandN_unfold (answers : Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature) (N : HashOutput)
    (wit : WCT9.Witness) (he : evalWithAnswerFn answers (expandN m pk σ) = some (N, wit)) :
    ∃ counter cs,
      evalWithAnswerFn answers (WCT9.digestSearch σ.rho m 0 WCT9.digestAttemptLimit) = some (counter, N) ∧
      evalWithAnswerFn answers (WCT9.expandLayersBC σ (N.toNat % 2 ^ 31) 4
        (.forest (evalWithAnswerFn answers (WCT9.recoverFts σ (N.toNat % 2 ^ 31) N)))) = some (pk, cs) ∧
      wit = ⟨σ, counter, fun lay => cs.getD lay.val 0⟩ := by
  simp only [expandN, evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (WCT9.digestSearch σ.rho m 0 WCT9.digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn answers (WCT9.expandLayersBC σ (output.toNat % 2 ^ 31) 4
          (.forest (evalWithAnswerFn answers (WCT9.recoverFts σ (output.toNat % 2 ^ 31) output)))) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some layers =>
          obtain ⟨root, cs⟩ := layers
          simp only [hl] at he
          split at he
          · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
          · rename_i hne
            simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            have hroot : root = pk := by simpa using hne
            subst hroot
            exact ⟨counter, cs, rfl, hl, rfl⟩
theorem layer_of_shaped (answers : Answers) (N : HashOutput) (wit : WCT9.Witness) (lay : Layer) (digits : List Nat)
    (hs : ClaudeWCT.W9.T3M.Extract.LayerShaped answers (witEnc N wit) (N.toNat % 2 ^ 31) lay digits) :
    wit.signature.layers lay = piecesSignature lay (Correctness.honestPieces answers lay
      (route (N.toNat % 2 ^ 31) lay).2 (route (N.toNat % 2 ^ 31) lay).1 digits) := by
  apply SigGolfCandidate.T3M.LayerSignature.ext'
  · funext i
    rw [← ClaudeWCT.W9.T3M.wvalue_witEnc N wit lay i, (hs.2 i.val i.isLt).1]
    simp [piecesSignature, Correctness.honestPieces]
  · funext j
    rw [← ClaudeWCT.W9.T3M.wpath_witEnc N wit lay j, (hs.1 j.val j.isLt).1]
    simp [piecesSignature, Correctness.honestPieces]
theorem layers_payload (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (hcache : published.region = Correctness.cacheRegion (Correctness.maskedTop answers))
    (N : HashOutput) (wit : WCT9.Witness)
    (hgood : ∀ lay : Layer, ClaudeWCT.W9.T3M.Extract.Good answers (witEnc N wit) (N.toNat % 2 ^ 31) lay) :
    ∀ n, n ≤ 4 → ∀ (msg : WCT9.LayerMsg) (root : Digest) (cs : List (BitVec 32)),
      (∀ k, n = k + 1 → msg = ClaudeWCT.W9.T3M.Extract.honestMsg answers (N.toNat % 2 ^ 31) (Fin.ofNat 4 k)) →
      evalWithAnswerFn answers (WCT9.expandLayersBC wit.signature (N.toNat % 2 ^ 31) n msg) = some (root, cs) →
      (∀ lay : Layer, lay.val < n → wit.counters lay = cs.getD lay.val 0) →
      ∃ pieces, evalWithAnswerFn answers (WCT9.signLayersBC published (N.toNat % 2 ^ 31) n msg) = some pieces ∧
        pieces.length = n ∧ ∀ lay : Layer, lay.val < n →
          wit.signature.layers lay = piecesSignature lay (pieces.getD lay.val ([], [])) := by
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
  intro n
  induction n with
  | zero =>
      intro _ msg root cs _ hexp _
      simp [WCT9.expandLayersBC] at hexp
  | succ n ih =>
      intro hn msg root cs hval hexp hctr
      have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
      have hmsg := hval n rfl
      have hlenAll := (WCT9.expandLayersBC_verified answers wit.signature (N.toNat % 2 ^ 31) (n + 1) hn msg root cs
        hexp).1
      simp only [WCT9.expandLayersBC, evalWithAnswerFn_bind] at hexp
      cases hs : evalWithAnswerFn answers (WCT9.layerCounterSearch (Fin.ofNat 4 n)
          (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 n)).2 (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 n)).1 msg 0
          counterLimit) with
      | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at hexp
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hsome := WCT9.layerCounterSearch_some answers (Fin.ofNat 4 n)
            (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 n)).2
            (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 n)).1 msg counterLimit 0 counter digits (by decide) hs
          have hvalid := Cost.validDigits_decode hsome.2.2
          simp only [hs] at hexp
          have hcounter : wit.counters (Fin.ofNat 4 n) = counter := by
            by_cases hn0 : n = 0
            · subst hn0
              simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq,
                Prod.mk.injEq] at hexp
              obtain ⟨-, hcs⟩ := hexp
              rw [hctr _ (by rw [hv]; omega), ← hcs, hv]
              rfl
            · simp only [hn0, if_false, evalWithAnswerFn_bind] at hexp
              generalize evalWithAnswerFn answers (WCT9.expandLayersBC wit.signature (N.toNat % 2 ^ 31) n
                (.pair (evalWithAnswerFn answers (WCT9.recoverLayerPair wit.signature (N.toNat % 2 ^ 31)
                  (Fin.ofNat 4 n) digits)).1 (evalWithAnswerFn answers (WCT9.recoverLayerPair wit.signature
                    (N.toNat % 2 ^ 31) (Fin.ofNat 4 n) digits)).2)) = res at hexp
              rcases res with _ | ⟨root', cs'⟩
              · simp at hexp
              · simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at hexp
                obtain ⟨-, hcs⟩ := hexp
                have hlen' : cs'.length = n := by rw [← hcs] at hlenAll; simpa using hlenAll
                rw [hctr _ (by rw [hv]; omega), ← hcs, hv, List.getD_append_right _ _ _ _ (by omega), hlen']
                simp
          obtain ⟨digitsG, ⟨_, hdec⟩, hshape⟩ := hgood (Fin.ofNat 4 n)
          rw [ClaudeWCT.W9.T3M.wbcCtr_witEnc, ClaudeWCT.W9.T3M.wbcPad_witEnc, hcounter, ← hmsg,
            ClaudeWCT.W9.T3M.BC.layerEncodingInputP_zero] at hdec
          rw [hsome.2.2, Option.some.injEq] at hdec
          subst hdec
          rename' digits => digitsG
          have hlayer := layer_of_shaped answers N wit (Fin.ofNat 4 n) digitsG hshape
          by_cases hn0 : n = 0
          · subst hn0
            have ht : (route (N.toNat % 2 ^ 31) 0).2 = 0 := route_top_tree (N.toNat % 2 ^ 31) hidx
            have htop := Correctness.eval_signTop_honest answers published (route (N.toNat % 2 ^ 31) 0).1
              digitsG hcache (route_leaf_bound (N.toNat % 2 ^ 31) 0) hvalid
            refine ⟨[Correctness.honestPieces answers 0 0 (route (N.toNat % 2 ^ 31) 0).1 digitsG], ?_, rfl, ?_⟩
            · simp only [WCT9.signLayersBC, evalWithAnswerFn_bind, hs, ite_true, evalWithAnswerFn_pure]
              rw [show (Fin.ofNat 4 0 : Layer) = 0 from rfl, htop]
            · intro lay hlay
              have hl0 : lay = 0 := Fin.ext (by simp at hlay ⊢; omega)
              subst hl0
              rw [show (Fin.ofNat 4 0 : Layer) = 0 from rfl, ht] at hlayer
              exact hlayer
          · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
            have hrecover : evalWithAnswerFn answers (WCT9.recoverLayerPair wit.signature (N.toNat % 2 ^ 31)
                (Fin.ofNat 4 (k + 1)) digitsG) =
                WCT9.builtPair answers (Fin.ofNat 4 (k + 1)) (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).2 := by
              apply WCT9.eval_recoverLayerPair_honest answers wit.signature _ _ digitsG hvalid
              · intro i
                rw [hlayer]
                simp [piecesSignature, Correctness.honestPieces, List.getD_eq_getElem, i.isLt]
              · intro j
                rw [hlayer]
                simp [piecesSignature, Correctness.honestPieces, List.getD_eq_getElem, j.isLt]
            have hnext : WCT9.LayerMsg.pair (WCT9.builtPair answers (Fin.ofNat 4 (k + 1))
                (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).2).1
                (WCT9.builtPair answers (Fin.ofNat 4 (k + 1)) (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).2).2 =
                ClaudeWCT.W9.T3M.Extract.honestMsg answers (N.toNat % 2 ^ 31) (Fin.ofNat 4 k) := by
              rw [ClaudeWCT.W9.T3.Security.BPB.honestMsg_lower answers (N.toNat % 2 ^ 31) k (by omega)]
              rfl
            simp only [show k + 1 ≠ 0 by omega, if_false, evalWithAnswerFn_bind, hrecover] at hexp
            generalize hres : evalWithAnswerFn answers (WCT9.expandLayersBC wit.signature (N.toNat % 2 ^ 31) (k + 1)
              (.pair (WCT9.builtPair answers (Fin.ofNat 4 (k + 1)) (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).2).1
                (WCT9.builtPair answers (Fin.ofNat 4 (k + 1))
                  (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).2).2)) = res at hexp
            rcases res with _ | ⟨root', cs'⟩
            · simp at hexp
            simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at hexp
            obtain ⟨-, hcs⟩ := hexp
            have hlen' : cs'.length = k + 1 := by rw [← hcs] at hlenAll; simpa using hlenAll
            obtain ⟨pieces, hpieces, hplen, hpagree⟩ := ih (by omega) _ root' cs'
              (fun k' hk' => by rw [hnext]; congr; omega) hres
              (fun lay hlay => by
                rw [hctr lay (by omega), ← hcs, List.getD_append _ _ _ _ (by omega)])
            have htree := Correctness.eval_buildTree_result answers (Fin.ofNat 4 (k + 1))
              (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).2
              (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).1 digitsG hvalid
              (route_leaf_bound (N.toNat % 2 ^ 31) _)
            refine ⟨pieces ++ [Correctness.honestPieces answers (Fin.ofNat 4 (k + 1))
              (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).2
              (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).1 digitsG], ?_,
              by simp [hplen], ?_⟩
            · rw [WCT9.signLayersBC]
              simp only [evalWithAnswerFn_bind, hs, htree, show k + 1 ≠ 0 by omega, ite_false]
              have hpair : WCT9.topPair (Fin.ofNat 4 (k + 1)) (Correctness.builtTree answers (Fin.ofNat 4 (k + 1))
                  (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).2) =
                  WCT9.builtPair answers (Fin.ofNat 4 (k + 1)) (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).2 :=
                rfl
              rw [hpair, hpieces]
              rfl
            · intro lay hlay
              by_cases hlt : lay.val < k + 1
              · rw [hpagree lay hlt, List.getD_append _ _ _ _ (by omega)]
              · have hle : lay = Fin.ofNat 4 (k + 1) := Fin.ext (by rw [hv]; omega)
                subst hle
                rw [hlayer, hv, List.getD_append_right _ _ _ _ (by omega), hplen]
                simp
theorem opening_ext {a b : WCT9.Opening} (hv : ∀ t, a.values t = b.values t) (hp : ∀ l, a.path l = b.path l) :
    a = b := by
  cases a
  cases b
  simp only [WCT9.Opening.mk.injEq]
  exact ⟨funext hv, funext hp⟩
theorem openings_of_honest (answers : Answers) (N : HashOutput) (wit : WCT9.Witness)
    (hH : ClaudeWCT.W9.T3M.WctExtract.WctHonest answers N (witEnc N wit)) (k : WCT9.Coord) :
    wit.signature.openings k = WCT9.expectedOpening answers (N.toNat % 2 ^ 31) N k := by
  obtain ⟨hval, hsib⟩ := hH.2 k
  apply opening_ext
  · intro t
    rw [← wreveal_witEnc N wit k t (WCT9.digit (WCT9.rank N k) t), (hval t).1]
    unfold WCT9.expectedOpening WCT9.honestOpening
    rw [WCT9.buildCoordinate_result]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp
    rfl
  · intro l
    rw [← wsib_witEnc N wit k l, (hsib l.val l.isLt).1]
    unfold WCT9.expectedOpening WCT9.honestOpening
    rw [WCT9.buildCoordinate_result]
    simp only [List.getD_eq_getElem?_getD]
    simp [treeValue, List.getD_eq_getElem?_getD, ClaudeWCT.W9.T3M.Extract.ftsLevels]
    rfl
theorem caseC_expansion_is_payload (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (message : Message) (pk : Digest) (signature : WCT9.Signature) (N : HashOutput) (wit : WCT9.Witness)
    (hcache : published.region = Correctness.cacheRegion (Correctness.maskedTop answers))
    (he : evalWithAnswerFn answers (expandN message pk signature) = some (N, wit))
    (hgood : ∀ lay : Layer, ClaudeWCT.W9.T3M.Extract.Good answers (witEnc N wit) (N.toNat % 2 ^ 31) lay)
    (hfts : ClaudeWCT.W9.T3M.WctExtract.WctHonest answers N (witEnc N wit)) :
    evalWithAnswerFn answers (ClaudeWCT.W9.T3.Security.BPB.payloadForNonce published signature.rho message) =
      some signature := by
  have F := expandN_facts answers message pk signature N wit he
  obtain ⟨counter, cs, hds, hel, hwit⟩ := expandN_unfold answers message pk signature N wit he
  have hopen : ∀ coord, signature.openings coord = WCT9.expectedOpening answers (N.toNat % 2 ^ 31) N coord := by
    intro coord
    rw [← F.sig]
    exact openings_of_honest answers N wit hfts coord
  have hrf : evalWithAnswerFn answers (WCT9.recoverFts signature (N.toNat % 2 ^ 31) N) =
      WCT9.honestForest answers (N.toNat % 2 ^ 31) :=
    WCT9.recoverFts_honest answers signature _ N hopen
  obtain ⟨pieces, hpieces, -, hpagree⟩ := layers_payload answers published hcache N wit hgood 4 le_rfl
    (.forest (WCT9.honestForest answers (N.toNat % 2 ^ 31))) pk cs
    (fun k hk => by
      obtain rfl : k = 3 := by omega
      exact (ClaudeWCT.W9.T3.Security.BPB.honestMsg_three answers _).symm)
    (by rw [F.sig, ← hrf]; exact hel)
    (fun lay _ => by rw [hwit])
  have hO : ∀ coord : WCT9.Coord,
      (List.ofFn (WCT9.expectedOpening answers (N.toNat % 2 ^ 31) N)).getD coord.val ⟨fun _ => 0, fun _ => 0⟩ =
        signature.openings coord := by
    intro coord
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact coord.isLt), List.getElem_ofFn]
    exact (hopen coord).symm
  have hL : ∀ lay : Layer, piecesSignature lay (pieces.getD lay.val ([], [])) = signature.layers lay := by
    intro lay
    have := hpagree lay lay.isLt
    rw [F.sig] at this
    exact this.symm
  unfold ClaudeWCT.W9.T3.Security.BPB.payloadForNonce
  simp only [evalWithAnswerFn_bind, hds, WCT9.eval_signForest, hpieces, evalWithAnswerFn_pure]
  congr 1
  clear hpieces hpagree hrf hopen hel hwit F he hds
  cases signature
  simp only [WCT9.assembledSignature, WCT9.Signature.mk.injEq]
  exact ⟨trivial, funext hO, funext hL⟩
end ClaudeWCT.W9.T3.Security.BSuf
namespace ClaudeWCT.W9.T3.Security.BPB
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M (wrho wdc)
open ClaudeWCT.W9.T3M (WBytes expandN witEnc expandN_facts eval_expandB wrho_witEnc wdc_witEnc)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem gameCaseC_signed_false (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (answers : Correctness.Answers)
    (result : FirstHit.Recorded Bool)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer) :
    ¬GameCaseC adversary answers id result := by
  rintro ⟨generated, hg, interaction, hi, hext, hpk, -, forgery, hforgery, hfresh, message, witness, hof, hsigned,
    hC⟩
  have hirun := FirstHit.recorded_support _ _ _ hi
  have hgext : SourceReplay.Extends generated.state interaction.state :=
    SourceReplay.run_extends _ generated.state _ hirun
  have hai : ∀ input answer, SourceReplay.known interaction.state input = some answer → answers input = answer :=
    fun input answer hk => ha input answer (SourceReplay.known_mono _ _ hext hk)
  have hgen : evalWithAnswerFn answers keygen = generated.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅, ∅)
      (generated.value, generated.state) (FirstHit.recorded_support _ _ _ hg)).eval answers
        (fun input answer hk => hai input answer (SourceReplay.known_mono _ _ hgext hk))
  have hcache : generated.value.2.region = Correctness.cacheRegion (Correctness.maskedTop answers) := by
    rw [← hgen]
    exact (Correctness.keygen_correct answers).2.1
  obtain ⟨entry, hentry, hmsg, σm, hσm, hrho⟩ := hsigned
  have hres := logged_resolves generated.value.2 _ generated.state _ hirun entry hentry
  have hlog : evalWithAnswerFn answers (FullGame.authenticatedSign generated.value.2 entry.1) = some σm := by
    rw [hres.eval answers hai, hσm]
  obtain ⟨-, -, hpay⟩ := authenticatedSign_payload answers generated.value.2 entry.1 σm hlog
  cases forgery with
  | witness m w =>
      exact hfresh ⟨entry, hentry, by rw [hmsg]; exact hof.1, by rw [hσm]; rfl⟩
  | signature m σ =>
      obtain ⟨hm, hexp⟩ := hof
      rw [eval_expandB] at hexp
      cases hx : evalWithAnswerFn answers (expandN m generated.value.1 σ) with
      | none => rw [hx] at hexp; simp at hexp
      | some x =>
          obtain ⟨N, wit⟩ := x
          rw [hx] at hexp
          simp only [Option.map_some, Option.some.injEq] at hexp
          subst hexp
          have F := expandN_facts answers m _ σ N wit hx
          obtain ⟨N', -, hN', -, -, hgood, hfts⟩ := hC
          have hNN : N' = N := by
            rw [← hN', wrho_witEnc, wdc_witEnc, F.sig, hm]
            exact F.digest
          subst hNN
          have hpayσ := BSuf.caseC_expansion_is_payload answers generated.value.2 m _ σ N' wit hcache hx
            (fun lay => (hgood lay).good) hfts
          have hrhoσ : σm.rho = σ.rho := by rw [hrho, wrho_witEnc, F.sig]
          rw [hmsg, hrhoσ, hm, hpayσ, Option.some.injEq] at hpay
          subst hpay
          exact hfresh ⟨entry, hentry, by rw [hmsg, hm], hσm⟩
theorem caseC_signed_impossible (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (_hclean : QueryRecorded.CleanWin q z.1) : ¬CaseCSigned adversary z :=
  gameCaseC_signed_false adversary z.2 _ (SeccLaw.completed_agrees adversary q hq z hz).2
end ClaudeWCT.W9.T3.Security.BPB
