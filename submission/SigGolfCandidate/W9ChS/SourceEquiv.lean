import SigGolfCandidate.W9Machine.WctChainSplit

namespace W9ChS
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M publicHash shortHash header)
open W9Machine W9Machine.Chain
theorem traceProgram_append (b : ChainWord → Word) (qs₁ qs₂ : List (List ChainWord))
    (as : List (BitVec 256)) :
    traceProgram b (qs₁ ++ qs₂) as = traceProgram b qs₁ as >>= fun as' => traceProgram b qs₂ as' := by
  induction qs₁ generalizing as with
  | nil => simp only [List.nil_append, traceProgram, pure_bind]
  | cons q qs ih => simp only [List.cons_append, traceProgram, ih, bind_assoc]
theorem sum_take_succ (l : List Nat) (t : Nat) :
    (l.take (t + 1)).sum = (l.take t).sum + l.getD t 0 := by
  induction l generalizing t with
  | nil => simp
  | cons x xs ih =>
    cases t with
    | zero => simp
    | succ t => simp only [List.take_succ_cons, List.sum_cons, ih, List.getD_cons_succ]; omega
theorem extract_lo (x : BitVec 256) :
    (x.extractLsb' 0 128).extractLsb' 0 64 = x.extractLsb' 0 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  rw [Nat.mod_mod_of_dvd _ (by norm_num)]
theorem extract_hi (x : BitVec 256) :
    (x.extractLsb' 0 128).extractLsb' 64 64 = x.extractLsb' 64 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod]
theorem orig_word {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u : MachineState} (hu : Pre w index k j rank u) (as : List (BitVec 256)) (off : Nat)
    (ho : off < 1024) (ha : off % 8 = 0) :
    chainValue (originalValue u index k j) as (.original off) =
      w.extractLsb' (8 * (ClaudeWCT.W9.T3M.regionBase k.val + off)) 64 := by
  have h := hu.witness off ho ha
  unfold OrigW at h
  have he : base k + off - 0x800 = ClaudeWCT.W9.T3M.regionBase k.val + off := by
    unfold base ClaudeWCT.W9.T3M.regionBase
    omega
  rw [he] at h
  exact h
theorem orig_block {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u : MachineState} (hu : Pre w index k j rank u) (as : List (BitVec 256)) (t c : Nat)
    (ht : t < 7) (hc : c < 192) (ha : c % 8 = 0) :
    chainValue (originalValue u index k j) as (.original (832 - 64 * t + c)) =
      w.extractLsb' (8 * (ClaudeWCT.W9.T3M.wctChainBlock k.val t + c)) 64 := by
  rw [orig_word hu as _ (by omega) (by omega)]
  unfold ClaudeWCT.W9.T3M.wctChainBlock
  rw [Nat.add_assoc]
theorem query_bytes {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u : MachineState} (hu : Pre w index k j rank u) (digits : List Nat) (t s : Nat)
    (ht : t < 7) (hs : s < digits.getD t 0) (as : List (BitVec 256)) (v : Digest)
    (hv : v = if s = 0 then ClaudeWCT.W9.T3M.wreveal w k.val t (digits.getD t 0)
      else (as.getD ((digits.take t).sum + s - 1) 0).extractLsb' 0 128) :
    wordBytes ((chainQueryWords digits t s).map (chainValue (originalValue u index k j) as)) =
      ClaudeWCT.W9.T3M.wctChainInputP index k.val j.val t (3 - digits.getD t 0 + s)
        (ClaudeWCT.W9.T3M.wcpads w k.val t).1 (ClaudeWCT.W9.T3M.wcpads w k.val t).2 v := by
  have hin : ClaudeWCT.W9.T3M.wctChainInputP index k.val j.val t (3 - digits.getD t 0 + s)
      (ClaudeWCT.W9.T3M.wcpads w k.val t).1 (ClaudeWCT.W9.T3M.wcpads w k.val t).2 v =
      blk4 (ClaudeWCT.W9.T3M.wcpads w k.val t).1
        (header 5 k.val index (3 - digits.getD t 0 + s + 256 * t) j.val)
        (ClaudeWCT.W9.T3M.wcpads w k.val t).2 v := by
    unfold ClaudeWCT.W9.T3M.wctChainInputP blk4
    rw [ClaudeWCT.WCT9.chain_header_eq]
  rw [hin, ← wordBytes_wordsOf (blk4 _ _ _ _) 8 (blk4_length _ _ _ _), wordsOf_blk4]
  congr 1
  have hp : ¬ SigGolfCandidate.T3.packedNodeTag 5 := by decide
  simp only [chainQueryWords, List.map_cons, List.map_nil, dlo, dhi, header_lo, header_hi,
    if_neg hp, ClaudeWCT.W9.T3M.wcpads, SigGolfCandidate.T3M.wdig_lo, SigGolfCandidate.T3M.wdig_hi,
    List.cons.injEq, and_true]
  have hd : digits.getD t 0 ≠ 0 := by omega
  refine ⟨by simpa using orig_block hu as t 0 ht (by decide) (by decide),
    orig_block hu as t 8 ht (by decide) (by decide), rfl, rfl,
    orig_block hu as t 32 ht (by decide) (by decide),
    by simpa only [Nat.add_assoc] using orig_block hu as t 40 ht (by decide) (by decide), ?_, ?_⟩
  · by_cases h0 : s = 0
    · rw [if_pos h0, hv, if_pos h0, ClaudeWCT.W9.T3M.wreveal, if_neg hd, ClaudeWCT.W9.T3M.wopen,
        SigGolfCandidate.T3M.wdig_lo]
      exact orig_block hu as t 48 ht (by decide) (by decide)
    · rw [if_neg h0, hv, if_neg h0, extract_lo]
      rfl
  · by_cases h0 : s = 0
    · rw [if_pos h0, hv, if_pos h0, ClaudeWCT.W9.T3M.wreveal, if_neg hd, ClaudeWCT.W9.T3M.wopen,
        SigGolfCandidate.T3M.wdig_hi]
      simpa only [Nat.add_assoc] using orig_block hu as t 56 ht (by decide) (by decide)
    · rw [if_neg h0, hv, if_neg h0, extract_hi]
      rfl
theorem shortHash_def (x : List UInt8) :
    shortHash x = publicHash x >>= fun a => pure (a.extractLsb' 0 128) := rfl
theorem sum_take_mono (l : List Nat) (a c : Nat) : (l.take a).sum ≤ (l.take (a + c)).sum := by
  induction c with
  | zero => exact le_refl _
  | succ c ih => rw [← Nat.add_assoc, sum_take_succ]; omega
theorem chain_cps {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u : MachineState} (hu : Pre w index k j rank u) (digits : List Nat) (t : Nat) (ht : t < 7)
    {β : Type} (r : Nat) : ∀ (s : Nat) (as : List (BitVec 256)) (v : Digest)
      (K : List (BitVec 256) → M β) (Kv : Digest → M β),
    s + r = digits.getD t 0 → as.length = (digits.take t).sum + s →
    v = (if s = 0 then ClaudeWCT.W9.T3M.wreveal w k.val t (digits.getD t 0)
      else (as.getD ((digits.take t).sum + s - 1) 0).extractLsb' 0 128) →
    (∀ new : List (BitVec 256), new.length = r →
      K (as ++ new) = Kv (if r = 0 then v else (new.getD (r - 1) 0).extractLsb' 0 128)) →
    (traceProgram (originalValue u index k j) ((List.range' s r).map (chainQueryWords digits t)) as
        >>= K) =
      ((List.range' (3 - digits.getD t 0 + s) r).foldlM
        (fun value step => shortHash (ClaudeWCT.W9.T3M.wctChainInputP index k.val j.val t step
          (ClaudeWCT.W9.T3M.wcpads w k.val t).1 (ClaudeWCT.W9.T3M.wcpads w k.val t).2 value)) v
        >>= Kv) := by
  induction r with
  | zero =>
    intro s as v K Kv _ _ _ hK
    simp only [List.range'_zero, List.map_nil, traceProgram, List.foldlM_nil, pure_bind]
    simpa using hK [] rfl
  | succ r ih =>
    intro s as v K Kv hsr hlen hv hK
    rw [List.range'_succ, List.map_cons, List.range'_succ, List.foldlM_cons]
    simp only [traceProgram, bind_assoc]
    rw [query_bytes hu digits t s ht (by omega) as v hv, shortHash_def, bind_assoc]
    simp only [pure_bind]
    refine congrArg (publicHash _ >>= ·) (funext fun ans => ?_)
    rw [show 3 - digits.getD t 0 + s + 1 = 3 - digits.getD t 0 + (s + 1) by omega]
    refine ih (s + 1) (as ++ [ans]) _ K Kv (by omega) (by simp [hlen]; omega) ?_ ?_
    · rw [if_neg (by omega), show (digits.take t).sum + (s + 1) - 1 = as.length by omega,
        List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
      rfl
    · intro new hnew
      rw [List.append_assoc, List.singleton_append, hK (ans :: new) (by simp [hnew])]
      congr 1
      cases r with
      | zero => simp
      | succ r => simp
def endOf (w : WBytes) (k : Fin 9) (digits : List Nat) (as : List (BitVec 256)) (t : Nat) :
    Digest :=
  if digits.getD t 0 = 0 then ClaudeWCT.W9.T3M.wleaf w k.val t
  else (as.getD ((digits.take (t + 1)).sum - 1) 0).extractLsb' 0 128
def chainProg (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (digits : List Nat) (t : Nat) :
    M Digest :=
  ClaudeWCT.W9.T3M.wctChainP index k.val j.val t (3 - digits.getD t 0) (digits.getD t 0)
    (ClaudeWCT.W9.T3M.wcpads w k.val t).1 (ClaudeWCT.W9.T3M.wcpads w k.val t).2
    (ClaudeWCT.W9.T3M.wreveal w k.val t (digits.getD t 0))
def chainQs (digits : List Nat) (t : Nat) : List (List ChainWord) :=
  (List.range (digits.getD t 0)).map (chainQueryWords digits t)
theorem outer_cps {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 728}
    {u : MachineState} (hu : Pre w index k j rank u) (digits : List Nat) (m : Nat) :
    ∀ (t : Nat) (as : List (BitVec 256)) (acc : List Digest),
    t + m = 7 → as.length = (digits.take t).sum → acc.length = t →
    (∀ i, i < t → acc.getD i 0 = endOf w k digits as i) →
    (traceProgram (originalValue u index k j) ((List.range' t m).flatMap (chainQs digits)) as
        >>= fun as' => pure ((List.finRange 7).map fun i => endOf w k digits as' i.val)) =
      ((List.range' t m).mapM (chainProg w index k j digits) >>= fun vs => pure (acc ++ vs)) := by
  induction m with
  | zero =>
    intro t as acc htm hlen hacc hE
    simp only [List.range'_zero, List.flatMap_nil, traceProgram, pure_bind, List.mapM_nil,
      List.append_nil]
    congr 1
    apply List.ext_getElem
    · simp [hacc]; omega
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk]
      rw [← hE i (by omega), List.getD_eq_getElem _ _ h2]
  | succ m ih =>
    intro t as acc htm hlen hacc hE
    rw [List.range'_succ, List.flatMap_cons, List.mapM_cons, traceProgram_append, bind_assoc]
    simp only [bind_assoc, pure_bind]
    unfold chainQs chainProg
    rw [List.range_eq_range', ClaudeWCT.W9.T3M.wctChainP]
    refine chain_cps hu digits t (by omega) (digits.getD t 0) 0 as _ _ _ (by omega)
      (by simpa using hlen) (by simp) ?_
    intro new hnew
    refine (ih (t + 1) (as ++ new) (acc ++ [if digits.getD t 0 = 0 then
        ClaudeWCT.W9.T3M.wreveal w k.val t (digits.getD t 0)
        else (new.getD (digits.getD t 0 - 1) 0).extractLsb' 0 128]) (by omega)
        (by rw [sum_take_succ]; simp [hlen, hnew]) (by simp [hacc]) ?_).trans ?_
    · intro i hi
      by_cases hit : i < t
      · rw [List.getD_append _ _ _ _ (by omega), hE i hit]
        unfold endOf
        split_ifs with hd
        · rfl
        · have h1 := sum_take_succ digits i
          have h2 := sum_take_mono digits (i + 1) (t - (i + 1))
          rw [show i + 1 + (t - (i + 1)) = t by omega] at h2
          rw [List.getD_append _ _ _ _ (by omega)]
      · have hit : i = t := by omega
        subst hit
        rw [List.getD_append_right _ _ _ _ (by omega), hacc, Nat.sub_self]
        unfold endOf
        split_ifs with hd
        · simp only [List.getD_cons_zero, ClaudeWCT.W9.T3M.wreveal, if_pos hd]
        · have h1 := sum_take_succ digits i
          rw [List.getD_append_right _ _ _ _ (by omega)]
          simp only [List.getD_cons_zero]
          congr 2
          omega
    · simp only [List.append_assoc, List.singleton_append]
      rfl
theorem sourceEquivalent : W9Machine.Chain.SourceEquivalent := by
  intro w index k j rank u hu
  have h := outer_cps hu (ClaudeWCT.WCT9.codeword rank) 7 0 [] [] rfl rfl rfl
    (fun i hi => absurd hi (Nat.not_lt_zero i))
  have hq : expectedQueries (ClaudeWCT.WCT9.codeword rank) =
      (List.range' 0 7).flatMap (chainQs (ClaudeWCT.WCT9.codeword rank)) := by
    rw [expectedQueries, List.range_eq_range']
    rfl
  have hp : program w index k j rank =
      (List.range' 0 7).mapM (chainProg w index k j (ClaudeWCT.WCT9.codeword rank)) := rfl
  rw [hq, hp]
  refine h.trans ?_
  simp only [List.nil_append, bind_pure]
end W9ChS
