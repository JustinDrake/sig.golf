import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Basic

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
private theorem hdrBlock_prefix' (a h : Digest) (rest : HashInput) :
    hdrBlock (bytesLE 16 a ++ bytesLE 16 h ++ rest) = bytesLE 16 h := by
  unfold hdrBlock
  rw [List.append_assoc, List.drop_left' (bytesLE_length 16 a), List.take_left' (bytesLE_length 16 h)]
private theorem hdrBlock_pad64' (input : HashInput) (h : 32 ≤ input.length) :
    hdrBlock (pad64 input) = hdrBlock input := by
  unfold hdrBlock pad64
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
private theorem hdrBlock_block4' (a b c d : Digest) : hdrBlock (block4 a b c d) = bytesLE 16 b := by
  unfold block4
  rw [List.append_assoc]
  exact hdrBlock_prefix' a b _
private theorem hdrBlock_listInput' (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    hdrBlock (pad64 (listInput first hdr rest)) = bytesLE 16 hdr := by
  have hl : 32 ≤ (listInput first hdr rest).length := by
    simp only [listInput, List.length_append, bytesLE_length]; omega
  rw [hdrBlock_pad64' _ hl]
  exact hdrBlock_prefix' first hdr _
private theorem bytesLE_zero' : bytesLE 16 (0 : Digest) = zero16 := by decide
theorem wctChainInput_block4 (index coord child t step : Nat) (value : Digest) :
    WCT9.chainInput index coord child t step value =
      block4 0 (header 5 coord index (step + 256 * t) child) 0 value := by
  rw [WCT9.chainInput_eq_header]
  simp only [block4, bytesLE_zero']
theorem pad64_wctChainInput (index coord child t step : Nat) (value : Digest) :
    pad64 (WCT9.chainInput index coord child t step value) = WCT9.chainInput index coord child t step value := by
  rw [wctChainInput_block4, pad64_block4]
theorem hdrBlock_wctChainInput (index coord child t step : Nat) (value : Digest) :
    hdrBlock (WCT9.chainInput index coord child t step value) =
      bytesLE 16 (header 5 coord index (step + 256 * t) child) := by
  rw [wctChainInput_block4, hdrBlock_block4']
theorem hdrBlock_wctLeafInput (index coord child : Nat) (ends : List Digest) :
    hdrBlock (pad64 (wctLeafInput index coord child ends)) = bytesLE 16 (header 6 coord index 0 child) :=
  hdrBlock_listInput' _ _ _
theorem hdrBlock_forestInput (index : Nat) (roots : List Digest) :
    hdrBlock (pad64 (forestInput index roots)) = bytesLE 16 (header 15 0 index 0 0) :=
  hdrBlock_listInput' _ _ _
theorem hdrBlock_nodeInputP (tag lay tree heap : Nat) (left pad right : Digest) :
    hdrBlock (pad64 (nodeInputP tag lay tree heap left pad right)) = bytesLE 16 (header tag lay tree 0 heap) := by
  rw [pad64_nodeInputP, nodeInputP, hdrBlock_block4']
theorem hdrBlock_wotsChainInput (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    hdrBlock (chainInput lay tree leaf i step value) = bytesLE 16 (chainHeader lay tree leaf i step) := by
  exact chainInput_header _ _ _ _ _ _
theorem hdrBlock_leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    hdrBlock (pad64 (leafInput lay tree leaf ends)) = bytesLE 16 (header 2 lay.val tree 0 leaf) :=
  hdrBlock_listInput' _ _ _
theorem listInput_length' (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    (listInput first hdr rest).length = 32 + 16 * rest.length := by
  simp only [listInput, List.length_append, bytesLE_length, digest_list_bytes_length]
theorem hdrBlock_honestInput (answers : Answers) (p : Pos) :
    hdrBlock (honestInput answers p) = bytesLE 16 p.hdr := by
  cases p with
  | chain lay tree lf i step =>
      simp only [honestInput, Pos.hdr]
      rw [chainInput_padded, hdrBlock_wotsChainInput]
  | leaf lay tree lf => simp only [honestInput, Pos.hdr, leafInput]; rw [hdrBlock_listInput']
  | node lay tree level nd =>
      simp only [honestInput, Pos.hdr]; rw [hdrBlock_nodeInputP]
  | forest index => simp only [honestInput, Pos.hdr]; rw [hdrBlock_forestInput]
  | wctChain index coord child t step =>
      simp only [honestInput, Pos.hdr]; rw [pad64_wctChainInput, hdrBlock_wctChainInput]
  | wctLeaf index coord child =>
      simp only [honestInput, Pos.hdr]; rw [hdrBlock_wctLeafInput]
  | wctNode index coord level nd =>
      simp only [honestInput, Pos.hdr]; rw [hdrBlock_nodeInputP]
def Pos.fields : Pos → Nat × Nat × Nat × Nat × Nat
  | .chain lay tree lf i step => (1, lay.val, tree, step + 256 * i, lf)
  | .leaf lay tree lf => (2, lay.val, tree, 0, lf)
  | .node lay tree level nd => (3, lay.val, tree, 0, 2 ^ (height lay - level - 1) + nd)
  | .forest index => (15, 0, index, 0, 0)
  | .wctChain index coord child t step => (5, coord, index, step + 256 * t, child)
  | .wctLeaf index coord child => (6, coord, index, 0, child)
  | .wctNode index coord level nd => (11, coord, index, 0, 2 ^ (7 - level - 1) + nd)
theorem Pos.hdr_eq (p : Pos) (hn : p.fields.1 ≠ 1) :
    p.hdr = header p.fields.1 p.fields.2.1 p.fields.2.2.1 p.fields.2.2.2.1 p.fields.2.2.2.2 := by
  cases p <;> first | rfl | exact False.elim (hn rfl)
theorem heap_lt {e x : Nat} (hx : x < 2 ^ e) (he : e ≤ 12) : 2 ^ e + x < 2 ^ 32 := by
  have : 2 ^ e ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) he
  have : (2 : Nat) ^ 12 = 4096 := by norm_num
  have : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  omega
theorem heap_inj {e f x y : Nat} (hx : x < 2 ^ e) (hy : y < 2 ^ f) (h : 2 ^ e + x = 2 ^ f + y) : e = f ∧ x = y := by
  have key : ∀ {e f x y : Nat}, x < 2 ^ e → e < f → 2 ^ e + x < 2 ^ f + y := by
    intro e f x y hx hef
    have : 2 ^ (e + 1) ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hef
    rw [pow_succ] at this
    omega
  rcases Nat.lt_trichotomy e f with hlt | heq | hgt
  · exact absurd h (ne_of_lt (key hx hlt))
  · subst heq; exact ⟨rfl, by omega⟩
  · exact absurd h.symm (ne_of_lt (key hy hgt))
private theorem height_le' (lay : Layer) : height lay ≤ 12 := by fin_cases lay <;> decide
theorem Pos.fields_bounded {p : Pos} (hb : p.Bounded) :
    p.fields.1 < 256 ∧ p.fields.2.1 < 256 ∧ p.fields.2.2.1 < 2 ^ 40 ∧ p.fields.2.2.2.1 < 2 ^ 32 ∧
      p.fields.2.2.2.2 < 2 ^ 32 := by
  have hl : ∀ lay : Layer, lay.val < 256 := fun lay => lt_trans lay.isLt (by decide)
  cases p with
  | chain lay tree lf i step =>
      obtain ⟨h1, h2, h3, h4⟩ := hb
      simp only [Pos.fields]
      exact ⟨by decide, hl lay, by omega, by omega, by omega⟩
  | leaf lay tree lf =>
      simp only [Pos.fields]; exact ⟨by decide, hl lay, hb.1, by norm_num, hb.2⟩
  | node lay tree level nd =>
      obtain ⟨h1, h2, h3⟩ := hb
      simp only [Pos.fields]
      refine ⟨by decide, hl lay, h1, by norm_num, ?_⟩
      exact heap_lt h3 (le_trans (Nat.sub_le _ _) (le_trans (Nat.sub_le _ _) (height_le' lay)))
  | forest index =>
      simp only [Pos.fields]; exact ⟨by decide, by decide, hb, by norm_num, by norm_num⟩
  | wctChain index coord child t step =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hb
      simp only [Pos.fields]
      refine ⟨by decide, by omega, by omega, by omega, by omega⟩
  | wctLeaf index coord child =>
      obtain ⟨h1, h2, h3⟩ := hb
      simp only [Pos.fields]
      refine ⟨by decide, by omega, by omega, by norm_num, by omega⟩
  | wctNode index coord level nd =>
      obtain ⟨h1, h2, h3, h4⟩ := hb
      simp only [Pos.fields]
      exact ⟨by decide, by omega, by omega, by norm_num, heap_lt h4 (by omega)⟩
theorem Pos.fields_injective {p p' : Pos} (hb : p.Bounded) (hb' : p'.Bounded) (he : p.fields = p'.fields) :
    p = p' := by
  cases p <;> cases p' <;> simp only [Pos.fields, Prod.mk.injEq] at he <;>
    (try (obtain ⟨h, _⟩ := he; exact absurd h (by decide)))
  · obtain ⟨-, hl, ht, hp, hlf⟩ := he
    obtain ⟨-, -, -, hs⟩ := hb
    obtain ⟨-, -, -, hs'⟩ := hb'
    obtain ⟨h1, h2⟩ := pack_nat_injective (base := 256) (by omega : _ < 256) (by omega : _ < 256) hp
    rw [Fin.ext hl, ht, hlf, h1, h2]
  · obtain ⟨-, hl, ht, -, hlf⟩ := he
    rw [Fin.ext hl, ht, hlf]
  · obtain ⟨-, hl, ht, -, hh⟩ := he
    have hlay := Fin.ext hl
    subst hlay ht
    obtain ⟨-, h1, h2⟩ := hb
    obtain ⟨-, h1', h2'⟩ := hb'
    obtain ⟨e, x⟩ := heap_inj h2 h2' hh
    rw [x]
    congr 1
    omega
  · obtain ⟨-, -, ht, -, -⟩ := he
    rw [ht]
  · obtain ⟨-, hc, ht, hp, hj⟩ := he
    obtain ⟨-, -, -, -, hs⟩ := hb
    obtain ⟨-, -, -, -, hs'⟩ := hb'
    obtain ⟨h1, h2⟩ := pack_nat_injective (show _ < 256 by omega) (show _ < 256 by omega) hp
    rw [hc, ht, hj, h1, h2]
  · obtain ⟨-, hc, ht, -, hj⟩ := he
    rw [hc, ht, hj]
  · obtain ⟨-, hc, ht, -, hh⟩ := he
    subst hc ht
    obtain ⟨-, -, h1, h2⟩ := hb
    obtain ⟨-, -, h1', h2'⟩ := hb'
    obtain ⟨e, x⟩ := heap_inj h2 h2' hh
    rw [show _ = _ from x]
    congr 1
    omega
private theorem Pos.hdr_injective_nonchain {p p' : Pos} (hb : p.Bounded) (hb' : p'.Bounded)
    (hn : p.fields.1 ≠ 1) (hn' : p'.fields.1 ≠ 1) (h : p.hdr = p'.hdr) : p = p' := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := Pos.fields_bounded hb
  obtain ⟨b1, b2, b3, b4, b5⟩ := Pos.fields_bounded hb'
  rw [Pos.hdr_eq p hn, Pos.hdr_eq p' hn'] at h
  obtain ⟨e1, e2, e3, e4, e5⟩ := header_injective a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 h
  exact Pos.fields_injective hb hb' (Prod.ext e1 (Prod.ext e2 (Prod.ext e3 (Prod.ext e4 e5))))
theorem Pos.hdr_injective {p p' : Pos} (hb : p.Bounded) (hb' : p'.Bounded)
    (h : p.hdr = p'.hdr) : p = p' := by
  by_cases hn : p.fields.1 = 1
  · have hp : ∃ lay tree leaf i step, p = .chain lay tree leaf i step := by
      cases p <;> simp_all [Pos.fields]
    obtain ⟨lay, tree, leaf, i, step, rfl⟩ := hp
    by_cases hn' : p'.fields.1 = 1
    · have hp' : ∃ lay tree leaf i step, p' = .chain lay tree leaf i step := by
        cases p' <;> simp_all [Pos.fields]
      obtain ⟨lay', tree', leaf', i', step', rfl⟩ := hp'
      obtain ⟨ht, hf, hi, hs⟩ := hb
      obtain ⟨ht', hf', hi', hs'⟩ := hb'
      obtain ⟨hl, ht, hf, hi, hs⟩ := chainHeader_low_injective ht hf hi hs ht' hf' hi' hs'
        (congrArg (BitVec.extractLsb' 0 64) h)
      subst_vars
      rfl
    · rw [Pos.hdr_eq p' hn'] at h
      exact False.elim (chainHeader_ne_header _ _ _ _ _ _ _ _ _ _ h)
  · by_cases hn' : p'.fields.1 = 1
    · have hp' : ∃ lay tree leaf i step, p' = .chain lay tree leaf i step := by
        cases p' <;> simp_all [Pos.fields]
      obtain ⟨lay', tree', leaf', i', step', rfl⟩ := hp'
      rw [Pos.hdr_eq p hn] at h
      exact False.elim (chainHeader_ne_header _ _ _ _ _ _ _ _ _ _ h.symm)
    · exact Pos.hdr_injective_nonchain hb hb' hn hn' h
theorem Pos.canonicalHeader_eq {p : Pos} (hb : p.Bounded) :
    canonicalHeader (bytesLE 16 p.hdr) = bytesLE 16 p.hdr := by
  cases p with
  | chain lay tree leaf i step =>
      exact canonicalHeader_high_zero _
        (SigGolfCandidate.T3M.chainHeader_high_zero lay tree leaf i step hb.1 hb.2.1 hb.2.2.1 hb.2.2.2)
  | _ =>
      apply canonicalHeader_marker_ne
      simp only [Pos.hdr, header_firstByte]
      decide
noncomputable def posOf (input : HashInput) : Option Pos := by
  classical
  exact if h : ∃ p : Pos, p.Bounded ∧ canonicalHeader (hdrBlock input) = bytesLE 16 p.hdr
    then some (Classical.choose h) else none
theorem posOf_key_eq {input : HashInput} {p : Pos} (hb : p.Bounded)
    (h : canonicalHeader (hdrBlock input) = bytesLE 16 p.hdr) :
    posOf input = some p := by
  classical
  have hex : ∃ p : Pos, p.Bounded ∧ canonicalHeader (hdrBlock input) = bytesLE 16 p.hdr := ⟨p, hb, h⟩
  unfold posOf
  rw [dif_pos hex]
  have hs := Classical.choose_spec hex
  exact congrArg some (Pos.hdr_injective hs.1 hb (bytesLE_injective (hs.2.symm.trans h)))
theorem posOf_eq {input : HashInput} {p : Pos} (hb : p.Bounded)
    (h : hdrBlock input = bytesLE 16 p.hdr) : posOf input = some p := by
  apply posOf_key_eq hb
  rw [h, Pos.canonicalHeader_eq hb]
theorem hitIn_posOf {answers : Answers} {qs : List Spec.Domain} (h : HitIn answers qs) :
    ∃ pos actual, pos.Bounded ∧ .inl (.inr actual) ∈ qs ∧ posOf actual = some pos ∧
      HashHit answers (honestInput answers pos) actual := by
  obtain ⟨pos, actual, hb, hq, hh, hs⟩ := h
  refine ⟨pos, actual, hb, hq, posOf_key_eq hb ?_, hh⟩
  rw [hs, hdrBlock_honestInput, Pos.canonicalHeader_eq hb]
end ClaudeWCT.W9.T3M.Extract
