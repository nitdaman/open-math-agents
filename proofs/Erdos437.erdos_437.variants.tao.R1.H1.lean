import OMAReductions.R_Erdos437_erdos_437_variants_tao_R1
import Mathlib

/-!
The smooth-number blocking argument of Bui, Pratt and Zaharescu, as used in
Tao's treatment of Erdős 437. In each block, linear dependence of exponent
parities supplies a nonempty subcollection whose product is a square.
-/

namespace SmoothSquareBlocks

open Erdos437

lemma square_selection (y : ℕ) (A : Finset ℕ) (hsize : y.primesBelow.card < A.card)
    (hsmooth : ∀ n ∈ A, n ∈ Nat.smoothNumbers y) :
    ∃ B ⊆ A, B.Nonempty ∧ IsSquare (B.prod id) := by
  classical
  let v (n : A) : y.primesBelow → ZMod 2 := fun p => (n.val.factorization p.val : ZMod 2)
  have dep : ¬ LinearIndependent (ZMod 2) v := by
    intro h
    have := h.fintype_card_le_finrank
    simp only [Fintype.card_coe, Module.finrank_pi] at this
    omega
  obtain ⟨c, hsum, i, hi⟩ := Fintype.not_linearIndependent_iff.mp dep
  let T : Finset A := Finset.univ.filter (fun i => c i ≠ 0)
  let B := T.map (Function.Embedding.subtype (· ∈ A))
  have hsub : B ⊆ A := by
    intro n hn
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hn
    exact j.property
  refine ⟨B, hsub, ⟨i, Finset.mem_map.mpr ⟨i, by simpa [T] using hi, rfl⟩⟩, ?_⟩
  let N := B.prod id
  have hNZ : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun n hn => (hsmooth n (hsub hn)).1
  have hpar (p : ℕ) (hp : p ∈ N.primeFactors) : Even (N.factorization p) := by
    have hNsmooth : N ∈ Nat.factoredNumbers y.primesBelow := by
      apply Finset.prod_induction _ _ (fun a b ha hb => Nat.mul_mem_factoredNumbers ha hb)
        (show 1 ∈ Nat.factoredNumbers y.primesBelow from ⟨one_ne_zero, by simp⟩)
      intro n hn
      simpa [Nat.smoothNumbers_eq_factoredNumbers_primesBelow] using hsmooth n (hsub hn)
    let p' : y.primesBelow := ⟨p, Nat.primeFactors_subset_of_mem_factoredNumbers hNsmooth hp⟩
    have he := congrFun hsum p'
    change (∑ j : A, c j • v j) p' = 0 at he
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
    have hcoeff (j : A) : (if c j ≠ 0 then v j p' else 0) = c j * v j p' := by
      by_cases h : c j = 0
      · simp [h]
      · have h1 : c j = (1 : ZMod 2) := Fin.eq_one_of_ne_zero (c j) h
        rw [if_pos h, h1, one_mul]
    apply ZMod.natCast_eq_zero_iff_even.mp
    dsimp only [N]
    rw [Nat.factorization_prod (g := id) (fun n hn => (hsmooth n (hsub hn)).1)]
    simp only [Finsupp.finsetSum_apply, Nat.cast_sum]
    change (∑ j ∈ B, ((j.factorization p : ℕ) : ZMod 2)) = 0
    simpa only [B, T, Finset.sum_map, Function.Embedding.subtype_apply, Finset.sum_filter,
      ← hcoeff] using he
  change IsSquare N
  rw [Nat.prod_primeFactors_pow_factorization hNZ]
  exact Finset.isSquare_prod _ (fun p hp => (hpar p hp).isSquare_pow p)

lemma count_prepend {b s : List ℕ} (hb : b ≠ []) (hsq : IsSquare b.prod) :
    squarePartialProducts s + 1 ≤ squarePartialProducts (b ++ s) := by
  classical
  let I (a : List ℕ) := (Finset.range a.length).filter (fun i => IsSquare (a.take (i + 1)).prod)
  let shift : ℕ ↪ ℕ := ⟨fun i => b.length + i, fun _ _ => Nat.add_left_cancel⟩
  have hlen : 0 < b.length := List.length_pos_iff.mpr hb
  have hnot : b.length - 1 ∉ (I s).map shift := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
    change b.length + i = b.length - 1 at hi
    omega
  have hsub : insert (b.length - 1) ((I s).map shift) ⊆ I (b ++ s) := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · refine Finset.mem_filter.mpr ⟨by simp; omega, ?_⟩
      simpa only [Nat.sub_add_cancel hlen, List.take_append_length] using hsq
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
      obtain ⟨hlt, hi⟩ := Finset.mem_filter.mp hi
      have hi' := Finset.mem_range.mp hlt
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
      · change b.length + i < (b ++ s).length
        simpa using Nat.add_lt_add_left hi' b.length
      · change IsSquare (((b ++ s).take (b.length + i + 1)).prod)
        rw [Nat.add_assoc, List.take_length_add_append, List.prod_append]
        exact hsq.mul hi
  have := Finset.card_le_card hsub
  simpa [hnot, I, squarePartialProducts] using this

lemma extract_blocks (y : ℕ) (hy : y.primesBelow.card < y) (k : ℕ)
    (l : List ℕ) (ordered : l.Pairwise (· < ·)) (smooth : ∀ n ∈ l, n ∈ Nat.smoothNumbers y)
    (len : k * y ≤ l.length) :
    ∃ a : List ℕ, a.Pairwise (· < ·) ∧ (∀ n ∈ a, n ∈ l) ∧ k ≤ squarePartialProducts a := by
  classical
  induction k generalizing l with
  | zero => exact ⟨[], by simp, by simp, Nat.zero_le _⟩
  | succ k ih =>
    let front := l.take y
    let rest := l.drop y
    have split : front ++ rest = l := List.take_append_drop _ _
    have hpair := List.pairwise_append.mp (show (front ++ rest).Pairwise (· < ·) by simpa only [split] using ordered)
    have hle : y ≤ l.length := by rw [Nat.succ_mul] at len; omega
    have card : front.toFinset.card = y := by
      rw [List.toFinset_card_of_nodup (hpair.1.imp fun h => ne_of_lt h)]
      simp [front, hle]
    have frontMem (n : ℕ) (h : n ∈ front) : n ∈ l := List.mem_of_mem_take h
    have restMem (n : ℕ) (h : n ∈ rest) : n ∈ l := List.mem_of_mem_drop h
    obtain ⟨B, hB, hBne, hBsq⟩ := square_selection y front.toFinset (by simpa only [card] using hy)
      (fun n hn => smooth n (frontMem n (List.mem_toFinset.mp hn)))
    let b := B.sort (· ≤ ·)
    have bs : b.Pairwise (· < ·) := (Finset.sortedLT_sort B).pairwise
    have bm (n : ℕ) (hn : n ∈ b) : n ∈ front := List.mem_toFinset.mp (hB (by simpa [b] using hn))
    have bn : b ≠ [] := by
      obtain ⟨n, hn⟩ := hBne
      intro he
      have mem : n ∈ b := by simpa [b] using hn
      simp [he] at mem
    have bp : IsSquare b.prod := by
      have he := List.prod_toFinset id (bs.imp fun h => ne_of_lt h)
      have e : B.prod id = b.prod := by simpa [b] using he
      exact e ▸ hBsq
    obtain ⟨s, hs, hm, hc⟩ := ih rest hpair.2.1 (fun n hn => smooth n (restMem n hn))
      (by rw [Nat.succ_mul] at len; simp only [rest, List.length_drop]; omega)
    refine ⟨b ++ s, List.pairwise_append.mpr ⟨bs, hs, ?_⟩, ?_, ?_⟩
    · exact fun n hn m h => hpair.2.2 _ (bm n hn) _ (hm m h)
    · intro n hn
      rcases List.mem_append.mp hn with h | h
      · exact frontMem n (bm n h)
      · exact restMem n (hm n h)
    · exact (Nat.add_le_add_right hc 1).trans (count_prepend bn bp)

end SmoothSquareBlocks

theorem OMA.solution : OMA.R_Erdos437_erdos_437_variants_tao_R1.H1 := by
  classical
  intro x y hy
  let A := x.smoothNumbersUpTo y
  have py : y.primesBelow.card < y := by
    have h : y.primesBelow ⊂ Finset.range y := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
      intro eq
      have : 0 ∈ y.primesBelow := by rw [eq]; exact Finset.mem_range.mpr hy
      exact Nat.not_prime_zero (Nat.mem_primesBelow.mp this).2
    simpa using Finset.card_lt_card h
  have hL (a : List ℕ) (ha : a.Pairwise (· < ·)) (hm : ∀ n ∈ a, n ∈ A) :
      Erdos437.squarePartialProducts a ≤ Erdos437.L x := by
    unfold Erdos437.L
    apply le_csSup
    · refine ⟨x, ?_⟩
      rintro _ ⟨s, hsort, hmem, rfl⟩
      have subset : s.toFinset ⊆ Finset.Icc 1 x := fun n hn => hmem n (List.mem_toFinset.mp hn)
      have card := Finset.card_le_card subset
      rw [List.toFinset_card_of_nodup (hsort.imp fun h => ne_of_lt h), Nat.card_Icc] at card
      exact (Finset.card_filter_le _ _).trans (by simpa using card)
    · refine ⟨a, ha, ?_, rfl⟩
      intro n hn
      obtain ⟨hbound, hsm⟩ := Nat.mem_smoothNumbersUpTo.mp (hm n hn)
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hsm.1, hbound⟩
  obtain ⟨a, ha, hmem, hcount⟩ := SmoothSquareBlocks.extract_blocks y py (A.card / y)
    (A.sort (· ≤ ·)) (Finset.sortedLT_sort A).pairwise
    (fun n hn => (Nat.mem_smoothNumbersUpTo.mp (by simpa using hn : n ∈ A)).2)
    (by simpa using Nat.div_mul_le_self A.card y)
  have hq := hcount.trans (hL a ha fun n hn => by simpa using hmem n hn)
  have hlt : A.card < (Erdos437.L x + 1) * y :=
    (Nat.div_lt_iff_lt_mul hy).mp (Nat.lt_succ_of_le hq)
  exact_mod_cast hlt.le
