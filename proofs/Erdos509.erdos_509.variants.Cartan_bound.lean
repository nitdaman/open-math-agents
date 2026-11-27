import FormalConjectures.ErdosProblems.«509»
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Multiset.Fintype

/-!
# Cartan's covering bound

A greedy choice of discs covers the points with a sufficiently large local root count.
The product estimate counts roots with their multiplicities.
-/

open scoped BigOperators
open Polynomial

private noncomputable def indicesIn {α : Type*} (a : α → ℂ) (S : Finset α) (z : ℂ) (r : ℝ) :
    Finset α :=
  S.filter fun i => dist z (a i) ≤ r

private lemma mem_indicesIn {α : Type*} {a : α → ℂ} {S : Finset α} {z : ℂ}
    {r : ℝ} {i : α} : i ∈ indicesIn a S z r ↔ i ∈ S ∧ dist z (a i) ≤ r :=
  Finset.mem_filter

private lemma indicesIn_subset {α : Type*} (a : α → ℂ) (S : Finset α) (z : ℂ) (r : ℝ) :
    indicesIn a S z r ⊆ S :=
  fun _ hi => (mem_indicesIn.mp hi).1

private lemma indicesIn_mono {α : Type*} (a : α → ℂ) {S T : Finset α}
    (h : S ⊆ T) (z : ℂ) (r : ℝ) : indicesIn a S z r ⊆ indicesIn a T z r := by
  intro i hi
  obtain ⟨hiS, hir⟩ := mem_indicesIn.mp hi
  exact mem_indicesIn.mpr ⟨h hiS, hir⟩

private lemma greedy_cover {α : Type*} [DecidableEq α] (a : α → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (S : Finset α) :
    ∃ D : List (ℂ × ℝ), (∀ d ∈ D, 0 < d.2) ∧
      (D.map Prod.snd).sum ≤ 2 * δ * (S.card : ℝ) ∧
      ∀ (z : ℂ) (j : ℕ), 0 < j → j ≤ (indicesIn a S z (δ * j)).card →
        ∃ d ∈ D, dist z d.1 ≤ d.2 := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · let P (k : ℕ) := ∃ c : ℂ, k ≤ (indicesIn a S c (δ * k)).card
      obtain ⟨i, hi⟩ := hS
      have hS1 : 1 ≤ S.card := Finset.one_le_card.mpr ⟨i, hi⟩
      have hP1 : P 1 := by
        refine ⟨a i, Finset.one_le_card.mpr ⟨i, mem_indicesIn.mpr ⟨hi, ?_⟩⟩⟩
        simpa using hδ.le
      let k := Nat.findGreatest P S.card
      have hk1 : 1 ≤ k := Nat.le_findGreatest hS1 hP1
      have hk0 : 0 < k := by omega
      have hkS : k ≤ S.card := Nat.findGreatest_le (P := P) _
      obtain ⟨c, hc⟩ : P k := Nat.findGreatest_spec hS1 hP1
      obtain ⟨U, hU, hUk⟩ := Finset.exists_subset_card_eq hc
      have hUS : U ⊆ S := hU.trans (indicesIn_subset a S c (δ * k))
      let T := S \ U
      have hTcard : T.card = S.card - k := by
        rw [show T = S \ U from rfl, Finset.card_sdiff_of_subset hUS, hUk]
      have hTsub : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.sdiff_subset, fun h => by rw [h] at hTcard; omega⟩
      obtain ⟨D, hDpos, hDsum, hDcover⟩ := ih T hTsub
      let R := 2 * δ * (k : ℝ)
      have hR : 0 < R := by dsimp [R]; positivity
      refine ⟨(c, R) :: D, ?_, ?_, ?_⟩
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact hR
        · exact hDpos d hd
      · have ht : (T.card : ℝ) + k = S.card := by
          exact_mod_cast (show T.card + k = S.card by omega)
        simp only [List.map_cons, List.sum_cons]
        change R + (D.map Prod.snd).sum ≤ _
        rw [← ht, mul_add]
        dsimp [R]
        linarith
      · intro z j hj0 hj
        by_cases hhit : ∃ i ∈ U, i ∈ indicesIn a S z (δ * j)
        · obtain ⟨i, hiU, hiZ⟩ := hhit
          have hjS : j ≤ S.card := hj.trans (Finset.card_le_card (indicesIn_subset a S z (δ*j)))
          have hjk : j ≤ k := Nat.le_findGreatest hjS (show P j from ⟨z, hj⟩)
          have hzc := (mem_indicesIn.mp hiZ).2
          have hic := (mem_indicesIn.mp (hU hiU)).2
          refine ⟨(c, R), List.mem_cons_self, ?_⟩
          change dist z c ≤ R
          calc
            dist z c ≤ dist z (a i) + dist (a i) c := dist_triangle _ _ _
            _ ≤ δ * j + δ * k := add_le_add hzc (by rwa [dist_comm])
            _ ≤ R := by
              have hjkr : (j : ℝ) ≤ k := by exact_mod_cast hjk
              have := mul_le_mul_of_nonneg_left hjkr hδ.le
              dsimp [R]
              linarith
        · have hs : indicesIn a S z (δ * j) ⊆ indicesIn a T z (δ * j) := by
            intro i hi
            obtain ⟨hiS, hiz⟩ := mem_indicesIn.mp hi
            have hiU : i ∉ U := fun hm => hhit ⟨i, hm, hi⟩
            exact mem_indicesIn.mpr ⟨Finset.mem_sdiff.mpr ⟨hiS, hiU⟩, hiz⟩
          obtain ⟨d, hd, hzd⟩ := hDcover z j hj0 (hj.trans (Finset.card_le_card hs))
          exact ⟨d, List.mem_cons_of_mem _ hd, hzd⟩
    · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      refine ⟨[], by simp, by simp, ?_⟩
      intro z j hj0 hj
      simp [indicesIn] at hj
      omega

private lemma product_bound {α : Type*} [DecidableEq α] (a : α → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (z : ℂ) (S : Finset α) :
    (∀ j : ℕ, 0 < j → (indicesIn a S z (δ * j)).card < j) →
    δ ^ S.card * (S.card.factorial : ℝ) ≤ ∏ i ∈ S, dist z (a i) ∧
      (S.Nonempty → δ ^ S.card * (S.card.factorial : ℝ) < ∏ i ∈ S, dist z (a i)) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hs
    by_cases hS : S.Nonempty
    · obtain ⟨i, hi, hil⟩ : ∃ i ∈ S, δ * (S.card : ℝ) < dist z (a i) := by
        by_contra! hno
        have hall : S ⊆ indicesIn a S z (δ * S.card) := by
          intro i hi
          exact mem_indicesIn.mpr ⟨hi, hno i hi⟩
        have hlt := hs S.card (Finset.card_pos.mpr hS)
        exact (not_lt_of_ge (Finset.card_le_card hall)) hlt
      let T := S.erase i
      have htSub : T ⊂ S := Finset.erase_ssubset hi
      have htCard : T.card + 1 = S.card := Finset.card_erase_add_one hi
      have hT : ∀ j : ℕ, 0 < j → (indicesIn a T z (δ * j)).card < j := by
        intro j hj
        exact (Finset.card_le_card (indicesIn_mono a htSub.le z (δ * j))).trans_lt (hs j hj)
      have htd := (ih T htSub hT).1
      have hp : 0 < δ ^ T.card * (T.card.factorial : ℝ) := by
        exact mul_pos (pow_pos hδ _) (by exact_mod_cast Nat.factorial_pos T.card)
      have hi0 : 0 ≤ dist z (a i) := dist_nonneg
      have hsplit :
          δ ^ S.card * (S.card.factorial : ℝ) =
            (δ * (S.card : ℝ)) * (δ ^ T.card * (T.card.factorial : ℝ)) := by
        rw [← htCard, pow_succ, Nat.factorial_succ, Nat.cast_mul]
        ring
      have hprod : δ ^ S.card * (S.card.factorial : ℝ) < ∏ j ∈ S, dist z (a j) := calc
        _ = _ := hsplit
        _ < dist z (a i) * (δ ^ T.card * (T.card.factorial : ℝ)) :=
          mul_lt_mul_of_pos_right hil hp
        _ ≤ dist z (a i) * ∏ j ∈ T, dist z (a j) := mul_le_mul_of_nonneg_left htd hi0
        _ = _ := Finset.mul_prod_erase S (fun j => dist z (a j)) hi
      exact ⟨hprod.le, fun _ => hprod⟩
    · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      simp

private lemma factorial_bound (n : ℕ) (hn : 0 < n) :
    1 ≤ (Real.exp 1 / (n : ℝ)) ^ n * (n.factorial : ℝ) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hfp : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have he : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    simp [← Real.exp_nat_mul]
  have hb := Real.pow_div_factorial_le_exp (n : ℝ) hnp.le n
  rw [he] at hb
  have hmul := (div_le_iff₀ hfp).mp hb
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos hnp n)]
  simpa using hmul

theorem OMA.solution : type_of% @Erdos509.erdos_509.variants.Cartan_bound := by
  classical
  intro f hf hd
  have hn : 0 < f.natDegree := Nat.pos_of_ne_zero hd
  have hnR : (0 : ℝ) < f.natDegree := by exact_mod_cast hn
  let δ := Real.exp 1 / (f.natDegree : ℝ)
  have hδ : 0 < δ := div_pos (Real.exp_pos _) hnR
  have hscale : δ * (f.natDegree : ℝ) = Real.exp 1 := div_mul_cancel₀ _ hnR.ne'
  have hsplit : f.Splits := IsAlgClosed.splits f
  let a (i : f.roots) : ℂ := i
  let S : Finset f.roots := Finset.univ
  have hS : S.card = f.natDegree := by
    change Fintype.card f.roots = f.natDegree
    rw [Multiset.card_coe, hsplit.natDegree_eq_card_roots]
  have hEval (z : ℂ) : ‖f.eval z‖ = ∏ i ∈ S, dist z (a i) := by
    have hp : f.eval z = ∏ i ∈ S, (z - a i) := by
      rw [hsplit.eval_eq_prod_roots_of_monic hf, Finset.prod]
      change (f.roots.map (fun w : ℂ => z - w)).prod =
        ((Finset.univ : Finset f.roots).val.map (fun i : f.roots => z - (i : ℂ))).prod
      rw [Multiset.map_univ]
    simp only [hp, norm_prod, dist_eq_norm]
  obtain ⟨D, hDpos, hDsum, hDcover⟩ := greedy_cover a δ hδ S
  let C (i : Fin D.length) : ℂ := (D.get i).1
  let R (i : Fin D.length) : ℝ := (D.get i).2
  refine ⟨Fin D.length, ⟨{
    C := C
    R := R
    h_cover := ?_
    h_summable := (hasSum_fintype R).summable
    h_bdd := ?_
    h_pos := ?_ }⟩⟩
  · intro z hz
    change ‖f.eval z‖ ≤ 1 at hz
    obtain ⟨j, hj0, hj⟩ : ∃ j : ℕ, 0 < j ∧ j ≤ (indicesIn a S z (δ * j)).card := by
      by_contra! hnone
      have hne : S.Nonempty := Finset.card_pos.mp (by rw [hS]; exact hn)
      have hgt := (product_bound a δ hδ z S hnone).2 hne
      rw [hS, ← hEval] at hgt
      exact (not_lt_of_ge hz) ((factorial_bound _ hn).trans_lt hgt)
    obtain ⟨d, hdD, hzd⟩ := hDcover z j hj0 hj
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hdD
    exact Set.mem_iUnion.mpr ⟨i, Metric.mem_closedBall.mpr hzd⟩
  · rw [tsum_fintype]
    calc
      (∑ i : Fin D.length, R i) = (D.map Prod.snd).sum := by
        rw [← Fin.sum_ofFn]
        congr 1
        exact List.ofFn_getElem_eq_map D Prod.snd
      _ ≤ 2 * δ * (S.card : ℝ) := hDsum
      _ = 2 * Real.exp 1 := by rw [hS, mul_assoc, hscale]
  · intro i
    exact hDpos (D.get i) (List.get_mem D i)
