import FormalConjectures.ErdosProblems.«1130»

-- Problem: Erdős Problem 1130 — erdos sqrt
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1130.lean:184 (declaration Erdos1130.erdos_1130.variants.erdos_sqrt)
-- Credit: @koolkao (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof idea (Erdős 1947, Theorem 2): S = sum of l_k^2 satisfies S - 1 of degree 2n - 2 with
-- positive top coefficient and S = 1 at the nodes. If every interior gap had a point with S >= 1,
-- the divided difference of S - 1 over the 2n - 1 interleaved points would be <= 0, a contradiction.
-- On a gap with S < 1, Cauchy-Schwarz gives sum of |l_k| < sqrt n.

namespace OMA.E1130

open Erdos1129 Finset Polynomial

/-- Sign of the divided-difference denominator at a point of a strictly increasing sequence. -/
lemma sign_prod (v : ℕ → ℝ) (hv : StrictMono v) (i m : ℕ) (hm : i + 1 ≤ m) :
    0 < (-1 : ℝ) ^ (m - 1 - i) * ∏ j ∈ (range m).erase i, (v i - v j) := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [show i + 1 - 1 - i = 0 by omega, pow_zero, one_mul, range_add_one,
      erase_insert (by simp)]
    exact prod_pos fun j hj => sub_pos.mpr (hv (mem_range.mp hj))
  | succ m hm ih =>
    have hne : m ≠ i := by omega
    rw [range_add_one, erase_insert_of_ne hne, prod_insert (by simp),
      show m + 1 - 1 - i = (m - 1 - i) + 1 by omega, pow_succ]
    have hd : v i - v m < 0 := sub_neg.mpr (hv (by omega))
    have e : (-1 : ℝ) ^ (m - 1 - i) * (-1) * ((v i - v m) * ∏ j ∈ (range m).erase i, (v i - v j))
        = ((-1 : ℝ) ^ (m - 1 - i) * ∏ j ∈ (range m).erase i, (v i - v j)) * (-(v i - v m)) := by
      ring
    rw [e]
    exact mul_pos ih (by linarith)

/-- The polynomial `S = ∑ l_k ^ 2`. -/
noncomputable def Spoly {n : ℕ} (x : Fin n → ℝ) : ℝ[X] :=
  ∑ k, (Lagrange.basis univ x k) ^ 2

lemma eval_basis_node {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x) (k j : Fin n) :
    (Lagrange.basis univ x k).eval (x j) = if k = j then 1 else 0 := by
  split_ifs with h
  · subst h; exact Lagrange.eval_basis_self hx.injOn (mem_univ _)
  · exact Lagrange.eval_basis_of_ne h (mem_univ _)

lemma eval_Spoly_node {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x) (j : Fin n) :
    (Spoly x).eval (x j) = 1 := by
  rw [Spoly, eval_finsetSum]
  simp only [eval_pow, eval_basis_node x hx]
  rw [sum_eq_single j (fun b _ hb => by rw [if_neg hb]; norm_num) (by simp)]
  simp

lemma lebesgue_node {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x) (j : Fin n) :
    lebesgueFunction x (x j) = 1 := by
  simp only [lebesgueFunction, eval_basis_node x hx]
  rw [sum_eq_single j (fun b _ hb => by rw [if_neg hb]; norm_num) (by simp)]
  simp

lemma natDegree_basis' {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x) (k : Fin n) :
    (Lagrange.basis univ x k).natDegree = n - 1 := by
  rw [Lagrange.natDegree_basis hx.injOn (mem_univ _), card_univ, Fintype.card_fin]

lemma coeff_sq_basis {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x) (k : Fin n) :
    0 < ((Lagrange.basis univ x k) ^ 2).coeff (2 * n - 2) := by
  have hne : Lagrange.basis univ x k ≠ 0 := Lagrange.basis_ne_zero hx.injOn (mem_univ _)
  have hd : ((Lagrange.basis univ x k) ^ 2).natDegree = 2 * n - 2 := by
    rw [natDegree_pow, natDegree_basis' x hx]; omega
  rw [← hd, coeff_natDegree, leadingCoeff_pow]
  exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (leadingCoeff_ne_zero.mpr hne)))

lemma natDegree_P {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x) :
    (Spoly x - 1).natDegree ≤ 2 * n - 2 := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine natDegree_pow_le.trans ?_
  rw [natDegree_basis' x hx]; omega

lemma coeff_P_pos {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : Function.Injective x) :
    0 < (Spoly x - 1).coeff (2 * n - 2) := by
  rw [coeff_sub, coeff_one, if_neg (by omega), sub_zero, Spoly, finsetSum_coeff]
  have : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  exact sum_pos (fun k _ => coeff_sq_basis x hx k) this

/-- Erdős: some interior gap has `S < 1` on its interior. -/
lemma good_gap (n : ℕ) (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : StrictMono x) :
    ∃ i : ℕ, ∃ h : i + 1 < n, ∀ t, x ⟨i, by omega⟩ < t → t < x ⟨i + 1, h⟩ →
      (Spoly x).eval t < 1 := by
  by_contra hcon
  simp only [not_exists, not_forall, not_lt] at hcon
  set X : ℕ → ℝ := fun k => if h : k < n then x ⟨k, h⟩ else x ⟨n - 1, by omega⟩ + 1 + k with hX
  have hXX : ∀ k, X k < X (k + 1) := by
    intro k
    simp only [hX]
    by_cases h1 : k + 1 < n
    · rw [dif_pos (by omega), dif_pos h1]
      exact hx (Fin.mk_lt_mk.mpr (by omega))
    · rw [dif_neg h1]
      by_cases h2 : k < n
      · rw [dif_pos h2]
        have : k = n - 1 := by omega
        subst this
        have : (0 : ℝ) ≤ ((n - 1 + 1 : ℕ) : ℝ) := by positivity
        linarith
      · rw [dif_neg h2]; push_cast; linarith
  have hy : ∀ k, ∃ t, X k < t ∧ t < X (k + 1) ∧ (k + 1 < n → 1 ≤ (Spoly x).eval t) := by
    intro k
    by_cases h : k + 1 < n
    · obtain ⟨t, h1, h2, h3⟩ := hcon k h
      refine ⟨t, ?_, ?_, fun _ => h3⟩
      · simp only [hX, dif_pos (show k < n by omega)]; exact h1
      · simp only [hX, dif_pos h]; exact h2
    · refine ⟨(X k + X (k + 1)) / 2, by linarith [hXX k], by linarith [hXX k], fun h' => absurd h' h⟩
  choose Y hY1 hY2 hY3 using hy
  set v : ℕ → ℝ := fun j => if j % 2 = 0 then X (j / 2) else Y (j / 2) with hv
  have hvmono : StrictMono v := by
    refine strictMono_nat_of_lt_succ fun j => ?_
    rcases Nat.even_or_odd' j with ⟨k, rfl | rfl⟩
    · simp only [hv, show 2 * k % 2 = 0 by omega, show (2 * k + 1) % 2 = 1 by omega,
        show 2 * k / 2 = k by omega, show (2 * k + 1) / 2 = k by omega]
      simpa using hY1 k
    · simp only [hv, show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1 + 1) % 2 = 0 by omega,
        show (2 * k + 1) / 2 = k by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
      simpa using hY2 k
  have hdeg : (Spoly x - 1).degree < #(range (2 * n - 1)) := by
    rw [card_range]
    refine (degree_le_of_natDegree_le (natDegree_P x hx.injective)).trans_lt ?_
    exact_mod_cast (show 2 * n - 2 < 2 * n - 1 by omega)
  have key := Lagrange.coeff_eq_sum hvmono.injective.injOn hdeg
  rw [card_range, show 2 * n - 1 - 1 = 2 * n - 2 by omega] at key
  have hpos := coeff_P_pos hn x hx.injective
  have hle : ∑ j ∈ range (2 * n - 1), (Spoly x - 1).eval (v j) /
      ∏ l ∈ (range (2 * n - 1)).erase j, (v j - v l) ≤ 0 := by
    refine sum_nonpos fun j hj => ?_
    have hj' := mem_range.mp hj
    rcases Nat.even_or_odd' j with ⟨k, rfl | rfl⟩
    · have hk : k < n := by omega
      have : v (2 * k) = x ⟨k, hk⟩ := by
        simp only [hv, hX, show 2 * k % 2 = 0 by omega, show 2 * k / 2 = k by omega,
          if_true, dif_pos hk]
      rw [this, eval_sub, eval_Spoly_node x hx.injective, eval_one, sub_self, zero_div]
    · have hk : k + 1 < n := by omega
      have hval : 0 ≤ (Spoly x - 1).eval (v (2 * k + 1)) := by
        simp only [hv, show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega]
        simp only [eval_sub, eval_one, one_ne_zero, if_false]
        linarith [hY3 k hk]
      have hs := sign_prod v hvmono (2 * k + 1) (2 * n - 1) (by omega)
      rw [show 2 * n - 1 - 1 - (2 * k + 1) = 2 * (n - k - 2) + 1 by omega, pow_succ,
        pow_mul] at hs
      norm_num at hs
      exact div_nonpos_of_nonneg_of_nonpos hval (by linarith)
  linarith

theorem main (n : ℕ) (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : IsNodeSet x) :
    Erdos1130.upsilon x < Real.sqrt n := by
  obtain ⟨i, hi, hS⟩ := good_gap n hn x hx.1
  have hle : Erdos1130.upsilon x ≤ gapMax x (i + 1) := by
    unfold Erdos1130.upsilon
    exact ciInf_le (Set.finite_range _).bddBelow (⟨i + 1, by omega⟩ : Fin (n + 1))
  refine hle.trans_lt ?_
  have e1 : extendedNodes x (i + 1) = x ⟨i, by omega⟩ := by
    rw [extendedNodes, dif_pos ⟨by omega, by omega⟩]
    exact congrArg x (Fin.ext (by simp))
  have e2 : extendedNodes x (i + 1 + 1) = x ⟨i + 1, hi⟩ := by
    rw [extendedNodes, dif_pos ⟨by omega, by omega⟩]
    exact congrArg x (Fin.ext (by simp))
  have hab : x ⟨i, by omega⟩ < x ⟨i + 1, hi⟩ := hx.1 (Fin.mk_lt_mk.mpr (by omega))
  have hcont : Continuous (lebesgueFunction x) := by
    unfold lebesgueFunction
    exact continuous_finsetSum _ fun k _ => (Polynomial.continuous _).abs
  have h1n : (1 : ℝ) < Real.sqrt n := by
    rw [Real.lt_sqrt zero_le_one]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [gapMax, e1, e2, isCompact_Icc.sSup_lt_iff_of_continuous (Set.nonempty_Icc.mpr hab.le)
    hcont.continuousOn]
  rintro t ⟨ht1, ht2⟩
  rcases ht1.eq_or_lt with h | h
  · rw [← h, lebesgue_node x hx.1.injective]; exact h1n
  rcases ht2.eq_or_lt with h' | h'
  · rw [h', lebesgue_node x hx.1.injective]; exact h1n
  have hSt := hS t h h'
  have hL0 : 0 ≤ lebesgueFunction x t :=
    sum_nonneg fun k _ => abs_nonneg _
  rw [Real.lt_sqrt hL0]
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n)))
    (f := fun k => |(Lagrange.basis univ x k).eval t|)
  simp only [sq_abs, card_univ, Fintype.card_fin] at hcs
  have hSe : (Spoly x).eval t = ∑ k, ((Lagrange.basis univ x k).eval t) ^ 2 := by
    simp [Spoly, eval_finsetSum]
  have hnpos : (0 : ℝ) < n := by positivity
  calc lebesgueFunction x t ^ 2 ≤ n * (Spoly x).eval t := by
        rw [hSe]; exact hcs
    _ < n * 1 := mul_lt_mul_of_pos_left hSt hnpos
    _ = n := mul_one _

end OMA.E1130

theorem OMA.solution : type_of% @Erdos1130.erdos_1130.variants.erdos_sqrt := by
  intro n hn x hx
  exact OMA.E1130.main n hn x hx

