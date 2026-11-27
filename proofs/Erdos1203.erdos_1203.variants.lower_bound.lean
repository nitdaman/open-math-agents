import FormalConjectures.ErdosProblems.«1203»

-- Problem: Erdős Problem 1203 — lower bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1203.lean:53 (declaration Erdos1203.erdos_1203.variants.lower_bound)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Erdős Problem 1203: `F n ≥ 1 - o(1)`

Here `F n = ⨆ k, ω (n + k) * (log (log k) / log k)`.

Two things have to be shown.

* The supremum is a supremum of a bounded family (otherwise it would be `0` by convention).
  A number `m ≥ 1` with `r` distinct prime factors is at least `r !`, and `r ! ≥ (r / e) ^ r`,
  so `r * (log r - 1) ≤ log m`. For `k ≥ max n 3` this gives `ω (n + k) * log (log k) ≤ 6 * log k`.
  The finitely many smaller `k` are bounded by the sum of their absolute values.

* A good `k`. Take `n + k = lcm (1, …, n)`, so that `ω (n + k) = π n` and
  `log (n + k) = ψ n`. Chebyshev's bounds `n * log 2 - log (n + 1) ≤ ψ n ≤ π n * log n`
  and the monotonicity of `log x / x` give
  `π n * (log (log k) / log k) ≥ π n * (log (ψ n) / ψ n) ≥ log (ψ n) / log n ≥ 1 - ε`
  once `log n` is large compared with `1 / ε`.
-/

open Filter Real
open scoped ArithmeticFunction.omega

namespace OMAaux

/-- The factorial of the size of a set of positive integers is at most their product. -/
lemma factorial_card_le_prod (S : Finset ℕ) :
    (∀ s ∈ S, 1 ≤ s) → S.card.factorial ≤ ∏ s ∈ S, s := by
  refine Finset.induction_on_max S ?_ ?_
  · intro _
    simp
  · intro a S ha ih h
    have hnot : a ∉ S := fun hmem => lt_irrefl a (ha a hmem)
    have hih := ih (fun s hs => h s (Finset.mem_insert_of_mem hs))
    have hsub : S ⊆ Finset.Ico 1 a := fun s hs =>
      Finset.mem_Ico.mpr ⟨h s (Finset.mem_insert_of_mem hs), ha s hs⟩
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hc
    have ha1 : 1 ≤ a := h a (Finset.mem_insert_self a S)
    have hcard : S.card + 1 ≤ a := by omega
    rw [Finset.card_insert_of_notMem hnot, Finset.prod_insert hnot, Nat.factorial_succ]
    exact Nat.mul_le_mul hcard hih

/-- A positive integer with `r` distinct prime factors is at least `r !`. -/
lemma factorial_omega_le (m : ℕ) (hm : 1 ≤ m) : (ω m).factorial ≤ m := by
  have h1 : ω m = m.primeFactors.card := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]
  rw [h1]
  refine le_trans (factorial_card_le_prod m.primeFactors ?_)
    (Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m))
  intro p hp
  exact (Nat.prime_of_mem_primeFactors hp).pos

/-- If `log (r !) ≤ 2 * L` with `L ≥ 1`, then `r * log L ≤ 6 * L`. -/
lemma key_bound (r : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hfac : Real.log (r.factorial : ℝ) ≤ 2 * L) : (r : ℝ) * Real.log L ≤ 6 * L := by
  have hL0 : 0 < L := by linarith
  have hl : 0 ≤ Real.log L := Real.log_nonneg hL
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp only [Nat.cast_zero, zero_mul]
    positivity
  have hx : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hx0 : (0 : ℝ) < r := by linarith
  -- `r * log r ≤ r + log (r !)`, from `r ^ r / r ! ≤ exp r`
  have h1 : (r : ℝ) * Real.log r ≤ r + Real.log (r.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (r : ℝ) hx0.le r
    have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
    rw [div_le_iff₀ hf] at h
    have h2 := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at h2
    exact h2
  have h3 : (r : ℝ) * (Real.log r - 1) ≤ 2 * L := by linarith
  rcases le_or_gt (Real.log L / 2) (Real.log r - 1) with hc | hc
  · have h4 : (r : ℝ) * (Real.log L / 2) ≤ r * (Real.log r - 1) :=
      mul_le_mul_of_nonneg_left hc hx0.le
    linarith
  · have hs : 0 < √L := Real.sqrt_pos.mpr hL0
    have hsq : √L * √L = L := Real.mul_self_sqrt hL0.le
    have h5 : Real.log L ≤ 2 * √L := by
      have h := Real.log_le_sub_one_of_pos hs
      rw [Real.log_sqrt hL0.le] at h
      linarith
    have h6 : (r : ℝ) < 3 * √L := by
      have h7 : Real.log r < 1 + Real.log L / 2 := by linarith
      have h8 : (r : ℝ) < Real.exp (1 + Real.log L / 2) := by
        have h := Real.exp_lt_exp.mpr h7
        rwa [Real.exp_log hx0] at h
      rw [Real.exp_add, Real.exp_half, Real.exp_log hL0] at h8
      have h9 : Real.exp 1 * √L ≤ 3 * √L :=
        mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hs.le
      linarith
    calc (r : ℝ) * Real.log L ≤ (3 * √L) * (2 * √L) :=
          mul_le_mul h6.le h5 hl (by positivity)
      _ = 6 * (√L * √L) := by ring
      _ = 6 * L := by rw [hsq]

/-- The family whose supremum is `F n` is bounded above. -/
lemma bddAbove_range (n : ℕ) :
    BddAbove (Set.range fun k : ℕ =>
      (ω (n + k) : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))) := by
  refine ⟨6 + ∑ j ∈ Finset.range (n + 3),
    |(ω (n + j) : ℝ) * (Real.log (Real.log (j : ℝ)) / Real.log (j : ℝ))|, ?_⟩
  rintro _ ⟨k, rfl⟩
  have hsum : 0 ≤ ∑ j ∈ Finset.range (n + 3),
      |(ω (n + j) : ℝ) * (Real.log (Real.log (j : ℝ)) / Real.log (j : ℝ))| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  by_cases hk : k < n + 3
  · have h1 := Finset.single_le_sum
      (f := fun j : ℕ => |(ω (n + j) : ℝ) * (Real.log (Real.log (j : ℝ)) / Real.log (j : ℝ))|)
      (fun i _ => abs_nonneg _) (Finset.mem_range.mpr hk)
    have h2 := le_abs_self ((ω (n + k) : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)))
    simp only at h1 ⊢
    linarith
  · have hk' : n + 3 ≤ k := not_lt.mp hk
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (by omega : 3 ≤ k)
    have hL : 1 ≤ Real.log (k : ℝ) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith [Real.exp_one_lt_three]
    have hfac : Real.log (((ω (n + k)).factorial : ℕ) : ℝ) ≤ 2 * Real.log (k : ℝ) := by
      have h1 : (ω (n + k)).factorial ≤ n + k := factorial_omega_le (n + k) (by omega)
      have h1' : (((ω (n + k)).factorial : ℕ) : ℝ) ≤ ((n + k : ℕ) : ℝ) := by exact_mod_cast h1
      have hnk : (n : ℝ) ≤ k := by exact_mod_cast (by omega : n ≤ k)
      have h2 : (((ω (n + k)).factorial : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
        push_cast at h1'
        linarith
      have h3 : Real.log (((ω (n + k)).factorial : ℕ) : ℝ) ≤ Real.log (2 * (k : ℝ)) :=
        Real.log_le_log (by exact_mod_cast Nat.factorial_pos _) h2
      rw [Real.log_mul (by norm_num) (by positivity)] at h3
      have h4 : Real.log 2 ≤ Real.log (k : ℝ) := Real.log_le_log (by norm_num) (by linarith)
      linarith
    have key := key_bound (ω (n + k)) (Real.log (k : ℝ)) hL hfac
    have hLpos : 0 < Real.log (k : ℝ) := by linarith
    have h6 : (ω (n + k) : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)) ≤ 6 := by
      rw [← mul_div_assoc, div_le_iff₀ hLpos]
      exact key
    simp only
    linarith

/-- `(n + 1) * (n + 27) ≤ 2 ^ n` for `n ≥ 9`. -/
lemma pow_bound (n : ℕ) (hn : 9 ≤ n) : (n + 1) * (n + 27) ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    nlinarith

/-- The choice `n + k = lcm (1, …, n)` makes the `k`-th term at least `1 - ε`. -/
lemma witness (ε : ℝ) (n : ℕ) (hn : 9 ≤ n)
    (hlog : -Real.log (Real.log 2 / 2) ≤ ε * Real.log (n : ℝ)) :
    1 - ε ≤ (ω (n + (n.lcmUpto - n)) : ℝ) *
      (Real.log (Real.log ((n.lcmUpto - n : ℕ) : ℝ)) / Real.log ((n.lcmUpto - n : ℕ) : ℝ)) := by
  have hp := pow_bound n hn
  -- `n + 27 ≤ lcm (1, …, n)`
  have hlcm : n + 27 ≤ n.lcmUpto := by
    have h := Chebyshev.two_pow_le_mul_lcmUpto n
    exact Nat.le_of_mul_le_mul_left (le_trans hp h) (Nat.succ_pos n)
  have hadd : n + (n.lcmUpto - n) = n.lcmUpto := Nat.add_sub_of_le (by omega)
  have hk27 : 27 ≤ n.lcmUpto - n := by omega
  have hkle : n.lcmUpto - n ≤ n.lcmUpto := Nat.sub_le _ _
  -- `ω (lcm (1, …, n)) = π n`
  have hω : ω (n + (n.lcmUpto - n)) = n.primeCounting := by
    rw [hadd, ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
    exact (congrArg Finset.card (Nat.primeFactors_lcmUpto n)).trans
      (Nat.primesLE_card_eq_primeCounting n)
  rw [hω]
  -- notation: `T = ψ n = log (lcm)`, `L = log k`
  have hT1 := Chebyshev.psi_le_primeCounting_mul_log n
  have hT2 := Chebyshev.psi_ge n
  have hTeq := Chebyshev.psi_eq_log_lcmUpto n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  -- `log (n + 1) ≤ n * log 2 / 2`, from `(n + 1) ^ 2 ≤ 2 ^ n`
  have hlog1 : Real.log ((n : ℝ) + 1) ≤ n * Real.log 2 / 2 := by
    have h1 : (n + 1) ^ 2 ≤ 2 ^ n := by nlinarith
    have h2 : ((n : ℝ) + 1) ^ 2 ≤ (2 : ℝ) ^ n := by exact_mod_cast h1
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_pow, Real.log_pow] at h3
    push_cast at h3
    linarith
  -- `ψ n ≥ (log 2 / 2) * n`
  have hTc : Real.log 2 / 2 * (n : ℝ) ≤ Chebyshev.psi (n : ℝ) := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hTpos : 0 < Chebyshev.psi (n : ℝ) := lt_of_lt_of_le (by positivity) hTc
  -- `exp 1 ≤ log k ≤ ψ n`
  have hkR : (27 : ℝ) ≤ ((n.lcmUpto - n : ℕ) : ℝ) := by exact_mod_cast hk27
  have hkpos : (0 : ℝ) < ((n.lcmUpto - n : ℕ) : ℝ) := by linarith
  have hexp3 : Real.exp (Real.exp 1) < 27 := by
    have h1 : Real.exp (Real.exp 1) < Real.exp 3 := Real.exp_lt_exp.mpr Real.exp_one_lt_three
    have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h3 : Real.exp 1 ^ 3 < 3 ^ 3 :=
      pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num)
    rw [h2] at h1
    linarith
  have hL1 : Real.exp 1 ≤ Real.log ((n.lcmUpto - n : ℕ) : ℝ) := by
    rw [Real.le_log_iff_exp_le hkpos]
    linarith
  have hLT : Real.log ((n.lcmUpto - n : ℕ) : ℝ) ≤ Chebyshev.psi (n : ℝ) := by
    rw [hTeq]
    exact Real.log_le_log hkpos (by exact_mod_cast hkle)
  have hT3 : Real.exp 1 ≤ Chebyshev.psi (n : ℝ) := le_trans hL1 hLT
  -- monotonicity of `log x / x`
  have hanti : Real.log (Chebyshev.psi (n : ℝ)) / Chebyshev.psi (n : ℝ) ≤
      Real.log (Real.log ((n.lcmUpto - n : ℕ) : ℝ)) / Real.log ((n.lcmUpto - n : ℕ) : ℝ) :=
    Real.log_div_self_antitoneOn (Set.mem_Ici.mpr hL1) (Set.mem_Ici.mpr hT3) hLT
  -- `log (ψ n) ≥ (1 - ε) * log n`
  have hlogT : (1 - ε) * Real.log (n : ℝ) ≤ Real.log (Chebyshev.psi (n : ℝ)) := by
    have h1 : Real.log (Real.log 2 / 2 * (n : ℝ)) ≤ Real.log (Chebyshev.psi (n : ℝ)) :=
      Real.log_le_log (by positivity) hTc
    rw [Real.log_mul (by positivity) hn0.ne'] at h1
    linarith
  have hlogT0 : 0 ≤ Real.log (Chebyshev.psi (n : ℝ)) :=
    Real.log_nonneg (le_trans (by linarith [Real.add_one_le_exp 1]) hT3)
  have hπ : (0 : ℝ) ≤ (n.primeCounting : ℝ) := Nat.cast_nonneg _
  -- chain the inequalities
  calc 1 - ε ≤ Real.log (Chebyshev.psi (n : ℝ)) / Real.log (n : ℝ) := by
        rw [le_div_iff₀ hlogn]
        exact hlogT
    _ ≤ (n.primeCounting : ℝ) * (Real.log (Chebyshev.psi (n : ℝ)) / Chebyshev.psi (n : ℝ)) := by
        rw [← mul_div_assoc, div_le_div_iff₀ hlogn hTpos]
        nlinarith
    _ ≤ (n.primeCounting : ℝ) * (Real.log (Real.log ((n.lcmUpto - n : ℕ) : ℝ)) /
          Real.log ((n.lcmUpto - n : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hanti hπ

end OMAaux

theorem OMA.solution : type_of% @Erdos1203.erdos_1203.variants.lower_bound := by
  intro ε hε
  have h1 : ∀ᶠ n : ℕ in atTop, -Real.log (Real.log 2 / 2) ≤ ε * Real.log (n : ℝ) := by
    have ht : Tendsto (fun n : ℕ => ε * Real.log (n : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop hε (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact ht.eventually_ge_atTop _
  filter_upwards [h1, eventually_ge_atTop 9] with n hn1 hn9
  have hw := OMAaux.witness ε n hn9 hn1
  have hb := le_ciSup (OMAaux.bddAbove_range n) (n.lcmUpto - n)
  show 1 - ε ≤ Erdos1203.F n
  unfold Erdos1203.F
  exact le_trans hw hb
