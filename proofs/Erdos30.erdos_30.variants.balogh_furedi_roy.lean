import FormalConjectures.ErdosProblems.«30»

-- Problem: Erdős Problem 30 — balogh furedi roy
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/30.lean:97 (declaration Erdos30.erdos_30.variants.balogh_furedi_roy)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Balogh, Füredi and Roy: h(N) ≤ √N + 0.998 N^{1/4} for large N.
-- Proved here from a stronger explicit bound, h(N) ≤ √N + (49/50) N^{1/4} for N ≥ 10^8, obtained by an
-- independent weighted Erdős–Turán argument (two-step window, four-block test function).

-- A weighted Erdős–Turán argument with a two-step window.
--
-- Let A ⊆ {1, …, N} be a Sidon set with k elements and let t ≥ 1. Give every integer window start j
-- the weight U_a(j) = [a - 2t < j ≤ a] + 2 [a - t < j ≤ a] of an element a (so a window of length 2t
-- sees a with weight 3 in its first half and 1 in its second half) and put B_j = Σ_{a ∈ A} U_a(j).
--   * Σ_j B_j² = Σ_{a,b} corr(a,b) with corr(a,b) ≤ c(|a - b|), c(0) = 10t and Σ_{d=1}^{2t} c(d) = 8t² - 5t.
--     Distinct pairs of a Sidon set have distinct differences, so Σ_j B_j² ≤ 10tk + 16t².
--   * For the test function φ = 14, 50, 38, 42 on the four blocks (-2t,-t], (-t,0], (0,t], (t,2t] and 41
--     afterwards, Σ_j φ_j U_a(j) ≥ 164 t for every a in [1, N], and Σ_j φ_j² = 1681 N + 2542 t.
-- Cauchy–Schwarz gives (164 t k)² ≤ (1681 N + 2542 t)(16 t² + 10 t k), and t ≈ (16/25) N^{3/4} yields
-- k ≤ √N + 0.9722 N^{1/4} + O(1); we prove k ≤ √N + (49/50) N^{1/4} for N ≥ 10^8.

namespace OMA.Sidon

open Finset

/-- Indicator of the integer interval `(c, d]`. -/
def ind (c d j : ℤ) : ℤ := if c < j ∧ j ≤ d then 1 else 0

lemma ind_mul (c d c' d' j : ℤ) :
    ind c d j * ind c' d' j = ind (max c c') (min d d') j := by
  unfold ind
  by_cases h1 : c < j ∧ j ≤ d
  · by_cases h2 : c' < j ∧ j ≤ d'
    · have h3 : max c c' < j ∧ j ≤ min d d' := ⟨max_lt h1.1 h2.1, le_min h1.2 h2.2⟩
      rw [if_pos h1, if_pos h2, if_pos h3, mul_one]
    · have h3 : ¬ (max c c' < j ∧ j ≤ min d d') := fun h =>
        h2 ⟨lt_of_le_of_lt (le_max_right _ _) h.1, h.2.trans (min_le_right _ _)⟩
      rw [if_pos h1, if_neg h2, if_neg h3, mul_zero]
  · have h3 : ¬ (max c c' < j ∧ j ≤ min d d') := fun h =>
      h1 ⟨lt_of_le_of_lt (le_max_left _ _) h.1, h.2.trans (min_le_left _ _)⟩
    rw [if_neg h1, if_neg h3, zero_mul]

lemma sum_ind (lo hi c d : ℤ) :
    ∑ j ∈ Ioc lo hi, ind c d j = ((min hi d - max lo c).toNat : ℤ) := by
  have hf : (Ioc lo hi).filter (fun j => c < j ∧ j ≤ d) = Ioc (max lo c) (min hi d) := by
    ext j
    simp only [mem_filter, mem_Ioc, max_lt_iff, le_min_iff]
    tauto
  unfold ind
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, hf, Int.card_Ioc]
  simp

/-- The test function. -/
def phi (t j : ℤ) : ℤ :=
  41 - 27 * ind (-2 * t) (-t) j + 9 * ind (-t) 0 j - 3 * ind 0 t j + ind t (2 * t) j

/-- The weight that the window starting at `j` gives to the element `a`. -/
def U (t a j : ℤ) : ℤ := ind (a - 2 * t) a j + 2 * ind (a - t) a j

lemma cover (t N a : ℤ) (ht : 0 < t) (ha1 : 1 ≤ a) (haN : a ≤ N) :
    164 * t ≤ ∑ j ∈ Ioc (-2 * t) N, phi t j * U t a j := by
  have e : ∀ j, phi t j * U t a j =
      41 * ind (a - 2 * t) a j + 82 * ind (a - t) a j
      - 27 * ind (max (-2 * t) (a - 2 * t)) (min (-t) a) j
      - 54 * ind (max (-2 * t) (a - t)) (min (-t) a) j
      + 9 * ind (max (-t) (a - 2 * t)) (min 0 a) j
      + 18 * ind (max (-t) (a - t)) (min 0 a) j
      - 3 * ind (max 0 (a - 2 * t)) (min t a) j
      - 6 * ind (max 0 (a - t)) (min t a) j
      + ind (max t (a - 2 * t)) (min (2 * t) a) j
      + 2 * ind (max t (a - t)) (min (2 * t) a) j := by
    intro j
    simp only [← ind_mul]
    unfold phi U
    ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_ind]
  rcases le_or_gt a t with h1 | h1
  · simp (disch := omega) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right,
      Int.toNat_of_nonneg, Int.toNat_of_nonpos, Nat.cast_zero]
    omega
  rcases le_or_gt a (2 * t) with h2 | h2
  · simp (disch := omega) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right,
      Int.toNat_of_nonneg, Int.toNat_of_nonpos, Nat.cast_zero]
    omega
  rcases le_or_gt a (3 * t) with h3 | h3
  · simp (disch := omega) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right,
      Int.toNat_of_nonneg, Int.toNat_of_nonpos, Nat.cast_zero]
    omega
  rcases le_or_gt a (4 * t) with h4 | h4
  · simp (disch := omega) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right,
      Int.toNat_of_nonneg, Int.toNat_of_nonpos, Nat.cast_zero]
    omega
  · simp (disch := omega) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right,
      Int.toNat_of_nonneg, Int.toNat_of_nonpos, Nat.cast_zero]
    omega

lemma phi_sq (t j : ℤ) (ht : 0 ≤ t) :
    phi t j ^ 2 = 1681 - 1485 * ind (-2 * t) (-t) j + 819 * ind (-t) 0 j
      - 237 * ind 0 t j + 83 * ind t (2 * t) j := by
  unfold phi ind
  split_ifs <;> first | omega | norm_num

lemma sum_phi_sq (t N : ℤ) (ht : 0 < t) (hN : 2 * t ≤ N) :
    ∑ j ∈ Ioc (-2 * t) N, phi t j ^ 2 = 1681 * N + 2542 * t := by
  simp only [phi_sq t _ ht.le, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_ind, Finset.sum_const, Int.card_Ioc, nsmul_eq_mul]
  omega

/-- The autocorrelation of the window. -/
def cc (t d : ℤ) : ℤ := if d ≤ t then 10 * t - 7 * d else if d ≤ 2 * t then 3 * (2 * t - d) else 0

lemma corr_le (t N a b : ℤ) (ht : 0 < t) (ha1 : 1 ≤ a) (hab : a ≤ b) (hbN : b ≤ N) :
    ∑ j ∈ Ioc (-2 * t) N, U t a j * U t b j ≤ cc t (b - a) := by
  have e : ∀ j, U t a j * U t b j =
      ind (max (a - 2 * t) (b - 2 * t)) (min a b) j
      + 2 * ind (max (a - 2 * t) (b - t)) (min a b) j
      + 2 * ind (max (a - t) (b - 2 * t)) (min a b) j
      + 4 * ind (max (a - t) (b - t)) (min a b) j := by
    intro j
    simp only [← ind_mul]
    unfold U
    ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, sum_ind]
  unfold cc
  split_ifs <;> omega

lemma lin_sum (x β : ℤ) :
    ∀ n : ℕ, 2 * ∑ k ∈ Finset.range n, (x + β * k) = 2 * n * x + β * n * (n - 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

lemma cc_sum (t : ℕ) :
    ∑ e ∈ Finset.range (2 * t), cc t ((e : ℤ) + 1) = 8 * (t : ℤ) ^ 2 - 5 * t := by
  rw [two_mul, Finset.sum_range_add]
  have h1 : ∀ e ∈ Finset.range t, cc t ((e : ℤ) + 1) = (10 * (t : ℤ) - 7) + (-7) * e := by
    intro e he
    have := Finset.mem_range.1 he
    unfold cc
    rw [if_pos (by omega)]
    ring
  have h2 : ∀ e ∈ Finset.range t, cc t (((t + e : ℕ) : ℤ) + 1) = (3 * (t : ℤ) - 3) + (-3) * e := by
    intro e he
    have := Finset.mem_range.1 he
    unfold cc
    rw [if_neg (by push_cast; omega), if_pos (by push_cast; omega)]
    push_cast
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  have a1 := lin_sum (10 * (t : ℤ) - 7) (-7) t
  have a2 := lin_sum (3 * (t : ℤ) - 3) (-3) t
  nlinarith [a1, a2]

/-- Distinct pairs of a Sidon set have distinct differences, so a sum over pairs of a function of
the difference is bounded by the sum of that function over all differences. -/
lemma pair_bound (A : Finset ℕ) (hS : IsSidon (A : Set ℕ)) (F : ℕ → ℕ → ℤ) (g : ℕ → ℤ) (d0 : ℤ)
    (n : ℕ) (hsymm : ∀ a b, F a b = F b a) (hdiag : ∀ a ∈ A, F a a ≤ d0)
    (hoff : ∀ a ∈ A, ∀ b ∈ A, a < b → F a b ≤ g (b - a - 1))
    (hg0 : ∀ e, 0 ≤ g e) (hgz : ∀ e, n ≤ e → g e = 0) :
    ∑ a ∈ A, ∑ b ∈ A, F a b ≤ A.card * d0 + 2 * ∑ e ∈ Finset.range n, g e := by
  rw [← Finset.sum_product' (f := F), ← Finset.diag_union_offDiag A,
    Finset.sum_union (Finset.disjoint_diag_offDiag A)]
  have h1 : ∑ p ∈ A.diag, F p.1 p.2 ≤ A.card * d0 := by
    rw [Finset.sum_diag]
    calc ∑ a ∈ A, F a a ≤ ∑ _a ∈ A, d0 := Finset.sum_le_sum hdiag
      _ = A.card * d0 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hL : ∑ p ∈ A.offDiag.filter (fun p => p.1 < p.2), F p.1 p.2 ≤ ∑ e ∈ Finset.range n, g e := by
    have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1 - 1)
        ((A.offDiag.filter (fun p => p.1 < p.2) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      intro p hp q hq hpq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_offDiag] at hp hq
      have hpq' : p.2 - p.1 = q.2 - q.1 := by
        have : p.2 - p.1 - 1 = q.2 - q.1 - 1 := hpq
        omega
      have := Finset.IsSidon.eq_of_tsub hS hp.1.2.1 hp.1.1 hq.1.2.1 hq.1.1 hp.2 hq.2 hpq'
      exact Prod.ext this.2 this.1
    calc ∑ p ∈ A.offDiag.filter (fun p => p.1 < p.2), F p.1 p.2
        ≤ ∑ p ∈ A.offDiag.filter (fun p => p.1 < p.2), g (p.2 - p.1 - 1) := by
          apply Finset.sum_le_sum
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_offDiag] at hp
          exact hoff p.1 hp.1.1 p.2 hp.1.2.1 hp.2
      _ = ∑ e ∈ (A.offDiag.filter (fun p => p.1 < p.2)).image (fun p : ℕ × ℕ => p.2 - p.1 - 1), g e :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ e ∈ (A.offDiag.filter (fun p => p.1 < p.2)).image (fun p : ℕ × ℕ => p.2 - p.1 - 1)
            ∪ Finset.range n, g e :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun e _ _ => hg0 e)
      _ = ∑ e ∈ Finset.range n, g e := by
          symm
          apply Finset.sum_subset Finset.subset_union_right
          intro e _ he
          exact hgz e (by simpa using he)
  have hR : ∑ p ∈ A.offDiag.filter (fun p => ¬ p.1 < p.2), F p.1 p.2 =
      ∑ p ∈ A.offDiag.filter (fun p => p.1 < p.2), F p.1 p.2 := by
    apply Finset.sum_nbij' Prod.swap Prod.swap
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_offDiag] at hp
      simp only [Finset.mem_filter, Finset.mem_offDiag, Prod.fst_swap, Prod.snd_swap]
      exact ⟨⟨hp.1.2.1, hp.1.1, fun h => hp.1.2.2 h.symm⟩, by omega⟩
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_offDiag] at hp
      simp only [Finset.mem_filter, Finset.mem_offDiag, Prod.fst_swap, Prod.snd_swap]
      exact ⟨⟨hp.1.2.1, hp.1.1, fun h => hp.1.2.2 h.symm⟩, by omega⟩
    · intro p _
      exact Prod.swap_swap p
    · intro p _
      exact Prod.swap_swap p
    · intro p _
      exact hsymm p.1 p.2
  have h2 : ∑ p ∈ A.offDiag, F p.1 p.2 ≤ 2 * ∑ e ∈ Finset.range n, g e := by
    rw [← Finset.sum_filter_add_sum_filter_not A.offDiag (fun p => p.1 < p.2), hR]
    linarith
  linarith

/-- The main inequality, in integers. -/
theorem core (A : Finset ℕ) (N t : ℕ) (ht : 0 < t) (h2t : 2 * t ≤ N)
    (hA : A ⊆ Finset.Icc 1 N) (hS : IsSidon (A : Set ℕ)) :
    (164 * (t : ℤ) * A.card) ^ 2 ≤ (1681 * (N : ℤ) + 2542 * t) * (16 * (t : ℤ) ^ 2 + 10 * t * A.card) := by
  have htz : (0 : ℤ) < t := by exact_mod_cast ht
  have hNz : 2 * (t : ℤ) ≤ N := by exact_mod_cast h2t
  have hmem : ∀ a ∈ A, (1 : ℤ) ≤ a ∧ (a : ℤ) ≤ N := fun a ha => by
    have := Finset.mem_Icc.1 (hA ha)
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  have hcov : 164 * (t : ℤ) * A.card ≤
      ∑ j ∈ Ioc (-2 * (t : ℤ)) N, phi t j * ∑ a ∈ A, U t a j := by
    have e : ∑ j ∈ Ioc (-2 * (t : ℤ)) N, phi t j * ∑ a ∈ A, U t a j =
        ∑ a ∈ A, ∑ j ∈ Ioc (-2 * (t : ℤ)) N, phi t j * U t a j := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    rw [e]
    calc 164 * (t : ℤ) * A.card = ∑ _a ∈ A, 164 * (t : ℤ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum fun a ha => cover t N a htz (hmem a ha).1 (hmem a ha).2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Ioc (-2 * (t : ℤ)) N) (fun j => phi t j)
    (fun j => ∑ a ∈ A, U t a j)
  have hsymm : ∀ a b : ℕ, ∑ j ∈ Ioc (-2 * (t : ℤ)) N, U t a j * U t b j =
      ∑ j ∈ Ioc (-2 * (t : ℤ)) N, U t b j * U t a j :=
    fun a b => Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hdiag : ∀ a ∈ A, ∑ j ∈ Ioc (-2 * (t : ℤ)) N, U t a j * U t a j ≤ 10 * (t : ℤ) := by
    intro a ha
    have h := corr_le t N a a htz (hmem a ha).1 le_rfl (hmem a ha).2
    have hc : cc t ((a : ℤ) - a) = 10 * t := by
      unfold cc
      rw [if_pos (by omega)]
      ring
    rw [hc] at h
    exact h
  have hoff : ∀ a ∈ A, ∀ b ∈ A, a < b →
      ∑ j ∈ Ioc (-2 * (t : ℤ)) N, U t a j * U t b j ≤ cc t (((b - a - 1 : ℕ) : ℤ) + 1) := by
    intro a ha b hb hab
    have h := corr_le t N a b htz (hmem a ha).1 (by exact_mod_cast hab.le) (hmem b hb).2
    have hc : ((b - a - 1 : ℕ) : ℤ) + 1 = (b : ℤ) - a := by omega
    rw [hc]
    exact h
  have hg0 : ∀ e : ℕ, 0 ≤ cc t ((e : ℤ) + 1) := by
    intro e
    unfold cc
    split_ifs <;> omega
  have hgz : ∀ e : ℕ, 2 * t ≤ e → cc t ((e : ℤ) + 1) = 0 := by
    intro e he
    unfold cc
    rw [if_neg (by omega), if_neg (by omega)]
  have hp := pair_bound A hS (fun a b => ∑ j ∈ Ioc (-2 * (t : ℤ)) N, U t a j * U t b j)
    (fun e => cc t ((e : ℤ) + 1)) (10 * (t : ℤ)) (2 * t) hsymm hdiag hoff hg0 hgz
  rw [cc_sum] at hp
  have hB : ∑ j ∈ Ioc (-2 * (t : ℤ)) N, (∑ a ∈ A, U t a j) ^ 2 ≤
      16 * (t : ℤ) ^ 2 + 10 * t * A.card := by
    have e : ∑ j ∈ Ioc (-2 * (t : ℤ)) N, (∑ a ∈ A, U t a j) ^ 2 =
        ∑ a ∈ A, ∑ b ∈ A, ∑ j ∈ Ioc (-2 * (t : ℤ)) N, U t a j * U t b j := by
      simp only [sq, Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    rw [e]
    nlinarith [hp, htz]
  have hn0 : (0 : ℤ) ≤ 164 * (t : ℤ) * A.card := by positivity
  have hphi := sum_phi_sq t N htz hNz
  calc (164 * (t : ℤ) * A.card) ^ 2
      ≤ (∑ j ∈ Ioc (-2 * (t : ℤ)) N, phi t j * ∑ a ∈ A, U t a j) ^ 2 :=
        pow_le_pow_left₀ hn0 hcov 2
    _ ≤ (∑ j ∈ Ioc (-2 * (t : ℤ)) N, phi t j ^ 2) *
          ∑ j ∈ Ioc (-2 * (t : ℤ)) N, (∑ a ∈ A, U t a j) ^ 2 := hcs
    _ = (1681 * (N : ℤ) + 2542 * t) * ∑ j ∈ Ioc (-2 * (t : ℤ)) N, (∑ a ∈ A, U t a j) ^ 2 := by
        rw [hphi]
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)

/-- The real-variable endgame: with `τ` within 1 of `(16/25) y³`, the main inequality fails as soon
as `K > y² + (49/50) y`. -/
lemma endgame (y τ K : ℝ) (hy : 100 ≤ y) (h1 : 16 / 25 * y ^ 3 ≤ τ) (h2 : τ < 16 / 25 * y ^ 3 + 1)
    (hK : y ^ 2 + 49 / 50 * y < K) :
    (1681 * y ^ 4 + 2542 * τ) * (16 * τ + 10 * K) < 26896 * τ * K ^ 2 := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hyy : 100 * y ≤ y ^ 2 := by nlinarith
  have hy3 : 10000 * y ≤ y ^ 3 := by nlinarith
  have hτ0 : 0 < τ := by
    have : (0 : ℝ) < 16 / 25 * y ^ 3 := by positivity
    linarith
  have hk0 : (0 : ℝ) ≤ y ^ 2 + 49 / 50 * y := by positivity
  -- the derivative condition
  have hc1 : (0 : ℝ) ≤ 26896 * (y ^ 2 + 49 / 50 * y) - 25420 := by nlinarith
  have hA1 : 16 / 25 * y ^ 3 * (26896 * (y ^ 2 + 49 / 50 * y) - 25420) ≤
      τ * (26896 * (y ^ 2 + 49 / 50 * y) - 25420) := mul_le_mul_of_nonneg_right h1 hc1
  have hD1 : 0 ≤ 16 / 25 * y ^ 3 * (26896 * (y ^ 2 + 49 / 50 * y) - 25420) - 16810 * y ^ 4 := by
    have e : 16 / 25 * y ^ 3 * (26896 * (y ^ 2 + 49 / 50 * y) - 25420) - 16810 * y ^ 4 =
        y ^ 3 * (430336 / 25 * y ^ 2 + 36982 / 625 * y - 81344 / 5) := by ring
    rw [e]
    exact mul_nonneg (by positivity) (by nlinarith)
  have hD : 0 ≤ 26896 * τ * (y ^ 2 + 49 / 50 * y) - 10 * (1681 * y ^ 4 + 2542 * τ) := by
    have e : 26896 * τ * (y ^ 2 + 49 / 50 * y) - 10 * (1681 * y ^ 4 + 2542 * τ) =
        τ * (26896 * (y ^ 2 + 49 / 50 * y) - 25420) - 16810 * y ^ 4 := by ring
    rw [e]
    linarith
  have hmono : 26896 * τ * (y ^ 2 + 49 / 50 * y) - 10 * (1681 * y ^ 4 + 2542 * τ) ≤
      26896 * τ * K - 10 * (1681 * y ^ 4 + 2542 * τ) := by
    have := mul_le_mul_of_nonneg_left hK.le (by positivity : (0 : ℝ) ≤ 26896 * τ)
    linarith
  have hB : (y ^ 2 + 49 / 50 * y) *
      (26896 * τ * (y ^ 2 + 49 / 50 * y) - 10 * (1681 * y ^ 4 + 2542 * τ)) ≤
      K * (26896 * τ * K - 10 * (1681 * y ^ 4 + 2542 * τ)) :=
    mul_le_mul hK.le hmono hD (hk0.trans hK.le)
  -- positivity of the value at the threshold, by concavity in τ
  have g1 : 0 < 26896 * (16 / 25 * y ^ 3) * (y ^ 2 + 49 / 50 * y) ^ 2 -
      (1681 * y ^ 4 + 2542 * (16 / 25 * y ^ 3)) * (16 * (16 / 25 * y ^ 3) + 10 * (y ^ 2 + 49 / 50 * y)) := by
    have e : 26896 * (16 / 25 * y ^ 3) * (y ^ 2 + 49 / 50 * y) ^ 2 -
        (1681 * y ^ 4 + 2542 * (16 / 25 * y ^ 3)) *
          (16 * (16 / 25 * y ^ 3) + 10 * (y ^ 2 + 49 / 50 * y)) =
        y ^ 4 * (168182 / 625 * y ^ 2 - 253293941 / 15625 * y - 1992928 / 125) := by ring
    rw [e]
    exact mul_pos (by positivity) (by nlinarith)
  have g2 : 0 < 26896 * (16 / 25 * y ^ 3 + 1) * (y ^ 2 + 49 / 50 * y) ^ 2 -
      (1681 * y ^ 4 + 2542 * (16 / 25 * y ^ 3 + 1)) *
        (16 * (16 / 25 * y ^ 3 + 1) + 10 * (y ^ 2 + 49 / 50 * y)) := by
    have e : 26896 * (16 / 25 * y ^ 3 + 1) * (y ^ 2 + 49 / 50 * y) ^ 2 -
        (1681 * y ^ 4 + 2542 * (16 / 25 * y ^ 3 + 1)) *
          (16 * (16 / 25 * y ^ 3 + 1) + 10 * (y ^ 2 + 49 / 50 * y)) =
        (26896 * (16 / 25 * y ^ 3) * (y ^ 2 + 49 / 50 * y) ^ 2 -
        (1681 * y ^ 4 + 2542 * (16 / 25 * y ^ 3)) *
          (16 * (16 / 25 * y ^ 3) + 10 * (y ^ 2 + 49 / 50 * y))) +
        (656 * y ^ 3 + 256824 / 625 * y ^ 2 - 124558 / 5 * y - 40672) := by ring
    rw [e]
    have : (0 : ℝ) < 656 * y ^ 3 + 256824 / 625 * y ^ 2 - 124558 / 5 * y - 40672 := by nlinarith
    linarith
  have gid : 26896 * τ * (y ^ 2 + 49 / 50 * y) ^ 2 -
      (1681 * y ^ 4 + 2542 * τ) * (16 * τ + 10 * (y ^ 2 + 49 / 50 * y)) =
      (16 / 25 * y ^ 3 + 1 - τ) * (26896 * (16 / 25 * y ^ 3) * (y ^ 2 + 49 / 50 * y) ^ 2 -
        (1681 * y ^ 4 + 2542 * (16 / 25 * y ^ 3)) *
          (16 * (16 / 25 * y ^ 3) + 10 * (y ^ 2 + 49 / 50 * y))) +
      (τ - 16 / 25 * y ^ 3) * (26896 * (16 / 25 * y ^ 3 + 1) * (y ^ 2 + 49 / 50 * y) ^ 2 -
        (1681 * y ^ 4 + 2542 * (16 / 25 * y ^ 3 + 1)) *
          (16 * (16 / 25 * y ^ 3 + 1) + 10 * (y ^ 2 + 49 / 50 * y))) +
      40672 * (τ - 16 / 25 * y ^ 3) * (16 / 25 * y ^ 3 + 1 - τ) := by ring
  have gpos : 0 < 26896 * τ * (y ^ 2 + 49 / 50 * y) ^ 2 -
      (1681 * y ^ 4 + 2542 * τ) * (16 * τ + 10 * (y ^ 2 + 49 / 50 * y)) := by
    rw [gid]
    have p1 := mul_pos (sub_pos.2 h2) g1
    have p2 := mul_nonneg (sub_nonneg.2 h1) g2.le
    have p3 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 40672) (sub_nonneg.2 h1))
      (sub_pos.2 h2).le
    linarith
  nlinarith [hB, gpos]

/-- Every Sidon set in `{1, …, N}` has at most `√N + (49/50) N^{1/4}` elements, for `N ≥ 10^8`. -/
theorem bound (N : ℕ) (hN : 100000000 ≤ N) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (hS : IsSidon (A : Set ℕ)) :
    (A.card : ℝ) ≤ Real.sqrt N + 49 / 50 * Real.sqrt (Real.sqrt N) := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.sqrt (Real.sqrt N) := ⟨_, rfl⟩
  have hsN : (10000 : ℝ) ≤ Real.sqrt N := by
    rw [Real.le_sqrt' (by norm_num)]
    have : (100000000 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hy100 : (100 : ℝ) ≤ y := by
    rw [hy, Real.le_sqrt' (by norm_num)]
    linarith
  have hy2 : y ^ 2 = Real.sqrt N := by
    rw [hy]
    exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hy4 : y ^ 4 = N := by
    have : y ^ 4 = (y ^ 2) ^ 2 := by ring
    rw [this, hy2]
    exact Real.sq_sqrt (Nat.cast_nonneg N)
  have hy0 : (0 : ℝ) < y := by linarith
  have hq0 : (0 : ℝ) ≤ 16 / 25 * y ^ 3 := by positivity
  have h1 : 16 / 25 * y ^ 3 ≤ (⌈16 / 25 * y ^ 3⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈16 / 25 * y ^ 3⌉₊ : ℝ) < 16 / 25 * y ^ 3 + 1 := Nat.ceil_lt_add_one hq0
  have ht : 0 < ⌈16 / 25 * y ^ 3⌉₊ := Nat.ceil_pos.2 (by positivity)
  have h2t : 2 * ⌈16 / 25 * y ^ 3⌉₊ ≤ N := by
    have h3 : (1000000 : ℝ) ≤ y ^ 3 := by nlinarith [mul_le_mul hy100 hy100 (by norm_num) hy0.le]
    have h4 : y ^ 4 = y * y ^ 3 := by ring
    have h5 : (2 : ℝ) * (⌈16 / 25 * y ^ 3⌉₊ : ℝ) ≤ (N : ℝ) := by
      rw [← hy4, h4]
      nlinarith [mul_le_mul_of_nonneg_right hy100 (by positivity : (0 : ℝ) ≤ y ^ 3)]
    exact_mod_cast h5
  have hc := core A N ⌈16 / 25 * y ^ 3⌉₊ ht h2t hA hS
  have hcR : (164 * (⌈16 / 25 * y ^ 3⌉₊ : ℝ) * A.card) ^ 2 ≤
      (1681 * y ^ 4 + 2542 * (⌈16 / 25 * y ^ 3⌉₊ : ℝ)) *
        (16 * (⌈16 / 25 * y ^ 3⌉₊ : ℝ) ^ 2 + 10 * (⌈16 / 25 * y ^ 3⌉₊ : ℝ) * A.card) := by
    rw [hy4]
    exact_mod_cast hc
  rw [← hy, ← hy2]
  by_contra hcon
  push Not at hcon
  have hτ0 : (0 : ℝ) < (⌈16 / 25 * y ^ 3⌉₊ : ℝ) := by exact_mod_cast ht
  have hend := endgame y (⌈16 / 25 * y ^ 3⌉₊ : ℝ) (A.card : ℝ) hy100 h1 h2 hcon
  have e1 : (164 * (⌈16 / 25 * y ^ 3⌉₊ : ℝ) * A.card) ^ 2 =
      (⌈16 / 25 * y ^ 3⌉₊ : ℝ) * (26896 * (⌈16 / 25 * y ^ 3⌉₊ : ℝ) * (A.card : ℝ) ^ 2) := by ring
  have e2 : (1681 * y ^ 4 + 2542 * (⌈16 / 25 * y ^ 3⌉₊ : ℝ)) *
      (16 * (⌈16 / 25 * y ^ 3⌉₊ : ℝ) ^ 2 + 10 * (⌈16 / 25 * y ^ 3⌉₊ : ℝ) * A.card) =
      (⌈16 / 25 * y ^ 3⌉₊ : ℝ) * ((1681 * y ^ 4 + 2542 * (⌈16 / 25 * y ^ 3⌉₊ : ℝ)) *
        (16 * (⌈16 / 25 * y ^ 3⌉₊ : ℝ) + 10 * A.card)) := by ring
  rw [e1, e2] at hcR
  have := le_of_mul_le_mul_left hcR hτ0
  linarith

lemma h_le (N : ℕ) (hN : 100000000 ≤ N) :
    (Erdos30.h N : ℝ) ≤ Real.sqrt N + 49 / 50 * Real.sqrt (Real.sqrt N) := by
  have hX : (0 : ℝ) ≤ Real.sqrt N + 49 / 50 * Real.sqrt (Real.sqrt N) := by positivity
  have hle : Erdos30.h N ≤ ⌊Real.sqrt N + 49 / 50 * Real.sqrt (Real.sqrt N)⌋₊ := by
    show Finset.maxSidonSubsetCard (Finset.Icc 1 N) ≤ _
    unfold Finset.maxSidonSubsetCard
    apply Finset.sup_le
    intro B hB
    rw [Finset.mem_filter, Finset.mem_powerset] at hB
    exact Nat.le_floor (bound N hN B hB.1 hB.2)
  calc (Erdos30.h N : ℝ) ≤ (⌊Real.sqrt N + 49 / 50 * Real.sqrt (Real.sqrt N)⌋₊ : ℝ) := by
        exact_mod_cast hle
    _ ≤ _ := Nat.floor_le hX

lemma rpow_quarter (N : ℕ) : (N : ℝ) ^ (4⁻¹ : ℝ) = Real.sqrt (Real.sqrt N) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N)]
  norm_num

end OMA.Sidon


theorem OMA.solution : type_of% @Erdos30.erdos_30.variants.balogh_furedi_roy := by
  rw [Filter.eventually_atTop]
  refine ⟨100000000, fun N hN => ?_⟩
  have h := OMA.Sidon.h_le N hN
  have h0 := Real.sqrt_nonneg (Real.sqrt (N : ℝ))
  rw [OMA.Sidon.rpow_quarter]
  have e : (0.998 : ℝ) = 499 / 500 := by norm_num
  rw [e]
  linarith
