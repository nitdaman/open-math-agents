import FormalConjectures.ErdosProblems.«1028»

-- Problem: Erdős Problem 1028 — upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1028.lean:78 (declaration Erdos1028.erdos_1028.variants.upper_bound)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Sylvester–Hadamard colouring gives H(n) ≪ n^{3/2}. -/

namespace OMA

/-- sign factor of the Sylvester–Hadamard matrix -/
def sgn (p q : Bool) : ℤ := if (p && q) then -1 else 1

/-- Sylvester–Hadamard matrix indexed by the cube `Fin k → Bool` -/
def had (k : ℕ) (a b : Fin k → Bool) : ℤ := ∏ i, sgn (a i) (b i)

lemma had_symm (k : ℕ) (a b : Fin k → Bool) : had k a b = had k b a := by
  unfold had sgn
  congr 1; ext i; rw [Bool.and_comm]

lemma had_pm (k : ℕ) (a b : Fin k → Bool) : had k a b = 1 ∨ had k a b = -1 := by
  have h : |had k a b| = 1 := by
    unfold had
    rw [Finset.abs_prod]
    apply Finset.prod_eq_one
    intro i _
    unfold sgn
    split_ifs <;> simp
  rcases abs_eq (zero_le_one) |>.mp h with h | h
  · exact Or.inl h
  · exact Or.inr h

lemma factor_sum (p p' : Bool) :
    ∑ c : Bool, sgn p c * sgn p' c = if p = p' then 2 else 0 := by
  cases p <;> cases p' <;> decide

lemma orth (k : ℕ) (a a' : Fin k → Bool) :
    ∑ b, had k a b * had k a' b = if a = a' then (2 : ℤ) ^ k else 0 := by
  unfold had
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i c => sgn (a i) c * sgn (a' i) c)]
  simp_rw [factor_sum]
  split_ifs with h
  · subst h
    simp
  · obtain ⟨i, hi⟩ : ∃ i, a i ≠ a' i := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

lemma cs_bound (k : ℕ) (S : Finset (Fin k → Bool)) :
    (∑ a ∈ S, ∑ b ∈ S, had k a b) ^ 2 ≤ 2 ^ k * (S.card : ℤ) ^ 2 := by
  set v : (Fin k → Bool) → ℤ := fun b => ∑ a ∈ S, had k a b with hv
  have hT : (∑ a ∈ S, ∑ b ∈ S, had k a b) = ∑ b ∈ S, 1 * v b := by
    rw [Finset.sum_comm]; simp [hv]
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℤ)) v
  have h2 : ∑ b ∈ S, v b ^ 2 ≤ ∑ b, v b ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)
  have h3 : ∑ b, v b ^ 2 = 2 ^ k * (S.card : ℤ) := by
    have : ∀ b, v b ^ 2 = ∑ a ∈ S, ∑ a' ∈ S, had k a b * had k a' b := by
      intro b
      rw [sq, hv, Finset.sum_mul_sum]
    simp_rw [this]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := Finset.univ) (t := S)]
    simp_rw [orth]
    simp [Finset.sum_ite_eq, mul_comm]
  rw [hT]
  simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h1
  calc (∑ b ∈ S, 1 * v b) ^ 2 ≤ (S.card : ℤ) * ∑ b ∈ S, v b ^ 2 := h1
    _ ≤ (S.card : ℤ) * (2 ^ k * S.card) := by
        apply mul_le_mul_of_nonneg_left (h2.trans h3.le) (by positivity)
    _ = 2 ^ k * (S.card : ℤ) ^ 2 := by ring

/-- the symmetric decomposition of a full double sum -/
lemma full_sum (g : ℕ → ℕ → ℤ) (hg : ∀ x y, g x y = g y x) (X : Finset ℕ) :
    ∑ x ∈ X, ∑ y ∈ X, g x y
      = 2 * (∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), g x y) + ∑ x ∈ X, g x x := by
  have hsplit : ∀ x y, g x y = (if x < y then g x y else 0) + (if y < x then g x y else 0)
      + (if x = y then g x y else 0) := by
    intro x y
    rcases lt_trichotomy x y with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  have hA : ∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), g x y
      = ∑ x ∈ X, ∑ y ∈ X, (if x < y then g x y else 0) := by
    simp [Finset.sum_filter]
  have hB : ∑ x ∈ X, ∑ y ∈ X, (if y < x then g x y else 0)
      = ∑ x ∈ X, ∑ y ∈ X, (if x < y then g x y else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    rw [hg]
  have hC : ∑ x ∈ X, ∑ y ∈ X, (if x = y then g x y else 0) = ∑ x ∈ X, g x x := by
    apply Finset.sum_congr rfl; intro x hx
    rw [Finset.sum_ite_eq]; simp [hx]
  conv_lhs => enter [2, x, 2, y]; rw [hsplit x y]
  simp only [Finset.sum_add_distrib]
  rw [hB, hC, hA]; ring

lemma H_le (n : ℕ) (hn : 1 ≤ n) : Erdos1028.H n ≤ Nat.sqrt (2 * n ^ 3) := by
  set k := Nat.log 2 n + 1 with hk
  have hlt : n < 2 ^ k := Nat.lt_pow_succ_log_self (by norm_num) n
  have hle : 2 ^ k ≤ 2 * n := by
    rw [hk, pow_succ, mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))
  let e : ℕ → (Fin k → Bool) := fun x i => x.testBit i.val
  let f : ℕ → ℕ → ℤ := fun x y => had k (e x) (e y)
  apply Nat.sInf_le
  refine ⟨f, fun x y => had_pm k _ _, ?_⟩
  intro X hX
  have hXn : ∀ x ∈ X, x < 2 ^ k := by
    intro x hx
    have := Finset.mem_Icc.mp (hX hx)
    omega
  have hinj : Set.InjOn e X := by
    intro x hx y hy hxy
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < k
    · exact congrFun hxy ⟨i, hi⟩
    · have hpow : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hXn x hx) hpow),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hXn y hy) hpow)]
  have hcardX : X.card ≤ n := by
    have := Finset.card_le_card hX
    simpa using this
  -- full sum bound
  have hT : (∑ x ∈ X, ∑ y ∈ X, f x y) ^ 2 ≤ 2 ^ k * (X.card : ℤ) ^ 2 := by
    have h := cs_bound k (X.image e)
    rw [Finset.card_image_of_injOn hinj] at h
    rw [Finset.sum_image hinj] at h
    simp_rw [Finset.sum_image hinj] at h
    exact h
  have hsym : ∀ x y, f x y = f y x := fun x y => had_symm k _ _
  have hdec := full_sum f hsym X
  set P := ∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), f x y with hP
  set D := ∑ x ∈ X, f x x with hD
  set T := ∑ x ∈ X, ∑ y ∈ X, f x y with hTdef
  have hDabs : |D| ≤ X.card := by
    rw [hD]
    calc |∑ x ∈ X, f x x| ≤ ∑ x ∈ X, |f x x| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x ∈ X, (1 : ℤ) := by
          apply Finset.sum_congr rfl; intro x _
          rcases had_pm k (e x) (e x) with h | h <;> simp [f, h]
      _ = X.card := by simp
  have hcardZ : (X.card : ℤ) ≤ n := by exact_mod_cast hcardX
  have h2k : ((2 ^ k : ℕ) : ℤ) ≤ 2 * n := by exact_mod_cast hle
  push_cast at h2k
  have hT' : T ^ 2 ≤ 2 * (n : ℤ) * n ^ 2 := by
    have hc0 : (0 : ℤ) ≤ X.card := by positivity
    calc T ^ 2 ≤ 2 ^ k * (X.card : ℤ) ^ 2 := hT
      _ ≤ 2 * (n : ℤ) * n ^ 2 := by
        apply mul_le_mul h2k (pow_le_pow_left₀ hc0 hcardZ 2) (by positivity) (by positivity)
  have hD2 : D ^ 2 ≤ (n : ℤ) ^ 2 := by
    have : |D| ≤ (n : ℤ) := hDabs.trans hcardZ
    nlinarith [abs_nonneg D, sq_abs D]
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hP2 : P ^ 2 ≤ 2 * (n : ℤ) ^ 3 := by
    have h2P : 2 * P = T - D := by linarith
    have : (2 * P) ^ 2 ≤ 2 * T ^ 2 + 2 * D ^ 2 := by
      rw [h2P]; nlinarith [sq_nonneg (T + D)]
    nlinarith
  unfold Erdos1028.imbalance
  rw [← hP]
  have hnat : P.natAbs ≤ Nat.sqrt (2 * n ^ 3) := by
    apply Nat.le_sqrt'.mpr
    have : ((P.natAbs ^ 2 : ℕ) : ℤ) ≤ ((2 * n ^ 3 : ℕ) : ℤ) := by
      push_cast
      rw [sq_abs]
      exact hP2
    exact_mod_cast this
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hnat

end OMA

theorem OMA.solution : type_of% @Erdos1028.erdos_1028.variants.upper_bound := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hH := H_le n hn
  have hsq : ((Nat.sqrt (2 * n ^ 3) : ℕ) : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ 3 := by
    have := Nat.sqrt_le' (2 * n ^ 3)
    exact_mod_cast this
  have hHr : (Erdos1028.H n : ℝ) ≤ (Nat.sqrt (2 * n ^ 3) : ℝ) := by exact_mod_cast hH
  have hy : ((n : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (n : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hy0 : 0 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
  have hH0 : 0 ≤ (Erdos1028.H n : ℝ) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hH0, abs_of_nonneg hy0]
  have hs0 : 0 ≤ ((Nat.sqrt (2 * n ^ 3) : ℕ) : ℝ) := by positivity
  nlinarith
