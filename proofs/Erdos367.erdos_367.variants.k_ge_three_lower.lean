import FormalConjectures.ErdosProblems.«367»

-- Problem: Erdős Problem 367 — k ge three lower
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/367.lean:79 (declaration Erdos367.erdos_367.variants.k_ge_three_lower)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter

namespace OMA.E367

open Erdos367

lemma B_eq (m : ℕ) :
    B 2 m = (m.factorization.filter (fun p => 2 ≤ m.factorization p)).prod (fun p k => p ^ k) := by
  unfold B Finsupp.prod
  rw [Finsupp.support_filter]
  apply Finset.prod_congr rfl
  intro p hp
  beta_reduce
  rw [Finsupp.filter_apply, if_pos (Finset.mem_filter.1 hp).2]

lemma sq_dvd_B (m d : ℕ) (hm : m ≠ 0) (h : d ^ 2 ∣ m) : d ^ 2 ∣ B 2 m := by
  have hd : d ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, zero_dvd_iff] at h
    exact hm h
  set f := m.factorization.filter (fun p => 2 ≤ m.factorization p) with hfdef
  have hf : ∀ p ∈ f.support, p.Prime := by
    intro p hp
    rw [hfdef, Finsupp.support_filter, Finset.mem_filter] at hp
    exact Nat.prime_of_mem_primeFactors (by rw [← Nat.support_factorization]; exact hp.1)
  have hBf : (B 2 m).factorization = f := by
    rw [B_eq]
    exact Nat.prod_pow_factorization_eq_self hf
  have hB0 : B 2 m ≠ 0 := by
    rw [B_eq]
    unfold Finsupp.prod
    exact Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hf p hp).ne_zero
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd) hB0, hBf]
  have hdm := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd) hm).2 h
  rw [Finsupp.le_def] at hdm ⊢
  intro p
  have h1 := hdm p
  rw [hfdef, Finsupp.filter_apply]
  split_ifs with hc
  · exact h1
  · rw [Nat.factorization_pow] at h1 ⊢
    simp only [Finsupp.smul_apply, smul_eq_mul] at h1 ⊢
    omega

lemma B_ge (m d : ℕ) (hm : m ≠ 0) (h : d ^ 2 ∣ m) : d ^ 2 ≤ B 2 m := by
  have hB0 : B 2 m ≠ 0 := by
    rw [B_eq]
    unfold Finsupp.prod
    refine Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ ?_
    rw [Finsupp.support_filter, Finset.mem_filter] at hp
    exact (Nat.prime_of_mem_primeFactors (by rw [← Nat.support_factorization]; exact hp.1)).ne_zero
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hB0) (sq_dvd_B m d hm h)

def uv : ℕ → ℕ × ℕ
  | 0 => (3, 2)
  | s + 1 => ((uv s).1 ^ 2 + 2 * (uv s).2 ^ 2, 2 * (uv s).1 * (uv s).2)

lemma uv_prop (s : ℕ) : (uv s).1 ^ 2 = 2 * (uv s).2 ^ 2 + 1 ∧ 2 ^ (s + 1) ∣ (uv s).1 - 1 ∧
    2 ^ (s + 1) ∣ (uv s).2 ∧ 1 ≤ (uv s).2 ∧ 2 * (uv s).1 ≤ 6 ^ (2 ^ s) ∧
    (uv s).2 < (uv s).1 ∧ 3 ≤ (uv s).1 ∧ s ≤ (uv s).1 := by
  induction s with
  | zero => simp [uv]
  | succ s ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih
    set u := (uv s).1 with hu
    set v := (uv s).2 with hv
    have e1 : (uv (s + 1)).1 = u ^ 2 + 2 * v ^ 2 := rfl
    have e2 : (uv (s + 1)).2 = 2 * u * v := rfl
    rw [e1, e2]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · zify at h1 ⊢
      linear_combination ((u : ℤ) ^ 2 - 2 * (v : ℤ) ^ 2 + 1) * h1
    · have : u ^ 2 + 2 * v ^ 2 - 1 = 4 * v ^ 2 := by
        rw [h1]
        omega
      rw [this]
      obtain ⟨k, hk⟩ := h3
      exact Dvd.intro (2 ^ (s + 2) * k ^ 2) (by rw [hk]; ring)
    · obtain ⟨k, hk⟩ := h3
      exact Dvd.intro (u * k) (by rw [hk]; ring)
    · have : 1 ≤ u := by omega
      nlinarith
    · have h9 : 2 * (u ^ 2 + 2 * v ^ 2) + 2 = (2 * u) ^ 2 := by
        rw [mul_pow, h1]
        ring
      have h10 : (2 * u) ^ 2 ≤ (6 ^ (2 ^ s)) ^ 2 := Nat.pow_le_pow_left h5 2
      have h11 : (6 ^ (2 ^ s)) ^ 2 = 6 ^ (2 ^ (s + 1)) := by
        rw [← pow_mul, pow_succ]
      omega
    · nlinarith
    · nlinarith
    · nlinarith

lemma prod_three (g : ℕ → ℕ) (n : ℕ) :
    ∏ m ∈ Finset.Ico n (n + 3), g m = g n * g (n + 1) * g (n + 2) := by
  rw [show n + 3 = (n + 2) + 1 by ring, Finset.prod_Ico_succ_top (by omega),
    Finset.prod_Ico_succ_top (by omega), show n + 1 = n + 0 + 1 by ring,
    Finset.prod_Ico_succ_top (by omega)]
  simp

lemma log_bound (n a : ℕ) (hn : 1 ≤ n) (hnb : n ≤ 9 * 36 ^ (2 ^ a)) :
    Real.log n ≤ 43 * 2 ^ a := by
  have h1 : (n : ℝ) ≤ 9 * 36 ^ (2 ^ a) := by
    have := Nat.cast_le (α := ℝ) |>.2 hnb
    rw [Nat.cast_mul, Nat.cast_pow] at this
    norm_num at this
    exact this
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h9 : Real.log n ≤ Real.log (9 * 36 ^ (2 ^ a)) := Real.log_le_log hn0 h1
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h9
  have l9 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 by norm_num)
  have l36 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 36 by norm_num)
  have h2a : (1 : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  have h3 : ((2 ^ a : ℕ) : ℝ) * Real.log 36 ≤ ((2 ^ a : ℕ) : ℝ) * 35 :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h4 : ((2 ^ a : ℕ) : ℝ) = (2 : ℝ) ^ a := by push_cast; ring
  rw [h4] at h3 h9 h2a
  linarith

end OMA.E367

theorem OMA.solution : type_of% @Erdos367.erdos_367.variants.k_ge_three_lower := by
  refine ⟨1 / 43, by norm_num, ?_⟩
  refine Filter.frequently_atTop.2 (fun a => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := OMA.E367.uv_prop a
  set u := (OMA.E367.uv a).1 with hu
  set v := (OMA.E367.uv a).2 with hv
  set x := u + 2 * v with hx
  set y := u + v with hy
  have hxy : x ^ 2 + 1 = 2 * y ^ 2 := by
    zify at h1 ⊢
    rw [hx, hy]
    push_cast
    linear_combination (-1 : ℤ) * h1
  have hx1 : 3 ≤ x := by omega
  have hsq : x ^ 2 - 1 = (x - 1) * (x + 1) := by
    obtain ⟨w, hw⟩ : ∃ w, x = w + 1 := ⟨x - 1, by omega⟩
    rw [hw]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have hdiv : 2 ^ (a + 2) ∣ x ^ 2 - 1 := by
    rw [hsq, pow_succ]
    apply mul_dvd_mul
    · have : x - 1 = (u - 1) + 2 * v := by omega
      rw [this]
      obtain ⟨k, hk⟩ := h3
      exact Nat.dvd_add h2 (Dvd.intro (2 * k) (by rw [hk]; ring))
    · obtain ⟨k, hk⟩ := (pow_dvd_pow 2 (by omega : 1 ≤ a + 1)).trans h2
      exact ⟨k + v + 1, by rw [pow_one] at hk; omega⟩
  set e := (a + 2) / 2 with he
  have hB1 : 2 ^ (a + 1) ≤ Erdos367.B 2 (x ^ 2 - 1) := by
    have hd : (2 ^ e) ^ 2 ∣ x ^ 2 - 1 := by
      rw [← pow_mul]
      exact (pow_dvd_pow 2 (by omega)).trans hdiv
    have := OMA.E367.B_ge (x ^ 2 - 1) (2 ^ e) (by
      have : 9 ≤ x ^ 2 := by nlinarith
      omega) hd
    calc 2 ^ (a + 1) ≤ 2 ^ (e * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (2 ^ e) ^ 2 := by rw [pow_mul]
      _ ≤ _ := this
  have hB2 : x ^ 2 ≤ Erdos367.B 2 (x ^ 2) :=
    OMA.E367.B_ge (x ^ 2) x (by positivity) dvd_rfl
  have hB3 : y ^ 2 ≤ Erdos367.B 2 (x ^ 2 + 1) :=
    OMA.E367.B_ge (x ^ 2 + 1) y (by omega) (by rw [hxy]; exact Dvd.intro_left 2 rfl)
  set n := x ^ 2 - 1 with hn
  have hn1 : n + 1 = x ^ 2 := by have : 9 ≤ x ^ 2 := by nlinarith
                                 omega
  have hn2 : n + 2 = x ^ 2 + 1 := by omega
  refine ⟨n, ?_, ?_⟩
  · have : x ≤ x ^ 2 := by nlinarith
    omega
  rw [OMA.E367.prod_three, hn1, hn2]
  have hP : 2 ^ (a + 1) * x ^ 2 * y ^ 2 ≤
      Erdos367.B 2 n * Erdos367.B 2 (x ^ 2) * Erdos367.B 2 (x ^ 2 + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul hB1 hB2) hB3
  have hPr : ((2 ^ (a + 1) * x ^ 2 * y ^ 2 : ℕ) : ℝ) ≤
      ((Erdos367.B 2 n * Erdos367.B 2 (x ^ 2) * Erdos367.B 2 (x ^ 2 + 1) : ℕ) : ℝ) := by
    exact_mod_cast hP
  -- bound on n
  have hu2 : u ^ 2 ≤ 36 ^ (2 ^ a) := by
    have : u ≤ 6 ^ (2 ^ a) := by omega
    calc u ^ 2 ≤ (6 ^ (2 ^ a)) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 36 ^ (2 ^ a) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hnb : n ≤ 9 * 36 ^ (2 ^ a) := by
    have : x ≤ 3 * u := by omega
    have : x ^ 2 ≤ 9 * u ^ 2 := by nlinarith
    omega
  have hnpos : (1 : ℝ) ≤ n := by
    have : 9 ≤ x ^ 2 := by nlinarith
    exact_mod_cast (by omega : 1 ≤ n)
  have hlog : Real.log n ≤ 43 * 2 ^ a := OMA.E367.log_bound n a (by exact_mod_cast hnpos) hnb
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hnpos
  have hnx : (n : ℝ) ≤ x ^ 2 := by exact_mod_cast (by omega : n ≤ x ^ 2)
  have hxy' : ((x : ℝ) ^ 2) ≤ 2 * y ^ 2 := by
    have : x ^ 2 ≤ 2 * y ^ 2 := by omega
    exact_mod_cast this
  have hn2r : (n : ℝ) ^ 2 ≤ 2 * x ^ 2 * y ^ 2 := by
    have h0 : (0 : ℝ) ≤ n := by linarith
    calc (n : ℝ) ^ 2 ≤ ((x : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ h0 hnx 2
      _ = (x : ℝ) ^ 2 * (x : ℝ) ^ 2 := by ring
      _ ≤ (x : ℝ) ^ 2 * (2 * (y : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hxy' (by positivity)
      _ = 2 * (x : ℝ) ^ 2 * (y : ℝ) ^ 2 := by ring
  refine le_trans ?_ hPr
  push_cast
  have h2a : (0 : ℝ) < 2 ^ a := by positivity
  calc 1 / 43 * ((n : ℝ) ^ 2 * Real.log n) ≤ 1 / 43 * ((2 * x ^ 2 * y ^ 2) * (43 * 2 ^ a)) := by
        gcongr
    _ = 2 ^ (a + 1) * (x : ℝ) ^ 2 * (y : ℝ) ^ 2 := by ring
