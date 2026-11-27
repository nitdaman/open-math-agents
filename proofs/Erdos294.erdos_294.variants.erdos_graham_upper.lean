import FormalConjectures.ErdosProblems.«294»

-- Problem: Erdős Problem 294 — erdos graham upper
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/294.lean:82 (declaration Erdos294.erdos_294.variants.erdos_graham_upper)
-- Credit: @vkascheev (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Real

namespace OMAHelp

theorem key (p N : ℕ) (hp : p.Prime) (h : (N / p) * Nat.lcmUpto (N / p) < p) :
    ¬ Erdos294.HasUnitFractionSolution p N := by
  rintro ⟨s, hps, hs, hsum⟩
  set L := N / p with hL
  set D := Nat.lcmUpto L with hD
  set J := s.filter (fun n => p ∣ n) with hJ
  set R := s.filter (fun n => ¬ p ∣ n) with hR
  set E := ∏ n ∈ R, n with hE
  have hp2 := hp.two_le
  have hpos : ∀ n ∈ s, 0 < n := fun n hn => by have := (hs n hn).1; omega
  have hDpos : 0 < D := Nat.lcmUpto_pos L
  have hdivJ : ∀ n ∈ J, n / p ∣ D := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have h1 : 1 ≤ n / p := (Nat.one_le_div_iff hp.pos).2 (hs n hn.1).1
    have h2 : n / p ≤ L := Nat.div_le_div_right (hs n hn.1).2
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.2 ⟨h1, h2⟩)
  have hdivR : ∀ n ∈ R, n ∣ E := fun n hn => Finset.dvd_prod_of_mem _ hn
  have hnat : p * D * E = (∑ n ∈ R, p * D * (E / n)) + E * ∑ n ∈ J, D / (n / p) := by
    apply Nat.cast_injective (R := ℚ)
    have e1 : ((p * D * E : ℕ) : ℚ) = ∑ n ∈ s, ((p * D * E : ℕ) : ℚ) * (1 / n) := by
      rw [← Finset.mul_sum, hsum, mul_one]
    rw [e1, ← Finset.sum_filter_add_sum_filter_not s (fun n => p ∣ n)]
    push_cast
    rw [add_comm, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro n hn
      have hn0 : (n : ℚ) ≠ 0 := by
        have := hpos n (Finset.mem_filter.1 hn).1; positivity
      rw [Nat.cast_div (hdivR n hn) hn0]
      field_simp
    · apply Finset.sum_congr rfl
      intro n hn
      have hnp : p ∣ n := (Finset.mem_filter.1 hn).2
      have hn0 : 0 < n := hpos n (Finset.mem_filter.1 hn).1
      have hq0 : ((n / p : ℕ) : ℚ) ≠ 0 := by
        have : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn0 hnp) hp.pos
        positivity
      rw [Nat.cast_div (hdivJ n hn) hq0, Nat.cast_div hnp (by exact_mod_cast hp.ne_zero)]
      have : (n : ℚ) ≠ 0 := by positivity
      have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      field_simp
  set A := ∑ n ∈ J, D / (n / p) with hA
  have hdvd : p ∣ E * A := by
    have h1 : p ∣ ∑ n ∈ R, p * D * (E / n) :=
      Finset.dvd_sum fun n _ => by rw [mul_assoc]; exact dvd_mul_right _ _
    have h2 : p ∣ p * D * E := by rw [mul_assoc]; exact dvd_mul_right _ _
    rw [hnat] at h2
    exact (Nat.dvd_add_right h1).1 h2
  have hpJ : p ∈ J := Finset.mem_filter.2 ⟨hps, dvd_refl p⟩
  have hApos : 0 < A := by
    have : D / (p / p) ≤ A := Finset.single_le_sum (f := fun n => D / (n / p))
      (fun _ _ => Nat.zero_le _) hpJ
    rw [Nat.div_self hp.pos, Nat.div_one] at this
    omega
  have hcard : J.card ≤ L := by
    have hsub : J ⊆ (Finset.Icc 1 L).image (fun j => j * p) := by
      intro n hn
      rw [Finset.mem_image]
      have hn' := Finset.mem_filter.1 hn
      refine ⟨n / p, Finset.mem_Icc.2 ⟨(Nat.one_le_div_iff hp.pos).2 (hs n hn'.1).1,
        Nat.div_le_div_right (hs n hn'.1).2⟩, Nat.div_mul_cancel hn'.2⟩
    calc J.card ≤ ((Finset.Icc 1 L).image (fun j => j * p)).card := Finset.card_le_card hsub
      _ ≤ (Finset.Icc 1 L).card := Finset.card_image_le
      _ = L := by simp
  have hAle : A ≤ L * D := by
    calc A ≤ J.card • D := Finset.sum_le_card_nsmul _ _ _ (fun n _ => Nat.div_le_self _ _)
      _ ≤ L * D := by rw [smul_eq_mul]; exact Nat.mul_le_mul_right _ hcard
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with hE' | hA'
  · obtain ⟨n, hn, hpn⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hE'
    exact (Finset.mem_filter.1 hn).2 hpn
  · have := Nat.le_of_dvd hApos hA'
    omega


theorem bound_ev : ∀ᶠ N : ℕ in atTop, (Erdos294.t N : ℝ) ≤ 200 * ((N : ℝ) / log N) := by
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 := hlog.eventually (Real.isLittleO_log_id_atTop.bound (by norm_num : (0:ℝ) < 1 / 4))
  have h2 := hlog.eventually_ge_atTop 1
  filter_upwards [h1, h2, eventually_ge_atTop 2] with N h1 h2 hN2
  set x := log (N : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  have hNpos : (0 : ℝ) < N := by have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
                                 linarith
  have hxN : x < N := by
    have := Real.log_le_sub_one_of_pos hNpos
    linarith
  have hexp : exp x = N := exp_log hNpos
  have hq0 : 0 ≤ 100 * (N : ℝ) / x := by positivity
  have hq1 : 1 ≤ 100 * (N : ℝ) / x := by
    rw [le_div_iff₀ hx0]; linarith
  set n0 := ⌊100 * (N : ℝ) / x⌋₊ with hn0def
  have hn0 : n0 ≠ 0 := (Nat.floor_pos.2 hq1).ne'
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul n0 hn0
  have hp_gt : 100 * (N : ℝ) / x < p := by
    have h3 := Nat.lt_floor_add_one (100 * (N : ℝ) / x)
    have h4 : (n0 : ℝ) + 1 ≤ p := by exact_mod_cast hlt
    linarith
  have hp_le : (p : ℝ) ≤ 200 * ((N : ℝ) / x) := by
    have h3 : (p : ℝ) ≤ 2 * n0 := by exact_mod_cast hle
    have h4 := Nat.floor_le hq0
    have : 200 * ((N : ℝ) / x) = 2 * (100 * N / x) := by ring
    linarith
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hkey : (N / p) * Nat.lcmUpto (N / p) < p := by
    set L := N / p with hLdef
    have hL : (L : ℝ) ≤ x / 100 := by
      have h5 := (div_lt_iff₀ hx0).1 hp_gt
      calc (L : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
        _ ≤ x / 100 := by
          rw [div_le_div_iff₀ hppos (by norm_num)]; nlinarith
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have hD : (Nat.lcmUpto L : ℝ) ≤ exp (0.07 * x) := by
      have hψ := Chebyshev.psi_le_const_mul_self hL0
      rw [Chebyshev.psi_eq_log_lcmUpto] at hψ
      have hl4 : log 4 ≤ 3 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4); linarith
      have hDpos : (0 : ℝ) < Nat.lcmUpto L := by exact_mod_cast Nat.lcmUpto_pos L
      calc (Nat.lcmUpto L : ℝ) = exp (log (Nat.lcmUpto L)) := (exp_log hDpos).symm
        _ ≤ exp (0.07 * x) := exp_le_exp.2 (by nlinarith)
    have hlx : log x ≤ x / 4 := by
      have := h1
      simp only [norm_eq_abs, id] at this
      rw [abs_of_pos hx0] at this
      have := le_abs_self (log x)
      linarith
    have hx2 : x ^ 2 ≤ exp (x / 2) := by
      calc x ^ 2 = exp (log x) ^ 2 := by rw [exp_log hx0]
        _ = exp (2 * log x) := by rw [← exp_nat_mul]; norm_num
        _ ≤ exp (x / 2) := exp_le_exp.2 (by linarith)
    have hmain : (x / 100) * exp (0.07 * x) ≤ 100 * (N : ℝ) / x := by
      rw [le_div_iff₀ hx0]
      have e1 : exp (x / 2) * exp (0.07 * x) ≤ exp x := by
        rw [← exp_add]; exact exp_le_exp.2 (by linarith)
      have e2 : x ^ 2 * exp (0.07 * x) ≤ exp (x / 2) * exp (0.07 * x) :=
        mul_le_mul_of_nonneg_right hx2 (exp_pos _).le
      nlinarith [exp_pos (0.07 * x)]
    have : ((L * Nat.lcmUpto L : ℕ) : ℝ) < p := by
      push_cast
      calc (L : ℝ) * Nat.lcmUpto L ≤ (x / 100) * exp (0.07 * x) :=
            mul_le_mul hL hD (by positivity) (by positivity)
        _ < p := by linarith
    exact_mod_cast this
  have ht : Erdos294.t N ≤ p := Nat.sInf_le ⟨hp.pos, key p N hp hkey⟩
  have : (Erdos294.t N : ℝ) ≤ p := by exact_mod_cast ht
  linarith

end OMAHelp

theorem OMA.solution : type_of% @Erdos294.erdos_294.variants.erdos_graham_upper := by
  apply Asymptotics.IsBigO.of_bound 200
  filter_upwards [OMAHelp.bound_ev, eventually_ge_atTop 2] with N h hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) (log_nonneg hN'))]
  exact h
