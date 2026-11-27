import FormalConjectures.ErdosProblems.«967»

-- Problem: Erdős Problem 967 — yip
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/967.lean:66 (declaration Erdos967.erdos_967.variants.yip)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace E967W9

open Erdos967 Complex

lemma summand_eq (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    summand t n = ((1 / (n : ℝ) : ℝ) : ℂ) * Complex.exp (((-(t * Real.log n)) : ℝ) * Complex.I) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold summand
  rw [Complex.cpow_def_of_ne_zero hn0]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hpos.le]
  rw [hlog]
  have : (Real.log n : ℂ) * (1 + t * I) = (Real.log n : ℂ) + (t * Real.log n : ℝ) * I := by
    push_cast; ring
  rw [this, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hpos]
  have h2 : Complex.exp (((-(t * Real.log n)) : ℝ) * I) =
      (Complex.exp ((t * Real.log n : ℝ) * I))⁻¹ := by
    rw [← Complex.exp_neg]; push_cast; ring_nf
  rw [h2]
  push_cast
  field_simp

lemma norm_summand (t : ℝ) {n : ℕ} (hn : 1 ≤ n) : ‖summand t n‖ = 1 / (n : ℝ) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [summand_eq t hn, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

lemma re_mul_conj (t : ℝ) (u : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (u * (starRingEnd ℂ) (summand t n)).re =
      ‖u‖ * (1 / (n : ℝ)) * Real.cos (t * Real.log n + u.arg) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I u]
  rw [summand_eq t hn]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [map_mul, map_add, Complex.conj_ofReal, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re,
    Complex.neg_im]
  rw [Real.cos_add, Real.cos_neg, Real.sin_neg]
  ring

/-- the block lemma -/
lemma block (τ φ : ℝ) (hτ : 0 < τ) (N : ℕ) :
    ∃ F : Finset ℕ, (∀ n ∈ F, N ≤ n ∧ 1 ≤ n ∧ 3 / 4 ≤ Real.cos (τ * Real.log n + φ)) ∧
      (Real.exp (1 / τ) - 1) / (2 * Real.exp (1 / τ)) ≤ ∑ n ∈ F, (1 / (n : ℝ)) := by
  set lam := Real.exp (1 / τ) with hlam
  have hlam1 : 1 < lam := by
    have h0 : (0:ℝ) < 1 / τ := by positivity
    have := Real.add_one_lt_exp h0.ne'; rw [hlam]; linarith
  set M0 : ℝ := max (N : ℝ) (2 / (lam - 1)) + 1 with hM0
  have hM0pos : 0 < M0 := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have := le_max_left (N : ℝ) (2 / (lam - 1)); linarith
  obtain ⟨m, hm⟩ := exists_nat_ge ((τ * Real.log M0 + 1 / 2 + φ) / (2 * Real.pi))
  have hpi := Real.pi_pos
  have hm' : τ * Real.log M0 + 1 / 2 + φ ≤ m * (2 * Real.pi) := by
    rw [div_le_iff₀ (by positivity)] at hm; linarith
  set X := Real.exp ((m * (2 * Real.pi) - 1 / 2 - φ) / τ) with hX
  have hXpos : 0 < X := Real.exp_pos _
  have hXM : M0 ≤ X := by
    rw [hX, ← Real.exp_log hM0pos]
    apply Real.exp_le_exp.mpr
    rw [le_div_iff₀ hτ]; linarith
  have hXN : (N : ℝ) + 1 ≤ X := by have := le_max_left (N : ℝ) (2 / (lam - 1)); linarith
  have hX2 : 2 ≤ (lam - 1) * X := by
    have h1 := le_max_right (N : ℝ) (2 / (lam - 1))
    have h2 : 2 / (lam - 1) ≤ X := by linarith
    rw [div_le_iff₀ (by linarith)] at h2; linarith
  have hlogX : Real.log X = (m * (2 * Real.pi) - 1 / 2 - φ) / τ := by rw [hX, Real.log_exp]
  refine ⟨Finset.Icc ⌈X⌉₊ ⌊lam * X⌋₊, ?_, ?_⟩
  · intro n hn
    rw [Finset.mem_Icc] at hn
    have h1 : X ≤ n := (Nat.ceil_le).mp hn.1
    have h2 : (n : ℝ) ≤ lam * X := (Nat.le_floor_iff (by positivity)).mp hn.2
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hXpos h1
    refine ⟨?_, ?_, ?_⟩
    · have : (N : ℝ) < n := by linarith
      exact_mod_cast this.le
    · have : (0 : ℝ) < n := hnpos
      exact_mod_cast this
    · have hl1 : Real.log X ≤ Real.log n := Real.log_le_log hXpos h1
      have hl2 : Real.log n ≤ Real.log X + 1 / τ := by
        have := Real.log_le_log hnpos h2
        rwa [Real.log_mul (by positivity) hXpos.ne', hlam, Real.log_exp, add_comm] at this
      rw [hlogX] at hl1 hl2
      have e1 : τ * ((m * (2 * Real.pi) - 1 / 2 - φ) / τ) = m * (2 * Real.pi) - 1 / 2 - φ := by
        field_simp
      have e2 : τ * (1 / τ) = 1 := by field_simp
      have k1 := mul_le_mul_of_nonneg_left hl1 hτ.le
      have k2 := mul_le_mul_of_nonneg_left hl2 hτ.le
      rw [e1] at k1
      rw [mul_add, e1, e2] at k2
      rw [← Real.cos_sub_nat_mul_two_pi _ m]
      set y := τ * Real.log n + φ - m * (2 * Real.pi)
      have hy1 : -(1 / 2) ≤ y := by simp only [y]; linarith
      have hy2 : y ≤ 1 / 2 := by simp only [y]; linarith
      have := Real.one_sub_sq_div_two_le_cos (x := y)
      nlinarith
  · have hterm : ∀ n ∈ Finset.Icc ⌈X⌉₊ ⌊lam * X⌋₊, 1 / (lam * X) ≤ 1 / (n : ℝ) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have h1 : X ≤ n := (Nat.ceil_le).mp hn.1
      have h2 : (n : ℝ) ≤ lam * X := (Nat.le_floor_iff (by positivity)).mp hn.2
      exact one_div_le_one_div_of_le (lt_of_lt_of_le hXpos h1) h2
    have hsum := Finset.card_nsmul_le_sum _ _ _ hterm
    rw [nsmul_eq_mul, Nat.card_Icc] at hsum
    have hc1 : (⌈X⌉₊ : ℝ) < X + 1 := Nat.ceil_lt_add_one hXpos.le
    have hc2 : lam * X - 1 < (⌊lam * X⌋₊ : ℝ) := Nat.sub_one_lt_floor _
    have hcard : (lam - 1) * X - 1 ≤ ((⌊lam * X⌋₊ + 1 - ⌈X⌉₊ : ℕ) : ℝ) := by
      have hle : ⌈X⌉₊ ≤ ⌊lam * X⌋₊ + 1 := by
        have : (⌈X⌉₊ : ℝ) ≤ (⌊lam * X⌋₊ : ℝ) + 1 := by nlinarith
        exact_mod_cast this
      rw [Nat.cast_sub hle]; push_cast; nlinarith
    have hlamX : 0 < lam * X := by positivity
    calc (lam - 1) / (2 * lam) = ((lam - 1) * X / 2) * (1 / (lam * X)) := by
          field_simp
      _ ≤ ((⌊lam * X⌋₊ + 1 - ⌈X⌉₊ : ℕ) : ℝ) * (1 / (lam * X)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
      _ ≤ _ := hsum


/-- inclusion condition -/
def good (t : ℝ) (n : ℕ) (r : ℂ) : Prop :=
  2 ≤ n ∧ ‖summand t n‖ ≤ ‖r‖ / 2 ∧
    ‖summand t n‖ * ‖r‖ / 2 ≤ (r * (starRingEnd ℂ) (summand t n)).re

open Classical in
/-- residual -/
noncomputable def res (t : ℝ) : ℕ → ℂ
  | 0 => -1
  | n + 1 => if good t n (res t n) then res t n - summand t n else res t n

open Classical in
/-- chosen terms -/
noncomputable def gg (t : ℝ) (n : ℕ) : ℂ := if good t n (res t n) then summand t n else 0

open Classical in
/-- chosen norms -/
noncomputable def ff (t : ℝ) (n : ℕ) : ℝ := if good t n (res t n) then ‖summand t n‖ else 0

lemma res_succ (t : ℝ) (n : ℕ) : res t (n + 1) = res t n - gg t n := by
  simp only [res, gg]; split_ifs <;> simp

lemma step (t : ℝ) {n : ℕ} {r : ℂ} (h : good t n r) :
    ‖r - summand t n‖ ≤ ‖r‖ - ‖summand t n‖ / 4 ∧ ‖r‖ / 2 ≤ ‖r - summand t n‖ := by
  obtain ⟨-, h1, h2⟩ := h
  set w := summand t n
  have hsq : ‖r - w‖ ^ 2 = ‖r‖ ^ 2 + ‖w‖ ^ 2 - 2 * (r * (starRingEnd ℂ) w).re := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
  have hw0 := norm_nonneg w
  have hr0 := norm_nonneg r
  have hd0 := norm_nonneg (r - w)
  constructor
  · have hsq2 : ‖r - w‖ ^ 2 ≤ (‖r‖ - ‖w‖ / 4) ^ 2 := by nlinarith
    have hy0 : 0 ≤ ‖r‖ - ‖w‖ / 4 := by linarith
    by_contra hc
    push Not at hc
    nlinarith
  · have := norm_sub_norm_le r w
    linarith

lemma res_pos (t : ℝ) : ∀ n, 0 < ‖res t n‖
  | 0 => by simp [res]
  | n + 1 => by
    have ih := res_pos t n
    simp only [res]
    split_ifs with h
    · have := (step t h).2; linarith
    · exact ih

lemma res_dec (t : ℝ) (n : ℕ) : ‖res t (n + 1)‖ ≤ ‖res t n‖ - ff t n / 4 := by
  simp only [res, ff]
  split_ifs with h
  · exact (step t h).1
  · simp

lemma ff_nonneg (t : ℝ) (n : ℕ) : 0 ≤ ff t n := by
  simp only [ff]; split_ifs <;> simp

lemma ff_sum_aux (t : ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range N, ff t i ≤ 4 * (‖res t 0‖ - ‖res t N‖) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have := res_dec t N
    linarith

lemma ff_sum (t : ℝ) (N : ℕ) : ∑ i ∈ Finset.range N, ff t i ≤ 4 := by
  have h := ff_sum_aux t N
  have h0 : ‖res t 0‖ = 1 := by simp [res]
  have := res_pos t N
  linarith

lemma res_eq (t : ℝ) (N : ℕ) : res t N = -1 - ∑ i ∈ Finset.range N, gg t i := by
  induction N with
  | zero => simp [res]
  | succ N ih => rw [res_succ, ih, Finset.sum_range_succ]; ring

lemma norm_gg_le (t : ℝ) (n : ℕ) : ‖gg t n‖ ≤ ff t n := by
  simp only [gg, ff]; split_ifs <;> simp

lemma key (t : ℝ) (ht : t ≠ 0) (hff : Summable (ff t)) (r : ℂ)
    (hlim : Filter.Tendsto (res t) Filter.atTop (nhds r)) (hr : r ≠ 0) : False := by
  set L := ‖r‖ with hLdef
  have hL : 0 < L := norm_pos_iff.mpr hr
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hlim (L / 10) (by positivity)
  obtain ⟨N2, hN2⟩ := exists_nat_ge (5 / (2 * L))
  set τ := |t| with hτdef
  set φ := if 0 < t then r.arg else -r.arg with hφdef
  have hτ : 0 < τ := abs_pos.mpr ht
  have hcos : ∀ n : ℕ, Real.cos (τ * Real.log n + φ) = Real.cos (t * Real.log n + r.arg) := by
    intro n
    by_cases h : 0 < t
    · simp only [hτdef, hφdef, h, if_true, abs_of_pos h]
    · have : t < 0 := lt_of_le_of_ne (not_lt.mp h) ht
      simp only [hτdef, hφdef, h, if_false, abs_of_neg this]
      rw [← Real.cos_neg]; ring_nf
  set δ := (Real.exp (1 / τ) - 1) / (2 * Real.exp (1 / τ)) with hδdef
  have hδ : 0 < δ := by
    have h0 : (0:ℝ) < 1 / τ := by positivity
    have := Real.add_one_lt_exp h0.ne'
    have : 1 < Real.exp (1 / τ) := by linarith
    apply div_pos (by linarith) (by positivity)
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hff δ hδ
  obtain ⟨F, hF1, hF2⟩ := block τ φ hτ (N1 + N2 + 2 + s.sup id + 1)
  have hdisj : Disjoint F s := by
    rw [Finset.disjoint_left]
    intro n hnF hns
    have h1 : n ≤ s.sup id := Finset.le_sup (f := id) hns
    have h2 := (hF1 n hnF).1
    omega
  have hgoodF : ∀ n ∈ F, ff t n = 1 / (n : ℝ) := by
    intro n hn
    obtain ⟨hnN, hn1, hc⟩ := hF1 n hn
    have hn2 : 2 ≤ n := by omega
    have hnN1 : N1 ≤ n := by omega
    have hnN2 : (N2 : ℝ) ≤ n := by exact_mod_cast (show N2 ≤ n by omega)
    have hd := hN1 n hnN1
    rw [dist_eq_norm] at hd
    have hw := norm_summand t hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    set q := 1 / (n : ℝ) with hq
    have hqpos : 0 < q := by positivity
    have hinv : q ≤ 2 * L / 5 := by
      rw [hq, div_le_iff₀ hnpos]
      have : 5 / (2 * L) ≤ n := le_trans hN2 hnN2
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have hres1 : ‖res t n‖ ≤ L + L / 10 := by
      have := norm_sub_norm_le (res t n) r; linarith
    have hres2 : L - L / 10 ≤ ‖res t n‖ := by
      have := norm_sub_norm_le r (res t n)
      rw [norm_sub_rev] at this; linarith
    have hre := re_mul_conj t r hn1
    rw [← hcos n] at hre
    have hcross : |((res t n - r) * (starRingEnd ℂ) (summand t n)).re| ≤ ‖res t n - r‖ * q := by
      calc |((res t n - r) * (starRingEnd ℂ) (summand t n)).re|
          ≤ ‖(res t n - r) * (starRingEnd ℂ) (summand t n)‖ := Complex.abs_re_le_norm _
        _ = ‖res t n - r‖ * q := by rw [norm_mul, Complex.norm_conj, hw]
    have hsplit : (res t n * (starRingEnd ℂ) (summand t n)).re =
        (r * (starRingEnd ℂ) (summand t n)).re +
          ((res t n - r) * (starRingEnd ℂ) (summand t n)).re := by
      rw [← Complex.add_re]; ring_nf
    have hg : good t n (res t n) := by
      refine ⟨hn2, ?_, ?_⟩
      · rw [hw]; linarith
      · rw [hw, hsplit, hre]
        have k1 : q * ‖res t n‖ ≤ q * (L + L / 10) := mul_le_mul_of_nonneg_left hres1 hqpos.le
        have k2 : L * q * (3 / 4) ≤ L * q * Real.cos (τ * Real.log n + φ) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
        have k3 : ‖res t n - r‖ * q ≤ L / 10 * q := mul_le_mul_of_nonneg_right hd.le hqpos.le
        have k4 := (abs_le.mp hcross).1
        nlinarith
    simp only [ff, hg, if_true, hw]
  have h1 := hs F hdisj
  rw [Finset.sum_congr rfl hgoodF] at h1
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun n _ => by positivity))] at h1
  linarith

theorem main (t : ℝ) (ht : t ≠ 0) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ 1 < a 0 ∧ Summable (fun k : ℕ => 1 / (a k : ℝ)) ∧
      (1 + (∑' k, summand t (a k)) = 0) := by
  have hff : Summable (ff t) := summable_of_sum_range_le (ff_nonneg t) (ff_sum t)
  have hgg : Summable (gg t) := Summable.of_norm_bounded hff (norm_gg_le t)
  have hlim : Filter.Tendsto (res t) Filter.atTop (nhds (-1 - ∑' n, gg t n)) := by
    have h2 := (hgg.hasSum.tendsto_sum_nat).const_sub (-1 : ℂ)
    refine h2.congr' ?_
    exact Filter.Eventually.of_forall (fun n => (res_eq t n).symm)
  have hzero : -1 - ∑' n, gg t n = 0 := by
    by_contra hne
    exact key t ht hff _ hlim hne
  rw [hzero] at hlim
  set p : ℕ → Prop := fun n => good t n (res t n) with hp
  have hinf : {n | p n}.Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨B, hB⟩ := hfin.bddAbove
    have hconst : ∀ k, res t (B + 1 + k) = res t (B + 1) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [← add_assoc, res_succ, ih]
        have hng : ¬ p (B + 1 + k) := by
          intro hpk
          have := hB hpk
          omega
        simp only [gg, hp] at hng ⊢
        simp [hng]
    have hlim2 : Filter.Tendsto (res t) Filter.atTop (nhds (res t (B + 1))) := by
      refine tendsto_const_nhds.congr' ?_
      rw [Filter.EventuallyEq, Filter.eventually_atTop]
      refine ⟨B + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      exact (hconst k).symm
    have := tendsto_nhds_unique hlim2 hlim
    have := res_pos t (B + 1)
    simp_all
  set a := Nat.nth p with ha
  have hmem : ∀ k, p (a k) := Nat.nth_mem_of_infinite hinf
  have hmono : StrictMono a := Nat.nth_strictMono hinf
  refine ⟨a, hmono, ?_, ?_, ?_⟩
  · have := (hmem 0).1; omega
  · have heq : (fun k : ℕ => 1 / (a k : ℝ)) = ff t ∘ a := by
      funext k
      have hk := hmem k
      have h1 : 1 ≤ a k := by have := hk.1; omega
      simp only [Function.comp, ff]
      rw [if_pos hk, norm_summand t h1]
    rw [heq]
    exact hff.comp_injective hmono.injective
  · have h1 : (∑' k, summand t (a k)) = ∑' k, gg t (a k) := by
      congr 1; funext k
      simp only [gg]; rw [if_pos (hmem k)]
    have h2 : (∑' k, gg t (a k)) = ∑' n, gg t n := by
      apply hmono.injective.tsum_eq
      intro x hx
      rw [Nat.range_nth_of_infinite hinf]
      by_contra hxp
      apply hx
      simp only [gg]
      exact if_neg hxp
    rw [h1, h2]
    linear_combination -hzero

end E967W9

theorem OMA.solution : type_of% @Erdos967.erdos_967.variants.yip := by
  intro t ht
  exact E967W9.main t ht
