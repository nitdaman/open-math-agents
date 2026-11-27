import FormalConjectures.LittProblems.«1»

-- Problem: Lam--Litt conjecture — eisenstein
-- Upstream: formal-conjectures FormalConjectures/LittProblems/1.lean:106 (declaration LamLitt.lam_litt.variants.eisenstein)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target.

open PowerSeries Polynomial

namespace OMA

/-- The subring of power series with coefficients in `R`. -/
noncomputable def serSub (R : Subring ℚ) : Subring ℚ⟦X⟧ := (PowerSeries.map R.subtype).range

lemma mem_serSub {R : Subring ℚ} {p : ℚ⟦X⟧} : p ∈ serSub R ↔ ∀ n, PowerSeries.coeff n p ∈ R := by
  constructor
  · rintro ⟨q, rfl⟩ n
    simp
  · intro h
    refine ⟨PowerSeries.mk fun n => ⟨PowerSeries.coeff n p, h n⟩, ?_⟩
    ext n
    simp

lemma eval_mem_serSub {R : Subring ℚ} (Pm : ℚ⟦X⟧[X]) (hP : ∀ i, Pm.coeff i ∈ serSub R)
    (g : ℚ⟦X⟧) (hg : g ∈ serSub R) : Pm.eval g ∈ serSub R := by
  rw [Polynomial.eval_eq_sum_range]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hP i) (Subring.pow_mem _ hg i)

lemma mem_adjoin_of_den_dvd {N : ℕ} (hN : N ≠ 0) {q : ℚ} (h : q.den ∣ N) :
    q ∈ LamLitt.ℤAdjoinInvNat N := by
  obtain ⟨c, hc⟩ := h
  have hq : q = ((q.num * c : ℤ) : ℚ) * (1 / (N : ℚ)) := by
    have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
    have h1 : (q.den : ℚ) * q = q.num := by rw [mul_comm]; exact Rat.mul_den_eq_num q
    have hcN : (N : ℚ) = q.den * c := by rw [hc]; push_cast; ring
    rw [hcN] at hN' ⊢
    push_cast
    field_simp
    have : (c : ℚ) ≠ 0 := right_ne_zero_of_mul hN'
    rw [← h1]
    field_simp
  rw [hq]
  refine Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (Algebra.subset_adjoin rfl)


lemma key (f : ℚ⟦X⟧) (Pm : ℚ⟦X⟧[X]) (hP : Pm.eval f = 0) (m k : ℕ) (u0 : ℚ)
    (hlt : ∀ i < m, PowerSeries.coeff i (Pm.derivative.eval f) = 0)
    (hm : PowerSeries.coeff m (Pm.derivative.eval f) = u0) (hk : m < k) :
    PowerSeries.coeff (k + m) (Pm.eval ((trunc k f : ℚ[X]) : ℚ⟦X⟧)) + u0 * PowerSeries.coeff k f = 0 := by
  set g : ℚ⟦X⟧ := ((trunc k f : ℚ[X]) : ℚ⟦X⟧) with hg
  have hcg : ∀ i, PowerSeries.coeff i g = if i < k then PowerSeries.coeff i f else 0 := by
    intro i
    rw [hg, Polynomial.coeff_coe, coeff_trunc]
  have hy : (X : ℚ⟦X⟧) ^ k ∣ f - g := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro i hi
    rw [map_sub, hcg, if_pos hi, sub_self]
  obtain ⟨y', hy'⟩ := hy
  have hy0 : PowerSeries.coeff 0 y' = PowerSeries.coeff k f := by
    have := congrArg (PowerSeries.coeff k) hy'
    rw [map_sub, hcg, if_neg (lt_irrefl k), sub_zero, PowerSeries.coeff_X_pow_mul'] at this
    simpa using this.symm
  obtain ⟨K, hK⟩ := Polynomial.binomExpansion Pm g (f - g)
  rw [add_sub_cancel, hP] at hK
  have hD : (X : ℚ⟦X⟧) ^ k ∣ Pm.derivative.eval f - Pm.derivative.eval g := by
    refine dvd_trans ⟨y', hy'⟩ (Polynomial.sub_dvd_eval_sub f g _)
  have hDc : ∀ i < k, PowerSeries.coeff i (Pm.derivative.eval g) = PowerSeries.coeff i (Pm.derivative.eval f) := by
    intro i hi
    have := (PowerSeries.X_pow_dvd_iff.mp hD) i hi
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  have h2 := congrArg (PowerSeries.coeff (k + m)) hK
  rw [map_zero, map_add, map_add] at h2
  have e1 : PowerSeries.coeff (k + m) (Pm.derivative.eval g * (f - g)) = u0 * PowerSeries.coeff k f := by
    rw [hy', mul_left_comm, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel_left,
      PowerSeries.coeff_mul, Finset.sum_eq_single (m, 0)]
    · simp only
      rw [hDc m hk, hm, hy0]
    · rintro ⟨a, b⟩ hab hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      by_cases ha : a < m
      · rw [hDc a (by omega), hlt a ha, zero_mul]
      · exfalso
        apply hne
        have : a = m ∧ b = 0 := by simp at hab ⊢; omega
        simp [this.1, this.2]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp)) h
  have e2 : PowerSeries.coeff (k + m) (K * (f - g) ^ 2) = 0 := by
    have : (X : ℚ⟦X⟧) ^ (2 * k) ∣ K * (f - g) ^ 2 := by
      refine dvd_mul_of_dvd_right ?_ _
      rw [hy', mul_pow, ← pow_mul, mul_comm k 2]
      exact dvd_mul_right _ _
    exact (PowerSeries.X_pow_dvd_iff.mp this) _ (by omega)
  rw [e1, e2] at h2
  linarith

lemma exists_P (f : ℚ⟦X⟧) (hAlg : IsAlgebraic ℚ[X] f) :
    ∃ P : ℚ[X][X], Polynomial.aeval f P = 0 ∧
      Polynomial.aeval f (Polynomial.derivative P) ≠ 0 := by
  obtain ⟨P0, hP0, hP0'⟩ := hAlg
  have hex : ∃ d, ∃ P : ℚ[X][X], P ≠ 0 ∧ Polynomial.aeval f P = 0 ∧ P.natDegree = d :=
    ⟨_, P0, hP0, hP0', rfl⟩
  classical
  obtain ⟨P, hPne, hPa, hPd⟩ := Nat.find_spec hex
  refine ⟨P, hPa, fun hD => ?_⟩
  by_cases h0 : P.natDegree = 0
  · rw [Polynomial.eq_C_of_natDegree_eq_zero h0] at hPa hPne
    simp only [Polynomial.aeval_C] at hPa
    have : P.coeff 0 = 0 := by
      have h : ((P.coeff 0 : ℚ[X]) : ℚ⟦X⟧) = 0 := hPa
      exact Polynomial.coe_eq_zero_iff.mp h
    exact hPne (by rw [this]; simp)
  · have hlt := Polynomial.natDegree_derivative_lt h0
    have hne : Polynomial.derivative P ≠ 0 := by
      intro h
      exact h0 (Polynomial.derivative_eq_zero.mp h)
    have := Nat.find_min hex (m := (Polynomial.derivative P).natDegree) (by omega)
    exact this ⟨_, hne, hD, rfl⟩

theorem main (f : ℚ⟦X⟧) (hAlg : IsAlgebraic ℚ[X] f) :
    ∃ N : ℕ, LamLitt.IsCoeffIntegralAdjointInvNat f N := by
  classical
  obtain ⟨P, hPa, hDa⟩ := exists_P f hAlg
  set Pm : ℚ⟦X⟧[X] := P.map (algebraMap ℚ[X] ℚ⟦X⟧) with hPm
  have hP : Pm.eval f = 0 := by
    rw [hPm, Polynomial.eval_map, ← Polynomial.aeval_def]; exact hPa
  have hD : Pm.derivative.eval f ≠ 0 := by
    rw [hPm, Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]; exact hDa
  set D := Pm.derivative.eval f with hDdef
  have hex : ∃ n, PowerSeries.coeff n D ≠ 0 := by
    by_contra h
    push Not at h
    exact hD (by ext n; simpa using h n)
  set m := Nat.find hex with hmdef
  set u0 := PowerSeries.coeff m D with hu0def
  have hu0 : u0 ≠ 0 := Nat.find_spec hex
  have hlt : ∀ i < m, PowerSeries.coeff i D = 0 := fun i hi => by
    have := Nat.find_min hex hi
    push Not at this
    exact this
  set s0 : Finset ℚ := P.support.biUnion fun i =>
    (P.coeff i).support.image (fun j => (P.coeff i).coeff j) with hs0
  set s : Finset ℚ := insert 0 (insert u0⁻¹ (s0 ∪ (Finset.range (m + 1)).image
    (fun j => PowerSeries.coeff j f))) with hs
  have hspos : (∏ q ∈ s, q.den) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q _ => q.den_nz
  refine ⟨∏ q ∈ s, q.den, ?_⟩
  set N := ∏ q ∈ s, q.den with hN
  have hmemS : ∀ q ∈ s, q ∈ LamLitt.ℤAdjoinInvNat N := fun q hq =>
    mem_adjoin_of_den_dvd hspos (Finset.dvd_prod_of_mem _ hq)
  set R : Subring ℚ := (LamLitt.ℤAdjoinInvNat N).toSubring with hR
  have hRmem : ∀ q ∈ s, q ∈ R := hmemS
  have hPcoef : ∀ i, Pm.coeff i ∈ serSub R := by
    intro i
    rw [mem_serSub]
    intro n
    rw [hPm, Polynomial.coeff_map]
    have e : PowerSeries.coeff n (algebraMap ℚ[X] ℚ⟦X⟧ (P.coeff i)) = (P.coeff i).coeff n :=
      Polynomial.coeff_coe _ _
    rw [e]
    by_cases h1 : P.coeff i = 0
    · rw [h1]; simp
    · by_cases h2 : (P.coeff i).coeff n = 0
      · rw [h2]; exact R.zero_mem
      · apply hRmem
        simp only [hs, hs0, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion,
          Finset.mem_image, Polynomial.mem_support_iff]
        right; right; left
        exact ⟨i, h1, n, h2, rfl⟩
  have hall : ∀ k, PowerSeries.coeff k f ∈ R := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : k ≤ m
      · apply hRmem
        simp only [hs, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_range]
        right; right; right
        exact ⟨k, by omega, rfl⟩
      · push Not at hk
        have hkey := key f Pm hP m k u0 hlt rfl hk
        have hg : (((trunc k f : ℚ[X]) : ℚ⟦X⟧)) ∈ serSub R := by
          rw [mem_serSub]
          intro n
          rw [Polynomial.coeff_coe, coeff_trunc]
          split_ifs with h
          · exact ih n h
          · exact R.zero_mem
        have hmem := (mem_serSub.mp (eval_mem_serSub Pm hPcoef _ hg)) (k + m)
        have hu : u0⁻¹ ∈ R := hRmem _ (by simp [hs])
        have : PowerSeries.coeff k f = -u0⁻¹ * PowerSeries.coeff (k + m)
            (Pm.eval ((trunc k f : ℚ[X]) : ℚ⟦X⟧)) := by
          field_simp
          linarith
        rw [this]
        exact R.mul_mem (R.neg_mem hu) hmem
  exact hall

end OMA

theorem OMA.solution : type_of% @LamLitt.lam_litt.variants.eisenstein := by
  intro f hAlg
  exact OMA.main f hAlg
