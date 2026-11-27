import FormalConjectures.ErdosProblems.«305»

-- Problem: Erdős Problem 305 — prime lower bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/305.lean (declaration Erdos305.erdos_305.variants.prime_lower_bound)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA305

/-- A sum of unit fractions with denominators prime to `p` has denominator prime to `p`. -/
lemma den_not_dvd (p : ℕ) (hp : p.Prime) (E : Finset ℕ) (h : ∀ n ∈ E, ¬ p ∣ n) :
    ¬ p ∣ (∑ n ∈ E, (1 : ℚ) / n).den := by
  induction E using Finset.induction_on with
  | empty => simpa using hp.one_lt.ne'
  | insert x E hx ih =>
    rw [Finset.sum_insert hx]
    intro hd
    have h1 : p ∣ ((1 : ℚ) / x).den * (∑ n ∈ E, (1 : ℚ) / n).den :=
      hd.trans (Rat.add_den_dvd _ _)
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · rw [one_div, Rat.inv_natCast_den] at h2
      split_ifs at h2 with hx0
      · exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
      · exact h x (Finset.mem_insert_self _ _) h2
    · exact ih (fun n hn => h n (Finset.mem_insert_of_mem hn)) h2

lemma eq_of_den (p a a' : ℕ) (hp : p.Prime) (ha : a < p) (ha' : a' < p) (X : ℚ)
    (hX : ¬ p ∣ X.den) (heq : (a : ℚ) / p - a' / p = X) : a = a' := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq : ((a : ℚ) - a') * X.den = p * X.num := by
    rw [← Rat.mul_den_eq_num, ← heq]
    field_simp
  have hz : ((a : ℤ) - a') * (X.den : ℤ) = p * X.num := by exact_mod_cast hq
  have hdvd : (p : ℤ) ∣ ((a : ℤ) - a') * (X.den : ℤ) := ⟨X.num, hz⟩
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hdvd with h | h
  · have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega
  · exact absurd (Int.natCast_dvd_natCast.mp h) hX

lemma exists_rep (p a : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (ha : a < p) :
    ∃ E : Finset ℕ, 0 ∉ E ∧ ∑ n ∈ E, (1 : ℚ) / n = a / p := by
  classical
  set T := p with hTdef
  have hT : p < 2 ^ T := Nat.lt_two_pow_self
  set q := a * 2 ^ T / p with hqdef
  set r := a * 2 ^ T % p with hrdef
  have hdm : p * q + r = a * 2 ^ T := Nat.div_add_mod _ _
  have hq : q < 2 ^ T := by
    rw [hqdef, Nat.div_lt_iff_lt_mul hp.pos]
    calc a * 2 ^ T < p * 2 ^ T := Nat.mul_lt_mul_of_pos_right ha (by positivity)
      _ = 2 ^ T * p := by ring
  have hr : r < 2 ^ T := lt_trans (Nat.mod_lt _ hp.pos) hT
  have hbits : ∀ m, m < 2 ^ T → ∀ i ∈ m.bitIndices.toFinset, i < T := by
    intro m hm i hi
    have h1 := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi)
    have h2 : 2 ^ i < 2 ^ T := lt_of_le_of_lt h1 hm
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
  let E1 := q.bitIndices.toFinset.image (fun i => 2 ^ (T - i))
  let E2 := r.bitIndices.toFinset.image (fun i => p * 2 ^ (T - i))
  have hinj1 : Set.InjOn (fun i => 2 ^ (T - i)) (q.bitIndices.toFinset : Set ℕ) := by
    intro i hi j hj hij
    have hi' := hbits q hq i hi
    have hj' := hbits q hq j hj
    have := Nat.pow_right_injective le_rfl hij
    omega
  have hinj2 : Set.InjOn (fun i => p * 2 ^ (T - i)) (r.bitIndices.toFinset : Set ℕ) := by
    intro i hi j hj hij
    have hi' := hbits r hr i hi
    have hj' := hbits r hr j hj
    have h1 : 2 ^ (T - i) = 2 ^ (T - j) := Nat.eq_of_mul_eq_mul_left hp.pos hij
    have := Nat.pow_right_injective le_rfl h1
    omega
  have hdisj : Disjoint E1 E2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hx2
    have hpd : p ∣ 2 ^ (T - i) := ⟨2 ^ (T - j), hj.symm⟩
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd)
    exact hp2 this
  refine ⟨E1 ∪ E2, ?_, ?_⟩
  · intro h0
    rcases Finset.mem_union.mp h0 with h | h
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
      exact absurd hi (by positivity)
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
      exact absurd hi (Nat.pos_iff_ne_zero.mp (Nat.mul_pos hp.pos (by positivity)))
  · rw [Finset.sum_union hdisj, Finset.sum_image (fun x hx y hy h => hinj1 hx hy h),
      Finset.sum_image (fun x hx y hy h => hinj2 hx hy h)]
    have hT2 : (2 : ℚ) ^ T ≠ 0 := by positivity
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have s1 : ∀ i ∈ q.bitIndices.toFinset, (1 : ℚ) / ((2 ^ (T - i) : ℕ) : ℚ) =
        (2 : ℚ) ^ i / 2 ^ T := by
      intro i hi
      have hiT := hbits q hq i hi
      have : (2 : ℚ) ^ T = 2 ^ (T - i) * 2 ^ i := by
        rw [← pow_add, Nat.sub_add_cancel hiT.le]
      rw [this]
      push_cast
      field_simp
    have s2 : ∀ i ∈ r.bitIndices.toFinset, (1 : ℚ) / ((p * 2 ^ (T - i) : ℕ) : ℚ) =
        (2 : ℚ) ^ i / (p * 2 ^ T) := by
      intro i hi
      have hiT := hbits r hr i hi
      have : (2 : ℚ) ^ T = 2 ^ (T - i) * 2 ^ i := by
        rw [← pow_add, Nat.sub_add_cancel hiT.le]
      rw [this]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl s1, Finset.sum_congr rfl s2, ← Finset.sum_div, ← Finset.sum_div]
    have hq' : ∑ i ∈ q.bitIndices.toFinset, (2 : ℚ) ^ i = q := by
      have hh := Nat.sum_map_two_pow_bitIndices q; rw [← List.sum_toFinset _ Nat.bitIndices_nodup] at hh; exact_mod_cast hh
    have hr' : ∑ i ∈ r.bitIndices.toFinset, (2 : ℚ) ^ i = r := by
      have hh := Nat.sum_map_two_pow_bitIndices r; rw [← List.sum_toFinset _ Nat.bitIndices_nodup] at hh; exact_mod_cast hh
    rw [hq', hr']
    have hdmQ : (p : ℚ) * q + r = a * 2 ^ T := by exact_mod_cast hdm
    rw [div_add_div _ _ hT2 (by positivity), div_eq_div_iff (by positivity) hp0]
    linear_combination (2 ^ T * (p : ℚ)) * hdmQ

end OMA305

open Erdos305 in
theorem OMA.solution : type_of% @Erdos305.erdos_305.variants.prime_lower_bound := by
  classical
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 3] with p hp3 hp
  set B := Dmax p with hB
  have hp2 : p ≠ 2 := by omega
  have hrep : ∀ a ∈ Finset.Ico 1 p, ∃ E : Finset ℕ, 0 ∉ E ∧ (∀ n ∈ E, n ≤ B) ∧
      ∑ n ∈ E, (1 : ℚ) / n = a / p := by
    intro a ha
    have hap : a < p := (Finset.mem_Ico.mp ha).2
    obtain ⟨E, hE0, hEs⟩ := OMA305.exists_rep p a hp hp2 hap
    have hne : {B' | ∃ E : Finset ℕ, 0 ∉ E ∧ (∀ n ∈ E, n ≤ B') ∧
        ∑ n ∈ E, (1 : ℚ) / n = a / p}.Nonempty :=
      ⟨E.sup id, E, hE0, fun n hn => Finset.le_sup (f := id) hn, hEs⟩
    obtain ⟨E', hE'0, hE'b, hE's⟩ := Nat.sInf_mem hne
    have hDle : D a p ≤ B := Finset.le_sup (f := fun a ↦ D a p) ha
    exact ⟨E', hE'0, fun n hn => (hE'b n hn).trans hDle, hE's⟩
  choose! g hg0 hgb hgs using hrep
  let φ : ℕ → Finset ℕ := fun a => (g a).filter (fun n => p ∣ n)
  have hmaps : ∀ a ∈ Finset.Ico 1 p,
      φ a ∈ ((Finset.Ioc 0 B).filter (fun n => p ∣ n)).powerset := by
    intro a ha
    rw [Finset.mem_powerset]
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero ?_, hgb a ha n hn.1⟩, hn.2⟩
    rintro rfl
    exact hg0 a ha hn.1
  have hinj : Set.InjOn φ (Finset.Ico 1 p : Set ℕ) := by
    intro a ha a' ha' hφ
    have ha1 := Finset.mem_coe.mp ha
    have ha1' := Finset.mem_coe.mp ha'
    have hs := hgs a ha1
    have hs' := hgs a' ha1'
    rw [← Finset.sum_filter_add_sum_filter_not (g a) (fun n => p ∣ n)] at hs
    rw [← Finset.sum_filter_add_sum_filter_not (g a') (fun n => p ∣ n)] at hs'
    have hφ' : (g a).filter (fun n => p ∣ n) = (g a').filter (fun n => p ∣ n) := hφ
    rw [hφ'] at hs
    set X := ∑ n ∈ (g a).filter (fun n => ¬ p ∣ n), (1 : ℚ) / n -
      ∑ n ∈ (g a').filter (fun n => ¬ p ∣ n), (1 : ℚ) / n with hX
    have hXeq : (a : ℚ) / p - a' / p = X := by rw [← hs, ← hs', hX]; ring
    have hXden : ¬ p ∣ X.den := by
      intro hd
      have h1 := hd.trans (Rat.sub_den_dvd _ _)
      rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · exact OMA305.den_not_dvd p hp _ (fun n hn => (Finset.mem_filter.mp hn).2) h2
      · exact OMA305.den_not_dvd p hp _ (fun n hn => (Finset.mem_filter.mp hn).2) h2
    exact OMA305.eq_of_den p a a' hp (Finset.mem_Ico.mp ha1).2 (Finset.mem_Ico.mp ha1').2
      X hXden hXeq
  have hcard := Finset.card_le_card_of_injOn φ (by intro a ha; exact hmaps a ha) hinj
  rw [Finset.card_powerset, Nat.Ioc_filter_dvd_card_eq_div, Nat.card_Ico] at hcard
  -- now `p - 1 ≤ 2 ^ (B / p)`
  set K := B / p with hK
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hKR : ((p : ℝ) - 1) ≤ 2 ^ K := by
    have : ((p - 1 : ℕ) : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast hcard
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)] at this
    exact this
  have hlog1 : Real.log ((p : ℝ) - 1) ≤ K * Real.log 2 := by
    have := Real.log_le_log (by linarith) hKR
    rwa [Real.log_pow] at this
  have hlog2 : Real.log p ≤ 2 * Real.log ((p : ℝ) - 1) := by
    have hsq : (p : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have := Real.log_le_log (by linarith) hsq
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hlogp : Real.log p ≤ 2 * K := by nlinarith
  have hKp : (K : ℝ) * p ≤ B := by exact_mod_cast Nat.div_mul_le_self B p
  have hlp0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  nlinarith
