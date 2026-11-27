import FormalConjectures.Wikipedia.WolstenholmePrime

-- Problem: Wolstenholme Prime — wolstenholme bernoulli
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/WolstenholmePrime.lean:71 (declaration WolstenholmePrime.wolstenholme_bernoulli)
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

section Helpers

open Finset
open scoped Nat

private lemma zmod_isUnit_natCast {M a : ℕ} (ha : a.Coprime M) : IsUnit (a : ZMod M) :=
  ⟨ZMod.unitOfCoprime a ha, rfl⟩

private lemma zmod_mul_ringInverse {M a : ℕ} (ha : a.Coprime M) :
    (a : ZMod M) * Ring.inverse (a : ZMod M) = 1 :=
  Ring.mul_inverse_cancel _ (zmod_isUnit_natCast ha)

private noncomputable def qmod (M : ℕ) (x : ℚ) : ZMod M :=
  (x.num : ZMod M) * Ring.inverse (x.den : ZMod M)

private lemma qmod_zero (M : ℕ) : qmod M 0 = 0 := by simp [qmod]

private lemma qmod_one (M : ℕ) : qmod M 1 = 1 := by simp [qmod]

private lemma qmod_nat (M n : ℕ) : qmod M (n : ℚ) = (n : ZMod M) := by
  simp [qmod]

private lemma qmod_int (M : ℕ) (z : ℤ) : qmod M (z : ℚ) = (z : ZMod M) := by
  simp [qmod]

private lemma qmod_neg (M : ℕ) (x : ℚ) : qmod M (-x) = -qmod M x := by
  simp [qmod, neg_mul]

private lemma qmod_mul_den {M : ℕ} (x : ℚ) (hx : x.den.Coprime M) :
    (x.den : ZMod M) * qmod M x = (x.num : ZMod M) := by
  unfold qmod
  rw [mul_left_comm, zmod_mul_ringInverse hx, mul_one]

private lemma qmod_eq_of_eq_div {M : ℕ} {x : ℚ} {a : ℤ} {b : ℕ}
    (hb : b.Coprime M) (hx : x.den.Coprime M) (h : x = (a : ℚ) / (b : ℚ)) :
    (b : ZMod M) * qmod M x = (a : ZMod M) := by
  rcases eq_or_ne M 1 with rfl | hM1
  · exact Subsingleton.elim _ _
  · have hb_ne0 : b ≠ 0 := by
      rintro rfl
      simp at hb
      exact hM1 hb
    have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb_ne0
    have hq : (x.num : ℚ) * (b : ℚ) = (a : ℚ) * (x.den : ℚ) := by
      calc (x.num : ℚ) * (b : ℚ) = (x * (x.den : ℚ)) * (b : ℚ) := by rw [Rat.mul_den_eq_num]
        _ = ((a : ℚ) / (b : ℚ)) * (b : ℚ) * (x.den : ℚ) := by rw [h]; ring
        _ = (a : ℚ) * (x.den : ℚ) := by rw [div_mul_cancel₀ _ hb0]
    have hz : x.num * (b : ℤ) = a * (x.den : ℤ) :=
      Int.cast_injective (α := ℚ) (by push_cast; exact hq)
    have hm : (x.num : ZMod M) * (b : ZMod M) = (a : ZMod M) * (x.den : ZMod M) := by
      simpa using congrArg (Int.cast : ℤ → ZMod M) hz
    have h1 : (x.den : ZMod M) * ((b : ZMod M) * qmod M x) = (x.den : ZMod M) * (a : ZMod M) := by
      calc (x.den : ZMod M) * ((b : ZMod M) * qmod M x)
          = (b : ZMod M) * ((x.den : ZMod M) * qmod M x) := by ring
        _ = (x.num : ZMod M) * (b : ZMod M) := by rw [qmod_mul_den x hx]; ring
        _ = (x.den : ZMod M) * (a : ZMod M) := by rw [hm]; ring
    exact (zmod_isUnit_natCast hx).mul_left_cancel h1

private lemma qmod_eq_div {M : ℕ} {x : ℚ} {a : ℤ} {b : ℕ}
    (hb : b.Coprime M) (hx : x.den.Coprime M) (h : x = (a : ℚ) / (b : ℚ)) :
    qmod M x = (a : ZMod M) * Ring.inverse (b : ZMod M) := by
  have h1 := congrArg (· * Ring.inverse (b : ZMod M)) (qmod_eq_of_eq_div hb hx h)
  simpa [mul_assoc, mul_comm (b : ZMod M) (qmod M x), zmod_mul_ringInverse hb] using h1

private lemma qmod_add {M : ℕ} {x y : ℚ} (hx : x.den.Coprime M) (hy : y.den.Coprime M) :
    qmod M (x + y) = qmod M x + qmod M y := by
  have hxy : (x + y).den.Coprime M := (hx.mul_left hy).coprime_dvd_left (Rat.add_den_dvd x y)
  have hx0 : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
  have hy0 : (y.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr y.den_nz
  have hdiv : x + y = ((x.num * (y.den : ℤ) + y.num * (x.den : ℤ) : ℤ) : ℚ) /
      ((x.den * y.den : ℕ) : ℚ) := by
    calc x + y = (x * (x.den : ℚ)) / (x.den : ℚ) + (y * (y.den : ℚ)) / (y.den : ℚ) := by
          rw [mul_div_cancel_right₀ _ hx0, mul_div_cancel_right₀ _ hy0]
      _ = (x.num : ℚ) / (x.den : ℚ) + (y.num : ℚ) / (y.den : ℚ) := by
          rw [Rat.mul_den_eq_num, Rat.mul_den_eq_num]
      _ = ((x.num * (y.den : ℤ) + y.num * (x.den : ℤ) : ℤ) : ℚ) /
            ((x.den * y.den : ℕ) : ℚ) := by
          push_cast; field_simp
  have heq := qmod_eq_of_eq_div (hx.mul_left hy) hxy hdiv
  have hprod : ((x.den * y.den : ℕ) : ZMod M) * (qmod M x + qmod M y) =
      ((x.num * (y.den : ℤ) + y.num * (x.den : ℤ) : ℤ) : ZMod M) := by
    push_cast
    calc ((x.den : ZMod M) * (y.den : ZMod M)) * (qmod M x + qmod M y)
        = ((x.den : ZMod M) * qmod M x) * (y.den : ZMod M) +
          ((y.den : ZMod M) * qmod M y) * (x.den : ZMod M) := by ring
      _ = (x.num : ZMod M) * (y.den : ZMod M) + (y.num : ZMod M) * (x.den : ZMod M) := by
          rw [qmod_mul_den x hx, qmod_mul_den y hy]
  exact (zmod_isUnit_natCast (hx.mul_left hy)).mul_left_cancel (heq.trans hprod.symm)

private lemma qmod_sub {M : ℕ} {x y : ℚ} (hx : x.den.Coprime M) (hy : y.den.Coprime M) :
    qmod M (x - y) = qmod M x - qmod M y := by
  rw [sub_eq_add_neg, qmod_add hx (by simpa using hy), qmod_neg, sub_eq_add_neg]

private lemma qmod_mul {M : ℕ} {x y : ℚ} (hx : x.den.Coprime M) (hy : y.den.Coprime M) :
    qmod M (x * y) = qmod M x * qmod M y := by
  have hxy : (x * y).den.Coprime M := (hx.mul_left hy).coprime_dvd_left (Rat.mul_den_dvd x y)
  have hx0 : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
  have hy0 : (y.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr y.den_nz
  have hdiv : x * y = ((x.num * y.num : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ) := by
    calc x * y = ((x * (x.den : ℚ)) / (x.den : ℚ)) * ((y * (y.den : ℚ)) / (y.den : ℚ)) := by
          rw [mul_div_cancel_right₀ _ hx0, mul_div_cancel_right₀ _ hy0]
      _ = ((x.num : ℚ) / (x.den : ℚ)) * ((y.num : ℚ) / (y.den : ℚ)) := by
          rw [Rat.mul_den_eq_num, Rat.mul_den_eq_num]
      _ = ((x.num * y.num : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ) := by
          push_cast; ring
  have heq := qmod_eq_of_eq_div (hx.mul_left hy) hxy hdiv
  have hprod : ((x.den * y.den : ℕ) : ZMod M) * (qmod M x * qmod M y) =
      ((x.num * y.num : ℤ) : ZMod M) := by
    push_cast
    calc ((x.den : ZMod M) * (y.den : ZMod M)) * (qmod M x * qmod M y)
        = ((x.den : ZMod M) * qmod M x) * ((y.den : ZMod M) * qmod M y) := by ring
      _ = (x.num : ZMod M) * (y.num : ZMod M) := by
          rw [qmod_mul_den x hx, qmod_mul_den y hy]
  exact (zmod_isUnit_natCast (hx.mul_left hy)).mul_left_cancel (heq.trans hprod.symm)

private lemma den_pow_coprime {M : ℕ} {x : ℚ} (hx : x.den.Coprime M) (n : ℕ) :
    (x ^ n).den.Coprime M := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact (ih.mul_left hx).coprime_dvd_left (Rat.mul_den_dvd _ _)

private lemma qmod_pow {M : ℕ} {x : ℚ} (hx : x.den.Coprime M) (n : ℕ) :
    qmod M (x ^ n) = qmod M x ^ n := by
  induction n with
  | zero => simp [qmod_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, qmod_mul (den_pow_coprime hx n) hx, ih]

private lemma den_sum_coprime {M : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, (f i).den.Coprime M) : (∑ i ∈ s, f i).den.Coprime M :=
  (Nat.Coprime.prod_left hf).coprime_dvd_left (Rat.den_sum_dvd_prod_den s f)

private lemma qmod_sum {M : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, (f i).den.Coprime M) :
    qmod M (∑ i ∈ s, f i) = ∑ i ∈ s, qmod M (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qmod_zero]
  | @insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    have ha_den : (f a).den.Coprime M := hf a (mem_insert_self a s)
    have hs_den := den_sum_coprime s f fun i hi => hf i (mem_insert_of_mem hi)
    rw [qmod_add ha_den hs_den, ih fun i hi => hf i (mem_insert_of_mem hi)]

private lemma qmod_cast {M M' : ℕ} (hd : M' ∣ M) {x : ℚ} (hx : x.den.Coprime M) :
    ZMod.castHom hd (ZMod M') (qmod M x) = qmod M' x := by
  have hx' : x.den.Coprime M' := hx.coprime_dvd_right hd
  have h1 := congrArg (ZMod.castHom hd (ZMod M')) (qmod_mul_den x hx)
  simp only [map_mul, map_natCast, map_intCast] at h1
  exact (zmod_isUnit_natCast hx').mul_left_cancel (h1.trans (qmod_mul_den x hx').symm)

private lemma qmod_zero_iff {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : x.den.Coprime p) :
    qmod p x = 0 ↔ (p : ℤ) ∣ x.num := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← (zmod_isUnit_natCast hx).mul_right_eq_zero, qmod_mul_den x hx]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd x.num p

private lemma qmod_p_pow_mul {p r : ℕ} {y : ℚ} (hy : y.den.Coprime p) :
    ((p : ℚ) ^ r * y).den.Coprime (p ^ r) ∧ qmod (p ^ r) ((p : ℚ) ^ r * y) = 0 := by
  have hpr : y.den.Coprime (p ^ r) := hy.pow_right r
  have hp_den : ((p : ℚ) ^ r).den.Coprime (p ^ r) := by simp
  have hden : ((p : ℚ) ^ r * y).den.Coprime (p ^ r) :=
    (hp_den.mul_left hpr).coprime_dvd_left (Rat.mul_den_dvd _ _)
  refine ⟨hden, ?_⟩
  rw [qmod_mul hp_den hpr, qmod_pow (by simp) r, qmod_nat]
  have hpz : ((p : ZMod (p ^ r)) ^ r) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [hpz, zero_mul]

private lemma den_one_div_coprime {M a : ℕ} (ha : a.Coprime M) :
    ((1 : ℚ) / (a : ℚ)).den.Coprime M := by
  have hdiv : ((1 : ℚ) / (a : ℚ)) = Rat.divInt 1 (a : ℤ) := by simp [Rat.divInt_eq_div]
  rw [hdiv]
  exact ha.coprime_dvd_left (Int.natCast_dvd_natCast.mp (Rat.den_dvd 1 (a : ℤ)))

private lemma den_mul_coprime {M : ℕ} {x y : ℚ} (hx : x.den.Coprime M) (hy : y.den.Coprime M) :
    (x * y).den.Coprime M := (hx.mul_left hy).coprime_dvd_left (Rat.mul_den_dvd x y)

private lemma den_add_coprime {M : ℕ} {x y : ℚ} (hx : x.den.Coprime M) (hy : y.den.Coprime M) :
    (x + y).den.Coprime M := (hx.mul_left hy).coprime_dvd_left (Rat.add_den_dvd x y)

private lemma den_sub_coprime {M : ℕ} {x y : ℚ} (hx : x.den.Coprime M) (hy : y.den.Coprime M) :
    (x - y).den.Coprime M := (hx.mul_left hy).coprime_dvd_left (Rat.sub_den_dvd x y)

private lemma not_dvd_den_bernoulli {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    ∀ n : ℕ, n = 0 ∨ ¬ (p - 1) ∣ n → (bernoulli n).den.Coprime p := by
  intro n hn
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · rcases eq_or_ne n 1 with rfl | hn1
    · rw [bernoulli_one]
      have hden : (-1 / 2 : ℚ).den = 2 := by norm_num
      rw [hden]
      exact (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    · rcases Nat.even_or_odd n with ⟨k, hk⟩ | hn_odd
      · rw [show k + k = 2 * k by omega] at hk
        subst hk
        have hndvd : ¬ (p - 1) ∣ 2 * k := by
          rcases hn with h | h
          · exact absurd h hn0
          · exact h
        obtain ⟨T, hT⟩ := Bernoulli.vonStaudt_clausen k
        have hB : bernoulli (2 * k) =
            (T : ℚ) - ∑ q ∈ (range (2 * k + 2)).filter
              (fun q => q.Prime ∧ (q - 1) ∣ 2 * k), (1 : ℚ) / q := by
          linarith
        rw [hB]
        have hsum_den :
            (∑ q ∈ (range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k),
              (1 : ℚ) / q).den.Coprime p := by
          refine den_sum_coprime _ _ fun q hq => ?_
          simp only [mem_filter, mem_range] at hq
          have hqne : q ≠ p := fun hqp => hndvd (hqp ▸ hq.2.2)
          have hqden : ((1 : ℚ) / q).den = q := by simp [hq.2.1.ne_zero]
          rw [hqden]
          exact (Nat.coprime_primes hq.2.1 hp).mpr hqne
        exact ((by simp : ((T : ℚ)).den.Coprime p).mul_left hsum_den).coprime_dvd_left
          (Rat.sub_den_dvd _ _)
      · rw [bernoulli_eq_zero_of_odd hn_odd (by omega)]
        simp

private lemma coprime_den_p_mul_bernoulli_pred {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    ((p : ℚ) * bernoulli (p - 1)).den.Coprime p := by
  obtain ⟨k, hk⟩ : ∃ k, p - 1 = 2 * k :=
    even_iff_two_dvd.mp (Nat.Prime.even_sub_one hp (by omega))
  have hk0 : 0 < k := by omega
  rw [hk]
  obtain ⟨T, hT⟩ := Bernoulli.vonStaudt_clausen k
  set S := ∑ q ∈ (range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k), (1 : ℚ) / q
  have hmem : p ∈ (range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k) := by
    simp only [mem_filter, mem_range]
    refine ⟨by omega, hp, by rw [← hk]⟩
  have hsplit : S = (1 : ℚ) / p +
      ∑ q ∈ ((range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k)).erase p,
        (1 : ℚ) / q := by
    simpa [S] using (add_sum_erase _ _ hmem).symm
  have hB : (p : ℚ) * bernoulli (2 * k) =
      (p : ℚ) * (T : ℚ) - 1 - (p : ℚ) *
        ∑ q ∈ ((range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k)).erase p,
          (1 : ℚ) / q := by
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hB0 : bernoulli (2 * k) = (T : ℚ) - S := by
      have : bernoulli (2 * k) + S = (T : ℚ) := by simpa [S] using hT.symm
      linarith
    rw [hB0, hsplit]
    field_simp [hp0]
    ring
  rw [hB]
  have hrest_den :
      (∑ q ∈ ((range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k)).erase p,
        (1 : ℚ) / q).den.Coprime p := by
    refine den_sum_coprime _ _ fun q hq => ?_
    rw [mem_erase, mem_filter] at hq
    have hqne : q ≠ p := hq.1
    have hqp : q.Prime := hq.2.2.1
    have hqden : ((1 : ℚ) / q).den = q := by simp [hqp.ne_zero]
    rw [hqden]
    exact (Nat.coprime_primes hq.2.2.1 hp).mpr hqne
  have hp_rest :
      ((p : ℚ) * ∑ q ∈ ((range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k)).erase p,
        (1 : ℚ) / q).den.Coprime p :=
    den_mul_coprime (by simp) hrest_den
  have h1 : ((p : ℚ) * (T : ℚ) - 1).den.Coprime p := by
    have hpt : (p : ℚ) * (T : ℚ) - 1 = (((p : ℤ) * T - 1 : ℤ) : ℚ) := by push_cast; ring
    rw [hpt, Rat.den_intCast]
    simp
  exact den_sub_coprime h1 hp_rest

private lemma exp_sub_one_ne_zero : PowerSeries.exp ℚ - 1 ≠ 0 := by
  intro h
  have := congrArg (PowerSeries.coeff 1) h
  simp at this

private lemma exp_add_rescale (x y : ℚ) :
    PowerSeries.rescale x (PowerSeries.exp ℚ) * PowerSeries.rescale y (PowerSeries.exp ℚ) =
      PowerSeries.rescale (x + y) (PowerSeries.exp ℚ) := by
  ext n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, Algebra.algebraMap_self]
  have hne : (n ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [← mul_left_inj' hne, Finset.sum_mul]
  have hrw : ((x + y) ^ n * (RingHom.id ℚ) (1 / (n ! : ℚ))) * (n ! : ℚ) = (x + y) ^ n := by
    simp; field_simp
  rw [hrw, add_pow]
  refine sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hc : (n.choose i : ℚ) * (i ! : ℚ) * ((n - i)! : ℚ) = (n ! : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  have hi0 : (i ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hni0 : ((n - i)! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - i))
  simp only [RingHom.id_apply]
  calc (x ^ i * (1 / (i ! : ℚ)) * (y ^ (n - i) * (1 / ((n - i)! : ℚ)))) * (n ! : ℚ)
      = x ^ i * y ^ (n - i) * ((n ! : ℚ) / ((i ! : ℚ) * ((n - i)! : ℚ))) := by ring
    _ = x ^ i * y ^ (n - i) * (n.choose i : ℚ) := by
        rw [← hc]; field_simp [hi0, hni0]

private lemma bernoulli_eval_add (n : ℕ) (x y : ℚ) :
    (Polynomial.bernoulli n).eval (x + y) =
      ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (Polynomial.bernoulli j).eval x * y ^ (n - j) := by
  let G : ℚ → PowerSeries ℚ := fun t =>
    PowerSeries.mk fun k => Polynomial.aeval t ((1 / (k ! : ℚ)) • Polynomial.bernoulli k)
  have hG : ∀ t, G t * (PowerSeries.exp ℚ - 1) = PowerSeries.X * PowerSeries.rescale t (PowerSeries.exp ℚ) :=
    fun t => Polynomial.bernoulli_generating_function t
  have heq : G (x + y) * (PowerSeries.exp ℚ - 1) =
      (G x * PowerSeries.rescale y (PowerSeries.exp ℚ)) * (PowerSeries.exp ℚ - 1) := by
    rw [hG (x + y), mul_right_comm, hG x, mul_assoc, exp_add_rescale x y]
  have hser : G (x + y) = G x * PowerSeries.rescale y (PowerSeries.exp ℚ) :=
    mul_right_cancel₀ exp_sub_one_ne_zero heq
  have hc := congrArg (PowerSeries.coeff n) hser
  simp only [G, PowerSeries.coeff_mk, Algebra.algebraMap_self, map_smul,
    Polynomial.coe_aeval_eq_eval, RingHom.id_apply, smul_eq_mul,
    PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp] at hc
  have hne : (n ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hc2 := congrArg (· * (n ! : ℚ)) hc
  have hl : 1 / (n ! : ℚ) * (Polynomial.bernoulli n).eval (x + y) * (n ! : ℚ) =
      (Polynomial.bernoulli n).eval (x + y) := by field_simp
  rw [hl, sum_mul] at hc2
  rw [hc2]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hch : (n.choose j : ℚ) * (j ! : ℚ) * ((n - j)! : ℚ) = (n ! : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
  have hj0 : (j ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hnj0 : ((n - j)! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - j))
  calc 1 / (j ! : ℚ) * (Polynomial.bernoulli j).eval x * (y ^ (n - j) * (1 / ((n - j)! : ℚ))) * (n ! : ℚ)
      = (Polynomial.bernoulli j).eval x * y ^ (n - j) *
          ((n ! : ℚ) / ((j ! : ℚ) * ((n - j)! : ℚ))) := by ring
    _ = (n.choose j : ℚ) * (Polynomial.bernoulli j).eval x * y ^ (n - j) := by
        rw [← hch]; field_simp [hj0, hnj0]

private lemma bernoulli_eval_one_half (n : ℕ) :
    (Polynomial.bernoulli n).eval (1 / 2 : ℚ) =
      (2 * (1 / 2 : ℚ) ^ n - 1) * bernoulli n := by
  let B0 : PowerSeries ℚ := bernoulliPowerSeries ℚ
  let G12 : PowerSeries ℚ :=
    PowerSeries.mk fun k => Polynomial.aeval (1 / 2 : ℚ) ((1 / (k ! : ℚ)) • Polynomial.bernoulli k)
  have hB0 : B0 * (PowerSeries.exp ℚ - 1) = PowerSeries.X :=
    bernoulliPowerSeries_mul_exp_sub_one ℚ
  have hG12 : G12 * (PowerSeries.exp ℚ - 1) =
      PowerSeries.X * PowerSeries.rescale (1 / 2 : ℚ) (PowerSeries.exp ℚ) :=
    Polynomial.bernoulli_generating_function (1 / 2 : ℚ)
  have hres : PowerSeries.rescale (1 / 2 : ℚ) B0 *
      (PowerSeries.rescale (1 / 2 : ℚ) (PowerSeries.exp ℚ) - 1) =
      PowerSeries.C (1 / 2 : ℚ) * PowerSeries.X := by
    have := congrArg (PowerSeries.rescale (1 / 2 : ℚ)) hB0
    simpa [PowerSeries.rescale_X] using this
  have hexp_sq : PowerSeries.exp ℚ - 1 =
      (PowerSeries.rescale (1 / 2 : ℚ) (PowerSeries.exp ℚ) - 1) *
        (PowerSeries.rescale (1 / 2 : ℚ) (PowerSeries.exp ℚ) + 1) := by
    have h2 : PowerSeries.rescale (1 / 2 : ℚ) (PowerSeries.exp ℚ) *
        PowerSeries.rescale (1 / 2 : ℚ) (PowerSeries.exp ℚ) = PowerSeries.exp ℚ := by
      rw [exp_add_rescale, add_halves, PowerSeries.rescale_one, RingHom.id_apply]
    linear_combination -h2
  have heq : (PowerSeries.C (2 : ℚ) * PowerSeries.rescale (1 / 2 : ℚ) B0 - B0) *
      (PowerSeries.exp ℚ - 1) = G12 * (PowerSeries.exp ℚ - 1) := by
    rw [sub_mul, hB0, hG12, hexp_sq]
    have h2x : PowerSeries.C (2 : ℚ) * (PowerSeries.C (1 / 2 : ℚ) * PowerSeries.X) =
        PowerSeries.X := by
      rw [← mul_assoc, ← map_mul]
      norm_num
    calc PowerSeries.C (2 : ℚ) * PowerSeries.rescale (1 / 2 : ℚ) B0 *
          ((PowerSeries.rescale (1 / 2 : ℚ) (PowerSeries.exp ℚ) - 1) *
            (PowerSeries.rescale (1 / 2 : ℚ) (PowerSeries.exp ℚ) + 1)) - PowerSeries.X
        = (PowerSeries.C (2 : ℚ) * (PowerSeries.rescale (1 / 2 : ℚ) B0 *
            (PowerSeries.rescale (1 / 2 : ℚ) (PowerSeries.exp ℚ) - 1))) *
            (PowerSeries.rescale (1 / 2 : ℚ) (PowerSeries.exp ℚ) + 1) - PowerSeries.X := by ring
      _ = PowerSeries.X * (PowerSeries.rescale (1 / 2 : ℚ) (PowerSeries.exp ℚ) + 1) -
            PowerSeries.X := by rw [hres, h2x]
      _ = PowerSeries.X * PowerSeries.rescale (1 / 2 : ℚ) (PowerSeries.exp ℚ) := by ring
  have hser := mul_right_cancel₀ exp_sub_one_ne_zero heq
  have hc := congrArg (PowerSeries.coeff n) hser
  simp only [B0, bernoulliPowerSeries, G12, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale, PowerSeries.coeff_mk, Algebra.algebraMap_self, map_smul,
    Polynomial.coe_aeval_eq_eval, RingHom.id_apply, smul_eq_mul] at hc
  have hne : (n ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hc2 := congrArg (· * (n ! : ℚ)) hc.symm
  field_simp [hne] at hc2 ⊢
  linarith [hc2]

private lemma prod_one_add_mod_quartic {ι R : Type*} [CommRing R] (s : Finset ι)
    (f : ι → R) (t : R) (ht : t ^ 4 = 0) :
    (6 : R) * ∏ i ∈ s, (1 + t * f i) =
      6 + 6 * t * (∑ i ∈ s, f i) +
      3 * t ^ 2 * ((∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, f i ^ 2) +
      t ^ 3 * ((∑ i ∈ s, f i) ^ 3 - 3 * (∑ i ∈ s, f i) * (∑ i ∈ s, f i ^ 2) +
        2 * ∑ i ∈ s, f i ^ 3) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, sum_insert ha, sum_insert ha]
    have hmul : (6 : R) * ((1 + t * f a) * ∏ i ∈ s, (1 + t * f i)) =
        (1 + t * f a) * ((6 : R) * ∏ i ∈ s, (1 + t * f i)) := by ring
    rw [hmul, ih]
    set s1 := ∑ i ∈ s, f i
    set s2 := ∑ i ∈ s, f i ^ 2
    set s3 := ∑ i ∈ s, f i ^ 3
    linear_combination
      (f a * s1 ^ 3 - 3 * f a * s1 * s2 + 2 * f a * s3 +
        t * f a * 0) * ht

private lemma sum_inv_pow_eq_zero_zmod {p m : ℕ} (hp : p.Prime) (hm1 : 1 ≤ m)
    (h2m : ¬ p ∣ 2 ^ m - 1) (hp2 : 2 < p) :
    ∑ k ∈ Ico 1 p, ((k : ZMod p)⁻¹) ^ m = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hfull : ∑ k ∈ Ico 1 p, ((k : ZMod p)⁻¹) ^ m = ∑ x : ZMod p, (x⁻¹) ^ m := by
    have hz : (0 : ZMod p)⁻¹ ^ m = 0 := by simp [zero_pow (by omega : m ≠ 0)]
    have hbij : ∑ k ∈ Ico 1 p, ((k : ZMod p)⁻¹) ^ m = ∑ x ∈ univ.erase (0 : ZMod p), (x⁻¹) ^ m := by
      refine sum_bij (fun k _ => (k : ZMod p)) (fun k hk => ?_)
        (fun a ha b hb hab => by
          rw [mem_Ico] at ha hb
          have : a % p = b % p := by
            have ha' : ((a : ZMod p)).val = ((b : ZMod p)).val := congrArg ZMod.val hab
            simpa [ZMod.val_natCast] using ha'
          rwa [Nat.mod_eq_of_lt ha.2, Nat.mod_eq_of_lt hb.2] at this)
        (fun x hx => by
          rw [mem_erase] at hx
          have hpos : 0 < x.val := Nat.pos_of_ne_zero fun h0 => hx.1 (by
            have := congrArg (Nat.cast : ℕ → ZMod p) h0
            simpa using this)
          exact ⟨x.val, mem_Ico.mpr ⟨hpos, ZMod.val_lt x⟩, by simp⟩)
        (fun _ _ => rfl)
      rw [mem_Ico] at hk
      rw [mem_erase]
      refine ⟨?_, mem_univ _⟩
      intro hz0
      rw [ZMod.natCast_eq_zero_iff] at hz0
      exact absurd (Nat.le_of_dvd hk.1 hz0) (by omega)
    rw [hbij, ← add_sum_erase univ (fun x : ZMod p => (x⁻¹) ^ m) (mem_univ (0 : ZMod p)), hz, zero_add]
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, ZMod.natCast_eq_zero_iff] at h
    exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  let e := Equiv.mulLeft₀ (2 : ZMod p) h2ne
  have hperm : ∑ x : ZMod p, (x⁻¹) ^ m = ∑ x : ZMod p, ((2 * x)⁻¹) ^ m :=
    (Fintype.sum_equiv e (fun x => ((e x)⁻¹) ^ m) (fun x => (x⁻¹) ^ m) (fun _ => rfl)).symm
  have hmul : ∑ x : ZMod p, ((2 * x)⁻¹) ^ m =
      ((2 : ZMod p)⁻¹) ^ m * ∑ x : ZMod p, (x⁻¹) ^ m := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_inv_rev, mul_pow, mul_comm ((2 : ZMod p)⁻¹ ^ m)]
  have hfact : (((2 : ZMod p)⁻¹) ^ m - 1) * ∑ x : ZMod p, (x⁻¹) ^ m = 0 := by
    have h1 := hperm.trans hmul
    linear_combination -h1
  have hne1 : ((2 : ZMod p)⁻¹) ^ m - 1 ≠ 0 := by
    intro h
    have hpow : (2 : ZMod p) ^ m = 1 := by
      have hh : ((2 : ZMod p)⁻¹) ^ m = 1 := sub_eq_zero.mp h
      calc (2 : ZMod p) ^ m = (2 : ZMod p) ^ m * (((2 : ZMod p)⁻¹) ^ m) := by rw [hh, mul_one]
        _ = ((2 : ZMod p) * (2 : ZMod p)⁻¹) ^ m := by rw [← mul_pow]
        _ = 1 := by rw [mul_inv_cancel₀ h2ne, one_pow]
    have h2dvd : p ∣ 2 ^ m - 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      have h1le : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by omega)
      rw [Nat.cast_sub h1le, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, hpow, sub_self]
    exact h2m h2dvd
  rw [hfull]
  exact (mul_eq_zero.mp hfact).resolve_left hne1

private lemma choose_mod_p_pow_four {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) :
    ((2 * p - 1).choose (p - 1) : ZMod (p ^ 4)) =
      1 - (p : ZMod (p ^ 4)) ^ 2 * ∑ k ∈ Ico 1 p, Ring.inverse (k : ZMod (p ^ 4)) ^ 2 := by
  let R := ZMod (p ^ 4)
  let t : R := (p : R)
  have ht4 : t ^ 4 = 0 := by
    change (p : ZMod (p ^ 4)) ^ 4 = 0
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hk_cop : ∀ k ∈ Ico 1 p, k.Coprime (p ^ 4) := by
    intro k hk
    rw [mem_Ico] at hk
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 hk.2)).symm.pow_right 4
  let u : ℕ → R := fun k => Ring.inverse (k : R)
  have hu : ∀ k ∈ Ico 1 p, (k : R) * u k = 1 := fun k hk => zmod_mul_ringInverse (hk_cop k hk)
  have hdesc : (2 * p - 1).descFactorial (p - 1) = (p - 1)! * (2 * p - 1).choose (p - 1) :=
    Nat.descFactorial_eq_factorial_mul_choose (2 * p - 1) (p - 1)
  have hdesc_prod : (2 * p - 1).descFactorial (p - 1) = ∏ k ∈ Ico 1 p, (p + k) := by
    rw [Nat.descFactorial_eq_prod_range]
    refine prod_bij (fun i _ => p - 1 - i) (fun i hi => ?_)
      (fun i₁ hi₁ i₂ hi₂ h => by rw [mem_range] at hi₁ hi₂; omega)
      (fun k hk => by rw [mem_Ico] at hk; exact ⟨p - 1 - k, mem_range.mpr (by omega), by omega⟩)
      (fun i hi => by rw [mem_range] at hi; omega)
    rw [mem_range] at hi
    rw [mem_Ico]
    omega
  have hfac_prod : (p - 1)! = ∏ k ∈ Ico 1 p, k := by
    have h := Finset.prod_Ico_id_eq_factorial (p - 1)
    rw [show p - 1 + 1 = p by omega] at h
    exact h.symm
  have hD_cop : (p - 1)!.Coprime (p ^ 4) := by
    refine (hp.coprime_iff_not_dvd.mpr ?_).symm.pow_right 4
    rw [Nat.Prime.dvd_factorial hp]
    omega
  have hprod_eq : (p - 1)! * (2 * p - 1).choose (p - 1) = ∏ k ∈ Ico 1 p, (p + k) := by
    rw [← hdesc, hdesc_prod]
  have hR_eq : ((p - 1)! : R) * ((2 * p - 1).choose (p - 1) : R) =
      ((p - 1)! : R) * ∏ k ∈ Ico 1 p, (1 + t * u k) := by
    have h0 : ((p - 1)! : R) * ((2 * p - 1).choose (p - 1) : R) = ∏ k ∈ Ico 1 p, (t + (k : R)) := by
      have hcast := congrArg (Nat.cast : ℕ → R) hprod_eq
      rw [Nat.cast_mul, Nat.cast_prod (fun k => p + k) (Ico 1 p)] at hcast
      refine hcast.trans (prod_congr rfl fun k _ => ?_)
      push_cast
      rfl
    have hfac_R : ((p - 1)! : R) = ∏ k ∈ Ico 1 p, (k : R) := by
      rw [hfac_prod]
      exact Nat.cast_prod (fun k : ℕ => k) (Ico 1 p)
    rw [h0, hfac_R, ← Finset.prod_mul_distrib]
    refine prod_congr rfl fun k hk => ?_
    exact (by rw [mul_add, mul_one, mul_left_comm, hu k hk, mul_one, add_comm] :
      (k : R) * (1 + t * u k) = t + (k : R)).symm
  have hP : ((2 * p - 1).choose (p - 1) : R) = ∏ k ∈ Ico 1 p, (1 + t * u k) := by
    exact (zmod_isUnit_natCast hD_cop).mul_left_cancel hR_eq
  have h6P : (6 : R) * ((2 * p - 1).choose (p - 1) : R) =
      6 + 6 * t * (∑ i ∈ Ico 1 p, u i) +
      3 * t ^ 2 * ((∑ i ∈ Ico 1 p, u i) ^ 2 - ∑ i ∈ Ico 1 p, u i ^ 2) +
      t ^ 3 * ((∑ i ∈ Ico 1 p, u i) ^ 3 - 3 * (∑ i ∈ Ico 1 p, u i) * (∑ i ∈ Ico 1 p, u i ^ 2) +
        2 * ∑ i ∈ Ico 1 p, u i ^ 3) := by
    rw [hP]
    exact prod_one_add_mod_quartic (Ico 1 p) u t ht4
  set S1 := ∑ k ∈ Ico 1 p, u k
  set S2 := ∑ k ∈ Ico 1 p, u k ^ 2
  set S3 := ∑ k ∈ Ico 1 p, u k ^ 3
  set S4 := ∑ k ∈ Ico 1 p, u k ^ 4
  have hS3_cast : ZMod.castHom (dvd_pow_self p (by omega : 4 ≠ 0)) (ZMod p) S3 = 0 := by
    letI : Fact p.Prime := ⟨hp⟩
    simp only [S3, map_sum, map_pow, u]
    have hmap : ∀ k ∈ Ico 1 p,
        ZMod.castHom (dvd_pow_self p (by omega : 4 ≠ 0)) (ZMod p) (Ring.inverse (k : R)) =
          (k : ZMod p)⁻¹ := by
      intro k hk
      have hk_ne : (k : ZMod p) ≠ 0 := by
        intro hz
        rw [ZMod.natCast_eq_zero_iff] at hz
        rw [mem_Ico] at hk
        exact absurd (Nat.le_of_dvd hk.1 hz) (by omega)
      have h1 := congrArg (ZMod.castHom (dvd_pow_self p (by omega : 4 ≠ 0)) (ZMod p)) (hu k hk)
      simp only [map_mul, map_natCast, map_one] at h1
      calc ZMod.castHom (dvd_pow_self p (by omega : 4 ≠ 0)) (ZMod p) (Ring.inverse (k : R))
          = (k : ZMod p)⁻¹ * ((k : ZMod p) *
              ZMod.castHom (dvd_pow_self p (by omega : 4 ≠ 0)) (ZMod p) (Ring.inverse (k : R))) := by
            rw [← mul_assoc, inv_mul_cancel₀ hk_ne, one_mul]
        _ = (k : ZMod p)⁻¹ := by rw [h1, mul_one]
    rw [sum_congr rfl fun k hk => by rw [hmap k hk]]
    exact sum_inv_pow_eq_zero_zmod hp (by omega)
      (by norm_num; exact Nat.not_dvd_of_pos_of_lt (by omega) hp7) (by omega)
  have hS2_cast : ZMod.castHom (dvd_pow_self p (by omega : 4 ≠ 0)) (ZMod p) S2 = 0 := by
    letI : Fact p.Prime := ⟨hp⟩
    simp only [S2, map_sum, map_pow, u]
    have hmap : ∀ k ∈ Ico 1 p,
        ZMod.castHom (dvd_pow_self p (by omega : 4 ≠ 0)) (ZMod p) (Ring.inverse (k : R)) =
          (k : ZMod p)⁻¹ := by
      intro k hk
      have hk_ne : (k : ZMod p) ≠ 0 := by
        intro hz
        rw [ZMod.natCast_eq_zero_iff] at hz
        rw [mem_Ico] at hk
        exact absurd (Nat.le_of_dvd hk.1 hz) (by omega)
      have h1 := congrArg (ZMod.castHom (dvd_pow_self p (by omega : 4 ≠ 0)) (ZMod p)) (hu k hk)
      simp only [map_mul, map_natCast, map_one] at h1
      calc ZMod.castHom (dvd_pow_self p (by omega : 4 ≠ 0)) (ZMod p) (Ring.inverse (k : R))
          = (k : ZMod p)⁻¹ * ((k : ZMod p) *
              ZMod.castHom (dvd_pow_self p (by omega : 4 ≠ 0)) (ZMod p) (Ring.inverse (k : R))) := by
            rw [← mul_assoc, inv_mul_cancel₀ hk_ne, one_mul]
        _ = (k : ZMod p)⁻¹ := by rw [h1, mul_one]
    rw [sum_congr rfl fun k hk => by rw [hmap k hk]]
    exact sum_inv_pow_eq_zero_zmod hp (by omega)
      (by norm_num; exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega : 3 < p)) (by omega)
  have hcast_zero_dvd : ∀ x : R,
      ZMod.castHom (dvd_pow_self p (by omega : 4 ≠ 0)) (ZMod p) x = 0 → ∃ c : R, x = t * c := by
    intro x hx
    haveI : NeZero (p ^ 4) := ⟨pow_ne_zero 4 hp.ne_zero⟩
    have hdvd : p ∣ x.val := by
      rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff] at hx
      exact hx
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨(c : R), ?_⟩
    have hcast := congrArg (Nat.cast : ℕ → R) hc
    rw [ZMod.natCast_zmod_val, Nat.cast_mul] at hcast
    exact hcast
  have hcast_zero_iff_mul_p3 : ∀ x : R,
      ZMod.castHom (dvd_pow_self p (by omega : 4 ≠ 0)) (ZMod p) x = 0 → t ^ 3 * x = 0 := by
    intro x hx
    obtain ⟨c, hc⟩ := hcast_zero_dvd x hx
    rw [hc]
    linear_combination c * ht4
  have ht3S3 : t ^ 3 * S3 = 0 := hcast_zero_iff_mul_p3 S3 hS3_cast
  have ht3S2 : t ^ 3 * S2 = 0 := hcast_zero_iff_mul_p3 S2 hS2_cast
  have hS2_dvd : ∃ d : R, S2 = t * d := hcast_zero_dvd S2 hS2_cast
  have hpair : 2 * S1 = -(t * S2 + t ^ 2 * S3 + t ^ 3 * S4) := by
    have h2S1 : 2 * S1 = ∑ k ∈ Ico 1 p, (u k + u (p - k)) := by
      rw [sum_add_distrib, two_mul]
      congr 1
      refine sum_bij (fun k _ => p - k) (fun k hk => ?_)
        (fun a ha b hb h => by rw [mem_Ico] at ha hb; omega)
        (fun k hk => by rw [mem_Ico] at hk; exact ⟨p - k, mem_Ico.mpr (by omega), by omega⟩)
        (fun k hk => by rw [mem_Ico] at hk; rw [Nat.sub_sub_self (by omega)])
      rw [mem_Ico] at hk ⊢; omega
    rw [h2S1]
    have hterm : ∀ k ∈ Ico 1 p,
        u k + u (p - k) = -(t * u k ^ 2 + t ^ 2 * u k ^ 3 + t ^ 3 * u k ^ 4) := by
      intro k hk
      rw [mem_Ico] at hk
      have hpk_mem : p - k ∈ Ico 1 p := mem_Ico.mpr (by omega)
      have hpk_sum : (k : R) + ((p - k : ℕ) : R) = t := by
        have h1 := congrArg (Nat.cast : ℕ → R) (show k + (p - k) = p by omega)
        simpa [Nat.cast_add, t] using h1
      have hsum_u : u k + u (p - k) = t * u k * u (p - k) := by
        calc u k + u (p - k)
            = u k * (((p - k : ℕ) : R) * u (p - k)) +
              u (p - k) * ((k : R) * u k) := by
                rw [hu (p - k) hpk_mem, mul_one, hu k (mem_Ico.mpr hk), mul_one]
          _ = ((p - k : ℕ) : R) * (u k * u (p - k)) + (k : R) * (u k * u (p - k)) := by ring
          _ = ((k : R) + ((p - k : ℕ) : R)) * (u k * u (p - k)) := by ring
          _ = t * u k * u (p - k) := by rw [hpk_sum]; ring
      have hprod_k : (k : R) * ((p - k : ℕ) : R) = t * (k : R) - (k : R) ^ 2 := by
        have hk_eq : ((p - k : ℕ) : R) = t - (k : R) := eq_sub_of_add_eq' hpk_sum
        rw [hk_eq]; ring
      have hid : (t * (k : R) - (k : R) ^ 2) * (u k ^ 2 + t * u k ^ 3 + t ^ 2 * u k ^ 4) =
          -1 + t ^ 3 * u k ^ 3 := by
        have hku : (k : R) * u k = 1 := hu k (mem_Ico.mpr hk)
        calc (t * (k : R) - (k : R) ^ 2) * (u k ^ 2 + t * u k ^ 3 + t ^ 2 * u k ^ 4)
            = t * ((k : R) * u k) * u k + t ^ 2 * ((k : R) * u k) * u k ^ 2 +
              t ^ 3 * ((k : R) * u k) * u k ^ 3 - ((k : R) * u k) ^ 2 -
              t * ((k : R) * u k) ^ 2 * u k - t ^ 2 * ((k : R) * u k) ^ 2 * u k ^ 2 := by ring
          _ = -1 + t ^ 3 * u k ^ 3 := by rw [hku]; ring
      have hid2 := congrArg (· * (t * u k * u (p - k))) hid
      have hlhs : (t * (k : R) - (k : R) ^ 2) * (u k ^ 2 + t * u k ^ 3 + t ^ 2 * u k ^ 4) *
          (t * u k * u (p - k)) = t * u k ^ 2 + t ^ 2 * u k ^ 3 + t ^ 3 * u k ^ 4 := by
        rw [← hprod_k]
        calc ((k : R) * ((p - k : ℕ) : R)) * (u k ^ 2 + t * u k ^ 3 + t ^ 2 * u k ^ 4) *
              (t * u k * u (p - k))
            = (((k : R) * u k) * (((p - k : ℕ) : R) * u (p - k))) *
                (t * (u k ^ 2 + t * u k ^ 3 + t ^ 2 * u k ^ 4)) := by ring
          _ = t * u k ^ 2 + t ^ 2 * u k ^ 3 + t ^ 3 * u k ^ 4 := by
              rw [hu k (mem_Ico.mpr hk), hu (p - k) hpk_mem, mul_one, one_mul]; ring
      have hrhs : (-1 + t ^ 3 * u k ^ 3) * (t * u k * u (p - k)) = -(u k + u (p - k)) := by
        calc (-1 + t ^ 3 * u k ^ 3) * (t * u k * u (p - k))
            = -(t * u k * u (p - k)) + t ^ 4 * u k ^ 4 * u (p - k) := by ring
          _ = -(u k + u (p - k)) := by rw [ht4, hsum_u]; ring
      rw [hlhs, hrhs] at hid2
      linear_combination hid2
    rw [sum_congr rfl hterm]
    simp only [sum_neg_distrib, sum_add_distrib, ← Finset.mul_sum]
    ring
  have hS1_dvd : ∃ c : R, S1 = t ^ 2 * c := by
    obtain ⟨d, hd⟩ := hS2_dvd
    have h2S1_t2 : 2 * S1 = t ^ 2 * (-d - S3 - t * S4) := by
      rw [hpair, hd]
      ring
    have h2_cop : Nat.Coprime 2 (p ^ 4) :=
      ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_right 4
    refine ⟨Ring.inverse (2 : R) * (-d - S3 - t * S4), ?_⟩
    have hinv2 : Ring.inverse (2 : R) * 2 = 1 := by
      rw [mul_comm]; exact zmod_mul_ringInverse h2_cop
    calc S1 = Ring.inverse (2 : R) * (2 * S1) := by
          rw [← mul_assoc, hinv2, one_mul]
      _ = Ring.inverse (2 : R) * (t ^ 2 * (-d - S3 - t * S4)) := by rw [h2S1_t2]
      _ = t ^ 2 * (Ring.inverse (2 : R) * (-d - S3 - t * S4)) := by ring
  obtain ⟨c, hc⟩ := hS1_dvd
  have hS1_sq : S1 ^ 2 = 0 := by
    rw [hc]
    linear_combination (t ^ 4 * c ^ 2) * 0 + (c ^ 2) * ht4
  have hS1_cu : S1 ^ 3 = 0 := by rw [pow_succ, hS1_sq, zero_mul]
  have ht3_S1_S2 : t ^ 3 * (S1 * S2) = 0 := by
    rw [hc]
    linear_combination (t * c * S2) * ht4
  have h6tS1 : 6 * t * S1 = -3 * t ^ 2 * S2 := by
    have := congrArg (3 * t * ·) hpair
    calc 6 * t * S1 = 3 * t * (2 * S1) := by ring
      _ = 3 * t * -(t * S2 + t ^ 2 * S3 + t ^ 3 * S4) := this
      _ = -3 * t ^ 2 * S2 - 3 * (t ^ 3 * S3) - 3 * (t ^ 4 * S4) := by ring
      _ = -3 * t ^ 2 * S2 := by rw [ht3S3, ht4]; ring
  have h6eq : (6 : R) * ((2 * p - 1).choose (p - 1) : R) = (6 : R) * (1 - t ^ 2 * S2) := by
    rw [h6P, hS1_sq, hS1_cu, h6tS1]
    calc 6 + -3 * t ^ 2 * S2 + 3 * t ^ 2 * (0 - S2) +
          t ^ 3 * (0 - 3 * S1 * S2 + 2 * S3)
        = 6 - 6 * t ^ 2 * S2 - 3 * (t ^ 3 * (S1 * S2)) + 2 * (t ^ 3 * S3) := by ring
      _ = (6 : R) * (1 - t ^ 2 * S2) := by rw [ht3_S1_S2, ht3S3]; ring
  have h6_cop : Nat.Coprime 6 (p ^ 4) := by
    have h6p : Nat.Coprime 6 p := by
      refine (hp.coprime_iff_not_dvd.mpr ?_).symm
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega : 6 < p)
    exact h6p.pow_right 4
  exact (zmod_isUnit_natCast h6_cop).mul_left_cancel h6eq

private lemma not_dvd_of_lt_two_mul {a b : ℕ} (_ha : 0 < a) (hb0 : 0 < b) (hb1 : b ≠ a)
    (hb2 : b < 2 * a) : ¬ a ∣ b := by
  rintro ⟨t, rfl⟩
  rcases Nat.lt_trichotomy t 1 with ht | rfl | ht
  · have : t = 0 := by omega
    subst this; simp at hb0
  · exact hb1 (by simp)
  · have hle : 2 * a ≤ a * t := by
      rw [mul_comm 2 a]
      exact Nat.mul_le_mul_left a (by omega)
    omega

private lemma sum_pow_mod_p_sq {p m : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hm_pos : 0 < m) (hm_lt : m < 2 * p - 2) (hndvd : ¬ (p - 1) ∣ m)
    (hm_gap : m ≠ p - 1 ∧ m ≠ p) (hm_cop : (m + 1).Coprime p) :
    ∑ k ∈ Ico 1 p, (k : ZMod (p ^ 2)) ^ m =
      (p : ZMod (p ^ 2)) * qmod (p ^ 2) (bernoulli m) := by
  have hp2 : 2 < p := by omega
  have hfull : ∑ k ∈ Ico 1 p, (k : ℚ) ^ m = ∑ k ∈ range p, (k : ℚ) ^ m := by
    rw [Finset.sum_range_eq_add_Ico _ hp.pos, Nat.cast_zero, zero_pow hm_pos.ne', zero_add]
  have hfau := sum_range_pow p m
  rw [← hfull] at hfau
  have hm1_cop : (m + 1).Coprime (p ^ 2) := hm_cop.pow_right 2
  have hB_m_den : (bernoulli m).den.Coprime (p ^ 2) :=
    (not_dvd_den_bernoulli hp hp2 m (Or.inr hndvd)).pow_right 2
  have hterm_den : ∀ i ∈ range (m + 1),
      (bernoulli i * ((m + 1).choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / (m + 1 : ℚ)).den.Coprime
        (p ^ 2) := by
    intro i hi
    have hi_le : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
    by_cases him : i = m
    · subst him
      have heq : bernoulli i * ((i + 1).choose i : ℚ) * (p : ℚ) ^ (i + 1 - i) / (i + 1 : ℚ) =
          bernoulli i * (p : ℚ) := by
        have hi0 : (i + 1 : ℚ) ≠ 0 := by positivity
        rw [Nat.add_sub_cancel_left, pow_one, Nat.choose_succ_self_right]
        push_cast; field_simp
      rw [heq]
      exact den_mul_coprime hB_m_den (by simp)
    · by_cases hip : i = p - 1
      · subst hip
        have hexp : 3 ≤ m + 1 - (p - 1) := by have := hm_gap.1; have := hm_gap.2; omega
        have hp_split : (p : ℚ) ^ (m + 1 - (p - 1)) =
            (p : ℚ) ^ 3 * (p : ℚ) ^ (m + 1 - (p - 1) - 3) := by
          rw [← pow_add]; congr 1; omega
        have heq : bernoulli (p - 1) * ((m + 1).choose (p - 1) : ℚ) *
              (p : ℚ) ^ (m + 1 - (p - 1)) / (m + 1 : ℚ) =
            (p : ℚ) ^ 2 * (((p : ℚ) * bernoulli (p - 1)) * ((m + 1).choose (p - 1) : ℚ) *
              (p : ℚ) ^ (m + 1 - (p - 1) - 3) * (1 / (m + 1 : ℚ))) := by
          rw [hp_split]
          ring
        rw [heq]
        have hy_den : (((p : ℚ) * bernoulli (p - 1)) * ((m + 1).choose (p - 1) : ℚ) *
            (p : ℚ) ^ (m + 1 - (p - 1) - 3) * (1 / (m + 1 : ℚ))).den.Coprime p := by
          have h1 := coprime_den_p_mul_bernoulli_pred hp hp2
          have h2 : (((m + 1).choose (p - 1) : ℚ)).den.Coprime p := by simp
          have h2b : ((p : ℚ) ^ (m + 1 - (p - 1) - 3)).den.Coprime p := by
            rw [← Nat.cast_pow, Rat.den_natCast]; exact Nat.coprime_one_left p
          have h3 : (1 / (m + 1 : ℚ)).den.Coprime p := by
            simpa [Nat.cast_add, Nat.cast_one] using den_one_div_coprime hm_cop
          exact den_mul_coprime (den_mul_coprime (den_mul_coprime h1 h2) h2b) h3
        exact (qmod_p_pow_mul (r := 2) hy_den).1
      · have hBi : (bernoulli i).den.Coprime p := by
          refine not_dvd_den_bernoulli hp hp2 i ?_
          rcases eq_or_ne i 0 with rfl | hi0
          · left; rfl
          · right
            exact not_dvd_of_lt_two_mul (by omega) (Nat.pos_of_ne_zero hi0) hip (by omega)
        have hexp : 2 ≤ m + 1 - i := by omega
        have hp_split : (p : ℚ) ^ (m + 1 - i) = (p : ℚ) ^ 2 * (p : ℚ) ^ (m + 1 - i - 2) := by
          rw [← pow_add]; congr 1; omega
        have heq : bernoulli i * ((m + 1).choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / (m + 1 : ℚ) =
            (p : ℚ) ^ 2 * (bernoulli i * ((m + 1).choose i : ℚ) *
              (p : ℚ) ^ (m + 1 - i - 2) * (1 / (m + 1 : ℚ))) := by
          rw [hp_split]
          ring
        rw [heq]
        have hy_den : (bernoulli i * ((m + 1).choose i : ℚ) *
            (p : ℚ) ^ (m + 1 - i - 2) * (1 / (m + 1 : ℚ))).den.Coprime p := by
          have h2 : (((m + 1).choose i : ℚ)).den.Coprime p := by simp
          have h2b : ((p : ℚ) ^ (m + 1 - i - 2)).den.Coprime p := by
            rw [← Nat.cast_pow, Rat.den_natCast]; exact Nat.coprime_one_left p
          have h3 : (1 / (m + 1 : ℚ)).den.Coprime p := by
            simpa [Nat.cast_add, Nat.cast_one] using den_one_div_coprime hm_cop
          exact den_mul_coprime (den_mul_coprime (den_mul_coprime hBi h2) h2b) h3
        exact (qmod_p_pow_mul (r := 2) hy_den).1
  have hl_den : (∑ k ∈ Ico 1 p, (k : ℚ) ^ m).den.Coprime (p ^ 2) := by
    refine den_sum_coprime _ _ fun k _ => by norm_cast; simp
  have hq := congrArg (qmod (p ^ 2)) hfau
  rw [qmod_sum _ _ fun k _ => by norm_cast; simp, qmod_sum _ _ hterm_den] at hq
  have hlhs : ∑ k ∈ Ico 1 p, qmod (p ^ 2) ((k : ℚ) ^ m) =
      ∑ k ∈ Ico 1 p, (k : ZMod (p ^ 2)) ^ m := by
    refine sum_congr rfl fun k _ => ?_
    rw [qmod_pow (by simp), qmod_nat]
  rw [hlhs, Finset.sum_range_succ] at hq
  have hrest_zero : ∑ i ∈ range m,
      qmod (p ^ 2) (bernoulli i * ((m + 1).choose i : ℚ) *
        (p : ℚ) ^ (m + 1 - i) / (m + 1 : ℚ)) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi_lt : i < m := mem_range.mp hi
    by_cases hip : i = p - 1
    · subst hip
      have hexp : 3 ≤ m + 1 - (p - 1) := by have := hm_gap.1; have := hm_gap.2; omega
      have hp_split : (p : ℚ) ^ (m + 1 - (p - 1)) =
          (p : ℚ) ^ 3 * (p : ℚ) ^ (m + 1 - (p - 1) - 3) := by
        rw [← pow_add]; congr 1; omega
      have heq : bernoulli (p - 1) * ((m + 1).choose (p - 1) : ℚ) *
            (p : ℚ) ^ (m + 1 - (p - 1)) / (m + 1 : ℚ) =
          (p : ℚ) ^ 2 * (((p : ℚ) * bernoulli (p - 1)) * ((m + 1).choose (p - 1) : ℚ) *
            (p : ℚ) ^ (m + 1 - (p - 1) - 3) * (1 / (m + 1 : ℚ))) := by
        rw [hp_split]; ring
      rw [heq]
      have hy_den : (((p : ℚ) * bernoulli (p - 1)) * ((m + 1).choose (p - 1) : ℚ) *
          (p : ℚ) ^ (m + 1 - (p - 1) - 3) * (1 / (m + 1 : ℚ))).den.Coprime p := by
        have h1 := coprime_den_p_mul_bernoulli_pred hp hp2
        have h2 : (((m + 1).choose (p - 1) : ℚ)).den.Coprime p := by simp
        have h2b : ((p : ℚ) ^ (m + 1 - (p - 1) - 3)).den.Coprime p := by
          rw [← Nat.cast_pow, Rat.den_natCast]; exact Nat.coprime_one_left p
        have h3 : (1 / (m + 1 : ℚ)).den.Coprime p := by
          simpa [Nat.cast_add, Nat.cast_one] using den_one_div_coprime hm_cop
        exact den_mul_coprime (den_mul_coprime (den_mul_coprime h1 h2) h2b) h3
      exact (qmod_p_pow_mul (r := 2) hy_den).2
    · have hBi : (bernoulli i).den.Coprime p := by
        refine not_dvd_den_bernoulli hp hp2 i ?_
        rcases eq_or_ne i 0 with rfl | hi0
        · left; rfl
        · right
          exact not_dvd_of_lt_two_mul (by omega) (Nat.pos_of_ne_zero hi0) hip (by omega)
      have hp_split : (p : ℚ) ^ (m + 1 - i) = (p : ℚ) ^ 2 * (p : ℚ) ^ (m + 1 - i - 2) := by
        rw [← pow_add]; congr 1; omega
      have heq : bernoulli i * ((m + 1).choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / (m + 1 : ℚ) =
          (p : ℚ) ^ 2 * (bernoulli i * ((m + 1).choose i : ℚ) *
            (p : ℚ) ^ (m + 1 - i - 2) * (1 / (m + 1 : ℚ))) := by
        rw [hp_split]; ring
      rw [heq]
      have hy_den : (bernoulli i * ((m + 1).choose i : ℚ) *
          (p : ℚ) ^ (m + 1 - i - 2) * (1 / (m + 1 : ℚ))).den.Coprime p := by
        have h2 : (((m + 1).choose i : ℚ)).den.Coprime p := by simp
        have h2b : ((p : ℚ) ^ (m + 1 - i - 2)).den.Coprime p := by
          rw [← Nat.cast_pow, Rat.den_natCast]; exact Nat.coprime_one_left p
        have h3 : (1 / (m + 1 : ℚ)).den.Coprime p := by
          simpa [Nat.cast_add, Nat.cast_one] using den_one_div_coprime hm_cop
        exact den_mul_coprime (den_mul_coprime (den_mul_coprime hBi h2) h2b) h3
      exact (qmod_p_pow_mul (r := 2) hy_den).2
  have hlast : qmod (p ^ 2)
      (bernoulli m * ((m + 1).choose m : ℚ) * (p : ℚ) ^ (m + 1 - m) / (m + 1 : ℚ)) =
      (p : ZMod (p ^ 2)) * qmod (p ^ 2) (bernoulli m) := by
    have heq : bernoulli m * ((m + 1).choose m : ℚ) * (p : ℚ) ^ (m + 1 - m) / (m + 1 : ℚ) =
        (p : ℚ) * bernoulli m := by
      have hm0 : (m + 1 : ℚ) ≠ 0 := by positivity
      rw [Nat.add_sub_cancel_left, pow_one, Nat.choose_succ_self_right]
      push_cast; field_simp
    rw [heq, qmod_mul (by simp) hB_m_den, qmod_nat]
  rw [hrest_zero, zero_add, hlast] at hq
  exact hq

private lemma sum_inv_sq_mod_p_sq {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) :
    ∑ k ∈ Ico 1 p, Ring.inverse (k : ZMod (p ^ 2)) ^ 2 =
      (p : ZMod (p ^ 2)) *
        (2 * qmod (p ^ 2) (bernoulli (p - 3)) - qmod (p ^ 2) (bernoulli (2 * p - 4))) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hterm : ∀ k ∈ Ico 1 p,
      Ring.inverse (k : ZMod (p ^ 2)) ^ 2 =
        2 * (k : ZMod (p ^ 2)) ^ (p - 3) - (k : ZMod (p ^ 2)) ^ (2 * p - 4) := by
    intro k hk
    rw [mem_Ico] at hk
    have hkc : k.Coprime (p ^ 2) :=
      ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 hk.2)).symm).pow_right 2
    have hflt : ((k : ZMod p) ^ (p - 1)) = 1 := by
      refine ZMod.pow_card_sub_one_eq_one ?_
      intro hz
      rw [ZMod.natCast_eq_zero_iff] at hz
      exact absurd (Nat.le_of_dvd hk.1 hz) (by omega)
    have hp_dvd : p ∣ ((k : ZMod (p ^ 2)) ^ (p - 1) - 1).val := by
      have hc : (ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) (ZMod p))
          ((k : ZMod (p ^ 2)) ^ (p - 1) - 1) = 0 := by
        simp [hflt]
      have hval := congrArg (ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) (ZMod p))
        (ZMod.natCast_zmod_val ((k : ZMod (p ^ 2)) ^ (p - 1) - 1))
      rw [map_natCast, hc] at hval
      exact (ZMod.natCast_eq_zero_iff _ p).mp hval
    obtain ⟨c, hc⟩ := hp_dvd
    have ht_eq : (k : ZMod (p ^ 2)) ^ (p - 1) - 1 = (p : ZMod (p ^ 2)) * (c : ZMod (p ^ 2)) := by
      have := congrArg (Nat.cast : ℕ → ZMod (p ^ 2)) hc
      simpa using this
    have hp2_zero : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    have hsq0 : ((k : ZMod (p ^ 2)) ^ (p - 1) - 1) ^ 2 = 0 := by
      rw [ht_eq]; linear_combination (c : ZMod (p ^ 2)) ^ 2 * hp2_zero
    have hmul := congrArg (· * Ring.inverse (k : ZMod (p ^ 2)) ^ 2) hsq0
    have hku : (k : ZMod (p ^ 2)) * Ring.inverse (k : ZMod (p ^ 2)) = 1 :=
      zmod_mul_ringInverse hkc
    have hp3 : p - 1 = (p - 3) + 2 := by omega
    have h2p4 : 2 * (p - 1) = (2 * p - 4) + 2 := by omega
    have h1 : (k : ZMod (p ^ 2)) ^ (p - 1) * Ring.inverse (k : ZMod (p ^ 2)) ^ 2 =
        (k : ZMod (p ^ 2)) ^ (p - 3) := by
      rw [hp3, pow_add, mul_assoc, ← mul_pow, hku, one_pow, mul_one]
    have h2 : ((k : ZMod (p ^ 2)) ^ (p - 1)) ^ 2 * Ring.inverse (k : ZMod (p ^ 2)) ^ 2 =
        (k : ZMod (p ^ 2)) ^ (2 * p - 4) := by
      rw [← pow_mul, mul_comm (p - 1) 2, h2p4, pow_add, mul_assoc, ← mul_pow, hku, one_pow, mul_one]
    have hzero : ((k : ZMod (p ^ 2)) ^ (p - 1) - 1) ^ 2 * Ring.inverse (k : ZMod (p ^ 2)) ^ 2 =
        (k : ZMod (p ^ 2)) ^ (2 * p - 4) - 2 * (k : ZMod (p ^ 2)) ^ (p - 3) +
          Ring.inverse (k : ZMod (p ^ 2)) ^ 2 := by
      calc ((k : ZMod (p ^ 2)) ^ (p - 1) - 1) ^ 2 * Ring.inverse (k : ZMod (p ^ 2)) ^ 2
          = ((k : ZMod (p ^ 2)) ^ (p - 1)) ^ 2 * Ring.inverse (k : ZMod (p ^ 2)) ^ 2 -
              2 * ((k : ZMod (p ^ 2)) ^ (p - 1) * Ring.inverse (k : ZMod (p ^ 2)) ^ 2) +
              Ring.inverse (k : ZMod (p ^ 2)) ^ 2 := by ring
        _ = (k : ZMod (p ^ 2)) ^ (2 * p - 4) - 2 * (k : ZMod (p ^ 2)) ^ (p - 3) +
              Ring.inverse (k : ZMod (p ^ 2)) ^ 2 := by rw [h2, h1]
    rw [zero_mul] at hmul
    linear_combination hmul - hzero
  rw [sum_congr rfl hterm, sum_sub_distrib, ← Finset.mul_sum]
  have hs1 := sum_pow_mod_p_sq hp hp7 (m := p - 3) (by omega) (by omega)
    (not_dvd_of_lt_two_mul (by omega) (by omega) (by omega) (by omega))
    ⟨by omega, by omega⟩
    ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm)
  have hs2 := sum_pow_mod_p_sq hp hp7 (m := 2 * p - 4) (by omega) (by omega)
    (not_dvd_of_lt_two_mul (by omega) (by omega) (by omega) (by omega))
    ⟨by omega, by omega⟩
    ((hp.coprime_iff_not_dvd.mpr (fun hd => by
      have hd' : p ∣ 2 * p - 3 := by rwa [show (2 * p - 4) + 1 = 2 * p - 3 by omega] at hd
      have hsub : p ∣ 2 * p - (2 * p - 3) := Nat.dvd_sub (dvd_mul_left p 2) hd'
      have : 2 * p - (2 * p - 3) = 3 := by omega
      rw [this] at hsub
      exact absurd (Nat.le_of_dvd (by omega) hsub) (by omega))).symm)
  rw [hs1, hs2]
  ring

private lemma kummer_congr_p_sub_three {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) :
    (3 : ZMod p) * qmod p (bernoulli (2 * p - 4)) =
      (4 : ZMod p) * qmod p (bernoulli (p - 3)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 < p := by omega
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  let q := (p + 1) / 2
  have h2q : 2 * q = p + 1 := by
    have : 2 ∣ p + 1 := by
      rcases hp_odd with ⟨k, rfl⟩
      exact ⟨k + 1, by omega⟩
    exact Nat.mul_div_cancel' this
  have hq_eq : (q : ℚ) = (1 / 2 : ℚ) + (p : ℚ) / 2 := by
    have : (2 : ℚ) * (q : ℚ) = (p : ℚ) + 1 := by exact_mod_cast h2q
    linarith
  have hmod_step : ∀ m : ℕ, 0 < m → m + 1 < 2 * p - 2 → ¬ (p - 1) ∣ (m + 1) →
      m + 1 ≠ p →
      (m + 1 : ZMod p) * ∑ k ∈ range q, (k : ZMod p) ^ m =
        ((2 : ZMod p) * Ring.inverse (2 : ZMod p) ^ (m + 1) - 2) *
          qmod p (bernoulli (m + 1)) := by
    intro m hm_pos hm_lt hndvd hm_ne_p
    have hf := Polynomial.sum_range_pow_eq_bernoulli_sub q m
    rw [hq_eq, bernoulli_eval_add (m + 1) (1 / 2 : ℚ) ((p : ℚ) / 2),
      Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, mul_one,
      Nat.cast_one, one_mul, bernoulli_eval_one_half (m + 1)] at hf
    have h2_cop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    have h12_den : (1 / 2 : ℚ).den.Coprime p := by
      have : (1 / 2 : ℚ).den = 2 := by norm_num
      rw [this]; exact h2_cop
    have h2_rat_den : (2 : ℚ).den.Coprime p := by norm_num
    have h1_rat_den : (1 : ℚ).den.Coprime p := by norm_num
    have hB_m1_den : (bernoulli (m + 1)).den.Coprime p :=
      not_dvd_den_bernoulli hp hp2 (m + 1) (Or.inr hndvd)
    have hB_half_den : ∀ j : ℕ, j = 0 ∨ ¬ (p - 1) ∣ j →
        ((Polynomial.bernoulli j).eval (1 / 2 : ℚ)).den.Coprime p := by
      intro j hj
      rw [bernoulli_eval_one_half]
      have h_pow : (2 * (1 / 2 : ℚ) ^ j - 1).den.Coprime p := by
        have hp1 := den_pow_coprime h12_den j
        have hp2' := den_mul_coprime h2_rat_den hp1
        exact den_sub_coprime hp2' h1_rat_den
      exact den_mul_coprime h_pow (not_dvd_den_bernoulli hp hp2 j hj)
    have htail_den : ∀ j ∈ range (m + 1),
        (((m + 1).choose j : ℚ) * (Polynomial.bernoulli j).eval (1 / 2 : ℚ) *
          ((p : ℚ) / 2) ^ (m + 1 - j)).den.Coprime p := by
      intro j hj
      have hj_lt : j < m + 1 := mem_range.mp hj
      by_cases hjp : j = p - 1
      · subst hjp
        have hexp : 2 ≤ m + 1 - (p - 1) := by omega
        have hp_split : (p : ℚ) ^ (m + 1 - (p - 1)) =
            (p : ℚ) ^ 2 * (p : ℚ) ^ (m + 1 - (p - 1) - 2) := by
          rw [← pow_add]; congr 1; omega
        have hp_half : ((p : ℚ) / 2) ^ (m + 1 - (p - 1)) =
            (p : ℚ) ^ (m + 1 - (p - 1)) * (1 / 2 : ℚ) ^ (m + 1 - (p - 1)) := by ring
        have heq : ((m + 1).choose (p - 1) : ℚ) * (Polynomial.bernoulli (p - 1)).eval (1 / 2 : ℚ) *
              ((p : ℚ) / 2) ^ (m + 1 - (p - 1)) =
            (p : ℚ) * (((m + 1).choose (p - 1) : ℚ) *
              (2 * (1 / 2 : ℚ) ^ (p - 1) - 1) * ((p : ℚ) * bernoulli (p - 1)) *
              (1 / 2 : ℚ) ^ (m + 1 - (p - 1)) * (p : ℚ) ^ (m + 1 - (p - 1) - 2)) := by
          rw [bernoulli_eval_one_half, hp_half, hp_split]
          ring
        rw [heq]
        have hy_den : (((m + 1).choose (p - 1) : ℚ) *
            (2 * (1 / 2 : ℚ) ^ (p - 1) - 1) * ((p : ℚ) * bernoulli (p - 1)) *
            (1 / 2 : ℚ) ^ (m + 1 - (p - 1)) * (p : ℚ) ^ (m + 1 - (p - 1) - 2)).den.Coprime p := by
          have ha : (2 * (1 / 2 : ℚ) ^ (p - 1) - 1).den.Coprime p :=
            den_sub_coprime (den_mul_coprime h2_rat_den (den_pow_coprime h12_den (p - 1))) h1_rat_den
          have hb := coprime_den_p_mul_bernoulli_pred hp hp2
          have hc := den_pow_coprime h12_den (m + 1 - (p - 1))
          have h1 : (((m + 1).choose (p - 1) : ℚ)).den.Coprime p := by
            rw [Rat.den_natCast]; exact Nat.coprime_one_left p
          have h2 : ((p : ℚ) ^ (m + 1 - (p - 1) - 2)).den.Coprime p := by
            rw [← Nat.cast_pow, Rat.den_natCast]; exact Nat.coprime_one_left p
          exact den_mul_coprime (den_mul_coprime (den_mul_coprime (den_mul_coprime h1 ha) hb) hc) h2
        simpa only [pow_one] using (qmod_p_pow_mul (r := 1) hy_den).1
      · have h2p2 : j < 2 * (p - 1) := by omega
        have hBj := hB_half_den j (by
          rcases eq_or_ne j 0 with rfl | hj0
          · left; rfl
          · right
            exact not_dvd_of_lt_two_mul (by omega) (Nat.pos_of_ne_zero hj0) hjp h2p2)
        have hp_split : (p : ℚ) ^ (m + 1 - j) = (p : ℚ) * (p : ℚ) ^ (m + 1 - j - 1) := by
          conv_lhs => rw [show m + 1 - j = (m + 1 - j - 1) + 1 by omega, pow_succ']
        have hp_half : ((p : ℚ) / 2) ^ (m + 1 - j) =
            (p : ℚ) ^ (m + 1 - j) * (1 / 2 : ℚ) ^ (m + 1 - j) := by ring
        have heq : ((m + 1).choose j : ℚ) * (Polynomial.bernoulli j).eval (1 / 2 : ℚ) *
              ((p : ℚ) / 2) ^ (m + 1 - j) =
            (p : ℚ) * (((m + 1).choose j : ℚ) * (Polynomial.bernoulli j).eval (1 / 2 : ℚ) *
              (1 / 2 : ℚ) ^ (m + 1 - j) * (p : ℚ) ^ (m + 1 - j - 1)) := by
          rw [hp_half, hp_split]; ring
        rw [heq]
        have hy_den : (((m + 1).choose j : ℚ) * (Polynomial.bernoulli j).eval (1 / 2 : ℚ) *
            (1 / 2 : ℚ) ^ (m + 1 - j) * (p : ℚ) ^ (m + 1 - j - 1)).den.Coprime p := by
          have h1 : (((m + 1).choose j : ℚ)).den.Coprime p := by
            rw [Rat.den_natCast]; exact Nat.coprime_one_left p
          have hc := den_pow_coprime h12_den (m + 1 - j)
          have h2 : ((p : ℚ) ^ (m + 1 - j - 1)).den.Coprime p := by
            rw [← Nat.cast_pow, Rat.den_natCast]; exact Nat.coprime_one_left p
          exact den_mul_coprime (den_mul_coprime (den_mul_coprime h1 hBj) hc) h2
        simpa only [pow_one] using (qmod_p_pow_mul (r := 1) hy_den).1
    have hq_congr := congrArg (qmod p) hf
    have hl_den1 : ((m + 1 : ℚ)).den.Coprime p := by
      have : (m : ℚ) + 1 = ((m + 1 : ℕ) : ℚ) := by push_cast; rfl
      rw [this, Rat.den_natCast]; exact Nat.coprime_one_left p
    have hl_den2 : (∑ k ∈ range q, (k : ℚ) ^ m).den.Coprime p :=
      den_sum_coprime _ _ fun k _ => by
        rw [← Nat.cast_pow, Rat.den_natCast]; exact Nat.coprime_one_left p
    have hmain_den : ((2 * (1 / 2 : ℚ) ^ (m + 1) - 1) * bernoulli (m + 1)).den.Coprime p := by
      have h_p := den_pow_coprime h12_den (m + 1)
      have h_p2 := den_mul_coprime h2_rat_den h_p
      have h_sub := den_sub_coprime h_p2 h1_rat_den
      exact den_mul_coprime h_sub hB_m1_den
    have hsum_tail_den := den_sum_coprime _ _ htail_den
    rw [qmod_mul hl_den1 hl_den2, qmod_sum _ _ fun k _ => by
        rw [← Nat.cast_pow, Rat.den_natCast]; exact Nat.coprime_one_left p,
      qmod_sub (den_add_coprime hsum_tail_den hmain_den) hB_m1_den,
      qmod_add hsum_tail_den hmain_den, qmod_sum _ _ htail_den] at hq_congr
    have htail_zero : ∑ j ∈ range (m + 1),
        qmod p (((m + 1).choose j : ℚ) * (Polynomial.bernoulli j).eval (1 / 2 : ℚ) *
          ((p : ℚ) / 2) ^ (m + 1 - j)) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj_lt : j < m + 1 := mem_range.mp hj
      by_cases hjp : j = p - 1
      · subst hjp
        have hexp : 2 ≤ m + 1 - (p - 1) := by omega
        have hp_split : (p : ℚ) ^ (m + 1 - (p - 1)) =
            (p : ℚ) ^ 2 * (p : ℚ) ^ (m + 1 - (p - 1) - 2) := by
          rw [← pow_add]; congr 1; omega
        have hp_half : ((p : ℚ) / 2) ^ (m + 1 - (p - 1)) =
            (p : ℚ) ^ (m + 1 - (p - 1)) * (1 / 2 : ℚ) ^ (m + 1 - (p - 1)) := by ring
        have heq : ((m + 1).choose (p - 1) : ℚ) * (Polynomial.bernoulli (p - 1)).eval (1 / 2 : ℚ) *
              ((p : ℚ) / 2) ^ (m + 1 - (p - 1)) =
            (p : ℚ) * (((m + 1).choose (p - 1) : ℚ) *
              (2 * (1 / 2 : ℚ) ^ (p - 1) - 1) * ((p : ℚ) * bernoulli (p - 1)) *
              (1 / 2 : ℚ) ^ (m + 1 - (p - 1)) * (p : ℚ) ^ (m + 1 - (p - 1) - 2)) := by
          rw [bernoulli_eval_one_half, hp_half, hp_split]; ring
        rw [heq]
        have hy_den : (((m + 1).choose (p - 1) : ℚ) *
            (2 * (1 / 2 : ℚ) ^ (p - 1) - 1) * ((p : ℚ) * bernoulli (p - 1)) *
            (1 / 2 : ℚ) ^ (m + 1 - (p - 1)) * (p : ℚ) ^ (m + 1 - (p - 1) - 2)).den.Coprime p := by
          have ha : (2 * (1 / 2 : ℚ) ^ (p - 1) - 1).den.Coprime p :=
            den_sub_coprime (den_mul_coprime h2_rat_den (den_pow_coprime h12_den (p - 1))) h1_rat_den
          have hb := coprime_den_p_mul_bernoulli_pred hp hp2
          have hc := den_pow_coprime h12_den (m + 1 - (p - 1))
          have h1 : (((m + 1).choose (p - 1) : ℚ)).den.Coprime p := by
            rw [Rat.den_natCast]; exact Nat.coprime_one_left p
          have h2 : ((p : ℚ) ^ (m + 1 - (p - 1) - 2)).den.Coprime p := by
            rw [← Nat.cast_pow, Rat.den_natCast]; exact Nat.coprime_one_left p
          exact den_mul_coprime (den_mul_coprime (den_mul_coprime (den_mul_coprime h1 ha) hb) hc) h2
        rw [qmod_mul (by rw [Rat.den_natCast]; exact Nat.coprime_one_left p) hy_den,
          qmod_nat, ZMod.natCast_self, zero_mul]
      · have h2p2 : j < 2 * (p - 1) := by omega
        have hBj := hB_half_den j (by
          rcases eq_or_ne j 0 with rfl | hj0
          · left; rfl
          · right
            exact not_dvd_of_lt_two_mul (by omega) (Nat.pos_of_ne_zero hj0) hjp h2p2)
        have hp_split : (p : ℚ) ^ (m + 1 - j) = (p : ℚ) * (p : ℚ) ^ (m + 1 - j - 1) := by
          conv_lhs => rw [show m + 1 - j = (m + 1 - j - 1) + 1 by omega, pow_succ']
        have hp_half : ((p : ℚ) / 2) ^ (m + 1 - j) =
            (p : ℚ) ^ (m + 1 - j) * (1 / 2 : ℚ) ^ (m + 1 - j) := by ring
        have heq : ((m + 1).choose j : ℚ) * (Polynomial.bernoulli j).eval (1 / 2 : ℚ) *
              ((p : ℚ) / 2) ^ (m + 1 - j) =
            (p : ℚ) * (((m + 1).choose j : ℚ) * (Polynomial.bernoulli j).eval (1 / 2 : ℚ) *
              (1 / 2 : ℚ) ^ (m + 1 - j) * (p : ℚ) ^ (m + 1 - j - 1)) := by
          rw [hp_half, hp_split]; ring
        rw [heq]
        have hy_den : (((m + 1).choose j : ℚ) * (Polynomial.bernoulli j).eval (1 / 2 : ℚ) *
            (1 / 2 : ℚ) ^ (m + 1 - j) * (p : ℚ) ^ (m + 1 - j - 1)).den.Coprime p := by
          have h1 : (((m + 1).choose j : ℚ)).den.Coprime p := by
            rw [Rat.den_natCast]; exact Nat.coprime_one_left p
          have hc := den_pow_coprime h12_den (m + 1 - j)
          have h2 : ((p : ℚ) ^ (m + 1 - j - 1)).den.Coprime p := by
            rw [← Nat.cast_pow, Rat.den_natCast]; exact Nat.coprime_one_left p
          exact den_mul_coprime (den_mul_coprime (den_mul_coprime h1 hBj) hc) h2
        rw [qmod_mul (by rw [Rat.den_natCast]; exact Nat.coprime_one_left p) hy_den,
          qmod_nat, ZMod.natCast_self, zero_mul]
    have hq12 : qmod p (1 / 2 : ℚ) = Ring.inverse (2 : ZMod p) := by
      simpa using qmod_eq_div (a := 1) h2_cop h12_den (by norm_num)
    have hq2_val : qmod p (2 : ℚ) = (2 : ZMod p) := by simpa using qmod_nat p 2
    have hmain_q : qmod p ((2 * (1 / 2 : ℚ) ^ (m + 1) - 1) * bernoulli (m + 1)) =
        (2 * Ring.inverse (2 : ZMod p) ^ (m + 1) - 1) * qmod p (bernoulli (m + 1)) := by
      have h_p := den_pow_coprime h12_den (m + 1)
      have h_p2 := den_mul_coprime h2_rat_den h_p
      rw [qmod_mul (den_sub_coprime h_p2 h1_rat_den) hB_m1_den,
        qmod_sub h_p2 h1_rat_den, qmod_mul h2_rat_den h_p,
        qmod_pow h12_den, hq12, hq2_val, qmod_one]
    rw [htail_zero, zero_add, hmain_q] at hq_congr
    have hpow_l : ∑ k ∈ range q, qmod p ((k : ℚ) ^ m) = ∑ k ∈ range q, (k : ZMod p) ^ m := by
      refine sum_congr rfl fun k _ => ?_
      rw [qmod_pow (by simp), qmod_nat]
    have hm1_l : qmod p ((m : ℚ) + 1) = (m : ZMod p) + 1 := by
      rw [show (m : ℚ) + 1 = ((m + 1 : ℕ) : ℚ) by push_cast; rfl, qmod_nat]
      push_cast; rfl
    rw [hm1_l, hpow_l] at hq_congr
    rw [hq_congr]
    ring
  have h1 := hmod_step (p - 4) (by omega) (by omega)
    (not_dvd_of_lt_two_mul (by omega) (by omega) (by omega) (by omega)) (by omega)
  have h2 := hmod_step (2 * p - 5) (by omega) (by omega)
    (not_dvd_of_lt_two_mul (by omega) (by omega) (by omega) (by omega)) (by omega)
  have hp_sub1_4 : p - 4 + 1 = p - 3 := by omega
  have h2p_sub1_5 : 2 * p - 5 + 1 = 2 * p - 4 := by omega
  rw [hp_sub1_4] at h1
  rw [h2p_sub1_5] at h2
  have hpow_sum : ∑ k ∈ range q, (k : ZMod p) ^ (2 * p - 5) =
      ∑ k ∈ range q, (k : ZMod p) ^ (p - 4) := by
    refine sum_congr rfl fun k _ => ?_
    by_cases hkz : (k : ZMod p) = 0
    · rw [hkz, zero_pow (by omega), zero_pow (by omega)]
    · have hflt := ZMod.pow_card_sub_one_eq_one hkz
      have hrw : 2 * p - 5 = (p - 1) + (p - 4) := by omega
      rw [hrw, pow_add, hflt, one_mul]
  have h2_cop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, ZMod.natCast_eq_zero_iff] at hz
    exact absurd (Nat.le_of_dvd (by omega) hz) (by omega)
  have h2_inv_flt : Ring.inverse (2 : ZMod p) ^ (p - 1) = 1 := by
    rw [Ring.inverse_eq_inv, ZMod.pow_card_sub_one_eq_one (inv_ne_zero h2ne)]
  have h2p4_eq : Ring.inverse (2 : ZMod p) ^ (2 * p - 4) =
      Ring.inverse (2 : ZMod p) ^ (p - 3) := by
    have hrw : 2 * p - 4 = (p - 1) + (p - 3) := by omega
    rw [hrw, pow_add, h2_inv_flt, one_mul]
  have hcoeff6 : (2 : ZMod p) * Ring.inverse (2 : ZMod p) ^ (p - 3) - 2 = 6 := by
    have hinv_eq : Ring.inverse (2 : ZMod p) ^ (p - 3) = (2 : ZMod p) ^ 2 := by
      have hmul2 : (2 : ZMod p) ^ (p - 3) * Ring.inverse (2 : ZMod p) ^ (p - 3) = 1 := by
        rw [← mul_pow, show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num,
          zmod_mul_ringInverse h2_cop, one_pow]
      have hp1 : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
      have hrw : p - 1 = (p - 3) + 2 := by omega
      rw [hrw, pow_add] at hp1
      calc Ring.inverse (2 : ZMod p) ^ (p - 3)
          = (2 : ZMod p) ^ (p - 3) * (2 : ZMod p) ^ 2 * Ring.inverse (2 : ZMod p) ^ (p - 3) := by
            rw [hp1, one_mul]
        _ = ((2 : ZMod p) ^ (p - 3) * Ring.inverse (2 : ZMod p) ^ (p - 3)) * (2 : ZMod p) ^ 2 := by
            ring
        _ = (2 : ZMod p) ^ 2 := by rw [hmul2, one_mul]
    rw [hinv_eq]
    norm_num
  rw [h2p4_eq, hcoeff6] at h2
  rw [hcoeff6] at h1
  have hm1_a : ((p - 4 : ℕ) : ZMod p) + 1 = -3 := by
    have : (p - 4 : ℕ) + 4 = p := by omega
    have h := congrArg (Nat.cast : ℕ → ZMod p) this
    push_cast at h
    rw [ZMod.natCast_self] at h
    linear_combination h
  have hm1_b : ((2 * p - 5 : ℕ) : ZMod p) + 1 = -4 := by
    have : (2 * p - 5 : ℕ) + 5 = 2 * p := by omega
    have h := congrArg (Nat.cast : ℕ → ZMod p) this
    push_cast at h
    rw [ZMod.natCast_self, mul_zero] at h
    linear_combination h
  rw [hm1_a] at h1
  rw [hm1_b, hpow_sum] at h2
  set S := ∑ k ∈ range q, (k : ZMod p) ^ (p - 4)
  have hrel : (6 : ZMod p) * (3 * qmod p (bernoulli (2 * p - 4)) - 4 * qmod p (bernoulli (p - 3))) = 0 := by
    calc (6 : ZMod p) * (3 * qmod p (bernoulli (2 * p - 4)) - 4 * qmod p (bernoulli (p - 3)))
        = 3 * (6 * qmod p (bernoulli (2 * p - 4))) - 4 * (6 * qmod p (bernoulli (p - 3))) := by ring
      _ = 3 * (-4 * S) - 4 * (-3 * S) := by rw [← h2, ← h1]
      _ = 0 := by ring
  have h6ne : (6 : ZMod p) ≠ 0 := by
    intro hz
    rw [show (6 : ZMod p) = ((6 : ℕ) : ZMod p) by norm_num, ZMod.natCast_eq_zero_iff] at hz
    exact absurd (Nat.le_of_dvd (by omega) hz) (by omega)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hrel).resolve_left h6ne)

end Helpers

theorem OMA.solution : type_of% @WolstenholmePrime.wolstenholme_bernoulli := by
  intro p
  constructor
  · rintro ⟨hp7, hp, hcong⟩
    refine ⟨hp7, hp, ?_⟩
    letI : Fact p.Prime := ⟨hp⟩
    have hp2 : 2 < p := by omega
    have hR : ((2 * p - 1).choose (p - 1) : ZMod (p ^ 4)) = 1 := by
      have := congrArg (Nat.cast : ℕ → ZMod (p ^ 4)) hcong
      simpa [Nat.ModEq, ZMod.natCast_eq_natCast_iff] using this
    rw [choose_mod_p_pow_four hp hp7] at hR
    have hp2S2 : (p : ZMod (p ^ 4)) ^ 2 * ∑ k ∈ Finset.Ico 1 p, Ring.inverse (k : ZMod (p ^ 4)) ^ 2 = 0 := by
      linear_combination -hR
    have hcast2 :
        ZMod.castHom (show p ^ 2 ∣ p ^ 4 from ⟨p ^ 2, by ring⟩) (ZMod (p ^ 2))
          (∑ k ∈ Finset.Ico 1 p, Ring.inverse (k : ZMod (p ^ 4)) ^ 2) =
        ∑ k ∈ Finset.Ico 1 p, Ring.inverse (k : ZMod (p ^ 2)) ^ 2 := by
      simp only [map_sum, map_pow]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_Ico] at hk
      have hkc4 : k.Coprime (p ^ 4) :=
        ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 hk.2)).symm).pow_right 4
      have hkc2 : k.Coprime (p ^ 2) :=
        ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 hk.2)).symm).pow_right 2
      have h1 := congrArg (ZMod.castHom (show p ^ 2 ∣ p ^ 4 from ⟨p ^ 2, by ring⟩) (ZMod (p ^ 2)))
        (zmod_mul_ringInverse hkc4)
      simp only [map_mul, map_natCast, map_one] at h1
      congr 1
      exact (zmod_isUnit_natCast hkc2).mul_left_cancel (h1.trans (zmod_mul_ringInverse hkc2).symm)
    have hp2_dvd_S2 : p ^ 2 ∣ (∑ k ∈ Finset.Ico 1 p, Ring.inverse (k : ZMod (p ^ 4)) ^ 2).val := by
      set S2 := ∑ k ∈ Finset.Ico 1 p, Ring.inverse (k : ZMod (p ^ 4)) ^ 2
      have hp4_pos : 0 < p ^ 4 := pow_pos hp.pos 4
      letI : NeZero (p ^ 4) := ⟨hp4_pos.ne'⟩
      have hp2_lt : p ^ 2 < p ^ 4 := by
        have h1 : 1 < p ^ 2 := Nat.one_lt_pow (by omega) hp.one_lt
        nlinarith
      have hmul_val : (p ^ 2 * S2.val) % p ^ 4 = 0 := by
        have h := congrArg ZMod.val hp2S2
        rw [ZMod.val_mul, ← Nat.cast_pow, ZMod.val_natCast_of_lt hp2_lt, ZMod.val_zero] at h
        exact h
      obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hmul_val
      have hd : p ^ 4 ∣ p ^ 2 * S2.val := ⟨q, hq⟩
      exact (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos 2)).mp (by rwa [show p ^ 2 * p ^ 2 = p ^ 4 by ring])
    have hS2_p2_zero : ∑ k ∈ Finset.Ico 1 p, Ring.inverse (k : ZMod (p ^ 2)) ^ 2 = 0 := by
      rw [← hcast2]
      have : ((∑ k ∈ Finset.Ico 1 p, Ring.inverse (k : ZMod (p ^ 4)) ^ 2).val : ZMod (p ^ 2)) = 0 :=
        (ZMod.natCast_eq_zero_iff _ (p ^ 2)).mpr hp2_dvd_S2
      rw [ZMod.castHom_apply, ← this]
      simp
    rw [sum_inv_sq_mod_p_sq hp hp7] at hS2_p2_zero
    have hp_dvd_diff : p ∣ (2 * qmod (p ^ 2) (bernoulli (p - 3)) - qmod (p ^ 2) (bernoulli (2 * p - 4))).val := by
      set D := 2 * qmod (p ^ 2) (bernoulli (p - 3)) - qmod (p ^ 2) (bernoulli (2 * p - 4))
      have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
      letI : NeZero (p ^ 2) := ⟨hp2_pos.ne'⟩
      have hp_lt : p < p ^ 2 := by nlinarith
      have hmul_val : (p * D.val) % p ^ 2 = 0 := by
        have h := congrArg ZMod.val hS2_p2_zero
        rw [ZMod.val_mul, ZMod.val_natCast_of_lt hp_lt, ZMod.val_zero] at h
        exact h
      obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hmul_val
      exact (Nat.mul_dvd_mul_iff_left hp.pos).mp (by rw [show p * p = p ^ 2 by ring]; exact ⟨q, hq⟩)
    have hD_p : (2 * qmod p (bernoulli (p - 3)) - qmod p (bernoulli (2 * p - 4))) = 0 := by
      have hB1 : (bernoulli (p - 3)).den.Coprime (p ^ 2) :=
        (not_dvd_den_bernoulli hp hp2 (p - 3) (Or.inr
          (not_dvd_of_lt_two_mul (by omega) (by omega) (by omega) (by omega)))).pow_right 2
      have hB2 : (bernoulli (2 * p - 4)).den.Coprime (p ^ 2) :=
        (not_dvd_den_bernoulli hp hp2 (2 * p - 4) (Or.inr
          (not_dvd_of_lt_two_mul (by omega) (by omega) (by omega) (by omega)))).pow_right 2
      have hdvd_p : p ∣ p ^ 2 := ⟨p, by ring⟩
      have hcast := congrArg (ZMod.castHom hdvd_p (ZMod p))
        (show 2 * qmod (p ^ 2) (bernoulli (p - 3)) - qmod (p ^ 2) (bernoulli (2 * p - 4)) =
          ((2 * qmod (p ^ 2) (bernoulli (p - 3)) - qmod (p ^ 2) (bernoulli (2 * p - 4))).val : ZMod (p ^ 2)) by
          simp)
      have hzero : (ZMod.castHom hdvd_p (ZMod p))
          ((2 * qmod (p ^ 2) (bernoulli (p - 3)) - qmod (p ^ 2) (bernoulli (2 * p - 4))).val : ZMod (p ^ 2)) = 0 := by
        simpa [ZMod.castHom_apply] using (ZMod.natCast_eq_zero_iff _ p).mpr hp_dvd_diff
      rw [hzero, map_sub, map_mul, map_ofNat, qmod_cast hdvd_p hB1, qmod_cast hdvd_p hB2] at hcast
      exact hcast
    have h2B : (2 : ZMod p) * qmod p (bernoulli (p - 3)) = 0 := by
      have hk := kummer_congr_p_sub_three hp hp7
      have heq : qmod p (bernoulli (2 * p - 4)) = 2 * qmod p (bernoulli (p - 3)) := (sub_eq_zero.mp hD_p).symm
      rw [heq] at hk
      linear_combination hk
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro hz
      rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, ZMod.natCast_eq_zero_iff] at hz
      exact absurd (Nat.le_of_dvd (by omega) hz) (by omega)
    have hBp : qmod p (bernoulli (p - 3)) = 0 := (mul_eq_zero.mp h2B).resolve_left h2ne
    rw [bernoulli_eq_bernoulli'_of_ne_one (by omega)] at hBp
    exact (qmod_zero_iff hp (by
      rw [← bernoulli_eq_bernoulli'_of_ne_one (by omega)]
      exact not_dvd_den_bernoulli hp hp2 (p - 3) (Or.inr
        (not_dvd_of_lt_two_mul (by omega) (by omega) (by omega) (by omega))))).mp hBp
  · rintro ⟨hp7, hp, hdvd⟩
    refine ⟨hp7, hp, ?_⟩
    letI : Fact p.Prime := ⟨hp⟩
    have hp2 : 2 < p := by omega
    have hBp_den : (bernoulli (p - 3)).den.Coprime p :=
      not_dvd_den_bernoulli hp hp2 (p - 3) (Or.inr
        (not_dvd_of_lt_two_mul (by omega) (by omega) (by omega) (by omega)))
    have hBp : qmod p (bernoulli (p - 3)) = 0 := by
      rw [qmod_zero_iff hp hBp_den, bernoulli_eq_bernoulli'_of_ne_one (by omega)]
      exact hdvd
    have hk := kummer_congr_p_sub_three hp hp7
    rw [hBp, mul_zero] at hk
    have h3ne : (3 : ZMod p) ≠ 0 := by
      intro hz
      rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) by norm_num, ZMod.natCast_eq_zero_iff] at hz
      exact absurd (Nat.le_of_dvd (by omega) hz) (by omega)
    have hB2p : qmod p (bernoulli (2 * p - 4)) = 0 := (mul_eq_zero.mp hk).resolve_left h3ne
    have hD_p : (2 * qmod p (bernoulli (p - 3)) - qmod p (bernoulli (2 * p - 4))) = 0 := by
      rw [hBp, hB2p]; ring
    have hdvd_p : p ∣ p ^ 2 := ⟨p, by ring⟩
    have hB1 : (bernoulli (p - 3)).den.Coprime (p ^ 2) := hBp_den.pow_right 2
    have hB2 : (bernoulli (2 * p - 4)).den.Coprime (p ^ 2) :=
      (not_dvd_den_bernoulli hp hp2 (2 * p - 4) (Or.inr
        (not_dvd_of_lt_two_mul (by omega) (by omega) (by omega) (by omega)))).pow_right 2
    set D := 2 * qmod (p ^ 2) (bernoulli (p - 3)) - qmod (p ^ 2) (bernoulli (2 * p - 4))
    have hD_cast : (D.val : ZMod p) = 0 := by
      have := congrArg (ZMod.castHom hdvd_p (ZMod p)) (show D = (D.val : ZMod (p ^ 2)) by simp)
      rw [map_sub, map_mul, map_ofNat, qmod_cast hdvd_p hB1, qmod_cast hdvd_p hB2, hD_p] at this
      simpa [ZMod.castHom_apply] using this.symm
    obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff D.val p).mp hD_cast
    have hD_eq : D = (p : ZMod (p ^ 2)) * (c : ZMod (p ^ 2)) := by
      have := congrArg (Nat.cast : ℕ → ZMod (p ^ 2)) hc
      simpa using this
    have hp2_zero : (p : ZMod (p ^ 2)) ^ 2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    have hS2_p2 : ∑ k ∈ Finset.Ico 1 p, Ring.inverse (k : ZMod (p ^ 2)) ^ 2 = 0 := by
      rw [sum_inv_sq_mod_p_sq hp hp7]
      change (p : ZMod (p ^ 2)) * D = 0
      rw [hD_eq]
      linear_combination (c : ZMod (p ^ 2)) * hp2_zero
    have hcast2 :
        ZMod.castHom (show p ^ 2 ∣ p ^ 4 from ⟨p ^ 2, by ring⟩) (ZMod (p ^ 2))
          (∑ k ∈ Finset.Ico 1 p, Ring.inverse (k : ZMod (p ^ 4)) ^ 2) = 0 := by
      rw [← hS2_p2]
      simp only [map_sum, map_pow]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_Ico] at hk
      have hkc4 : k.Coprime (p ^ 4) :=
        ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 hk.2)).symm).pow_right 4
      have hkc2 : k.Coprime (p ^ 2) :=
        ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 hk.2)).symm).pow_right 2
      have h1 := congrArg (ZMod.castHom (show p ^ 2 ∣ p ^ 4 from ⟨p ^ 2, by ring⟩) (ZMod (p ^ 2)))
        (zmod_mul_ringInverse hkc4)
      simp only [map_mul, map_natCast, map_one] at h1
      congr 1
      exact (zmod_isUnit_natCast hkc2).mul_left_cancel (h1.trans (zmod_mul_ringInverse hkc2).symm)
    set S2 := ∑ k ∈ Finset.Ico 1 p, Ring.inverse (k : ZMod (p ^ 4)) ^ 2
    have hdvd_S2 : p ^ 2 ∣ S2.val := by
      have : (S2.val : ZMod (p ^ 2)) = 0 := by simpa [ZMod.castHom_apply] using hcast2
      exact (ZMod.natCast_eq_zero_iff S2.val (p ^ 2)).mp this
    obtain ⟨d, hd⟩ := hdvd_S2
    have hS2_eq : S2 = (p : ZMod (p ^ 4)) ^ 2 * (d : ZMod (p ^ 4)) := by
      have := congrArg (Nat.cast : ℕ → ZMod (p ^ 4)) hd
      simpa [Nat.cast_pow] using this
    have hp4_zero : (p : ZMod (p ^ 4)) ^ 4 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    have hR : ((2 * p - 1).choose (p - 1) : ZMod (p ^ 4)) = 1 := by
      rw [choose_mod_p_pow_four hp hp7]
      change 1 - (p : ZMod (p ^ 4)) ^ 2 * S2 = 1
      rw [hS2_eq]
      linear_combination -(d : ZMod (p ^ 4)) * hp4_zero
    have hval := congrArg ZMod.val hR
    letI : NeZero (p ^ 4) := ⟨(pow_pos hp.pos 4).ne'⟩
    rw [ZMod.val_natCast, ← Nat.cast_one (R := ZMod (p ^ 4)), ZMod.val_natCast] at hval
    exact hval

