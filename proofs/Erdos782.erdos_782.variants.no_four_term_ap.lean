import FormalConjectures.ErdosProblems.«782»

namespace OMAErdos782

private lemma sq_mod_two (n : ℕ) : n ^ 2 % 2 = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [sq, Nat.mul_mod, h]

private lemma sq_mod_four_of_odd {n : ℕ} (h : n % 2 = 1) : n ^ 2 % 4 = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
  rw [hk]
  have h1 : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
  rw [h1]
  omega

private lemma sq_mod_four_of_even {n : ℕ} (h : n % 2 = 0) : n ^ 2 % 4 = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  rw [hk]
  have h1 : (2 * k) ^ 2 = 4 * (k * k) := by ring
  rw [h1]
  omega

private lemma coprime_mul_eq_mul_pos {A B C D : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hD : 0 < D) (hAB : Nat.Coprime A B) (hCD : Nat.Coprime C D) (heq : A * B = C * D) :
    ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      A = a * b ∧ B = c * d ∧ C = a * c ∧ D = b * d ∧
      Nat.Coprime a b ∧ Nat.Coprime a d ∧ Nat.Coprime b c ∧ Nat.Coprime c d := by
  set a := Nat.gcd A C
  have ha_pos : 0 < a := Nat.gcd_pos_of_pos_left C hA
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_left A C
  obtain ⟨c, hc⟩ := Nat.gcd_dvd_right A C
  have hb_pos : 0 < b := by
    by_contra h
    have : b = 0 := by omega
    rw [this, mul_zero] at hb
    omega
  have hc_pos : 0 < c := by
    by_contra h
    have : c = 0 := by omega
    rw [this, mul_zero] at hc
    omega
  have hbc : Nat.Coprime b c := by
    have hgcd : Nat.gcd (a * b) (a * c) = a := by rw [← hb, ← hc]
    rw [Nat.gcd_mul_left] at hgcd
    have h1 : a * Nat.gcd b c = a * 1 := by simpa using hgcd
    exact Nat.eq_of_mul_eq_mul_left ha_pos h1
  have hmul : b * B = c * D := by
    have h1 : a * (b * B) = a * (c * D) := by
      calc a * (b * B) = (a * b) * B := by ring
        _ = A * B := by rw [← hb]
        _ = C * D := heq
        _ = (a * c) * D := by rw [hc]
        _ = a * (c * D) := by ring
    exact Nat.eq_of_mul_eq_mul_left ha_pos h1
  obtain ⟨d, hd⟩ := hbc.symm.dvd_of_dvd_mul_left ⟨D, hmul⟩
  have hd_pos : 0 < d := by
    by_contra h
    have : d = 0 := by omega
    rw [this, mul_zero] at hd
    omega
  have hD_eq : D = b * d := by
    have h1 : c * D = c * (b * d) := by
      calc c * D = b * B := hmul.symm
        _ = b * (c * d) := by rw [hd]
        _ = c * (b * d) := by ring
    exact Nat.eq_of_mul_eq_mul_left hc_pos h1
  have hab : Nat.Coprime a b := by
    rw [hc, hD_eq] at hCD
    exact (Nat.coprime_mul_iff_right.mp (Nat.coprime_mul_iff_left.mp hCD).1).1
  have had : Nat.Coprime a d := by
    rw [hb, hd] at hAB
    exact (Nat.coprime_mul_iff_right.mp (Nat.coprime_mul_iff_left.mp hAB).1).2
  have hcd : Nat.Coprime c d := by
    rw [hc, hD_eq] at hCD
    exact (Nat.coprime_mul_iff_right.mp (Nat.coprime_mul_iff_left.mp hCD).2).2
  exact ⟨a, b, c, d, ha_pos, hb_pos, hc_pos, hd_pos, hb, hd, hc, hD_eq, hab, had, hbc, hcd⟩

private lemma isSquare_of_coprime_mul_eq_sq_left {x y z : ℕ} (hxy : Nat.Coprime x y)
    (heq : x * y = z ^ 2) : ∃ u : ℕ, x = u ^ 2 := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  · set u := Nat.gcd x z
    have hx_pos : 0 < x := Nat.pos_of_ne_zero hx
    have hu_pos : 0 < u := Nat.gcd_pos_of_pos_left z hx_pos
    obtain ⟨x', hx'⟩ := Nat.gcd_dvd_left x z
    obtain ⟨z', hz'⟩ := Nat.gcd_dvd_right x z
    have hx'_pos : 0 < x' := by
      by_contra h; have : x' = 0 := by omega
      rw [this, mul_zero] at hx'; omega
    have hcop_xz : Nat.Coprime x' z' := by
      have hgcd : Nat.gcd (u * x') (u * z') = u := by rw [← hx', ← hz']
      rw [Nat.gcd_mul_left] at hgcd
      exact Nat.eq_of_mul_eq_mul_left hu_pos (by simpa using hgcd)
    have hmul : x' * y = u * z' ^ 2 := by
      have h1 : u * (x' * y) = u * (u * z' ^ 2) := by
        calc u * (x' * y) = (u * x') * y := by ring
          _ = x * y := by rw [← hx']
          _ = z ^ 2 := heq
          _ = (u * z') ^ 2 := by rw [hz']
          _ = u * (u * z' ^ 2) := by ring
      exact Nat.eq_of_mul_eq_mul_left hu_pos h1
    have hx'_dvd_u : x' ∣ u := (hcop_xz.pow_right 2).dvd_of_dvd_mul_right ⟨y, hmul.symm⟩
    obtain ⟨k, hk⟩ := hx'_dvd_u
    have hy_eq : y = k * z' ^ 2 := by
      have h1 : x' * y = x' * (k * z' ^ 2) := by rw [hmul, hk]; ring
      exact Nat.eq_of_mul_eq_mul_left hx'_pos h1
    have hk_dvd_x : k ∣ x := ⟨x' * x', by change x = u * x' at hx'; rw [hx', hk]; ring⟩
    have hk_dvd_y : k ∣ y := ⟨z' ^ 2, hy_eq⟩
    have hk1 : k = 1 := by
      have hkg : k ∣ Nat.gcd x y := Nat.dvd_gcd hk_dvd_x hk_dvd_y
      rw [hxy.gcd_eq_one] at hkg
      exact Nat.dvd_one.mp hkg
    refine ⟨u, ?_⟩
    change x = u * x' at hx'
    rw [hx', hk, hk1, mul_one, sq]

private lemma coprime_mul_eq_sq {x y z : ℕ} (hxy : Nat.Coprime x y) (heq : x * y = z ^ 2) :
    ∃ u v : ℕ, x = u ^ 2 ∧ y = v ^ 2 ∧ Nat.Coprime u v := by
  obtain ⟨u, hx⟩ := isSquare_of_coprime_mul_eq_sq_left hxy heq
  obtain ⟨v, hy⟩ := isSquare_of_coprime_mul_eq_sq_left hxy.symm (by rwa [mul_comm])
  have huv : Nat.Coprime u v := by
    rw [hx, hy, sq, sq] at hxy
    exact (Nat.coprime_mul_iff_left.mp (Nat.coprime_mul_iff_right.mp hxy).1).1
  exact ⟨u, v, hx, hy, huv⟩

private lemma coprime_half_sum_diff {m n : ℕ} (hmn : Nat.Coprime m n) (hsame : m % 2 = n % 2)
    (hlt : n < m) : Nat.Coprime ((m + n) / 2) ((m - n) / 2) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hp1 : p ∣ (m + n) / 2 := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hp2 : p ∣ (m - n) / 2 := hpdvd.trans (Nat.gcd_dvd_right _ _)
  have hpm : p ∣ m := by
    have : (m + n) / 2 + (m - n) / 2 = m := by omega
    rw [← this]; exact dvd_add hp1 hp2
  have hpn : p ∣ n := by
    have : (m + n) / 2 - (m - n) / 2 = n := by omega
    rw [← this]; exact Nat.dvd_sub hp1 hp2
  have hpg : p ∣ Nat.gcd m n := Nat.dvd_gcd hpm hpn
  rw [hmn.gcd_eq_one] at hpg
  exact hp.not_dvd_one hpg

private lemma coprime_sq_add_four_sq {a d : ℕ} (had : Nat.Coprime a d) :
    Nat.Coprime (a ^ 2 + d ^ 2) (4 * a ^ 2 + d ^ 2) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hp1 : p ∣ a ^ 2 + d ^ 2 := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hp2 : p ∣ 4 * a ^ 2 + d ^ 2 := hpdvd.trans (Nat.gcd_dvd_right _ _)
  have hp3a : p ∣ 3 * a ^ 2 := by
    have hsub : 4 * a ^ 2 + d ^ 2 - (a ^ 2 + d ^ 2) = 3 * a ^ 2 := by omega
    rw [← hsub]
    exact Nat.dvd_sub hp2 hp1
  rcases hp.dvd_mul.mp hp3a with hp3 | hpa2
  · have hp_eq : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3
    subst hp_eq
    have hmod : (a ^ 2 + d ^ 2) % 3 = 0 := Nat.mod_eq_zero_of_dvd hp1
    have hsq : (a ^ 2 + d ^ 2) % 3 = ((a % 3) ^ 2 + (d % 3) ^ 2) % 3 := by
      simp [sq, Nat.add_mod, Nat.mul_mod]
    rw [hsq] at hmod
    have ha3 : 3 ∣ a := by
      rw [Nat.dvd_iff_mod_eq_zero]
      have ha_cases : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
      have hd_cases : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
      rcases ha_cases with ha | ha | ha <;> rcases hd_cases with hd | hd | hd <;>
        simp [ha, hd] at hmod <;> omega
    have hd3 : 3 ∣ d := by
      rw [Nat.dvd_iff_mod_eq_zero]
      have ha_cases : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
      have hd_cases : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
      rcases ha_cases with ha | ha | ha <;> rcases hd_cases with hd | hd | hd <;>
        simp [ha, hd] at hmod <;> omega
    have h3 : 3 ∣ Nat.gcd a d := Nat.dvd_gcd ha3 hd3
    rw [had.gcd_eq_one] at h3
    omega
  · have hpa : p ∣ a := hp.dvd_of_dvd_pow hpa2
    have hpd2 : p ∣ d ^ 2 := by
      have hsub : a ^ 2 + d ^ 2 - a ^ 2 = d ^ 2 := by omega
      rw [← hsub]
      exact Nat.dvd_sub hp1 hpa2
    have hpd : p ∣ d := hp.dvd_of_dvd_pow hpd2
    have hpg : p ∣ Nat.gcd a d := Nat.dvd_gcd hpa hpd
    rw [had.gcd_eq_one] at hpg
    exact hp.not_dvd_one hpg

private lemma eq_of_coprime_mul_eq {x y u v : ℕ} (hxy : Nat.Coprime x y) (huv : Nat.Coprime u v)
    (heq : x * u = y * v) : x = v ∧ y = u := by
  have hxv : x ∣ v := hxy.dvd_of_dvd_mul_left ⟨u, heq.symm⟩
  have hvx : v ∣ x := huv.symm.dvd_of_dvd_mul_right ⟨y, by rw [mul_comm v y, ← heq]⟩
  have h1 : x = v := Nat.dvd_antisymm hxv hvx
  have hyu : y ∣ u := hxy.symm.dvd_of_dvd_mul_left ⟨v, heq⟩
  have huy : u ∣ y := huv.dvd_of_dvd_mul_right ⟨x, by rw [mul_comm u x, heq]⟩
  exact ⟨h1, Nat.dvd_antisymm hyu huy⟩

private lemma system_S_to_P {A B C D : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hAB_lt : B < A) (hAB : Nat.Coprime A B) (hCD : Nat.Coprime C D)
    (hsq : A ^ 2 + D ^ 2 = C ^ 2 + B ^ 2) (hmul : A * B = 2 * C * D) :
    ∃ a d b c : ℕ, 0 < a ∧ 0 < d ∧ Nat.Coprime a d ∧
      a ^ 2 + d ^ 2 = b ^ 2 ∧ 4 * a ^ 2 + d ^ 2 = c ^ 2 ∧ c ≤ A := by
  have h2AB : 2 ∣ A * B := ⟨C * D, by linarith⟩
  rcases Nat.prime_two.dvd_mul.mp h2AB with ⟨A', hA'⟩ | ⟨B', hB'⟩
  · have hA'_pos : 0 < A' := by omega
    have hA'B : Nat.Coprime A' B := by
      rw [hA'] at hAB
      exact (Nat.coprime_mul_iff_left.mp hAB).2
    have hmul' : A' * B = C * D := by nlinarith
    obtain ⟨a, b, c, d, ha, hb, hc, hd, hA'eq, hBeq, hCeq, hDeq, _, had, hbc, _⟩ :=
      coprime_mul_eq_mul_pos hA'_pos hB hC hD hA'B hCD hmul'
    have hpoly : b ^ 2 * (4 * a ^ 2 + d ^ 2) = c ^ 2 * (a ^ 2 + d ^ 2) := by
      rw [hA', hA'eq, hBeq, hCeq, hDeq] at hsq
      zify at hsq ⊢
      linear_combination hsq
    have hcop1 : Nat.Coprime (b ^ 2) (c ^ 2) := hbc.pow 2 2
    have hcop2 : Nat.Coprime (4 * a ^ 2 + d ^ 2) (a ^ 2 + d ^ 2) :=
      (coprime_sq_add_four_sq had).symm
    obtain ⟨h1, h2⟩ := eq_of_coprime_mul_eq hcop1 hcop2 hpoly
    refine ⟨a, d, b, c, ha, hd, had, h1.symm, h2.symm, ?_⟩
    have hcB : c ≤ B := by
      rw [hBeq]
      exact Nat.le_mul_of_pos_right c hd
    omega
  · have hB'_pos : 0 < B' := by omega
    have hAB' : Nat.Coprime A B' := by
      rw [hB'] at hAB
      exact (Nat.coprime_mul_iff_right.mp hAB).2
    have hmul' : A * B' = C * D := by nlinarith
    obtain ⟨a, b, c, d, ha, hb, hc, hd, hAeq, hB'eq, hCeq, hDeq, _, had, hbc, _⟩ :=
      coprime_mul_eq_mul_pos hA hB'_pos hC hD hAB' hCD hmul'
    have hpoly : b ^ 2 * (a ^ 2 + d ^ 2) = c ^ 2 * (a ^ 2 + 4 * d ^ 2) := by
      rw [hB', hAeq, hB'eq, hCeq, hDeq] at hsq
      zify at hsq ⊢
      linear_combination hsq
    have hcop1 : Nat.Coprime (b ^ 2) (c ^ 2) := hbc.pow 2 2
    have hcop2 : Nat.Coprime (a ^ 2 + d ^ 2) (a ^ 2 + 4 * d ^ 2) := by
      have h := coprime_sq_add_four_sq had.symm
      rwa [add_comm (d ^ 2) (a ^ 2), add_comm (4 * d ^ 2) (a ^ 2)] at h
    obtain ⟨h1, h2⟩ := eq_of_coprime_mul_eq hcop1 hcop2 hpoly
    refine ⟨d, a, c, b, hd, ha, had.symm, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · rw [hAeq]
      exact Nat.le_mul_of_pos_left b ha

private lemma system_P_odd_step {a d b c : ℕ} (ha : 0 < a) (hd : 0 < d) (had : Nat.Coprime a d)
    (hdeven : ¬ 2 ∣ d) (hb : a ^ 2 + d ^ 2 = b ^ 2) (hc : 4 * a ^ 2 + d ^ 2 = c ^ 2) :
    ∃ a1 d1 b1 c1 : ℕ, 0 < a1 ∧ 0 < d1 ∧ Nat.Coprime a1 d1 ∧
      a1 ^ 2 + d1 ^ 2 = b1 ^ 2 ∧ 4 * a1 ^ 2 + d1 ^ 2 = c1 ^ 2 ∧ c1 < c := by
  have hd_odd : d % 2 = 1 := by omega
  have haeven : 2 ∣ a := by
    by_contra haodd
    have ha_odd : a % 2 = 1 := by omega
    have h1 := sq_mod_four_of_odd ha_odd
    have h2 := sq_mod_four_of_odd hd_odd
    have hbm : b ^ 2 % 4 = 2 := by rw [← hb]; omega
    rcases Nat.mod_two_eq_zero_or_one b with hb0 | hb1
    · have := sq_mod_four_of_even hb0; omega
    · have := sq_mod_four_of_odd hb1; omega
  obtain ⟨a', ha'⟩ := haeven
  have ha'_pos : 0 < a' := by omega
  have ha2_mod : a ^ 2 % 2 = 0 := by
    rw [ha']
    have h2 : (2 * a') ^ 2 = 2 * (2 * a' ^ 2) := by ring
    omega
  have hb_odd : b % 2 = 1 := by
    have h1 : b ^ 2 % 2 = 1 := by rw [← hb, Nat.add_mod, ha2_mod, sq_mod_two, hd_odd]
    rw [sq_mod_two] at h1; exact h1
  have hc_odd : c % 2 = 1 := by
    have h1 : c ^ 2 % 2 = 1 := by
      rw [← hc, Nat.add_mod]
      have h4 : (4 * a ^ 2) % 2 = 0 := by omega
      rw [h4, sq_mod_two, hd_odd]
    rw [sq_mod_two] at h1; exact h1
  have hdb : d < b := by nlinarith
  have hdc : d < c := by nlinarith
  have hbd_cop : Nat.Coprime b d := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpb : p ∣ b := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hpd : p ∣ d := hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hpa2 : p ∣ a ^ 2 := by
      have hsub : b ^ 2 - d ^ 2 = a ^ 2 := by omega
      rw [← hsub]
      exact Nat.dvd_sub (dvd_pow hpb (by norm_num)) (dvd_pow hpd (by norm_num))
    have hpa : p ∣ a := hp.dvd_of_dvd_pow hpa2
    have hpg : p ∣ Nat.gcd a d := Nat.dvd_gcd hpa hpd
    rw [had.gcd_eq_one] at hpg
    exact hp.not_dvd_one hpg
  have hcd_cop : Nat.Coprime c d := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpc : p ∣ c := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hpd : p ∣ d := hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hpne2 : p ≠ 2 := by intro h2; subst h2; exact hdeven hpd
    have hp4a2 : p ∣ 4 * a ^ 2 := by
      have hsub : c ^ 2 - d ^ 2 = 4 * a ^ 2 := by omega
      rw [← hsub]
      exact Nat.dvd_sub (dvd_pow hpc (by norm_num)) (dvd_pow hpd (by norm_num))
    have hpa2 : p ∣ a ^ 2 := by
      rcases hp.dvd_mul.mp hp4a2 with hp4 | hpa2
      · have : p ∣ 2 := hp.dvd_of_dvd_pow (by simpa using hp4 : p ∣ 2 ^ 2)
        exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this) hpne2
      · exact hpa2
    have hpa : p ∣ a := hp.dvd_of_dvd_pow hpa2
    have hpg : p ∣ Nat.gcd a d := Nat.dvd_gcd hpa hpd
    rw [had.gcd_eq_one] at hpg
    exact hp.not_dvd_one hpg
  have hxy1_cop : Nat.Coprime ((b + d) / 2) ((b - d) / 2) :=
    coprime_half_sum_diff hbd_cop (by omega) hdb
  have hxy1_mul : ((b + d) / 2) * ((b - d) / 2) = a' ^ 2 := by
    set x1 := (b + d) / 2
    set y1 := (b - d) / 2
    have h1 : 2 * x1 = b + d := by omega
    have h2 : 2 * y1 = b - d := by omega
    zify [hdb.le] at h1 h2 hb ha' ⊢
    have h4 : 4 * ((x1 : ℤ) * (y1 : ℤ)) = 4 * ((a' : ℤ) ^ 2) := by
      calc 4 * ((x1 : ℤ) * (y1 : ℤ))
          = (2 * (x1 : ℤ)) * (2 * (y1 : ℤ)) := by ring
        _ = ((b : ℤ) + (d : ℤ)) * ((b : ℤ) - (d : ℤ)) := by rw [h1, h2]
        _ = (b : ℤ) ^ 2 - (d : ℤ) ^ 2 := by ring
        _ = (a : ℤ) ^ 2 := by linarith only [hb]
        _ = (2 * (a' : ℤ)) ^ 2 := by rw [ha']
        _ = 4 * ((a' : ℤ) ^ 2) := by ring
    linarith only [h4]
  obtain ⟨p, q, hp_eq, hq_eq, hpq_cop⟩ := coprime_mul_eq_sq hxy1_cop hxy1_mul
  have hp_pos : 0 < p := by
    by_contra h; have : p = 0 := by omega
    rw [this] at hp_eq; omega
  have hq_pos : 0 < q := by
    by_contra h; have : q = 0 := by omega
    rw [this] at hq_eq; omega
  have ha'_pq : a' = p * q := by
    have hsq : a' ^ 2 = (p * q) ^ 2 := by
      calc a' ^ 2 = ((b + d) / 2) * ((b - d) / 2) := hxy1_mul.symm
        _ = p ^ 2 * q ^ 2 := by rw [hp_eq, hq_eq]
        _ = (p * q) ^ 2 := by ring
    exact (Nat.pow_left_inj (by norm_num : 2 ≠ 0)).mp hsq
  have hxy2_cop : Nat.Coprime ((c + d) / 2) ((c - d) / 2) :=
    coprime_half_sum_diff hcd_cop (by omega) hdc
  have hxy2_mul : ((c + d) / 2) * ((c - d) / 2) = a ^ 2 := by
    set x2 := (c + d) / 2
    set y2 := (c - d) / 2
    have h1 : 2 * x2 = c + d := by omega
    have h2 : 2 * y2 = c - d := by omega
    zify [hdc.le] at h1 h2 hc ⊢
    have h4 : 4 * ((x2 : ℤ) * (y2 : ℤ)) = 4 * ((a : ℤ) ^ 2) := by
      calc 4 * ((x2 : ℤ) * (y2 : ℤ))
          = (2 * (x2 : ℤ)) * (2 * (y2 : ℤ)) := by ring
        _ = ((c : ℤ) + (d : ℤ)) * ((c : ℤ) - (d : ℤ)) := by rw [h1, h2]
        _ = (c : ℤ) ^ 2 - (d : ℤ) ^ 2 := by ring
        _ = 4 * ((a : ℤ) ^ 2) := by linarith only [hc]
    linarith only [h4]
  obtain ⟨u, v, hu_eq, hv_eq, huv_cop⟩ := coprime_mul_eq_sq hxy2_cop hxy2_mul
  have hu_pos : 0 < u := by
    by_contra h; have : u = 0 := by omega
    rw [this] at hu_eq; omega
  have hv_pos : 0 < v := by
    by_contra h; have : v = 0 := by omega
    rw [this] at hv_eq; omega
  have ha_uv : a = u * v := by
    have hsq : a ^ 2 = (u * v) ^ 2 := by
      calc a ^ 2 = ((c + d) / 2) * ((c - d) / 2) := hxy2_mul.symm
        _ = u ^ 2 * v ^ 2 := by rw [hu_eq, hv_eq]
        _ = (u * v) ^ 2 := by ring
    exact (Nat.pow_left_inj (by norm_num : 2 ≠ 0)).mp hsq
  have hp2_sub_q2 : p ^ 2 = q ^ 2 + d := by omega
  have hu2_sub_v2 : u ^ 2 = v ^ 2 + d := by omega
  have huv_lt : v < u := by
    have : v ^ 2 < u ^ 2 := by omega
    nlinarith only [this]
  have hS_sq : u ^ 2 + q ^ 2 = p ^ 2 + v ^ 2 := by omega
  have hS_mul : u * v = 2 * p * q := by linarith only [ha', ha'_pq, ha_uv]
  obtain ⟨a1, d1, b1, c1, ha1, hd1, had1, hb1, hc1, hc1_le⟩ :=
    system_S_to_P hu_pos hv_pos hp_pos hq_pos huv_lt huv_cop hpq_cop hS_sq hS_mul
  have hu_lt_c : u < c := by
    have huc : u ^ 2 + v ^ 2 = c := by omega
    have hu_le : u ≤ u ^ 2 := Nat.le_self_pow (by norm_num : 2 ≠ 0) u
    have hv_pos2 : 0 < v ^ 2 := by positivity
    omega
  exact ⟨a1, d1, b1, c1, ha1, hd1, had1, hb1, hc1, lt_of_le_of_lt hc1_le hu_lt_c⟩

private lemma no_system_P :
    ∀ c : ℕ, ∀ a d b : ℕ, 0 < a → 0 < d → Nat.Coprime a d →
      a ^ 2 + d ^ 2 = b ^ 2 → 4 * a ^ 2 + d ^ 2 = c ^ 2 → False := by
  intro c
  induction c using Nat.strong_induction_on with
  | h c ih =>
    intro a d b ha hd had hb hc
    have hbc : b < c := by nlinarith
    by_cases hdeven : 2 ∣ d
    · obtain ⟨e, he⟩ := hdeven
      have he_pos : 0 < e := by omega
      have hc2 : 2 ∣ c := by
        have h2c2 : 2 ∣ c ^ 2 := ⟨2 * a ^ 2 + 2 * e ^ 2, by rw [← hc, he]; ring⟩
        exact Nat.prime_two.dvd_of_dvd_pow h2c2
      obtain ⟨f, hf⟩ := hc2
      have hea : Nat.Coprime e a := by
        rw [he] at had
        exact (Nat.coprime_mul_iff_right.mp had).2.symm
      have hf_eq : e ^ 2 + a ^ 2 = f ^ 2 := by nlinarith
      have hb_eq : 4 * e ^ 2 + a ^ 2 = b ^ 2 := by nlinarith
      exact ih b hbc e a f he_pos ha hea hf_eq hb_eq
    · obtain ⟨a1, d1, b1, c1, ha1, hd1, had1, hb1, hc1, hlt⟩ :=
        system_P_odd_step ha hd had hdeven hb hc
      exact ih c1 hlt a1 d1 b1 ha1 hd1 had1 hb1 hc1

private lemma no_system_S {A B C D : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hAB_lt : B < A) (hAB : Nat.Coprime A B) (hCD : Nat.Coprime C D)
    (hsq : A ^ 2 + D ^ 2 = C ^ 2 + B ^ 2) (hmul : A * B = 2 * C * D) : False := by
  obtain ⟨a, d, b, c, ha, hd, had, hb, hc, _⟩ :=
    system_S_to_P hA hB hC hD hAB_lt hAB hCD hsq hmul
  exact no_system_P c a d b ha hd had hb hc

private lemma no_R_S_T_U {R S T U : ℕ} (hR : 0 < R) (hS : 0 < S) (hT : 0 < T) (hU : 0 < U)
    (hRU : Nat.Coprime R U) (hTS : Nat.Coprime T S)
    (heq1 : T ^ 2 = S ^ 2 + 2 * R * U) (heq2 : R ^ 2 = U ^ 2 + T * S) : False := by
  have hTS_same : T % 2 = S % 2 := by
    have h1 : T ^ 2 % 2 = S ^ 2 % 2 := by
      have h2 : 2 * R * U = 2 * (R * U) := by ring
      rw [heq1, h2]; omega
    rw [sq_mod_two, sq_mod_two] at h1
    exact h1
  have hS_lt_T : S < T := by nlinarith
  have hU_lt_R : U < R := by nlinarith
  set α := (T + S) / 2
  set β := (T - S) / 2
  have hα_pos : 0 < α := by omega
  have hβ_pos : 0 < β := by omega
  have hαβ_cop : Nat.Coprime α β := coprime_half_sum_diff hTS hTS_same hS_lt_T
  have h1 : 2 * α = T + S := by omega
  have h2 : 2 * β = T - S := by omega
  have hS_sq : R ^ 2 + β ^ 2 = α ^ 2 + U ^ 2 := by
    zify [hS_lt_T.le] at h1 h2 heq2 ⊢
    nlinarith
  have hS_mul : R * U = 2 * α * β := by
    zify [hS_lt_T.le] at h1 h2 heq1 ⊢
    nlinarith
  exact no_system_S hR hU hα_pos hβ_pos hU_lt_R hRU hαβ_cop hS_sq hS_mul

private lemma no_sq_eq_two_mul_sq : ∀ x y : ℕ, 0 < x → y ^ 2 = 2 * x ^ 2 → False := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro y hx heq
    have hy2 : 2 ∣ y := Nat.prime_two.dvd_of_dvd_pow (n := 2) ⟨x ^ 2, heq⟩
    obtain ⟨y', rfl⟩ := hy2
    have hx2 : 2 ∣ x := Nat.prime_two.dvd_of_dvd_pow (n := 2) ⟨y' ^ 2, by linarith⟩
    obtain ⟨x', rfl⟩ := hx2
    have hx'_pos : 0 < x' := by omega
    exact ih x' (by omega) y' hx'_pos (by linarith)

private lemma no_four_odd_coprime_squares_ap {w1 x1 y1 z1 d1 : ℕ} (hd1 : 0 < d1)
    (hw1_pos : 0 < w1) (hwx_cop : Nat.Coprime w1 x1)
    (hw1_odd : w1 % 2 = 1) (hx1_odd : x1 % 2 = 1) (hy1_odd : y1 % 2 = 1) (hz1_odd : z1 % 2 = 1)
    (hx1_eq : x1 ^ 2 = w1 ^ 2 + d1) (hy1_eq : y1 ^ 2 = x1 ^ 2 + d1)
    (hz1_eq : z1 ^ 2 = y1 ^ 2 + d1) : False := by
  have hw1_lt_y1 : w1 < y1 := by nlinarith
  have hx1_lt_z1 : x1 < z1 := by nlinarith
  have hwy_cop : Nat.Coprime w1 y1 := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpw : p ∣ w1 := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hpy : p ∣ y1 := hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hpne2 : p ≠ 2 := by intro h2; subst h2; omega
    have hp2d1 : p ∣ 2 * d1 := by
      have hsub : y1 ^ 2 - w1 ^ 2 = 2 * d1 := by omega
      rw [← hsub]
      exact Nat.dvd_sub (dvd_pow hpy (by norm_num)) (dvd_pow hpw (by norm_num))
    have hpd1 : p ∣ d1 := by
      rcases hp.dvd_mul.mp hp2d1 with hp2 | hpd1
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2) hpne2
      · exact hpd1
    have hpx2 : p ∣ x1 ^ 2 := by
      rw [hx1_eq]
      exact dvd_add (dvd_pow hpw (by norm_num)) hpd1
    have hpx : p ∣ x1 := hp.dvd_of_dvd_pow hpx2
    have hpg : p ∣ Nat.gcd w1 x1 := Nat.dvd_gcd hpw hpx
    rw [hwx_cop.gcd_eq_one] at hpg
    exact hp.not_dvd_one hpg
  have hxz_cop : Nat.Coprime x1 z1 := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpx : p ∣ x1 := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hpz : p ∣ z1 := hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hpne2 : p ≠ 2 := by intro h2; subst h2; omega
    have hp2d1 : p ∣ 2 * d1 := by
      have hsub : z1 ^ 2 - x1 ^ 2 = 2 * d1 := by omega
      rw [← hsub]
      exact Nat.dvd_sub (dvd_pow hpz (by norm_num)) (dvd_pow hpx (by norm_num))
    have hpd1 : p ∣ d1 := by
      rcases hp.dvd_mul.mp hp2d1 with hp2 | hpd1
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2) hpne2
      · exact hpd1
    have hpw2 : p ∣ w1 ^ 2 := by
      have hsub : x1 ^ 2 - d1 = w1 ^ 2 := by omega
      rw [← hsub]
      exact Nat.dvd_sub (dvd_pow hpx (by norm_num)) hpd1
    have hpw : p ∣ w1 := hp.dvd_of_dvd_pow hpw2
    have hpg : p ∣ Nat.gcd w1 x1 := Nat.dvd_gcd hpw hpx
    rw [hwx_cop.gcd_eq_one] at hpg
    exact hp.not_dvd_one hpg
  set A0 := (y1 + w1) / 2
  set B0 := (y1 - w1) / 2
  set P0 := (z1 + x1) / 2
  set Q0 := (z1 - x1) / 2
  have hA0_pos : 0 < A0 := by omega
  have hB0_pos : 0 < B0 := by omega
  have hP0_pos : 0 < P0 := by omega
  have hQ0_pos : 0 < Q0 := by omega
  have hAB0_cop : Nat.Coprime A0 B0 := coprime_half_sum_diff hwy_cop.symm (by omega) hw1_lt_y1
  have hPQ0_cop : Nat.Coprime P0 Q0 := coprime_half_sum_diff hxz_cop.symm (by omega) hx1_lt_z1
  have hA0B0_eq : A0 * B0 = P0 * Q0 := by
    have h1 : 2 * A0 = y1 + w1 := by omega
    have h2 : 2 * B0 = y1 - w1 := by omega
    have h3 : 2 * P0 = z1 + x1 := by omega
    have h4 : 2 * Q0 = z1 - x1 := by omega
    zify [hw1_lt_y1.le, hx1_lt_z1.le] at h1 h2 h3 h4 hx1_eq hy1_eq hz1_eq ⊢
    have h4eq : 4 * ((A0 : ℤ) * (B0 : ℤ)) = 4 * ((P0 : ℤ) * (Q0 : ℤ)) := by
      calc 4 * ((A0 : ℤ) * (B0 : ℤ))
          = (2 * (A0 : ℤ)) * (2 * (B0 : ℤ)) := by ring
        _ = ((y1 : ℤ) + (w1 : ℤ)) * ((y1 : ℤ) - (w1 : ℤ)) := by rw [h1, h2]
        _ = (y1 : ℤ) ^ 2 - (w1 : ℤ) ^ 2 := by ring
        _ = (z1 : ℤ) ^ 2 - (x1 : ℤ) ^ 2 := by linarith only [hx1_eq, hy1_eq, hz1_eq]
        _ = ((z1 : ℤ) + (x1 : ℤ)) * ((z1 : ℤ) - (x1 : ℤ)) := by ring
        _ = (2 * (P0 : ℤ)) * (2 * (Q0 : ℤ)) := by rw [← h3, ← h4]
        _ = 4 * ((P0 : ℤ) * (Q0 : ℤ)) := by ring
    linarith only [h4eq]
  have hsq_rel : ((A0 : ℤ) ^ 2 + (B0 : ℤ) ^ 2) = ((P0 : ℤ) - (Q0 : ℤ)) ^ 2 := by
    have h1 : 2 * (A0 : ℤ) = (y1 : ℤ) + (w1 : ℤ) := by omega
    have h2 : 2 * (B0 : ℤ) = (y1 : ℤ) - (w1 : ℤ) := by omega
    have h3 : 2 * (P0 : ℤ) = (z1 : ℤ) + (x1 : ℤ) := by omega
    have h4 : 2 * (Q0 : ℤ) = (z1 : ℤ) - (x1 : ℤ) := by omega
    have h5 : (y1 : ℤ) ^ 2 + (w1 : ℤ) ^ 2 = 2 * (x1 : ℤ) ^ 2 := by
      have : y1 ^ 2 + w1 ^ 2 = 2 * x1 ^ 2 := by omega
      exact_mod_cast this
    have h4eq : 4 * ((A0 : ℤ) ^ 2 + (B0 : ℤ) ^ 2) = 4 * ((P0 : ℤ) - (Q0 : ℤ)) ^ 2 := by
      calc 4 * ((A0 : ℤ) ^ 2 + (B0 : ℤ) ^ 2)
          = (2 * (A0 : ℤ)) ^ 2 + (2 * (B0 : ℤ)) ^ 2 := by ring
        _ = ((y1 : ℤ) + (w1 : ℤ)) ^ 2 + ((y1 : ℤ) - (w1 : ℤ)) ^ 2 := by rw [h1, h2]
        _ = 2 * ((y1 : ℤ) ^ 2 + (w1 : ℤ) ^ 2) := by ring
        _ = 4 * (x1 : ℤ) ^ 2 := by linarith only [h5]
        _ = (2 * (x1 : ℤ)) ^ 2 := by ring
        _ = (2 * (P0 : ℤ) - 2 * (Q0 : ℤ)) ^ 2 := by rw [h3, h4]; ring
        _ = 4 * ((P0 : ℤ) - (Q0 : ℤ)) ^ 2 := by ring
    linarith only [h4eq]
  obtain ⟨r, s, t, u, hr, hs, ht, hu, hA0_eq, hB0_eq, hP0_eq, hQ0_eq, _, hru, hst, _⟩ :=
    coprime_mul_eq_mul_pos hA0_pos hB0_pos hP0_pos hQ0_pos hAB0_cop hPQ0_cop hA0B0_eq
  have hmaster : ((r : ℤ) ^ 2 - (u : ℤ) ^ 2) * ((t : ℤ) ^ 2 - (s : ℤ) ^ 2) =
      2 * (r : ℤ) * (s : ℤ) * (t : ℤ) * (u : ℤ) := by
    have hA0z : (A0 : ℤ) = (r : ℤ) * (s : ℤ) := by exact_mod_cast hA0_eq
    have hB0z : (B0 : ℤ) = (t : ℤ) * (u : ℤ) := by exact_mod_cast hB0_eq
    have hP0z : (P0 : ℤ) = (r : ℤ) * (t : ℤ) := by exact_mod_cast hP0_eq
    have hQ0z : (Q0 : ℤ) = (s : ℤ) * (u : ℤ) := by exact_mod_cast hQ0_eq
    rw [hA0z, hB0z, hP0z, hQ0z] at hsq_rel
    linear_combination -hsq_rel
  have hcop_ru_diff : IsCoprime ((r : ℤ) * (u : ℤ)) ((r : ℤ) ^ 2 - (u : ℤ) ^ 2) := by
    have h1 : IsCoprime (r : ℤ) (u : ℤ) := by exact_mod_cast hru.isCoprime
    have hr_diff : IsCoprime (r : ℤ) ((r : ℤ) ^ 2 - (u : ℤ) ^ 2) := by
      have h2 : IsCoprime (r : ℤ) (-(u : ℤ) ^ 2) := (h1.pow_right).neg_right
      simpa [sub_eq_add_neg, sq] using h2.add_mul_right_right (r : ℤ)
    have hu_diff : IsCoprime (u : ℤ) ((r : ℤ) ^ 2 - (u : ℤ) ^ 2) := by
      have h2 : IsCoprime (u : ℤ) ((r : ℤ) ^ 2) := h1.symm.pow_right
      simpa [sub_eq_add_neg, sq] using h2.add_mul_right_right (-(u : ℤ))
    exact hr_diff.mul_left hu_diff
  have hcop_ts_diff : IsCoprime ((t : ℤ) * (s : ℤ)) ((t : ℤ) ^ 2 - (s : ℤ) ^ 2) := by
    have h1 : IsCoprime (t : ℤ) (s : ℤ) := by exact_mod_cast hst.symm.isCoprime
    have ht_diff : IsCoprime (t : ℤ) ((t : ℤ) ^ 2 - (s : ℤ) ^ 2) := by
      have h2 : IsCoprime (t : ℤ) (-(s : ℤ) ^ 2) := (h1.pow_right).neg_right
      simpa [sub_eq_add_neg, sq] using h2.add_mul_right_right (t : ℤ)
    have hs_diff : IsCoprime (s : ℤ) ((t : ℤ) ^ 2 - (s : ℤ) ^ 2) := by
      have h2 : IsCoprime (s : ℤ) ((t : ℤ) ^ 2) := h1.symm.pow_right
      simpa [sub_eq_add_neg, sq] using h2.add_mul_right_right (-(s : ℤ))
    exact ht_diff.mul_left hs_diff
  have hru_dvd : (r : ℤ) * (u : ℤ) ∣ (t : ℤ) ^ 2 - (s : ℤ) ^ 2 := by
    have h1 : (r : ℤ) * (u : ℤ) ∣ ((r : ℤ) ^ 2 - (u : ℤ) ^ 2) * ((t : ℤ) ^ 2 - (s : ℤ) ^ 2) :=
      ⟨2 * (s : ℤ) * (t : ℤ), by linarith⟩
    exact hcop_ru_diff.dvd_of_dvd_mul_left h1
  have hts_dvd : (t : ℤ) * (s : ℤ) ∣ (r : ℤ) ^ 2 - (u : ℤ) ^ 2 := by
    have h1 : (t : ℤ) * (s : ℤ) ∣ ((r : ℤ) ^ 2 - (u : ℤ) ^ 2) * ((t : ℤ) ^ 2 - (s : ℤ) ^ 2) :=
      ⟨2 * (r : ℤ) * (u : ℤ), by linarith⟩
    exact hcop_ts_diff.dvd_of_dvd_mul_right h1
  obtain ⟨k1, hk1⟩ := hru_dvd
  obtain ⟨k2, hk2⟩ := hts_dvd
  have hprod_k : k1 * k2 = 2 := by
    have hrstu : (0 : ℤ) < (r : ℤ) * (s : ℤ) * (t : ℤ) * (u : ℤ) := by positivity
    have h1 : (k1 * k2) * ((r : ℤ) * (s : ℤ) * (t : ℤ) * (u : ℤ)) =
        2 * ((r : ℤ) * (s : ℤ) * (t : ℤ) * (u : ℤ)) := by
      calc (k1 * k2) * ((r : ℤ) * (s : ℤ) * (t : ℤ) * (u : ℤ))
          = ((t : ℤ) * (s : ℤ) * k2) * ((r : ℤ) * (u : ℤ) * k1) := by ring
        _ = ((r : ℤ) ^ 2 - (u : ℤ) ^ 2) * ((t : ℤ) ^ 2 - (s : ℤ) ^ 2) := by rw [← hk1, ← hk2]
        _ = 2 * ((r : ℤ) * (s : ℤ) * (t : ℤ) * (u : ℤ)) := by linarith
    exact mul_right_cancel₀ hrstu.ne' h1
  have hk_cases : (k1 = 2 ∧ k2 = 1) ∨ (k1 = 1 ∧ k2 = 2) ∨
      (k1 = -2 ∧ k2 = -1) ∨ (k1 = -1 ∧ k2 = -2) := by
    have hk1_dvd : k1 ∣ 2 := ⟨k2, hprod_k.symm⟩
    have hle : k1.natAbs ≤ 2 := Nat.le_of_dvd (by norm_num) (Int.natAbs_dvd_natAbs.mpr hk1_dvd)
    have hne0 : k1 ≠ 0 := by intro h0; rw [h0, zero_mul] at hprod_k; omega
    have hcases : k1 = 1 ∨ k1 = 2 ∨ k1 = -1 ∨ k1 = -2 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · right; left; exact ⟨rfl, by omega⟩
    · left; exact ⟨rfl, by omega⟩
    · right; right; right; exact ⟨rfl, by omega⟩
    · right; right; left; exact ⟨rfl, by omega⟩
  rcases hk_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact no_R_S_T_U hr hs ht hu hru hst.symm (by zify; linarith) (by zify; linarith)
  · exact no_R_S_T_U ht hu hr hs hst.symm hru (by zify; linarith) (by zify; linarith)
  · exact no_R_S_T_U hu ht hs hr hru.symm hst (by zify; linarith) (by zify; linarith)
  · exact no_R_S_T_U hs hr hu ht hst hru.symm (by zify; linarith) (by zify; linarith)

private lemma no_four_squares_ap {w x y z d : ℕ} (hd : 0 < d)
    (hx : x ^ 2 = w ^ 2 + d) (hy : y ^ 2 = x ^ 2 + d) (hz : z ^ 2 = y ^ 2 + d) : False := by
  have hw_pos : 0 < w := by
    by_contra h
    have hw0 : w = 0 := by omega
    subst hw0
    have hx_pos : 0 < x := by nlinarith
    exact no_sq_eq_two_mul_sq x y hx_pos (by linarith)
  set g := Nat.gcd w x
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left x hw_pos
  obtain ⟨w1, hw1⟩ := Nat.gcd_dvd_left w x
  obtain ⟨x1, hx1⟩ := Nat.gcd_dvd_right w x
  have hg2_pos : 0 < g ^ 2 := by positivity
  have hwx_eq : g ^ 2 * x1 ^ 2 = g ^ 2 * w1 ^ 2 + d := by
    calc g ^ 2 * x1 ^ 2 = (g * x1) ^ 2 := by ring
      _ = x ^ 2 := by rw [← hx1]
      _ = w ^ 2 + d := hx
      _ = (g * w1) ^ 2 + d := by rw [hw1]
      _ = g ^ 2 * w1 ^ 2 + d := by ring
  have hle : w1 ^ 2 ≤ x1 ^ 2 := by nlinarith
  have hd_dvd : g ^ 2 ∣ d := by
    refine ⟨x1 ^ 2 - w1 ^ 2, ?_⟩
    zify [hle] at hwx_eq ⊢
    linarith
  obtain ⟨d1, hd1⟩ := hd_dvd
  have hgy2 : g ^ 2 ∣ y ^ 2 := ⟨x1 ^ 2 + d1, by rw [hy, hx1, hd1]; ring⟩
  have hgy : g ∣ y := (Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp hgy2
  obtain ⟨y1, hy1⟩ := hgy
  have hgz2 : g ^ 2 ∣ z ^ 2 := ⟨y1 ^ 2 + d1, by rw [hz, hy1, hd1]; ring⟩
  have hgz : g ∣ z := (Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp hgz2
  obtain ⟨z1, hz1⟩ := hgz
  have hd1_pos : 0 < d1 := by nlinarith
  have hx1_eq : x1 ^ 2 = w1 ^ 2 + d1 := by
    have : g ^ 2 * x1 ^ 2 = g ^ 2 * (w1 ^ 2 + d1) := by rw [hwx_eq, hd1]; ring
    exact Nat.eq_of_mul_eq_mul_left hg2_pos this
  have hy1_eq : y1 ^ 2 = x1 ^ 2 + d1 := by
    have : g ^ 2 * y1 ^ 2 = g ^ 2 * (x1 ^ 2 + d1) := by
      calc g ^ 2 * y1 ^ 2 = (g * y1) ^ 2 := by ring
        _ = y ^ 2 := by rw [← hy1]
        _ = x ^ 2 + d := hy
        _ = (g * x1) ^ 2 + g ^ 2 * d1 := by rw [hx1, hd1]
        _ = g ^ 2 * (x1 ^ 2 + d1) := by ring
    exact Nat.eq_of_mul_eq_mul_left hg2_pos this
  have hz1_eq : z1 ^ 2 = y1 ^ 2 + d1 := by
    have : g ^ 2 * z1 ^ 2 = g ^ 2 * (y1 ^ 2 + d1) := by
      calc g ^ 2 * z1 ^ 2 = (g * z1) ^ 2 := by ring
        _ = z ^ 2 := by rw [← hz1]
        _ = y ^ 2 + d := hz
        _ = (g * y1) ^ 2 + g ^ 2 * d1 := by rw [hy1, hd1]
        _ = g ^ 2 * (y1 ^ 2 + d1) := by ring
    exact Nat.eq_of_mul_eq_mul_left hg2_pos this
  have hwx_cop : Nat.Coprime w1 x1 := by
    have hgcd : Nat.gcd (g * w1) (g * x1) = g := by rw [← hw1, ← hx1]
    rw [Nat.gcd_mul_left] at hgcd
    exact Nat.eq_of_mul_eq_mul_left hg_pos (by simpa using hgcd)
  have hw1_pos : 0 < w1 := by
    by_contra h; have : w1 = 0 := by omega
    rw [this, mul_zero] at hw1; omega
  have hd1_even : d1 % 2 = 0 := by
    by_contra hdodd
    have hwx_odd : w1 % 2 = 1 ∨ x1 % 2 = 1 := by
      by_contra h
      have h2g : 2 ∣ Nat.gcd w1 x1 := Nat.dvd_gcd (by omega) (by omega)
      rw [hwx_cop.gcd_eq_one] at h2g; omega
    rcases hwx_odd with hw_odd | hx_odd
    · have hy_odd : y1 % 2 = 1 := by
        have h1 : y1 ^ 2 % 2 = 1 := by
          have : y1 ^ 2 = w1 ^ 2 + 2 * d1 := by linarith
          rw [this, Nat.add_mod, sq_mod_two, hw_odd]; omega
        rwa [sq_mod_two] at h1
      have h1 := sq_mod_four_of_odd hw_odd
      have h2 := sq_mod_four_of_odd hy_odd
      have h3 : y1 ^ 2 = w1 ^ 2 + 2 * d1 := by linarith
      omega
    · have hz_odd : z1 % 2 = 1 := by
        have h1 : z1 ^ 2 % 2 = 1 := by
          have : z1 ^ 2 = x1 ^ 2 + 2 * d1 := by linarith
          rw [this, Nat.add_mod, sq_mod_two, hx_odd]; omega
        rwa [sq_mod_two] at h1
      have h1 := sq_mod_four_of_odd hx_odd
      have h2 := sq_mod_four_of_odd hz_odd
      have h3 : z1 ^ 2 = x1 ^ 2 + 2 * d1 := by linarith
      omega
  have hw1_odd : w1 % 2 = 1 := by
    by_contra h
    have hw2 : w1 % 2 = 0 := by omega
    have hx2 : x1 % 2 = 0 := by
      have h1 : x1 ^ 2 % 2 = 0 := by rw [hx1_eq, Nat.add_mod, sq_mod_two, hw2, hd1_even]
      rwa [sq_mod_two] at h1
    have h2g : 2 ∣ Nat.gcd w1 x1 := Nat.dvd_gcd (by omega) (by omega)
    rw [hwx_cop.gcd_eq_one] at h2g; omega
  have hx1_odd : x1 % 2 = 1 := by
    have h1 : x1 ^ 2 % 2 = 1 := by rw [hx1_eq, Nat.add_mod, sq_mod_two, hw1_odd, hd1_even]
    rwa [sq_mod_two] at h1
  have hy1_odd : y1 % 2 = 1 := by
    have h1 : y1 ^ 2 % 2 = 1 := by rw [hy1_eq, Nat.add_mod, sq_mod_two, hx1_odd, hd1_even]
    rwa [sq_mod_two] at h1
  have hz1_odd : z1 % 2 = 1 := by
    have h1 : z1 ^ 2 % 2 = 1 := by rw [hz1_eq, Nat.add_mod, sq_mod_two, hy1_odd, hd1_even]
    rwa [sq_mod_two] at h1
  exact no_four_odd_coprime_squares_ap hd1_pos hw1_pos hwx_cop
    hw1_odd hx1_odd hy1_odd hz1_odd hx1_eq hy1_eq hz1_eq

end OMAErdos782

theorem OMA.solution : type_of% @Erdos782.erdos_782.variants.no_four_term_ap := by
  intro t ht_sub ht_ap
  exfalso
  rcases ht_ap with ⟨a, d, hcard, ht_eq⟩
  have hd_pos : 0 < d := by
    by_contra hd0
    have hd_zero : d = 0 := by omega
    subst hd_zero
    have ht_sing : t = {a} := by
      ext m
      rw [ht_eq]
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, smul_zero, add_zero]
      constructor
      · rintro ⟨_, _, rfl⟩; rfl
      · rintro rfl; exact ⟨0, by norm_num, rfl⟩
    rw [ht_sing] at hcard
    have h1 : ENat.card ({a} : Set ℕ) = 1 := by simp
    rw [h1] at hcard
    exact absurd hcard (by decide)
  have hmem : ∀ n : ℕ, n < 4 → a + n * d ∈ t := by
    intro n hn
    rw [ht_eq]
    refine ⟨n, ?_, by simp⟩
    exact_mod_cast hn
  have h0 : IsSquare a := by simpa using ht_sub (hmem 0 (by omega))
  have h1 : IsSquare (a + d) := by simpa using ht_sub (hmem 1 (by omega))
  have h2 : IsSquare (a + 2 * d) := by simpa using ht_sub (hmem 2 (by omega))
  have h3 : IsSquare (a + 3 * d) := by simpa using ht_sub (hmem 3 (by omega))
  rcases h0 with ⟨w, hw⟩
  rcases h1 with ⟨x, hx⟩
  rcases h2 with ⟨y, hy⟩
  rcases h3 with ⟨z, hz⟩
  exact OMAErdos782.no_four_squares_ap (w := w) (x := x) (y := y) (z := z) hd_pos
    (by simp only [sq]; linarith)
    (by simp only [sq]; linarith)
    (by simp only [sq]; linarith)
