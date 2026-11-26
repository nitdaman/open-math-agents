import FormalConjectures.Wikipedia.WolstenholmePrime

open Polynomial Finset

namespace OMAWolstenholmeHarmonic

private noncomputable def risingPoly (n : ℕ) : ℤ[X] :=
  ∏ i ∈ Finset.range n, (X + C ((i + 1 : ℕ) : ℤ))

private lemma prod_range_succ_eq_factorial (n : ℕ) :
    ∏ i ∈ Finset.range n, (i + 1) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ, mul_comm]

private lemma prod_range_shift_mul_factorial (p k : ℕ) :
    p.factorial * ∏ i ∈ Finset.range k, (p + (i + 1)) = (p + k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih, Nat.add_succ, Nat.factorial_succ, mul_comm]

private lemma eval_p_risingPoly (p : ℕ) (hp : 1 ≤ p) :
    (risingPoly (p - 1)).eval (p : ℤ) =
      ((p - 1).factorial : ℤ) * ((2 * p - 1).choose (p - 1) : ℤ) := by
  unfold risingPoly
  rw [Polynomial.eval_prod]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  have hnat : ∏ i ∈ Finset.range (p - 1), (p + (i + 1)) =
      (p - 1).factorial * (2 * p - 1).choose (p - 1) := by
    have h1 := prod_range_shift_mul_factorial p (p - 1)
    have hadd : p + (p - 1) = 2 * p - 1 := by omega
    rw [hadd] at h1
    have h2 : (2 * p - 1).choose (p - 1) * (p - 1).factorial * p.factorial = (2 * p - 1).factorial := by
      have hle : p - 1 ≤ 2 * p - 1 := by omega
      have hsub : 2 * p - 1 - (p - 1) = p := by omega
      have hc := Nat.choose_mul_factorial_mul_factorial hle
      rw [hsub] at hc
      exact hc
    have hpos : 0 < p.factorial := Nat.factorial_pos p
    have h3 : p.factorial * ∏ i ∈ Finset.range (p - 1), (p + (i + 1)) =
        p.factorial * ((p - 1).factorial * (2 * p - 1).choose (p - 1)) := by
      rw [h1, ← h2]
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos h3
  have hcast : (∏ i ∈ Finset.range (p - 1), ((p : ℤ) + ((i + 1 : ℕ) : ℤ))) =
      ((∏ i ∈ Finset.range (p - 1), (p + (i + 1)) : ℕ) : ℤ) := by
    push_cast
    rfl
  rw [hcast, hnat]
  push_cast
  rfl

private lemma eval_neg_p_risingPoly (p : ℕ) (hp : 1 ≤ p) (hodd : Odd p) :
    (risingPoly (p - 1)).eval (-(p : ℤ)) = ((p - 1).factorial : ℤ) := by
  unfold risingPoly
  rw [Polynomial.eval_prod]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  have hterm : ∀ i ∈ Finset.range (p - 1),
      -(p : ℤ) + ((i + 1 : ℕ) : ℤ) = (-1 : ℤ) * (((p - 1 - 1 - i + 1 : ℕ) : ℤ)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    omega
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have heven : Even (p - 1) := by
    rcases hodd with ⟨k, rfl⟩
    exact ⟨k, by omega⟩
  rw [heven.neg_one_pow, one_mul]
  have hrefl : ∏ i ∈ Finset.range (p - 1), (((p - 1 - 1 - i + 1 : ℕ) : ℤ)) =
      ∏ i ∈ Finset.range (p - 1), ((i + 1 : ℕ) : ℤ) := by
    exact Finset.prod_range_reflect (fun j => ((j + 1 : ℕ) : ℤ)) (p - 1)
  rw [hrefl]
  have hcast : (∏ i ∈ Finset.range (p - 1), ((i + 1 : ℕ) : ℤ)) =
      ((∏ i ∈ Finset.range (p - 1), (i + 1) : ℕ) : ℤ) := by
    push_cast
    rfl
  rw [hcast, prod_range_succ_eq_factorial]

private lemma coeff_zero_and_one_prod (s : Finset ℕ) :
    (∏ i ∈ s, (X + C ((i + 1 : ℕ) : ℤ))).coeff 0 = (∏ i ∈ s, ((i + 1 : ℕ) : ℤ)) ∧
    (((∏ i ∈ s, (X + C ((i + 1 : ℕ) : ℤ))).coeff 1 : ℤ) : ℚ) =
      (∏ i ∈ s, ((i + 1 : ℕ) : ℚ)) * ∑ i ∈ s, ((i + 1 : ℕ) : ℚ)⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [Polynomial.coeff_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    set Q : ℤ[X] := ∏ i ∈ s, (X + C ((i + 1 : ℕ) : ℤ))
    have h0 : ((X + C ((a + 1 : ℕ) : ℤ)) * Q).coeff 0 = ((a + 1 : ℕ) : ℤ) * Q.coeff 0 := by
      simp [Polynomial.mul_coeff_zero]
    have h1 : ((X + C ((a + 1 : ℕ) : ℤ)) * Q).coeff 1 =
        Q.coeff 0 + ((a + 1 : ℕ) : ℤ) * Q.coeff 1 := by
      simp [add_mul, Polynomial.coeff_X_mul]
    constructor
    · rw [h0, ih.1]
    · rw [h1, Int.cast_add, Int.cast_mul, ih.1, ih.2]
      have hne : ((a + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hprod : ((∏ i ∈ s, ((i + 1 : ℕ) : ℤ) : ℤ) : ℚ) = ∏ i ∈ s, ((i + 1 : ℕ) : ℚ) := by
        push_cast
        rfl
      rw [hprod]
      have ha1 : (((a + 1 : ℕ) : ℤ) : ℚ) = ((a + 1 : ℕ) : ℚ) := by norm_cast
      rw [ha1]
      field_simp [hne]

private lemma coeff_one_risingPoly_rat (n : ℕ) :
    (((risingPoly n).coeff 1 : ℤ) : ℚ) = (n.factorial : ℚ) * harmonic n := by
  have h := (coeff_zero_and_one_prod (Finset.range n)).2
  unfold risingPoly harmonic
  rw [h]
  congr 1
  have hcast : (∏ i ∈ Finset.range n, ((i + 1 : ℕ) : ℚ)) =
      ((∏ i ∈ Finset.range n, (i + 1) : ℕ) : ℚ) := by
    push_cast
    rfl
  rw [hcast, prod_range_succ_eq_factorial]

private lemma map_risingPoly_zmod (p : ℕ) (hp : p.Prime) :
    (risingPoly (p - 1)).map (Int.castRingHom (ZMod p)) = (X ^ (p - 1) - 1 : (ZMod p)[X]) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hroots : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
    simpa [ZMod.card] using FiniteField.roots_X_pow_card_sub_X (ZMod p)
  have hmonic : (X ^ p - X : (ZMod p)[X]).Monic := by
    have hgt : 1 < p := hp.one_lt
    have hdeg : (X : (ZMod p)[X]).degree < (X ^ p : (ZMod p)[X]).degree := by
      simp only [Polynomial.degree_X, Polynomial.degree_X_pow]
      exact_mod_cast hgt
    exact (Polynomial.monic_X_pow p).sub_of_left hdeg
  have hcard : (X ^ p - X : (ZMod p)[X]).roots.card = (X ^ p - X : (ZMod p)[X]).natDegree := by
    rw [hroots, Finset.card_val, Finset.card_univ, ZMod.card]
    exact (FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp.one_lt).symm
  have hprod_all : (∏ a : ZMod p, (X - C a)) = (X ^ p - X : (ZMod p)[X]) := by
    have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
    rw [hroots] at h
    exact h
  have hsplit : X * (∏ a ∈ (Finset.univ : Finset (ZMod p)).erase 0, (X - C a)) =
      X * (X ^ (p - 1) - 1 : (ZMod p)[X]) := by
    have h0 : (∏ a : ZMod p, (X - C a)) =
        (X - C (0 : ZMod p)) * ∏ a ∈ (Finset.univ : Finset (ZMod p)).erase 0, (X - C a) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun a : ZMod p => X - C a) (Finset.mem_univ 0)]
    rw [map_zero, sub_zero] at h0
    rw [← h0, hprod_all]
    have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.pos).symm
    conv_rhs => rw [mul_sub, mul_one, ← pow_succ', ← hp1]
  have hXne : (X : (ZMod p)[X]) ≠ 0 := Polynomial.X_ne_zero
  have hprod_nz : (∏ a ∈ (Finset.univ : Finset (ZMod p)).erase 0, (X - C a)) =
      (X ^ (p - 1) - 1 : (ZMod p)[X]) :=
    mul_left_cancel₀ hXne hsplit
  rw [← hprod_nz]
  unfold risingPoly
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  refine Finset.prod_bij (fun i _ => -((i + 1 : ℕ) : ZMod p)) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [neg_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle := Nat.le_of_dvd (Nat.succ_pos i) hdvd
    omega
  · intro i hi j hj hij
    rw [Finset.mem_range] at hi hj
    have heq : ((i + 1 : ℕ) : ZMod p) = ((j + 1 : ℕ) : ZMod p) := neg_inj.mp hij
    have hval := congr_arg ZMod.val heq
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hval
    omega
  · intro a ha
    rw [Finset.mem_erase] at ha
    have hne : -a ≠ 0 := neg_ne_zero.mpr ha.1
    have hval_pos : 0 < (-a).val := by
      by_contra h
      have h0 : (-a).val = 0 := by omega
      exact hne ((ZMod.val_eq_zero (-a)).mp h0)
    refine ⟨(-a).val - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hlt : (-a).val < p := ZMod.val_lt (-a)
      omega
    · have h1 : (-a).val - 1 + 1 = (-a).val := Nat.sub_add_cancel hval_pos
      rw [h1, ZMod.natCast_zmod_val, neg_neg]
  · intro i _
    simp [map_neg]
    ring

private lemma dvd_coeff_three_risingPoly (p : ℕ) (hp : p.Prime) (hp7 : p > 7) :
    (p : ℤ) ∣ (risingPoly (p - 1)).coeff 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hmap := congr_arg (fun q => q.coeff 3) (map_risingPoly_zmod p hp)
  rw [Polynomial.coeff_map, eq_intCast] at hmap
  rw [hmap]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_one]
  have h1 : 3 ≠ p - 1 := by omega
  simp [h1]

private lemma eval_sub_eval_neg_modEq (p : ℕ) (hp : p.Prime) (hp7 : p > 7) :
    ((p : ℤ) ^ 4) ∣
      ((risingPoly (p - 1)).eval (p : ℤ) - (risingPoly (p - 1)).eval (-(p : ℤ))) -
        2 * (risingPoly (p - 1)).coeff 1 * (p : ℤ) := by
  set f := risingPoly (p - 1)
  have heval : f.eval (p : ℤ) - f.eval (-(p : ℤ)) =
      ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i * ((p : ℤ) ^ i - (-(p : ℤ)) ^ i) := by
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [heval]
  have hdeg : 4 ≤ f.natDegree + 1 := by
    have hfdeg : f.natDegree = p - 1 := by
      haveI : Fact p.Prime := ⟨hp⟩
      have hmap := map_risingPoly_zmod p hp
      have hge : (X ^ (p - 1) - 1 : (ZMod p)[X]).natDegree ≤ f.natDegree := by
        rw [← hmap]
        exact Polynomial.natDegree_map_le
      have hdeg_zmod : (X ^ (p - 1) - 1 : (ZMod p)[X]).natDegree = p - 1 := by
        have hpos : 0 < p - 1 := by omega
        exact Polynomial.natDegree_X_pow_sub_C
      have hle : f.natDegree ≤ p - 1 := by
        unfold f risingPoly
        calc (∏ i ∈ Finset.range (p - 1), (X + C ((i + 1 : ℕ) : ℤ))).natDegree
            ≤ ∑ i ∈ Finset.range (p - 1), (X + C ((i + 1 : ℕ) : ℤ)).natDegree :=
              Polynomial.natDegree_prod_le _ _
          _ = ∑ _i ∈ Finset.range (p - 1), 1 := by
              refine Finset.sum_congr rfl fun i _ => Polynomial.natDegree_X_add_C _
          _ = p - 1 := by simp
      omega
    omega
  have hsplit : ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i * ((p : ℤ) ^ i - (-(p : ℤ)) ^ i) =
      (∑ i ∈ Finset.range 4, f.coeff i * ((p : ℤ) ^ i - (-(p : ℤ)) ^ i)) +
      (∑ i ∈ Finset.Ico 4 (f.natDegree + 1), f.coeff i * ((p : ℤ) ^ i - (-(p : ℤ)) ^ i)) := by
    rw [← Finset.sum_range_add_sum_Ico _ hdeg]
  rw [hsplit]
  have hlow : ∑ i ∈ Finset.range 4, f.coeff i * ((p : ℤ) ^ i - (-(p : ℤ)) ^ i) =
      2 * f.coeff 1 * (p : ℤ) + 2 * f.coeff 3 * (p : ℤ) ^ 3 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  rw [hlow]
  have hsub : 2 * f.coeff 1 * (p : ℤ) + 2 * f.coeff 3 * (p : ℤ) ^ 3 +
      (∑ i ∈ Finset.Ico 4 (f.natDegree + 1), f.coeff i * ((p : ℤ) ^ i - (-(p : ℤ)) ^ i)) -
      2 * f.coeff 1 * (p : ℤ) =
      2 * f.coeff 3 * (p : ℤ) ^ 3 +
      (∑ i ∈ Finset.Ico 4 (f.natDegree + 1), f.coeff i * ((p : ℤ) ^ i - (-(p : ℤ)) ^ i)) := by
    ring
  rw [hsub]
  refine dvd_add ?_ ?_
  · obtain ⟨k, hk⟩ := dvd_coeff_three_risingPoly p hp hp7
    refine ⟨2 * k, ?_⟩
    rw [hk]
    ring
  · refine Finset.dvd_sum fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    refine dvd_mul_of_dvd_right (dvd_sub ?_ ?_) _
    · exact pow_dvd_pow (p : ℤ) hi.1
    · rw [neg_pow]
      exact dvd_mul_of_dvd_right (pow_dvd_pow (p : ℤ) hi.1) _

private lemma dvd_coeff_one_iff_dvd_harmonic_num (p : ℕ) (hp : p.Prime) :
    ((p : ℤ) ^ 3) ∣ (risingPoly (p - 1)).coeff 1 ↔
      ((p ^ 3 : ℕ) : ℤ) ∣ (harmonic (p - 1)).num := by
  set h := harmonic (p - 1)
  set c := (risingPoly (p - 1)).coeff 1
  have hrat : (c : ℚ) = ((p - 1).factorial : ℚ) * h := coeff_one_risingPoly_rat (p - 1)
  have hden_ne : (h.den : ℚ) ≠ 0 := by exact_mod_cast h.pos.ne'
  have hq : (c : ℚ) * (h.den : ℚ) = ((p - 1).factorial : ℚ) * (h.num : ℚ) := by
    have hmul : h * (h.den : ℚ) = (h.num : ℚ) := by
      calc h * (h.den : ℚ) = ((h.num : ℚ) / (h.den : ℚ)) * (h.den : ℚ) := by rw [Rat.num_div_den]
        _ = (h.num : ℚ) := div_mul_cancel₀ _ hden_ne
    rw [hrat, mul_assoc, hmul]
  have hint : c * (h.den : ℤ) = ((p - 1).factorial : ℤ) * h.num := by
    exact_mod_cast hq
  have hcop_fac_nat : Nat.Coprime (p ^ 3) (p - 1).factorial := by
    refine Nat.Coprime.pow_left 3 ?_
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    have hle := (hp.dvd_factorial).mp hdvd
    have hpos := hp.pos
    omega
  have hcop_fac : IsCoprime ((p : ℤ) ^ 3) ((p - 1).factorial : ℤ) := by
    exact_mod_cast hcop_fac_nat.isCoprime
  have hden_dvd_fac : (h.den : ℤ) ∣ ((p - 1).factorial : ℤ) := by
    have hcop_nd : IsCoprime (h.den : ℤ) h.num := by
      have hcop := h.reduced
      have h1 : IsCoprime h.num (h.den : ℤ) := by
        rw [Int.isCoprime_iff_nat_coprime]
        simpa using hcop
      exact h1.symm
    have hdvd_prod : (h.den : ℤ) ∣ ((p - 1).factorial : ℤ) * h.num := ⟨c, by linarith⟩
    exact hcop_nd.dvd_of_dvd_mul_right hdvd_prod
  have hcop_den : IsCoprime ((p : ℤ) ^ 3) (h.den : ℤ) := by
    rcases hden_dvd_fac with ⟨k, hk⟩
    rw [hk] at hcop_fac
    exact hcop_fac.of_mul_right_left
  have hcast3 : ((p ^ 3 : ℕ) : ℤ) = (p : ℤ) ^ 3 := by push_cast; rfl
  rw [hcast3]
  constructor
  · intro h1
    have h2 : (p : ℤ) ^ 3 ∣ ((p - 1).factorial : ℤ) * h.num := by
      rw [← hint]
      exact dvd_mul_of_dvd_left h1 _
    exact hcop_fac.dvd_of_dvd_mul_left h2
  · intro h1
    have h2 : (p : ℤ) ^ 3 ∣ c * (h.den : ℤ) := by
      rw [hint]
      exact dvd_mul_of_dvd_right h1 _
    exact hcop_den.dvd_of_dvd_mul_right h2

end OMAWolstenholmeHarmonic

theorem OMA.solution : type_of% @WolstenholmePrime.wolstenholme_harmonic := by
  intro p
  unfold WolstenholmePrime.IsWolstenholmePrime
  constructor
  · rintro ⟨hp7, hp, hmod⟩
    refine ⟨hp7, hp, ?_⟩
    rw [← OMAWolstenholmeHarmonic.dvd_coeff_one_iff_dvd_harmonic_num p hp]
    have hodd : Odd p := hp.odd_of_ne_two (by omega)
    have h1 := OMAWolstenholmeHarmonic.eval_p_risingPoly p (by omega)
    have h2 := OMAWolstenholmeHarmonic.eval_neg_p_risingPoly p (by omega) hodd
    have h3 := OMAWolstenholmeHarmonic.eval_sub_eval_neg_modEq p hp hp7
    have hdvd_choose : ((p ^ 4 : ℕ) : ℤ) ∣ ((2 * p - 1).choose (p - 1) : ℤ) - 1 := by
      have hm := (Nat.modEq_iff_dvd.mp hmod.symm)
      simpa using hm
    have hdvd_eval : ((p : ℤ) ^ 4) ∣
        ((OMAWolstenholmeHarmonic.risingPoly (p - 1)).eval (p : ℤ) -
         (OMAWolstenholmeHarmonic.risingPoly (p - 1)).eval (-(p : ℤ))) := by
      rw [h1, h2]
      have hfac : ((p - 1).factorial : ℤ) * ((2 * p - 1).choose (p - 1) : ℤ) -
          ((p - 1).factorial : ℤ) =
          ((p - 1).factorial : ℤ) * (((2 * p - 1).choose (p - 1) : ℤ) - 1) := by ring
      rw [hfac]
      have hcast : ((p : ℤ) ^ 4) = ((p ^ 4 : ℕ) : ℤ) := by push_cast; rfl
      rw [hcast]
      exact dvd_mul_of_dvd_right hdvd_choose _
    have hdvd_2cp : ((p : ℤ) ^ 4) ∣ 2 * (OMAWolstenholmeHarmonic.risingPoly (p - 1)).coeff 1 * (p : ℤ) := by
      have h := dvd_sub hdvd_eval h3
      have hsimp : ((OMAWolstenholmeHarmonic.risingPoly (p - 1)).eval (p : ℤ) -
          (OMAWolstenholmeHarmonic.risingPoly (p - 1)).eval (-(p : ℤ))) -
          (((OMAWolstenholmeHarmonic.risingPoly (p - 1)).eval (p : ℤ) -
          (OMAWolstenholmeHarmonic.risingPoly (p - 1)).eval (-(p : ℤ))) -
          2 * (OMAWolstenholmeHarmonic.risingPoly (p - 1)).coeff 1 * (p : ℤ)) =
          2 * (OMAWolstenholmeHarmonic.risingPoly (p - 1)).coeff 1 * (p : ℤ) := by ring
      rwa [hsimp] at h
    have hdvd_2c : ((p : ℤ) ^ 3) ∣ 2 * (OMAWolstenholmeHarmonic.risingPoly (p - 1)).coeff 1 := by
      have hpne : (p : ℤ) ≠ 0 := by positivity
      have hpow : (p : ℤ) ^ 4 = (p : ℤ) ^ 3 * (p : ℤ) := by ring
      rw [hpow] at hdvd_2cp
      exact (mul_dvd_mul_iff_right hpne).mp hdvd_2cp
    have hcop2 : IsCoprime ((p : ℤ) ^ 3) 2 := by
      have hnat : Nat.Coprime (p ^ 3) 2 := by
        refine Nat.Coprime.pow_left 3 ?_
        rw [hp.coprime_iff_not_dvd]
        intro h
        have := Nat.le_of_dvd (by norm_num) h
        omega
      exact_mod_cast hnat.isCoprime
    exact hcop2.dvd_of_dvd_mul_left hdvd_2c
  · rintro ⟨hp7, hp, hnum⟩
    refine ⟨hp7, hp, ?_⟩
    rw [← OMAWolstenholmeHarmonic.dvd_coeff_one_iff_dvd_harmonic_num p hp] at hnum
    have hodd : Odd p := hp.odd_of_ne_two (by omega)
    have h1 := OMAWolstenholmeHarmonic.eval_p_risingPoly p (by omega)
    have h2 := OMAWolstenholmeHarmonic.eval_neg_p_risingPoly p (by omega) hodd
    have h3 := OMAWolstenholmeHarmonic.eval_sub_eval_neg_modEq p hp hp7
    have hdvd_2cp : ((p : ℤ) ^ 4) ∣ 2 * (OMAWolstenholmeHarmonic.risingPoly (p - 1)).coeff 1 * (p : ℤ) := by
      obtain ⟨k, hk⟩ := hnum
      refine ⟨2 * k, ?_⟩
      rw [hk]
      ring
    have hdvd_eval : ((p : ℤ) ^ 4) ∣
        ((OMAWolstenholmeHarmonic.risingPoly (p - 1)).eval (p : ℤ) -
         (OMAWolstenholmeHarmonic.risingPoly (p - 1)).eval (-(p : ℤ))) := by
      have h := dvd_add h3 hdvd_2cp
      have hsimp : ((OMAWolstenholmeHarmonic.risingPoly (p - 1)).eval (p : ℤ) -
          (OMAWolstenholmeHarmonic.risingPoly (p - 1)).eval (-(p : ℤ))) -
          2 * (OMAWolstenholmeHarmonic.risingPoly (p - 1)).coeff 1 * (p : ℤ) +
          2 * (OMAWolstenholmeHarmonic.risingPoly (p - 1)).coeff 1 * (p : ℤ) =
          (OMAWolstenholmeHarmonic.risingPoly (p - 1)).eval (p : ℤ) -
          (OMAWolstenholmeHarmonic.risingPoly (p - 1)).eval (-(p : ℤ)) := by ring
      rwa [hsimp] at h
    rw [h1, h2] at hdvd_eval
    have hfac : ((p - 1).factorial : ℤ) * ((2 * p - 1).choose (p - 1) : ℤ) -
        ((p - 1).factorial : ℤ) =
        ((p - 1).factorial : ℤ) * (((2 * p - 1).choose (p - 1) : ℤ) - 1) := by ring
    rw [hfac] at hdvd_eval
    have hcop_fac : IsCoprime ((p : ℤ) ^ 4) ((p - 1).factorial : ℤ) := by
      have hnat : Nat.Coprime (p ^ 4) (p - 1).factorial := by
        refine Nat.Coprime.pow_left 4 ?_
        rw [hp.coprime_iff_not_dvd]
        intro hdvd
        have hle := (hp.dvd_factorial).mp hdvd
        omega
      exact_mod_cast hnat.isCoprime
    have hdvd_choose : ((p : ℤ) ^ 4) ∣ ((2 * p - 1).choose (p - 1) : ℤ) - 1 :=
      hcop_fac.dvd_of_dvd_mul_left hdvd_eval
    have hcast : ((p : ℤ) ^ 4) = ((p ^ 4 : ℕ) : ℤ) := by push_cast; rfl
    rw [hcast] at hdvd_choose
    exact (Nat.modEq_iff_dvd.mpr (by simpa using hdvd_choose)).symm
