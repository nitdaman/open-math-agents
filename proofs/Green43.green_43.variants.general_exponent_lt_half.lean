import FormalConjectures.GreensOpenProblems.«43»

-- Problem: Ben Green's Open Problem 43 — general exponent lt half
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/43.lean:183 (declaration Green43.green_43.variants.general_exponent_lt_half)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMAGreen43

open Finset

/-! ### Many primes in a dyadic interval (a quantitative Bertrand postulate) -/

/-- The contribution of the primes `≤ 2n/3` to the central binomial coefficient
(the same estimate as in Mathlib's proof of Bertrand's postulate). -/
lemma small_part (n : ℕ) (n_large : 2 < n) :
    ∏ x ∈ Finset.range (2 * n / 3 + 1), x ^ n.centralBinom.factorization x ≤
      (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  let f x := x ^ n.centralBinom.factorization x
  have : ∏ x ∈ S, f x = ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := by
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose h; dsimp only [f]
    rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom h, _root_.pow_zero]
  show ∏ x ∈ Finset.range (2 * n / 3 + 1), f x ≤ _
  rw [← this, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * n))]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
    · exact Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)
    have : (Finset.Icc 1 (Nat.sqrt (2 * n))).card = Nat.sqrt (2 * n) := by
      rw [Nat.card_Icc, Nat.add_sub_cancel]
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
  · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)
    refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

/-- The number of primes in `(m, 2m]`. -/
def K (m : ℕ) : ℕ := ((Finset.Ioc m (2 * m)).filter Nat.Prime).card

lemma centralBinom_le (m : ℕ) (hm : 2 < m) :
    m.centralBinom ≤ (2 * m) ^ Nat.sqrt (2 * m) * 4 ^ (2 * m / 3) * (2 * m) ^ K m := by
  set f : ℕ → ℕ := fun x => x ^ m.centralBinom.factorization x with hf
  have h0 : m.centralBinom = ∏ x ∈ Finset.range (2 * m + 1), f x :=
    (Nat.prod_pow_factorization_centralBinom m).symm
  rw [h0, ← Finset.prod_filter_mul_prod_filter_not (Finset.range (2 * m + 1))
    (· ≤ 2 * m / 3)]
  have hfil : (Finset.range (2 * m + 1)).filter (· ≤ 2 * m / 3) =
      Finset.range (2 * m / 3 + 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h; omega
    · intro h
      have : 2 * m / 3 ≤ 2 * m := Nat.div_le_self _ _
      omega
  rw [hfil]
  apply mul_le_mul' (small_part m hm)
  set P := (Finset.Ioc m (2 * m)).filter Nat.Prime with hP
  set R := (Finset.range (2 * m + 1)).filter (fun x => ¬ x ≤ 2 * m / 3) with hR
  calc ∏ x ∈ R, f x ≤ ∏ x ∈ R, (if x ∈ P then 2 * m else 1) := by
        apply Finset.prod_le_prod'
        intro x hx
        have hx' := Finset.mem_filter.mp hx
        have hx2 : x ≤ 2 * m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx'.1)
        have hx3 : 2 * m < 3 * x := by
          have := hx'.2
          rw [not_le, Nat.div_lt_iff_lt_mul (by norm_num)] at this
          omega
        split_ifs with hxP
        · have : f x = x ^ (Nat.choose (2 * m) m).factorization x := by
            simp only [hf, Nat.centralBinom_eq_two_mul_choose]
          rw [this]
          exact Nat.pow_factorization_choose_le (by omega)
        · by_cases hpr : x.Prime
          · have hxm : x ≤ m := by
              by_contra hc
              exact hxP (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hx2⟩, hpr⟩)
            simp only [hf]
            rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hm hxm hx3,
              pow_zero]
          · simp only [hf]
            rw [Nat.factorization_eq_zero_of_not_prime _ hpr, pow_zero]
    _ = ∏ x ∈ R ∩ P, 2 * m := Finset.prod_ite_mem _ _ _
    _ = (2 * m) ^ (R ∩ P).card := Finset.prod_const _
    _ ≤ (2 * m) ^ K m :=
        pow_le_pow_right₀ (by omega) (Finset.card_le_card Finset.inter_subset_right)

lemma K_lower (m : ℕ) (hm : 4 ≤ m) :
    (m : ℝ) * Real.log 4 / (3 * Real.log (2 * m)) - 1 - Real.sqrt (2 * m) ≤ K m := by
  have h1 : 4 ^ m < m * m.centralBinom := Nat.four_pow_lt_mul_centralBinom m hm
  have h2 := centralBinom_le m (by omega)
  have h3 : 4 ^ m < m * ((2 * m) ^ Nat.sqrt (2 * m) * 4 ^ (2 * m / 3) * (2 * m) ^ K m) :=
    lt_of_lt_of_le h1 (Nat.mul_le_mul_left _ h2)
  have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have h4 : (4 : ℝ) ^ m < m * ((2 * m) ^ Nat.sqrt (2 * m) * 4 ^ (2 * m / 3) * (2 * m) ^ K m) := by
    exact_mod_cast h3
  have h5 := Real.log_lt_log (by positivity) h4
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow] at h5
  set L := Real.log (2 * m) with hL
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hlogm : Real.log m ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hs : (Nat.sqrt (2 * m) : ℝ) ≤ Real.sqrt (2 * m) := by
    have := Real.nat_sqrt_le_real_sqrt (a := 2 * m)
    push_cast at this
    exact this
  have ht : ((2 * m / 3 : ℕ) : ℝ) ≤ 2 * m / 3 := by
    have := Nat.cast_div_le (α := ℝ) (m := 2 * m) (n := 3)
    push_cast at this
    exact this
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hsL := mul_le_mul_of_nonneg_right hs hLpos.le
  have htL := mul_le_mul_of_nonneg_right ht hlog4.le
  have e : (m : ℝ) * Real.log 4 / (3 * L) * L = m * Real.log 4 / 3 := by
    field_simp
  suffices hh : ((m : ℝ) * Real.log 4 / (3 * L) - 1 - Real.sqrt (2 * m)) * L ≤ K m * L from
    le_of_mul_le_mul_right hh hLpos
  rw [sub_mul, sub_mul, e]
  push_cast at h5
  nlinarith

/-! ### Inclusion–exclusion -/

lemma union_bound (T : Finset ℕ) (A : ℕ → Finset ℤ) :
    ∑ p ∈ T, (A p).card ≤
      (T.biUnion A).card + ∑ p ∈ T, ∑ q ∈ T.erase p, (A p ∩ A q).card := by
  classical
  let B : ℕ → Finset ℤ := fun p => A p \ (T.erase p).biUnion A
  have hdisj : (T : Set ℕ).PairwiseDisjoint B := by
    intro p hp q hq hpq
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hxp hxq
    have h1 := (Finset.mem_sdiff.mp hxp).2
    have h2 := (Finset.mem_sdiff.mp hxq).1
    exact h1 (Finset.mem_biUnion.mpr ⟨q, Finset.mem_erase.mpr ⟨Ne.symm hpq, hq⟩, h2⟩)
  have hsub : T.biUnion B ⊆ T.biUnion A := by
    intro x hx
    obtain ⟨p, hp, hx⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨p, hp, (Finset.mem_sdiff.mp hx).1⟩
  have hcard : (T.biUnion B).card = ∑ p ∈ T, (B p).card := Finset.card_biUnion hdisj
  have hB : ∀ p ∈ T, (A p).card ≤ (B p).card + ∑ q ∈ T.erase p, (A p ∩ A q).card := by
    intro p _
    have e := Finset.card_sdiff_add_card_inter (A p) ((T.erase p).biUnion A)
    have : (A p ∩ (T.erase p).biUnion A).card ≤ ∑ q ∈ T.erase p, (A p ∩ A q).card := by
      rw [Finset.inter_biUnion]
      exact Finset.card_biUnion_le
    simp only [B]
    omega
  calc ∑ p ∈ T, (A p).card ≤ ∑ p ∈ T, ((B p).card + ∑ q ∈ T.erase p, (A p ∩ A q).card) :=
        Finset.sum_le_sum hB
    _ = ∑ p ∈ T, (B p).card + ∑ p ∈ T, ∑ q ∈ T.erase p, (A p ∩ A q).card :=
        Finset.sum_add_distrib
    _ ≤ _ := by
        rw [← hcard]
        exact Nat.add_le_add_right (Finset.card_le_card hsub) _

/-- The residue class `c mod p` inside `[1, N]`. -/
def cls (N p : ℕ) (c : ℤ) : Finset ℤ :=
  (Finset.Icc (1 : ℤ) N).filter (fun n => (p : ℤ) ∣ n - c)

lemma card_cls_ge (N p : ℕ) (hp : 0 < p) (c : ℤ) : N / p ≤ (cls N p c).card := by
  set r : ℤ := (c - 1) % p + 1 with hr
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hr1 : 1 ≤ r := by have := Int.emod_nonneg (c - 1) hp'.ne'; omega
  have hrp : r ≤ p := by have := Int.emod_lt_of_pos (c - 1) hp'; omega
  have hrc : (p : ℤ) ∣ r - c := ⟨-((c - 1) / p), by rw [hr, Int.emod_def]; ring⟩
  have := Finset.card_le_card_of_injOn (s := Finset.range (N / p)) (t := cls N p c)
    (fun j : ℕ => r + (j : ℤ) * p) ?_ ?_
  · simpa using this
  · intro j hj
    have hj' : j < N / p := Finset.mem_range.mp hj
    have h1 : (j + 1) * p ≤ N := (Nat.mul_le_mul_right p hj').trans (Nat.div_mul_le_self N p)
    rw [Nat.succ_mul] at h1
    have h2 : (j : ℤ) * p + p ≤ N := by exact_mod_cast h1
    have h3 : (0 : ℤ) ≤ (j : ℤ) * p := by positivity
    unfold cls
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    have : r + (j : ℤ) * p - c = (r - c) + (j : ℤ) * p := by ring
    rw [this]
    exact dvd_add hrc (dvd_mul_left _ _)
  · intro i _ j _ hij
    have h : (i : ℤ) * p = (j : ℤ) * p := by simpa using hij
    exact_mod_cast mul_right_cancel₀ hp'.ne' h

lemma card_inter_le (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (c d : ℤ) :
    (cls N p c ∩ cls N q d).card ≤ N / (p * q) + 1 := by
  have hM : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hcop : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
  have := Finset.card_le_card_of_injOn (s := cls N p c ∩ cls N q d)
    (t := Finset.range (N / (p * q) + 1)) (fun n : ℤ => (n - 1).toNat / (p * q)) ?_ ?_
  · simpa using this
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_inter] at hn
    unfold cls at hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.div_le_div_right
    omega
  · intro n hn n' hn' h
    rw [Finset.mem_coe, Finset.mem_inter] at hn hn'
    unfold cls at hn hn'
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn hn'
    have hdp : (p : ℤ) ∣ n - n' := by
      have := dvd_sub hn.1.2 hn'.1.2
      rwa [show n - c - (n' - c) = n - n' by ring] at this
    have hdq : (q : ℤ) ∣ n - n' := by
      have := dvd_sub hn.2.2 hn'.2.2
      rwa [show n - d - (n' - d) = n - n' by ring] at this
    have hdM : ((p * q : ℕ) : ℤ) ∣ n - n' := by push_cast; exact hcop.mul_dvd hdp hdq
    set u := (n - 1).toNat with hu
    set u' := (n' - 1).toNat with hu'
    have hu1 : (u : ℤ) = n - 1 := Int.toNat_of_nonneg (by omega)
    have hu1' : (u' : ℤ) = n' - 1 := Int.toNat_of_nonneg (by omega)
    have e1 := Nat.div_add_mod u (p * q)
    have e2 := Nat.div_add_mod u' (p * q)
    have hr1 := Nat.mod_lt u hM
    have hr2 := Nat.mod_lt u' hM
    simp only at h
    rw [h] at e1
    set r := u % (p * q) with hr
    set r' := u' % (p * q) with hr'
    have key : r + u' = r' + u := by
      generalize p * q * (u' / (p * q)) = X at e1 e2
      omega
    have keyZ : (r : ℤ) + u' = r' + u := by exact_mod_cast key
    have hdiff : n - n' = (r : ℤ) - r' := by linarith
    rw [hdiff] at hdM
    have hr1Z : (r : ℤ) < ((p * q : ℕ) : ℤ) := by exact_mod_cast hr1
    have hr2Z : (r' : ℤ) < ((p * q : ℕ) : ℤ) := by exact_mod_cast hr2
    have hz := Int.eq_zero_of_abs_lt_dvd hdM (by
      rw [abs_lt]; constructor <;> linarith [(Nat.cast_nonneg r : (0:ℤ) ≤ r),
        (Nat.cast_nonneg r' : (0:ℤ) ≤ r')])
    have hrr : r = r' := by omega
    have huu : u = u' := by omega
    have : (u : ℤ) = u' := by rw [huu]
    linarith

/-! ### Asymptotics -/

lemma asym (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∀ᶠ x : ℝ in Filter.atTop,
      4 * x ^ (1 - δ) ≤ (x / 2) * Real.log 4 / (3 * Real.log (2 * x)) - 1 - Real.sqrt (2 * x) := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set c := δ * Real.log 4 / 24 with hc
  have hc0 : 0 < c := by positivity
  filter_upwards [Filter.eventually_ge_atTop 1,
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < δ / 2)).eventually_ge_atTop (12 / c),
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 / 2 - δ / 2)).eventually_ge_atTop
      (3 * Real.sqrt 2 / c),
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - δ / 2)).eventually_ge_atTop (3 / c)]
    with x hx1 h1 h2 h3
  have hx0 : 0 < x := by linarith
  have hlog2x : 0 < Real.log (2 * x) := Real.log_pos (by linarith)
  have hlog : Real.log (2 * x) ≤ (4 / δ) * x ^ (δ / 2) := by
    have h := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ 2 * x) (by positivity : 0 < δ / 2)
    rw [Real.mul_rpow (by norm_num) hx0.le] at h
    have h2le : (2 : ℝ) ^ (δ / 2) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith : δ / 2 ≤ 1)
      rwa [Real.rpow_one] at this
    have hxp : 0 ≤ x ^ (δ / 2) := by positivity
    calc Real.log (2 * x) ≤ 2 ^ (δ / 2) * x ^ (δ / 2) / (δ / 2) := h
      _ ≤ 2 * x ^ (δ / 2) / (δ / 2) := by gcongr
      _ = (4 / δ) * x ^ (δ / 2) := by field_simp; ring
  have hsplit0 : x ^ (1 - δ / 2) * x ^ (δ / 2) = x := by
    rw [← Real.rpow_add hx0]; norm_num
  have hmain : c * x ^ (1 - δ / 2) ≤ (x / 2) * Real.log 4 / (3 * Real.log (2 * x)) := by
    rw [le_div_iff₀ (by positivity)]
    calc c * x ^ (1 - δ / 2) * (3 * Real.log (2 * x))
        ≤ c * x ^ (1 - δ / 2) * (3 * ((4 / δ) * x ^ (δ / 2))) := by gcongr
      _ = (c * 12 / δ) * (x ^ (1 - δ / 2) * x ^ (δ / 2)) := by ring
      _ = (x / 2) * Real.log 4 := by rw [hsplit0, hc]; field_simp; ring
  have hsplit1 : x ^ (1 - δ / 2) = x ^ (1 - δ) * x ^ (δ / 2) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hsplit2 : x ^ (1 - δ / 2) = x ^ (1 / 2 : ℝ) * x ^ (1 / 2 - δ / 2) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hsqrt : Real.sqrt (2 * x) = Real.sqrt 2 * x ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow x]
  have ha : 4 * x ^ (1 - δ) ≤ c / 3 * x ^ (1 - δ / 2) := by
    rw [hsplit1]
    have hp : 0 ≤ x ^ (1 - δ) := by positivity
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg (by positivity : 0 ≤ c / 3) hp)
    have e : c / 3 * x ^ (1 - δ) * (12 / c) = 4 * x ^ (1 - δ) := by field_simp; ring
    nlinarith
  have hb : Real.sqrt (2 * x) ≤ c / 3 * x ^ (1 - δ / 2) := by
    rw [hsplit2, hsqrt]
    have hp : 0 ≤ x ^ (1 / 2 : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left h2 (mul_nonneg (by positivity : 0 ≤ c / 3) hp)
    have e : c / 3 * x ^ (1 / 2 : ℝ) * (3 * Real.sqrt 2 / c) = Real.sqrt 2 * x ^ (1 / 2 : ℝ) := by
      field_simp
    nlinarith
  have hcc : 1 ≤ c / 3 * x ^ (1 - δ / 2) := by
    have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ c / 3)
    have e : c / 3 * (3 / c) = 1 := by field_simp
    linarith
  linarith

end OMAGreen43

open Green43 in
set_option maxHeartbeats 1000000 in
theorem OMA.solution : type_of% @Green43.green_43.variants.general_exponent_lt_half := by
  intro α hα0 hα1
  unfold SievedLowerBoundExp SievedLowerBound
  intro ε hε
  set δ := min (ε / α) (1 / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (div_pos hε hα0) (by norm_num)
  have hδ2 : δ ≤ 1 / 2 := min_le_right _ _
  have hαδ : α * δ ≤ ε := by
    have := mul_le_mul_of_nonneg_left (min_le_left (ε / α) (1 / 2)) hα0.le
    rwa [mul_div_cancel₀ _ hα0.ne'] at this
  have hxN : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ α) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hα0).comp tendsto_natCast_atTop_atTop
  have hyN : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - 2 * α)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hxN.eventually (OMAGreen43.asym δ hδ0 hδ2),
    hxN.eventually (Filter.eventually_ge_atTop 32),
    hxN.eventually ((tendsto_rpow_atTop hδ0).eventually_ge_atTop 128),
    hyN.eventually (Filter.eventually_ge_atTop (17 / 3)),
    Filter.eventually_ge_atTop 1] with N hF3 hF1 hF2 hF4 hN1
  intro a
  set x : ℝ := (N : ℝ) ^ α with hx
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hx0 : 0 < x := by linarith
  -- 16 x + x² ≤ 3 N
  have hx2 : x ^ 2 = (N : ℝ) ^ (2 * α) := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; ring_nf
  have hNsplit : (N : ℝ) = (N : ℝ) ^ (2 * α) * (N : ℝ) ^ (1 - 2 * α) := by
    rw [← Real.rpow_add (by linarith)]; simp
  have hF4' : 16 * x + x ^ 2 ≤ 3 * N := by
    have h1 : 16 * x ≤ 16 * x ^ 2 := by nlinarith
    have h2 : 17 * (N : ℝ) ^ (2 * α) ≤ 3 * N := by
      have h0 : 0 ≤ (N : ℝ) ^ (2 * α) := by positivity
      have := mul_le_mul_of_nonneg_left hF4 (by positivity : (0 : ℝ) ≤ 3 * (N : ℝ) ^ (2 * α))
      have e : 3 * (N : ℝ) ^ (2 * α) * (17 / 3) = 17 * (N : ℝ) ^ (2 * α) := by ring
      have e2 : 3 * (N : ℝ) ^ (2 * α) * (N : ℝ) ^ (1 - 2 * α) = 3 * N := by
        rw [mul_assoc, ← hNsplit]
      linarith
    rw [hx2] at h1 ⊢
    linarith
  -- the primes
  set m := ⌊x⌋₊ with hm
  have hm1 : (m : ℝ) ≤ x := Nat.floor_le hx0.le
  have hm2 : x < m + 1 := Nat.lt_floor_add_one x
  have hm4 : 4 ≤ m := by
    have : (4 : ℝ) < m + 1 := by linarith
    have : (3 : ℝ) < m := by linarith
    exact_mod_cast (show (3 : ℝ) < m from this)
  have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm4
  have hKlow := OMAGreen43.K_lower m hm4
  have hK : 4 * x ^ (1 - δ) ≤ OMAGreen43.K m := by
    refine le_trans hF3 (le_trans ?_ hKlow)
    have hl1 : Real.log (2 * m) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
    have hl0 : 0 < Real.log (2 * m) := Real.log_pos (by linarith)
    have hs : Real.sqrt (2 * m) ≤ Real.sqrt (2 * x) := Real.sqrt_le_sqrt (by linarith)
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have hq : (x / 2) * Real.log 4 / (3 * Real.log (2 * x)) ≤
        (m : ℝ) * Real.log 4 / (3 * Real.log (2 * m)) := by
      apply div_le_div₀ (by positivity) _ (by positivity) (by linarith)
      exact mul_le_mul_of_nonneg_right (by linarith) hlog4.le
    linarith
  set L := ⌊x / 16⌋₊ with hL
  have hLle : (L : ℝ) ≤ x / 16 := Nat.floor_le (by positivity)
  have hLge : x / 16 - 1 < L := by
    have := Nat.lt_floor_add_one (x / 16); linarith
  have hxsplit : x = x ^ δ * x ^ (1 - δ) := by
    rw [← Real.rpow_add hx0]; simp
  have hL4 : 4 * x ^ (1 - δ) ≤ L := by
    have hp : 0 ≤ x ^ (1 - δ) := by positivity
    have : 128 * x ^ (1 - δ) ≤ x := by
      have := mul_le_mul_of_nonneg_right hF2 hp
      linarith [hxsplit]
    have : x / 32 ≤ x / 16 - 1 := by linarith
    linarith
  set k := min (OMAGreen43.K m) L with hk
  have hkR : (k : ℝ) = min (OMAGreen43.K m : ℝ) (L : ℝ) := by rw [hk]; push_cast; rfl
  have hk4 : 4 * x ^ (1 - δ) ≤ k := by rw [hkR]; exact le_min hK hL4
  have hkx : (k : ℝ) ≤ x / 16 := by rw [hkR]; exact (min_le_right _ _).trans hLle
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (s := (Finset.Ioc m (2 * m)).filter Nat.Prime)
    (n := k) (min_le_left _ _)
  have hTp : ∀ p ∈ T, p.Prime ∧ x ≤ p ∧ (p : ℝ) < 2 * x := by
    intro p hp
    have hp' := Finset.mem_filter.mp (hTsub hp)
    have hpI := Finset.mem_Ioc.mp hp'.1
    have hpr := hp'.2
    refine ⟨hpr, ?_, ?_⟩
    · have : (m : ℝ) + 1 ≤ p := by exact_mod_cast hpI.1
      linarith
    · have hne : p ≠ 2 * m := by
        intro h
        have h2 := (Nat.Prime.eq_one_or_self_of_dvd hpr 2 ⟨m, h⟩)
        omega
      have : (p : ℝ) ≤ 2 * m - 1 := by
        have : p ≤ 2 * m - 1 := by omega
        have h' : ((2 * m - 1 : ℕ) : ℝ) = 2 * m - 1 := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [← h']; exact_mod_cast this
      linarith
  -- union of classes inside the sieved set
  let A : ℕ → Finset ℤ := fun p => OMAGreen43.cls N p (a p)
  have hsubS : T.biUnion A ⊆ sievedSet N a x (2 * x) := by
    intro n hn
    obtain ⟨p, hp, hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨hpr, hpx, hpx2⟩ := hTp p hp
    simp only [A, OMAGreen43.cls, Finset.mem_filter] at hn
    unfold sievedSet
    simp only [Finset.mem_filter]
    exact ⟨hn.1, p, hpr, hpx, hpx2, hn.2⟩
  have hU := OMAGreen43.union_bound T A
  have hcardS : (T.biUnion A).card ≤ sievedCard N a x (2 * x) := by
    unfold sievedCard; exact Finset.card_le_card hsubS
  -- real estimates
  have hAp : ∀ p ∈ T, (N : ℝ) / (2 * x) - 1 ≤ (A p).card := by
    intro p hp
    obtain ⟨hpr, hpx, hpx2⟩ := hTp p hp
    have h1 := OMAGreen43.card_cls_ge N p hpr.pos (a p)
    have h2 : (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
      have := Nat.lt_div_mul_add (a := N) hpr.pos
      have h' : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast this
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
      rw [div_sub_one hp0.ne', div_le_iff₀ hp0]
      linarith
    have h3 : (N : ℝ) / (2 * x) ≤ N / p :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hpx2.le
    have h4 : (((N / p : ℕ)) : ℝ) ≤ (A p).card := by exact_mod_cast h1
    linarith
  have hApq : ∀ p ∈ T, ∀ q ∈ T.erase p, ((A p ∩ A q).card : ℝ) ≤ N / x ^ 2 + 1 := by
    intro p hp q hq
    obtain ⟨hpr, hpx, -⟩ := hTp p hp
    obtain ⟨hqr, hqx, -⟩ := hTp q (Finset.mem_of_mem_erase hq)
    have hpq : p ≠ q := Ne.symm (Finset.ne_of_mem_erase hq)
    have h1 := OMAGreen43.card_inter_le N p q hpr hqr hpq (a p) (a q)
    have h2 : (((N / (p * q) : ℕ)) : ℝ) ≤ N / (p * q) := by
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := p * q)
      push_cast at this; exact this
    have h3 : (N : ℝ) / (p * q) ≤ N / x ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      rw [sq]; exact mul_le_mul hpx hqx hx0.le (by linarith)
    have h4 : ((A p ∩ A q).card : ℝ) ≤ ((N / (p * q) + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h4
    linarith
  have hS1 : (k : ℝ) * ((N : ℝ) / (2 * x) - 1) ≤ ∑ p ∈ T, ((A p).card : ℝ) := by
    have := Finset.sum_le_sum hAp
    rw [Finset.sum_const, hTcard, nsmul_eq_mul] at this
    exact this
  have hS2 : ∑ p ∈ T, ∑ q ∈ T.erase p, ((A p ∩ A q).card : ℝ) ≤
      (k : ℝ) * ((k : ℝ) * (N / x ^ 2 + 1)) := by
    have hk0 : (0 : ℝ) ≤ N / x ^ 2 + 1 := by positivity
    calc ∑ p ∈ T, ∑ q ∈ T.erase p, ((A p ∩ A q).card : ℝ)
        ≤ ∑ p ∈ T, ∑ q ∈ T.erase p, ((N : ℝ) / x ^ 2 + 1) :=
          Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hApq p hp q hq
      _ ≤ ∑ p ∈ T, (k : ℝ) * (N / x ^ 2 + 1) := by
          apply Finset.sum_le_sum
          intro p hp
          rw [Finset.sum_const, nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ hk0
          have : (T.erase p).card ≤ k := hTcard ▸ Finset.card_erase_le
          exact_mod_cast this
      _ = (k : ℝ) * ((k : ℝ) * (N / x ^ 2 + 1)) := by
          rw [Finset.sum_const, hTcard, nsmul_eq_mul]
  have hUR : ∑ p ∈ T, ((A p).card : ℝ) ≤ ((T.biUnion A).card : ℝ) +
      ∑ p ∈ T, ∑ q ∈ T.erase p, ((A p ∩ A q).card : ℝ) := by exact_mod_cast hU
  have hcardR : ((T.biUnion A).card : ℝ) ≤ sievedCard N a x (2 * x) := by exact_mod_cast hcardS
  -- the main inequality
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hq1 : (k : ℝ) * (N / x ^ 2 + 1) ≤ N / (16 * x) + x / 16 := by
    have := mul_le_mul_of_nonneg_right hkx (by positivity : (0 : ℝ) ≤ N / x ^ 2 + 1)
    have e : x / 16 * (N / x ^ 2 + 1) = N / (16 * x) + x / 16 := by
      first | (field_simp; done) | (field_simp; ring)
    linarith
  have hq2 : 1 + x / 16 ≤ 3 * N / (16 * x) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hq3 : (N : ℝ) / (2 * x) - N / (16 * x) - N / (4 * x) = 3 * N / (16 * x) := by
    field_simp; ring
  have hmainR : (k : ℝ) * N / (4 * x) ≤ sievedCard N a x (2 * x) := by
    have h := mul_le_mul_of_nonneg_left hq1 hk0
    have e : (k : ℝ) * N / (4 * x) = (k : ℝ) * (N / (4 * x)) := by ring
    rw [e]
    have h4 : 0 ≤ (k : ℝ) * (3 * N / (16 * x) - 1 - x / 16) := mul_nonneg hk0 (by linarith)
    have e2 : (k : ℝ) * ((N : ℝ) / (2 * x) - 1) - (k : ℝ) * (N / (16 * x) + x / 16) -
        (k : ℝ) * (N / (4 * x)) = (k : ℝ) * (3 * N / (16 * x) - 1 - x / 16) := by
      rw [← hq3]; ring
    linarith
  -- conclude
  have hfin : (N : ℝ) ^ (1 - ε) ≤ (k : ℝ) * N / (4 * x) := by
    have h1 : 4 * x ^ (1 - δ) * N / (4 * x) ≤ (k : ℝ) * N / (4 * x) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hk4 (by positivity)
    have h2 : 4 * x ^ (1 - δ) * N / (4 * x) = N * x ^ (-δ) := by
      have : x ^ (1 - δ) = x * x ^ (-δ) := by
        rw [← Real.rpow_one_add' hx0.le (ne_of_gt (by linarith))]; ring_nf
      rw [this]; field_simp
    have h3 : x ^ (-δ) = (N : ℝ) ^ (-(α * δ)) := by
      rw [hx, ← Real.rpow_mul (by linarith)]; ring_nf
    have h4 : (N : ℝ) * (N : ℝ) ^ (-(α * δ)) = (N : ℝ) ^ (1 - α * δ) := by
      have hαδ' : α * δ < 1 / 4 := by nlinarith
      rw [← Real.rpow_one_add' (by linarith) (ne_of_gt (by linarith))]; ring_nf
    have h5 : (N : ℝ) ^ (1 - ε) ≤ (N : ℝ) ^ (1 - α * δ) :=
      Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
    rw [h2, h3, h4] at h1
    linarith
  linarith
