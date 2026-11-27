import FormalConjectures.Wikipedia.PowerfulNumbersDensity

-- Problem: Asymptotic density of powerful numbers — asymptotic erdos szekeres
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/PowerfulNumbersDensity.lean:64 (declaration PowerfulNumbersDensity.asymptotic_erdos_szekeres)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace W4Pow

open Real Filter Asymptotics Finset

noncomputable def f (n : ℕ) : ℝ := 1 / √((n : ℝ) ^ 3)

noncomputable def g (b : ℕ) : ℝ := if Squarefree b then 1 / √((b : ℝ) ^ 3) else 0

noncomputable def h3 (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 3

lemma sqrt_cube (x : ℝ) (hx : 0 ≤ x) : √(x ^ 3) = x ^ ((3 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma f_nonneg (n : ℕ) : 0 ≤ f n := by unfold f; positivity

lemma g_nonneg (n : ℕ) : 0 ≤ g n := by
  unfold g; split_ifs
  · positivity
  · exact le_refl _

lemma g_le_f (n : ℕ) : g n ≤ f n := by
  unfold g; split_ifs
  · exact le_refl _
  · exact f_nonneg n

lemma f_summable : Summable f := by
  have := Real.summable_nat_rpow_inv.2 (show (1 : ℝ) < 3 / 2 by norm_num)
  refine this.congr (fun n => ?_)
  simp [f, sqrt_cube _ (Nat.cast_nonneg n)]

lemma g_summable : Summable g := Summable.of_nonneg_of_le g_nonneg g_le_f f_summable

lemma h3_summable : Summable h3 := by
  show Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3)
  exact Real.summable_one_div_nat_pow.2 (by norm_num)

lemma unique {a b c d : ℕ} (ha : 0 < a) (hc : 0 < c) (hb : Squarefree b) (hd : Squarefree d)
    (h : a ^ 2 * b = c ^ 2 * d) : a = c ∧ b = d := by
  have hb0 : b ≠ 0 := hb.ne_zero
  have hd0 : d ≠ 0 := hd.ne_zero
  have key : ∀ (a b : ℕ), 0 < a → Squarefree b →
      ∀ p, b.factorization p = (a ^ 2 * b).factorization p % 2 := by
    intro a b ha hb p
    rw [Nat.factorization_mul (pow_ne_zero 2 ha.ne') hb.ne_zero, Nat.factorization_pow]
    have := hb.natFactorization_le_one p
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    omega
  have hbd : b = d := by
    apply Nat.eq_of_factorization_eq hb0 hd0
    intro p
    rw [key a b ha hb p, key c d hc hd p, h]
  subst hbd
  refine ⟨?_, rfl⟩
  have h2 : a ^ 2 = c ^ 2 := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hb0) h
  have : a ≤ c ∧ c ≤ a := ⟨by nlinarith, by nlinarith⟩
  omega

lemma powerful_decomp {n : ℕ} (hn : 0 < n) (hp : n.Powerful) :
    ∃ a b, 0 < a ∧ Squarefree b ∧ n = a ^ 2 * b ^ 3 := by
  obtain ⟨t, s, ht0, hs0, hst, htsq⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hdvd : t ∣ s := by
    rw [← Nat.factorization_le_iff_dvd ht0.ne' hs0.ne']
    intro p
    have h1 := htsq.natFactorization_le_one p
    by_cases hp0 : t.factorization p = 0
    · rw [hp0]; exact Nat.zero_le _
    · have hpp : p.Prime := by
        by_contra hnp
        exact hp0 (Nat.factorization_eq_zero_of_not_prime _ hnp)
      have hpt : p ∣ t := Nat.dvd_of_factorization_pos hp0
      have hpn : p ∈ n.primeFactors :=
        Nat.mem_primeFactors.2 ⟨hpp, hst ▸ dvd_mul_of_dvd_right hpt _, hn.ne'⟩
      have h2 : p ^ 2 ∣ n := hp p hpn
      have h3 : 2 ≤ n.factorization p := (hpp.pow_dvd_iff_le_factorization hn.ne').1 h2
      rw [← hst, Nat.factorization_mul (pow_ne_zero 2 hs0.ne') ht0.ne',
        Nat.factorization_pow] at h3
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h3
      omega
  obtain ⟨a, rfl⟩ := hdvd
  refine ⟨a, t, Nat.pos_of_ne_zero (by rintro rfl; simp at hs0), htsq, ?_⟩
  rw [← hst]; ring

lemma powerful_of (a b : ℕ) : (a ^ 2 * b ^ 3).Powerful := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  rcases (Nat.Prime.dvd_mul hpp).1 hd with h | h
  · exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (hpp.dvd_of_dvd_pow h) 2) _
  · exact dvd_mul_of_dvd_right ((pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans
      (pow_dvd_pow_of_dvd (hpp.dvd_of_dvd_pow h) 3)) _

lemma zeta_id : (∑' n, f n) = (∑' n, h3 n) * (∑' n, g n) := by
  rw [tsum_mul_tsum_of_summable_norm
    (by simpa [Real.norm_eq_abs, abs_of_nonneg, h3] using h3_summable)
    (by simpa [Real.norm_eq_abs, abs_of_nonneg (g_nonneg _)] using g_summable)]
  have hsupp : ∀ z : ℕ × ℕ, h3 z.1 * g z.2 ≠ 0 → 0 < z.1 ∧ Squarefree z.2 := by
    rintro ⟨a, b⟩ hz
    refine ⟨Nat.pos_of_ne_zero ?_, ?_⟩
    · rintro rfl; simp [h3] at hz
    · by_contra hb; simp [g, hb] at hz
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun z : Function.support (fun z : ℕ × ℕ => h3 z.1 * g z.2) => z.1.1 ^ 2 * z.1.2)
  · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ h
    obtain ⟨ha, hb⟩ := hsupp _ hab
    obtain ⟨hc, hd⟩ := hsupp _ hcd
    obtain ⟨rfl, rfl⟩ := unique ha hc hb hd h
    rfl
  · intro n hn
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · simp [f] at hn
      · exact h
    obtain ⟨t, s, _, hs0, hst, htsq⟩ := Nat.sq_mul_squarefree_of_pos hn0
    refine ⟨⟨(s, t), ?_⟩, hst⟩
    simp only [Function.mem_support, g, if_pos htsq, h3]
    have : (s : ℝ) ≠ 0 := by exact_mod_cast hs0.ne'
    have : (t : ℝ) ≠ 0 := by exact_mod_cast htsq.ne_zero
    have : √((t : ℝ) ^ 3) ≠ 0 := by positivity
    positivity
  · rintro ⟨⟨a, b⟩, hab⟩
    obtain ⟨ha, hb⟩ := hsupp _ hab
    simp only [f, g, if_pos hb, h3]
    push_cast
    have ha' : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    rw [show ((a : ℝ) ^ 2 * b) ^ 3 = ((a : ℝ) ^ 3) ^ 2 * (b : ℝ) ^ 3 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    field_simp

lemma zeta32 : (riemannZeta (3 / 2)).re = ∑' n, f n := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num)]
  have : ∀ n : ℕ, 1 / (n : ℂ) ^ (3 / 2 : ℂ) = ((f n : ℝ) : ℂ) := by
    intro n
    unfold f
    rw [sqrt_cube _ (Nat.cast_nonneg _), Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    rfl
  simp_rw [this]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]

lemma zeta3 : (riemannZeta 3).re = ∑' n, h3 n := by
  have := zeta_nat_eq_tsum_of_gt_one (k := 3) (by norm_num)
  push_cast at this
  rw [this]
  have : ∀ n : ℕ, 1 / (n : ℂ) ^ 3 = ((h3 n : ℝ) : ℂ) := by
    intro n; unfold h3; push_cast; rfl
  simp_rw [this]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]

lemma A_eq : PowerfulNumbersDensity.A = ∑' n, g n := by
  unfold PowerfulNumbersDensity.A
  rw [zeta32, zeta3, zeta_id]
  have hpos : 0 < ∑' n, h3 n := by
    have := h3_summable.le_tsum 1 (fun j _ => by unfold h3; positivity)
    rw [show h3 1 = 1 by simp [h3]] at this
    linarith
  field_simp

lemma tele (u : ℝ) (hu : 1 ≤ u) : 1 / √((u + 1) ^ 3) ≤ 2 * (1 / √u - 1 / √(u + 1)) := by
  set s := √u with hs
  set t := √(u + 1) with ht
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have ht0 : 0 < t := Real.sqrt_pos.2 (by linarith)
  have hss : s ^ 2 = u := Real.sq_sqrt (by linarith)
  have htt : t ^ 2 = u + 1 := Real.sq_sqrt (by linarith)
  have hst : s < t := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have h3 : √((u + 1) ^ 3) = t ^ 3 := by
    rw [← htt, show (t ^ 2) ^ 3 = (t ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [h3]
  have h1 : (t - s) * (t + s) = 1 := by nlinarith
  rw [show 2 * (1 / s - 1 / t) = 2 * (t - s) / (s * t) by field_simp,
    div_le_div_iff₀ (by positivity) (by positivity)]
  calc 1 * (s * t) = s * t * ((t - s) * (t + s)) := by rw [h1]; ring
    _ ≤ 2 * (t - s) * t ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ht0.le (sub_nonneg.2 hst.le))
        (sub_nonneg.2 hst.le)) (by positivity : (0 : ℝ) ≤ 2 * t + s)]

lemma tail_partial (K : ℕ) (hK : 1 ≤ K) (n : ℕ) :
    ∑ i ∈ range n, f (i + (K + 1)) ≤ 2 / √(K : ℝ) - 2 / √((n : ℝ) + K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hu : (1 : ℝ) ≤ (n : ℝ) + K := by
      have : (1 : ℝ) ≤ K := by exact_mod_cast hK
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have := tele ((n : ℝ) + K) hu
    have hf : f (n + (K + 1)) = 1 / √(((n : ℝ) + K + 1) ^ 3) := by
      unfold f; push_cast; ring_nf
    rw [hf]
    push_cast
    have e : (n : ℝ) + 1 + K = (n : ℝ) + K + 1 := by ring
    rw [e]
    have e1 : (2 : ℝ) / √((n : ℝ) + K) = 2 * (1 / √((n : ℝ) + K)) := by ring
    have e2 : (2 : ℝ) / √((n : ℝ) + K + 1) = 2 * (1 / √((n : ℝ) + K + 1)) := by ring
    linarith

lemma tail (K : ℕ) (hK : 1 ≤ K) : ∑' i, g (i + (K + 1)) ≤ 2 / √(K : ℝ) := by
  apply ((summable_nat_add_iff (K + 1)).2 g_summable).tsum_le_of_sum_range_le
  intro n
  calc ∑ i ∈ range n, g (i + (K + 1)) ≤ ∑ i ∈ range n, f (i + (K + 1)) :=
        sum_le_sum (fun i _ => g_le_f _)
    _ ≤ 2 / √(K : ℝ) - 2 / √((n : ℝ) + K) := tail_partial K hK n
    _ ≤ 2 / √(K : ℝ) := sub_le_self _ (by positivity)

lemma fiber (x : ℝ) (hx0 : 0 ≤ x) (b : ℕ) (hb : 1 ≤ b) :
    (Icc 1 ⌊x⌋₊).filter (fun a : ℕ => (((a ^ 2 * b ^ 3 : ℕ)) : ℝ) ≤ x) =
      Icc 1 ⌊√(x / (b : ℝ) ^ 3)⌋₊ := by
  have hb' : (0 : ℝ) < (b : ℝ) ^ 3 := by
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb
    positivity
  have key : ∀ a : ℕ, (((a ^ 2 * b ^ 3 : ℕ)) : ℝ) ≤ x ↔ a ≤ ⌊√(x / (b : ℝ) ^ 3)⌋₊ := by
    intro a
    rw [Nat.le_floor_iff (Real.sqrt_nonneg _), Real.le_sqrt (Nat.cast_nonneg _),
      le_div_iff₀ hb']
    · push_cast
      rfl
    · exact div_nonneg hx0 hb'.le
  ext a
  simp only [mem_filter, mem_Icc, key]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, ?_⟩, h2⟩
    have hx := (key a).2 h2
    apply Nat.le_floor
    have : (a : ℝ) ≤ ((a ^ 2 * b ^ 3 : ℕ) : ℝ) := by
      have : a ≤ a ^ 2 * b ^ 3 := by
        have : 1 ≤ b ^ 3 := Nat.one_le_pow _ _ hb
        nlinarith
      exact_mod_cast this
    linarith

lemma count (x : ℝ) (hx0 : 0 ≤ x) (K : ℕ) (hK : ∀ b : ℕ, 1 ≤ b → ((b : ℝ) ^ 3 ≤ x ↔ b ≤ K)) :
    (({n : ℕ | 0 < n ∧ n.Powerful ∧ (n : ℝ) ≤ x}.ncard : ℕ) : ℝ) =
      ∑ b ∈ (range (K + 1)).filter Squarefree, (⌊√(x / (b : ℝ) ^ 3)⌋₊ : ℝ) := by
  set T := (range (K + 1)).filter Squarefree with hT
  set D := ((Icc 1 ⌊x⌋₊) ×ˢ T).filter (fun z : ℕ × ℕ => (((z.1 ^ 2 * z.2 ^ 3 : ℕ)) : ℝ) ≤ x)
    with hD
  have hTsq : ∀ b ∈ T, Squarefree b ∧ 1 ≤ b := by
    intro b hb
    have := (mem_filter.1 hb).2
    exact ⟨this, Nat.pos_of_ne_zero this.ne_zero⟩
  have hset : {n : ℕ | 0 < n ∧ n.Powerful ∧ (n : ℝ) ≤ x} =
      ↑(D.image (fun z : ℕ × ℕ => z.1 ^ 2 * z.2 ^ 3)) := by
    ext n
    simp only [Set.mem_setOf_eq, coe_image, Set.mem_image, mem_coe]
    constructor
    · rintro ⟨hn, hp, hx⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := powerful_decomp hn hp
      have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb.ne_zero
      refine ⟨(a, b), ?_, rfl⟩
      rw [hD, mem_filter, mem_product, mem_Icc, hT, mem_filter, mem_range]
      have hb3 : b ^ 3 ≤ a ^ 2 * b ^ 3 := Nat.le_mul_of_pos_left _ (by positivity)
      have ha3 : a ≤ a ^ 2 * b ^ 3 := by
        have : 1 ≤ b ^ 3 := Nat.one_le_pow _ _ hb1
        nlinarith
      refine ⟨⟨⟨ha, Nat.le_floor ?_⟩, ?_, hb⟩, hx⟩
      · have : (a : ℝ) ≤ ((a ^ 2 * b ^ 3 : ℕ) : ℝ) := by exact_mod_cast ha3
        push_cast at hx this ⊢
        linarith
      · have : ((b : ℝ)) ^ 3 ≤ x := by
          have : ((b ^ 3 : ℕ) : ℝ) ≤ ((a ^ 2 * b ^ 3 : ℕ) : ℝ) := by exact_mod_cast hb3
          push_cast at hx this ⊢
          linarith
        have := (hK b hb1).1 this
        omega
    · rintro ⟨⟨a, b⟩, hz, rfl⟩
      rw [hD, mem_filter, mem_product, mem_Icc] at hz
      obtain ⟨⟨⟨ha, _⟩, hbT⟩, hx⟩ := hz
      obtain ⟨hb, hb1⟩ := hTsq b hbT
      refine ⟨by positivity, powerful_of a b, ?_⟩
      exact_mod_cast hx
  have hinj : Set.InjOn (fun z : ℕ × ℕ => z.1 ^ 2 * z.2 ^ 3) ↑D := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
    simp only [hD, coe_filter, mem_product, mem_Icc, Set.mem_setOf_eq] at hab hcd
    obtain ⟨hb, hb1⟩ := hTsq b hab.1.2
    obtain ⟨hd, hd1⟩ := hTsq d hcd.1.2
    have h' : (a * b) ^ 2 * b = (c * d) ^ 2 * d := by
      simp only at h
      rw [show (a * b) ^ 2 * b = a ^ 2 * b ^ 3 by ring, show (c * d) ^ 2 * d = c ^ 2 * d ^ 3 by ring]
      exact h
    obtain ⟨h1, rfl⟩ := unique (by have := hab.1.1.1; positivity)
      (by have := hcd.1.1.1; positivity) hb hd h'
    have : a = c := Nat.eq_of_mul_eq_mul_right hb1 h1
    rw [this]
  rw [hset, Set.ncard_coe_finset, card_image_of_injOn hinj, hD, card_filter,
    sum_product_right, Nat.cast_sum]
  apply sum_congr rfl
  intro b hb
  rw [← card_filter, fiber x hx0 b (hTsq b hb).2, Nat.card_Icc]
  simp

lemma main (x : ℝ) (hx : 1 ≤ x) :
    |(({n : ℕ | 0 < n ∧ n.Powerful ∧ (n : ℝ) ≤ x}.ncard : ℕ) : ℝ) - (∑' n, g n) * √x| ≤
      4 * x ^ ((1 : ℝ) / 3) := by
  set r := x ^ ((1 : ℝ) / 3) with hr
  have hx0 : 0 ≤ x := by linarith
  have hr3 : r ^ 3 = x := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have hr1 : 1 ≤ r := Real.one_le_rpow hx (by norm_num)
  set K := ⌊r⌋₊ with hKdef
  have hK1 : 1 ≤ K := Nat.le_floor (by exact_mod_cast hr1)
  have hKr : (K : ℝ) ≤ r := Nat.floor_le (by linarith)
  have hrK : r < K + 1 := Nat.lt_floor_add_one r
  have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK : ∀ b : ℕ, 1 ≤ b → ((b : ℝ) ^ 3 ≤ x ↔ b ≤ K) := by
    intro b _
    rw [hKdef, Nat.le_floor_iff (by linarith), ← hr3,
      pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by linarith) (by norm_num)]
  rw [count x hx0 K hK]
  set T := (range (K + 1)).filter Squarefree with hT
  have hsx : √x = r * √r := by
    rw [← hr3, show r ^ 3 = r ^ 2 * r by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by linarith)]
  have hy : ∀ b ∈ T, √(x / (b : ℝ) ^ 3) = √x * g b := by
    intro b hb
    have hsq := (mem_filter.1 hb).2
    rw [g, if_pos hsq, Real.sqrt_div hx0]
    ring
  have hsumT : ∑ b ∈ T, g b = ∑ b ∈ range (K + 1), g b := by
    rw [hT, sum_filter]
    apply sum_congr rfl
    intro b _
    unfold g
    split_ifs <;> rfl
  have hS : ∑' n, g n = ∑ b ∈ range (K + 1), g b + ∑' i, g (i + (K + 1)) :=
    (g_summable.sum_add_tsum_nat_add (K + 1)).symm
  have htail := tail K hK1
  have htail0 : 0 ≤ ∑' i, g (i + (K + 1)) := tsum_nonneg (fun i => g_nonneg _)
  have hcardT : (T.card : ℝ) ≤ r := by
    have : T ⊆ Icc 1 K := by
      intro b hb
      rw [hT, mem_filter, mem_range] at hb
      rw [mem_Icc]
      exact ⟨Nat.pos_of_ne_zero hb.2.ne_zero, by omega⟩
    have := card_le_card this
    rw [Nat.card_Icc] at this
    have : (T.card : ℝ) ≤ K := by exact_mod_cast (by omega : T.card ≤ K)
    linarith
  -- upper and lower bounds for the floor sum
  have hup : ∑ b ∈ T, (⌊√(x / (b : ℝ) ^ 3)⌋₊ : ℝ) ≤ √x * ∑ b ∈ T, g b := by
    rw [mul_sum]
    apply sum_le_sum
    intro b hb
    rw [← hy b hb]
    exact Nat.floor_le (Real.sqrt_nonneg _)
  have hlow : √x * ∑ b ∈ T, g b - T.card ≤ ∑ b ∈ T, (⌊√(x / (b : ℝ) ^ 3)⌋₊ : ℝ) := by
    rw [mul_sum, card_eq_sum_ones, Nat.cast_sum, ← sum_sub_distrib]
    apply sum_le_sum
    intro b hb
    rw [← hy b hb]
    have := Nat.lt_floor_add_one (√(x / (b : ℝ) ^ 3))
    push_cast
    linarith
  -- tail times sqrt x
  have hsqrtK : 2 * √r ≤ 3 * √(K : ℝ) := by
    have h1 : (2 * √r) ^ 2 ≤ (3 * √(K : ℝ)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
      linarith
    have : 0 ≤ 3 * √(K : ℝ) := by positivity
    nlinarith [Real.sqrt_nonneg r]
  have hKpos : 0 < √(K : ℝ) := Real.sqrt_pos.2 (by linarith)
  have htailx : √x * ∑' i, g (i + (K + 1)) ≤ 3 * r := by
    calc √x * ∑' i, g (i + (K + 1)) ≤ √x * (2 / √(K : ℝ)) :=
          mul_le_mul_of_nonneg_left htail (Real.sqrt_nonneg _)
      _ = r * (2 * √r) / √(K : ℝ) := by rw [hsx]; ring
      _ ≤ r * (3 * √(K : ℝ)) / √(K : ℝ) := by
          apply div_le_div_of_nonneg_right _ hKpos.le
          exact mul_le_mul_of_nonneg_left hsqrtK (by linarith)
      _ = 3 * r := by field_simp
  rw [abs_le]
  rw [hsumT] at hup hlow
  constructor
  · rw [hS] at *
    nlinarith
  · rw [hS]
    have : 0 ≤ √x * ∑' i, g (i + (K + 1)) := mul_nonneg (Real.sqrt_nonneg _) htail0
    nlinarith

end W4Pow

theorem OMA.solution : type_of% @PowerfulNumbersDensity.asymptotic_erdos_szekeres := by
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
    W4Pow.A_eq, ← Real.sqrt_eq_rpow]
  exact W4Pow.main x hx
