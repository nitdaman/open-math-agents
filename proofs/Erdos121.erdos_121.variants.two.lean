import FormalConjectures.ErdosProblems.«121»
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
Erdős, Sárközy and Sós, *On product representations of powers, I*,
European Journal of Combinatorics 16 (1995), pp. 567–588.
https://real.mtak.hu/110606/1/1-s2.0-019566989590039X-main.pdf
-/

open Filter Asymptotics ArithmeticFunction
open scoped BigOperators Moebius Topology

def OMA.squarefree_up_to (N : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter Squarefree

theorem OMA.squarefree_pair_equal {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (h : IsSquare (a * b)) : a = b := by
  obtain ⟨c, hc⟩ := h
  have hc₀ : c ≠ 0 := by
    intro hz
    simp [hz, ha.ne_zero, hb.ne_zero] at hc
  apply Nat.eq_of_factorization_eq ha.ne_zero hb.ne_zero
  intro p
  have hfac := congrArg (fun m : ℕ => m.factorization p) hc
  simp only [Nat.factorization_mul ha.ne_zero hb.ne_zero, Nat.factorization_mul hc₀ hc₀,
    Finsupp.add_apply] at hfac
  have ha' := ha.natFactorization_le_one p
  have hb' := hb.natFactorization_le_one p
  omega

theorem OMA.squarefree_extremal_eq (N : ℕ) :
    Erdos121.F 2 N = (OMA.squarefree_up_to N).card := by
  classical
  have hinterval : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  let B := OMA.squarefree_up_to N
  have hsub : B ⊆ Finset.Icc 1 N := by
    rw [hinterval]
    exact Finset.filter_subset _ _
  have hB (S : Finset ℕ) (hSB : S ⊆ B) (hcard : S.card = 2) :
      ¬IsSquare (∏ n ∈ S, n) := by
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    have ha := (Finset.mem_filter.mp (hSB (by simp : a ∈ ({a, b} : Finset ℕ)))).2
    have hb := (Finset.mem_filter.mp (hSB (by simp : b ∈ ({a, b} : Finset ℕ)))).2
    rw [Finset.prod_pair hab]
    exact fun hs => hab (OMA.squarefree_pair_equal ha hb hs)
  let T : Set ℕ := {m | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ S ⊆ A, S.card = 2 → ¬ IsSquare (∏ a ∈ S, a)) ∧ A.card = m}
  change sSup T = B.card
  have hBT : B.card ∈ T := ⟨B, hsub, hB, rfl⟩
  refine le_antisymm (csSup_le ⟨_, hBT⟩ ?_) (le_csSup ?_ hBT)
  · rintro m ⟨A, hA, hAsq, rfl⟩
    have hdecomp (a : A) : ∃ q r : ℕ, 0 < q ∧ 0 < r ∧ r ^ 2 * q = a.val ∧ Squarefree q :=
      Nat.sq_mul_squarefree_of_pos ((Finset.mem_Icc.mp (hA a.prop)).1.trans_lt' Nat.zero_lt_one)
    choose q r hq hr hprod hsf using hdecomp
    let f (a : A) : B := ⟨q a, by
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hq a, ?_⟩, hsf a⟩
      have hdiv : q a ∣ a.val := ⟨r a ^ 2, by rw [← hprod a, mul_comm]⟩
      have ha := Finset.mem_Icc.mp (hA a.prop)
      exact (Nat.le_of_dvd (by omega) hdiv).trans ha.2⟩
    have hf : Function.Injective f := by
      intro a b hf
      by_contra hab
      have hn : a.val ≠ b.val := fun he => hab (Subtype.ext he)
      have hqeq : q a = q b := congrArg Subtype.val hf
      let P : Finset ℕ := {a.val, b.val}
      have hP : P ⊆ A := Finset.insert_subset a.prop (Finset.singleton_subset_iff.mpr b.prop)
      have hPc : P.card = 2 := Finset.card_pair hn
      apply hAsq P hP hPc
      change IsSquare (∏ n ∈ ({a.val, b.val} : Finset ℕ), n)
      rw [Finset.prod_pair hn]
      refine ⟨r a * r b * q a, ?_⟩
      rw [← hprod a, ← hprod b, ← hqeq]
      ring
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  · refine ⟨(Finset.Icc 1 N).card, ?_⟩
    rintro m ⟨A, hA, -, rfl⟩
    exact Finset.card_le_card hA

theorem OMA.squarefree_moebius_indicator (n N : ℕ) (hn : 0 < n) (hN : n ≤ N) :
    (if Squarefree n then (1 : ℝ) else 0) =
      ∑ d ∈ Finset.Ioc 0 N, if d ^ 2 ∣ n then (μ d : ℝ) else 0 := by
  classical
  let r := Nat.floorRoot 2 n
  have hr : 0 < r := Nat.pos_of_ne_zero (Nat.floorRoot_ne_zero.mpr ⟨by decide, hn.ne'⟩)
  have hrdvd : r ^ 2 ∣ n := Nat.floorRoot_pow_dvd
  have hrle : r ≤ n := (le_self_pow (n := 2) (by omega : 1 ≤ r) (by decide)).trans
    (Nat.le_of_dvd hn hrdvd)
  have hfree : Squarefree n ↔ r = 1 := by
    constructor
    · intro h
      exact Nat.isUnit_iff.mp (h r (by simpa only [pow_two] using hrdvd))
    · intro he d hd
      have hd' : d ∣ r := Nat.pow_dvd_iff_dvd_floorRoot.mp (by simpa only [pow_two] using hd)
      rw [he] at hd'
      exact Nat.isUnit_iff.mpr (Nat.dvd_one.mp hd')
  have hfilter : (Finset.Ioc 0 N).filter (fun d => d ^ 2 ∣ n) = r.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors, Nat.pow_dvd_iff_dvd_floorRoot]
    change (0 < d ∧ d ≤ N) ∧ d ∣ r ↔ d ∣ r ∧ r ≠ 0
    constructor
    · exact fun hd => ⟨hd.2, hr.ne'⟩
    · intro hd
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd.1 hr, (Nat.le_of_dvd hr hd.1).trans (hrle.trans hN)⟩, hd.1⟩
  have hif : (if Squarefree n then (1 : ℝ) else 0) = (if r = 1 then 1 else 0) := by
    by_cases he : r = 1
    · simp [he, hfree.mpr he]
    · have hf : ¬Squarefree n := fun hs => he (hfree.mp hs)
      simp [he, hf]
  rw [hif, ← Finset.sum_filter, hfilter]
  have hm := congrArg (fun f : ArithmeticFunction ℤ => f r) moebius_mul_coe_zeta
  change (μ * ArithmeticFunction.zeta : ArithmeticFunction ℤ) r = (1 : ArithmeticFunction ℤ) r at hm
  rw [coe_mul_zeta_apply, one_apply] at hm
  exact_mod_cast hm.symm

theorem OMA.squarefree_count_formula (N : ℕ) :
    ((OMA.squarefree_up_to N).card : ℝ) =
      ∑ d ∈ Finset.Ioc 0 N, (μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) := by
  classical
  unfold OMA.squarefree_up_to
  have hcard : (((Finset.Ioc 0 N).filter Squarefree).card : ℝ) =
      ∑ _n ∈ (Finset.Ioc 0 N).filter Squarefree, (1 : ℝ) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hcard, Finset.sum_filter]
  calc
    _ = ∑ n ∈ Finset.Ioc 0 N, ∑ d ∈ Finset.Ioc 0 N, if d ^ 2 ∣ n then (μ d : ℝ) else 0 := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      obtain ⟨hp, hN⟩ := Finset.mem_Ioc.mp hn
      exact OMA.squarefree_moebius_indicator n N hp hN
    _ = ∑ d ∈ Finset.Ioc 0 N, ∑ n ∈ Finset.Ioc 0 N, if d ^ 2 ∣ n then (μ d : ℝ) else 0 :=
      Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div, mul_comm]

theorem OMA.floor_multiple_ratio_bounds (N q : ℕ) (hN : 0 < N) (hq : 0 < q) :
    1 / (q : ℝ) - 1 / (N : ℝ) ≤ ((N / q : ℕ) : ℝ) / (N : ℝ) ∧
      ((N / q : ℕ) : ℝ) / (N : ℝ) ≤ 1 / (q : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hfloor : N < (N / q + 1) * q := by
    apply (Nat.div_lt_iff_lt_mul hq).mp
    omega
  have hfloorR : (N : ℝ) < (((N / q : ℕ) : ℝ) + 1) * (q : ℝ) := by exact_mod_cast hfloor
  have hlt := (div_lt_iff₀ hqR).mpr hfloorR
  constructor
  · apply (le_div_iff₀ hNR).mpr
    have hid : (1 / (q : ℝ) - 1 / (N : ℝ)) * (N : ℝ) = (N : ℝ) / (q : ℝ) - 1 := by
      field_simp
    rw [hid]
    linarith
  · apply (div_le_iff₀ hNR).mpr
    simpa only [div_mul_eq_mul_div, one_mul] using
      (Nat.cast_div_le (m := N) (n := q) : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / (q : ℝ))

theorem OMA.floor_multiple_ratio_tendsto (q : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => ((N / q : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 (1 / (q : ℝ))) := by
  have hlow : Tendsto (fun N : ℕ => 1 / (q : ℝ) - 1 / (N : ℝ)) atTop (𝓝 (1 / (q : ℝ))) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := 1 / (q : ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact (OMA.floor_multiple_ratio_bounds N q hN hq).1
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact (OMA.floor_multiple_ratio_bounds N q hN hq).2

theorem OMA.moebius_inverse_square_sum : (∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2) = 6 / Real.pi ^ 2 := by
  have hL : LSeries (fun d : ℕ => (μ d : ℂ)) (2 : ℂ) =
      Complex.ofReal (∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2) := by
    rw [Complex.ofReal_tsum, LSeries]
    apply tsum_congr
    intro d
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · rw [LSeries.term_of_ne_zero hd]
      rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
      push_cast
      rfl
  have hs : 1 < (2 : ℂ).re := by norm_num
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, riemannZeta_two] at h
  change (Real.pi : ℂ) ^ 2 / 6 * LSeries (fun d : ℕ => (μ d : ℂ)) (2 : ℂ) = 1 at h
  rw [hL] at h
  have hr : Real.pi ^ 2 / 6 * (∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2) = 1 := by
    exact_mod_cast h
  apply (eq_div_iff (pow_ne_zero _ Real.pi_ne_zero)).mpr
  nlinarith only [hr]

theorem OMA.squarefree_density :
    Tendsto (fun N : ℕ => ((OMA.squarefree_up_to N).card : ℝ) / (N : ℝ))
      atTop (𝓝 (6 / Real.pi ^ 2)) := by
  classical
  let f (N d : ℕ) : ℝ := (μ d : ℝ) * (((N / d ^ 2 : ℕ) : ℝ) / (N : ℝ))
  let g (d : ℕ) : ℝ := (μ d : ℝ) / (d : ℝ) ^ 2
  have hpoint (d : ℕ) : Tendsto (fun N => f N d) atTop (𝓝 (g d)) := by
    rcases eq_or_ne d 0 with rfl | hd
    · simp [f, g]
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
      have hq := OMA.floor_multiple_ratio_tendsto (d ^ 2) (by positivity)
      simpa only [f, g, Nat.cast_pow, mul_one_div] using hq.const_mul (μ d : ℝ)
  have hseries : Summable (fun d : ℕ => 1 / (d : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ d, ‖f N d‖ ≤ 1 / (d : ℝ) ^ (2 : ℕ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    intro d
    rcases eq_or_ne d 0 with rfl | hd
    · simp [f]
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
      have hupper := (OMA.floor_multiple_ratio_bounds N (d ^ 2) hN (by positivity)).2
      rw [Nat.cast_pow] at hupper
      have hμZ : |μ d| ≤ 1 := by
        rw [abs_moebius]
        split_ifs <;> norm_num
      have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast hμZ
      have hnonneg : 0 ≤ ((N / d ^ 2 : ℕ) : ℝ) / (N : ℝ) := by positivity
      change ‖(μ d : ℝ) * (((N / d ^ 2 : ℕ) : ℝ) / (N : ℝ))‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnonneg]
      exact (mul_le_mul_of_nonneg_right hμ hnonneg).trans (by simpa only [one_mul] using hupper)
  have hlim := tendsto_tsum_of_dominated_convergence (f := f) (g := g) hseries hpoint hdom
  have hcount (N : ℕ) : ((OMA.squarefree_up_to N).card : ℝ) / (N : ℝ) = ∑' d, f N d := by
    have hs (d : ℕ) (hd : d ∉ Finset.Ioc 0 N) : f N d = 0 := by
      rcases eq_or_ne d 0 with rfl | hd₀
      · simp [f]
      · have hNd : N < d := by
          have hdpos := Nat.pos_of_ne_zero hd₀
          simp only [Finset.mem_Ioc, hdpos, true_and, not_le] at hd
          exact hd
        have hsquare : d ≤ d ^ 2 := le_self_pow (by omega) (by decide)
        simp [f, Nat.div_eq_of_lt (hNd.trans_le hsquare)]
    rw [tsum_eq_sum hs, OMA.squarefree_count_formula, Finset.sum_div]
    simp only [f, mul_div_assoc]
  simp_rw [← hcount] at hlim
  change Tendsto _ atTop (𝓝 (∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2)) at hlim
  rwa [OMA.moebius_inverse_square_sum] at hlim

theorem OMA.solution : type_of% @Erdos121.erdos_121.variants.two := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  let c : ℝ := 6 / Real.pi ^ 2
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hlim := OMA.squarefree_density.div_const c
  convert hlim using 1
  · funext N
    simp only [Pi.div_apply, OMA.squarefree_extremal_eq]
    rw [div_div, mul_comm]
  · change 𝓝 (1 : ℝ) = 𝓝 (c / c)
    rw [div_self hc]