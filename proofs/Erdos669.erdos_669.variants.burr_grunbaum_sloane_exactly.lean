import FormalConjectures.ErdosProblems.«669»
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

-- Problem: Erdős Problem 669 — burr grunbaum sloane exactly
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/669.lean:205 (declaration Erdos669.erdos_669.variants.burr_grunbaum_sloane_exactly)
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Formalization of the Burr-Grünbaum-Sloane asymptotic $f_3(n) = n^2/6 - O(n)$
for the Orchard problem using the trigonometric cubic parameterization
$t \mapsto (t / (t^2 + 1), t^3 / (t^2 + 1))$ at $t_k = \tan(\pi k / m)$ for odd $m$. -/

namespace OrchardProof

open Filter Erdos669
open scoped EuclideanGeometry

lemma ncard_lines_three_le (S : Finset ℝ²) :
    3 * (linesWithAtLeastPointsFor 3 (S : Set ℝ²)).ncard ≤ S.card.choose 2 := by
  classical
  have hfin : (linesWithAtLeastPointsFor 3 (S : Set ℝ²)).Finite := by
    refine ((S.finite_toSet.prod S.finite_toSet).image
      (fun pq : ℝ² × ℝ² => affineSpan ℝ {pq.1, pq.2})).subset ?_
    rintro L ⟨⟨p, hp, q, hq, -, rfl⟩, -⟩
    exact ⟨(p, q), Set.mk_mem_prod hp hq, rfl⟩
  let TF : Finset (AffineSubspace ℝ ℝ²) := hfin.toFinset
  have hTF_card : TF.card = (linesWithAtLeastPointsFor 3 (S : Set ℝ²)).ncard := by
    rw [← Set.ncard_coe_finset TF, Set.Finite.coe_toFinset]
  let pts : AffineSubspace ℝ ℝ² → Finset ℝ² := fun L => S.filter (fun p => p ∈ (L : Set ℝ²))
  have hpts_card : ∀ L ∈ TF, 3 ≤ ((pts L).powersetCard 2).card := by
    intro L hL
    have hLT : L ∈ linesWithAtLeastPointsFor 3 (S : Set ℝ²) := hfin.mem_toFinset.mp hL
    have hnc : 3 ≤ ((L : Set ℝ²) ∩ (S : Set ℝ²)).ncard := hLT.2
    have heq : (L : Set ℝ²) ∩ (S : Set ℝ²) = ((pts L : Finset ℝ²) : Set ℝ²) := by
      ext p
      simp [pts, and_comm]
    rw [heq, Set.ncard_coe_finset] at hnc
    rw [Finset.card_powersetCard]
    have hch : Nat.choose 3 2 ≤ Nat.choose (pts L).card 2 := Nat.choose_le_choose 2 hnc
    exact le_trans (by decide) hch
  have hdisj : (TF : Set (AffineSubspace ℝ ℝ²)).PairwiseDisjoint
      (fun L => (pts L).powersetCard 2) := by
    intro L₁ hL₁ L₂ hL₂ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    rw [Finset.mem_powersetCard] at he₁ he₂
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he₁.2
    have ha₁ : a ∈ (L₁ : Set ℝ²) := (Finset.mem_filter.mp (he₁.1 (by simp))).2
    have hb₁ : b ∈ (L₁ : Set ℝ²) := (Finset.mem_filter.mp (he₁.1 (by simp))).2
    have ha₂ : a ∈ (L₂ : Set ℝ²) := (Finset.mem_filter.mp (he₂.1 (by simp))).2
    have hb₂ : b ∈ (L₂ : Set ℝ²) := (Finset.mem_filter.mp (he₂.1 (by simp))).2
    have h1T : L₁ ∈ linesWithAtLeastPointsFor 3 (S : Set ℝ²) := hfin.mem_toFinset.mp hL₁
    have h2T : L₂ ∈ linesWithAtLeastPointsFor 3 (S : Set ℝ²) := hfin.mem_toFinset.mp hL₂
    rcases h1T.1 with ⟨p₁, -, q₁, -, hpq₁, rfl⟩
    rcases h2T.1 with ⟨p₂, -, q₂, -, hpq₂, rfl⟩
    have hspan₁ := affineSpan_pair_eq_of_mem_of_mem_of_ne ha₁ hb₁ hab
    have hspan₂ := affineSpan_pair_eq_of_mem_of_mem_of_ne ha₂ hb₂ hab
    exact hne (hspan₁.symm.trans hspan₂)
  have hsub : TF.biUnion (fun L => (pts L).powersetCard 2) ⊆ S.powersetCard 2 := by
    intro e he
    rw [Finset.mem_biUnion] at he
    rcases he with ⟨L, _, heL⟩
    rw [Finset.mem_powersetCard] at heL ⊢
    exact ⟨heL.1.trans (Finset.filter_subset _ _), heL.2⟩
  calc 3 * (linesWithAtLeastPointsFor 3 (S : Set ℝ²)).ncard
      = 3 * TF.card := by rw [hTF_card]
    _ = ∑ _L ∈ TF, 3 := by simp [mul_comm]
    _ ≤ ∑ L ∈ TF, ((pts L).powersetCard 2).card := Finset.sum_le_sum hpts_card
    _ = (TF.biUnion (fun L => (pts L).powersetCard 2)).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (S.powersetCard 2).card := Finset.card_le_card hsub
    _ = S.card.choose 2 := Finset.card_powersetCard 2 S

lemma three_mul_maxLinesAtLeast_le (n : ℕ) :
    3 * maxLinesAtLeast 3 n ≤ n.choose 2 := by
  have hsup : maxLinesAtLeast 3 n ≤ n.choose 2 / 3 := by
    refine csSup_le' ?_
    rintro m ⟨S, rfl, rfl⟩
    exact Nat.le_div_iff_mul_le (by decide : 0 < 3) |>.mpr
      (by simpa [Nat.mul_comm] using ncard_lines_three_le S)
  have hmul := Nat.mul_le_mul_left 3 hsup
  exact hmul.trans (Nat.mul_div_le (n.choose 2) 3)

noncomputable def theta (m : ℕ) (i : Fin m) : ℝ := Real.pi * (i.val : ℝ) / (m : ℝ)

noncomputable def tval (m : ℕ) (i : Fin m) : ℝ := Real.tan (theta m i)

noncomputable def curvePt (t : ℝ) : ℝ² := !₂[t / (t ^ 2 + 1), t ^ 3 / (t ^ 2 + 1)]

noncomputable def pt (m : ℕ) (i : Fin m) : ℝ² := curvePt (tval m i)

lemma cos_theta_ne_zero {m : ℕ} (hm : Odd m) (i : Fin m) : Real.cos (theta m i) ≠ 0 := by
  intro hcos
  rw [Real.cos_eq_zero_iff] at hcos
  rcases hcos with ⟨k, hk⟩
  have hm0 : (m : ℝ) ≠ 0 := by
    have : 0 < m := i.pos
    exact_mod_cast this.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have heq : (2 * (i.val : ℝ)) = (2 * (k : ℝ) + 1) * (m : ℝ) := by
    dsimp [theta] at hk
    field_simp [hm0] at hk
    linarith
  have heq_int : (2 * (i.val : ℤ)) = (2 * k + 1) * (m : ℤ) := by
    exact_mod_cast heq
  rcases hm with ⟨r, rfl⟩
  have hL : (2 * (i.val : ℤ)) % 2 = 0 := by omega
  have hR : ((2 * k + 1) * ((2 * r + 1 : ℕ) : ℤ)) % 2 = 1 := by
    rw [Int.mul_emod]
    push_cast
    norm_num [Int.add_emod, Int.mul_emod]
  rw [heq_int] at hL
  omega

lemma tval_injective {m : ℕ} (hm : Odd m) : Function.Injective (tval m) := by
  intro i j hij
  have hci : Real.cos (theta m i) ≠ 0 := cos_theta_ne_zero hm i
  have hcj : Real.cos (theta m j) ≠ 0 := cos_theta_ne_zero hm j
  dsimp [tval] at hij
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos] at hij
  have hsin : Real.sin (theta m i - theta m j) = 0 := by
    rw [Real.sin_sub]
    have hcross : Real.sin (theta m i) * Real.cos (theta m j) =
        Real.sin (theta m j) * Real.cos (theta m i) := (div_eq_div_iff hci hcj).mp hij
    linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast i.pos
  have heq_t : theta m i - theta m j = Real.pi * (((i.val : ℝ) - j.val) / m) := by
    dsimp [theta]
    ring
  have hdiff1 : (-1 : ℝ) < ((i.val : ℝ) - j.val) / m := by
    rw [lt_div_iff₀ hm_pos]
    have hj_lt : (j.val : ℝ) < (m : ℝ) := by exact_mod_cast j.isLt
    have hi0 : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
    linarith
  have hdiff2 : ((i.val : ℝ) - j.val) / m < 1 := by
    rw [div_lt_iff₀ hm_pos]
    have hi_lt : (i.val : ℝ) < (m : ℝ) := by exact_mod_cast i.isLt
    have hj0 : (0 : ℝ) ≤ (j.val : ℝ) := Nat.cast_nonneg _
    linarith
  have hlt1 : -Real.pi < theta m i - theta m j := by
    rw [heq_t]
    nlinarith [Real.pi_pos]
  have hlt2 : theta m i - theta m j < Real.pi := by
    rw [heq_t]
    nlinarith [Real.pi_pos]
  have hzero : theta m i - theta m j = 0 :=
    (Real.sin_eq_zero_iff_of_lt_of_lt hlt1 hlt2).mp hsin
  rw [heq_t] at hzero
  have hij_r : (i.val : ℝ) = (j.val : ℝ) := by
    have hdiv : ((i.val : ℝ) - j.val) / m = 0 := (mul_eq_zero.mp hzero).resolve_left Real.pi_ne_zero
    have hsub : (i.val : ℝ) - j.val = 0 := (div_eq_zero_iff.mp hdiv).resolve_right hm_pos.ne'
    linarith
  exact Fin.ext (by exact_mod_cast hij_r)

lemma curvePt_injective : Function.Injective curvePt := by
  intro t₁ t₂ h
  have h0 : t₁ / (t₁ ^ 2 + 1) = t₂ / (t₂ ^ 2 + 1) := congrArg (fun p : ℝ² => p 0) h
  have h1 : t₁ ^ 3 / (t₁ ^ 2 + 1) = t₂ ^ 3 / (t₂ ^ 2 + 1) := congrArg (fun p : ℝ² => p 1) h
  have hd1 : t₁ ^ 2 + 1 ≠ 0 := by positivity
  have hd2 : t₂ ^ 2 + 1 ≠ 0 := by positivity
  have h0' : t₁ * (t₂ ^ 2 + 1) = t₂ * (t₁ ^ 2 + 1) := (div_eq_div_iff hd1 hd2).mp h0
  have h1' : t₁ ^ 3 * (t₂ ^ 2 + 1) = t₂ ^ 3 * (t₁ ^ 2 + 1) := (div_eq_div_iff hd1 hd2).mp h1
  by_cases ht1 : t₁ = 0
  · subst ht1
    simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
      mul_one] at h0'
    exact h0'
  · have hsq : t₁ ^ 2 = t₂ ^ 2 := by
      have hmul : t₁ ^ 2 * (t₁ * (t₂ ^ 2 + 1)) = t₁ ^ 2 * (t₂ * (t₁ ^ 2 + 1)) := congrArg (t₁ ^ 2 * ·) h0'
      have hsub : t₁ ^ 2 * (t₂ * (t₁ ^ 2 + 1)) = t₂ ^ 3 * (t₁ ^ 2 + 1) := by linarith
      have hfac : (t₁ ^ 2 - t₂ ^ 2) * t₂ * (t₁ ^ 2 + 1) = 0 := by linarith
      rcases mul_eq_zero.mp hfac with hfac' | hpos
      · rcases mul_eq_zero.mp hfac' with hdiff | ht2
        · linarith
        · subst ht2
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
            mul_one, zero_mul] at h0'
          exact absurd h0' ht1
      · linarith [sq_nonneg t₁]
    rw [hsq] at h0'
    exact mul_right_cancel₀ hd2 h0'

lemma pt_injective {m : ℕ} (hm : Odd m) : Function.Injective (pt m) :=
  curvePt_injective.comp (tval_injective hm)

lemma collinear_iff_det_zero {a b c : ℝ²} (hab : a ≠ b) :
    Collinear ℝ ({a, b, c} : Set ℝ²) ↔
      (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0 := by
  constructor
  · intro hcol
    have hc : c ∈ line[ℝ, a, b] :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hab
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hc
    have h0 := congrArg (fun p : ℝ² => p 0) ht
    have h1 := congrArg (fun p : ℝ² => p 1) ht
    simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1
    have h0' : c 0 - a 0 = t * (b 0 - a 0) := by linarith
    have h1' : c 1 - a 1 = t * (b 1 - a 1) := by linarith
    rw [h0', h1']
    ring
  · intro hdet
    have hdiff : b 0 - a 0 ≠ 0 ∨ b 1 - a 1 ≠ 0 := by
      by_contra hc
      simp only [not_or, not_not, sub_eq_zero] at hc
      apply hab
      ext i
      fin_cases i <;> [exact hc.1.symm; exact hc.2.symm]
    have hmem : c ∈ line[ℝ, a, b] := by
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
      have heq_coords : ∀ t : ℝ, (AffineMap.lineMap a b t) 0 = c 0 →
          (AffineMap.lineMap a b t) 1 = c 1 → AffineMap.lineMap a b t = c := by
        intro t h0 h1
        ext i
        fin_cases i
        · exact h0
        · exact h1
      rcases hdiff with hdx | hdy
      · refine ⟨(c 0 - a 0) / (b 0 - a 0), heq_coords _ ?_ ?_⟩
        · simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          field_simp
          ring
        · simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          field_simp
          linarith
      · refine ⟨(c 1 - a 1) / (b 1 - a 1), heq_coords _ ?_ ?_⟩
        · simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          field_simp
          linarith
        · simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          field_simp
          ring
    refine ((collinear_insert_iff_of_mem_affineSpan hmem).2 (collinear_pair ℝ a b)).subset ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    tauto

lemma collinear_curvePt_iff {t₁ t₂ t₃ : ℝ} (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃) :
    Collinear ℝ ({curvePt t₁, curvePt t₂, curvePt t₃} : Set ℝ²) ↔
      t₁ + t₂ + t₃ = t₁ * t₂ * t₃ := by
  have hab : curvePt t₁ ≠ curvePt t₂ := fun h => h12 (curvePt_injective h)
  rw [collinear_iff_det_zero hab]
  dsimp [curvePt]
  have hd1 : t₁ ^ 2 + 1 ≠ 0 := by positivity
  have hd2 : t₂ ^ 2 + 1 ≠ 0 := by positivity
  have hd3 : t₃ ^ 2 + 1 ≠ 0 := by positivity
  have hdet_simp :
      (t₂ / (t₂ ^ 2 + 1) - t₁ / (t₁ ^ 2 + 1)) * (t₃ ^ 3 / (t₃ ^ 2 + 1) - t₁ ^ 3 / (t₁ ^ 2 + 1)) -
       (t₂ ^ 3 / (t₂ ^ 2 + 1) - t₁ ^ 3 / (t₁ ^ 2 + 1)) * (t₃ / (t₃ ^ 2 + 1) - t₁ / (t₁ ^ 2 + 1)) =
      ((t₂ / (t₂ ^ 2 + 1)) * (t₃ ^ 3 / (t₃ ^ 2 + 1)) - (t₂ ^ 3 / (t₂ ^ 2 + 1)) * (t₃ / (t₃ ^ 2 + 1))) -
      ((t₁ / (t₁ ^ 2 + 1)) * (t₃ ^ 3 / (t₃ ^ 2 + 1)) - (t₁ ^ 3 / (t₁ ^ 2 + 1)) * (t₃ / (t₃ ^ 2 + 1))) +
      ((t₁ / (t₁ ^ 2 + 1)) * (t₂ ^ 3 / (t₂ ^ 2 + 1)) - (t₁ ^ 3 / (t₁ ^ 2 + 1)) * (t₂ / (t₂ ^ 2 + 1))) := by
    ring
  have hmul : ((t₁ ^ 2 + 1) * (t₂ ^ 2 + 1) * (t₃ ^ 2 + 1)) *
      ((t₂ / (t₂ ^ 2 + 1) - t₁ / (t₁ ^ 2 + 1)) * (t₃ ^ 3 / (t₃ ^ 2 + 1) - t₁ ^ 3 / (t₁ ^ 2 + 1)) -
       (t₂ ^ 3 / (t₂ ^ 2 + 1) - t₁ ^ 3 / (t₁ ^ 2 + 1)) * (t₃ / (t₃ ^ 2 + 1) - t₁ / (t₁ ^ 2 + 1))) =
      (t₂ - t₁) * (t₃ - t₁) * (t₃ - t₂) * ((t₁ + t₂ + t₃) - t₁ * t₂ * t₃) := by
    rw [hdet_simp]
    field_simp
    ring
  have hpos : (t₁ ^ 2 + 1) * (t₂ ^ 2 + 1) * (t₃ ^ 2 + 1) ≠ 0 := by positivity
  constructor
  · intro h
    rw [h, mul_zero] at hmul
    have h21 : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr h12.symm
    have h31 : t₃ - t₁ ≠ 0 := sub_ne_zero.mpr h13.symm
    have h32 : t₃ - t₂ ≠ 0 := sub_ne_zero.mpr h23.symm
    have hsum : (t₁ + t₂ + t₃) - t₁ * t₂ * t₃ = 0 := by
      rcases mul_eq_zero.mp hmul.symm with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · rcases mul_eq_zero.mp h'' with h''' | h'''
          · exact absurd h''' h21
          · exact absurd h''' h31
        · exact absurd h'' h32
      · exact h'
    linarith
  · intro h
    have hzero : (t₂ - t₁) * (t₃ - t₁) * (t₃ - t₂) * ((t₁ + t₂ + t₃) - t₁ * t₂ * t₃) = 0 := by
      rw [h, sub_self, mul_zero]
    rw [hzero] at hmul
    exact (mul_eq_zero.mp hmul).resolve_left hpos

lemma tan_triple_eq_iff {α β γ : ℝ} (ha : Real.cos α ≠ 0) (hb : Real.cos β ≠ 0)
    (hc : Real.cos γ ≠ 0) :
    Real.tan α + Real.tan β + Real.tan γ = Real.tan α * Real.tan β * Real.tan γ ↔
      Real.sin (α + β + γ) = 0 := by
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
  have hsin : Real.sin (α + β + γ) =
      Real.sin α * Real.cos β * Real.cos γ + Real.cos α * Real.sin β * Real.cos γ +
      Real.cos α * Real.cos β * Real.sin γ - Real.sin α * Real.sin β * Real.sin γ := by
    rw [Real.sin_add, Real.sin_add, Real.cos_add]
    ring
  rw [hsin]
  have hden : Real.cos α * Real.cos β * Real.cos γ ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) hc
  constructor
  · intro h
    have hmul := congrArg (· * (Real.cos α * Real.cos β * Real.cos γ)) h
    field_simp at hmul
    linarith
  · intro h
    field_simp
    linarith

lemma sin_theta_sum_eq_zero_iff {m : ℕ} (i j l : Fin m) :
    Real.sin (theta m i + theta m j + theta m l) = 0 ↔ (i.val + j.val + l.val) % m = 0 := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast i.pos
  rw [Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    dsimp [theta] at hk
    have hk' : (k : ℝ) * (m : ℝ) = (i.val + j.val + l.val : ℕ) := by
      field_simp [hm_pos.ne'] at hk
      push_cast
      exact hk
    have hk_int : k * (m : ℤ) = ((i.val + j.val + l.val : ℕ) : ℤ) := by
      exact_mod_cast hk'
    have hdvd : (m : ℤ) ∣ ((i.val + j.val + l.val : ℕ) : ℤ) := ⟨k, by linarith⟩
    exact Nat.mod_eq_zero_of_dvd (Int.ofNat_dvd.mp hdvd)
  · intro hmod
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hmod
    refine ⟨(q : ℤ), ?_⟩
    dsimp [theta]
    have hqr : ((i.val : ℝ) + j.val + l.val) = (m : ℝ) * (q : ℝ) := by
      exact_mod_cast hq
    field_simp [hm_pos.ne']
    rw [hqr]
    push_cast
    ring

lemma collinear_pt_iff {m : ℕ} (hm : Odd m) {i j l : Fin m} (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) :
    Collinear ℝ ({pt m i, pt m j, pt m l} : Set ℝ²) ↔ (i.val + j.val + l.val) % m = 0 := by
  have htij : tval m i ≠ tval m j := fun h => hij (tval_injective hm h)
  have htil : tval m i ≠ tval m l := fun h => hil (tval_injective hm h)
  have htjl : tval m j ≠ tval m l := fun h => hjl (tval_injective hm h)
  dsimp [pt]
  rw [collinear_curvePt_iff htij htil htjl]
  dsimp [tval]
  rw [tan_triple_eq_iff (cos_theta_ne_zero hm i) (cos_theta_ne_zero hm j) (cos_theta_ne_zero hm l)]
  exact sin_theta_sum_eq_zero_iff i j l

lemma mod_eq_sub_mod {u v m : ℕ} (hm : 0 < m) (hv : v < m) (h : (u + v) % m = 0) :
    v = (m - u % m) % m := by
  have hu : u % m < m := Nat.mod_lt u hm
  have h1 : (u % m + v) % m = 0 := by rw [Nat.mod_add_mod]; exact h
  rcases Nat.eq_zero_or_pos (u % m) with hu0 | hu_pos
  · rw [hu0] at h1 ⊢
    simp only [zero_add, Nat.mod_eq_of_lt hv, tsub_zero, Nat.mod_self] at h1 ⊢
    exact h1
  · have hsum : u % m + v = m := by
      have hdiv := Nat.div_add_mod (u % m + v) m
      rw [h1, add_zero] at hdiv
      have hlt : u % m + v < 2 * m := by omega
      have hpos : 0 < u % m + v := by omega
      have hq : (u % m + v) / m = 1 := by
        rcases Nat.lt_trichotomy ((u % m + v) / m) 1 with hq0 | hq1 | hq2
        · have h0 : (u % m + v) / m = 0 := Nat.lt_one_iff.mp hq0
          rw [h0, mul_zero] at hdiv
          omega
        · exact hq1
        · have h2 : 2 ≤ (u % m + v) / m := hq2
          have hge : 2 * m ≤ m * ((u % m + v) / m) := (Nat.mul_le_mul_right m h2).trans_eq (Nat.mul_comm _ _)
          omega
      rw [hq, mul_one] at hdiv
      exact hdiv.symm
    have hlt2 : m - u % m < m := by omega
    rw [Nat.mod_eq_of_lt hlt2]
    omega

lemma mod_add_cancel {a b x c m : ℕ} (hm : 0 < m) (hx : x < m) (hc : c < m)
    (h1 : (a + b + x) % m = 0) (h2 : (a + b + c) % m = 0) : x = c := by
  rw [mod_eq_sub_mod hm hx h1, mod_eq_sub_mod hm hc h2]

def triples (m : ℕ) : Finset (Finset (Fin m)) :=
  ((Finset.univ : Finset (Fin m)).powersetCard 3).filter (fun s => (∑ i ∈ s, i.val) % m = 0)

lemma triples_card_lower {m : ℕ} (_hm : Odd m) (_hm3 : 3 ≤ m) :
    m.choose 2 ≤ 3 * (triples m).card + 2 * m := by
  classical
  let Triples := triples m
  let Pairs := ((Finset.univ : Finset (Fin m)).powersetCard 2).filter
    (fun p => ∃ c : Fin m, c ∉ p ∧ (c.val + ∑ i ∈ p, i.val) % m = 0)
  let Bad1 := (Finset.univ : Finset (Fin m)).image (fun a : Fin m =>
    let b : Fin m := ⟨(m - (2 * a.val) % m) % m, Nat.mod_lt _ a.pos⟩
    ({a, b} : Finset (Fin m)))
  let Bad2 := (Finset.univ : Finset (Fin m)).image (fun b : Fin m =>
    let a : Fin m := ⟨(m - (2 * b.val) % m) % m, Nat.mod_lt _ b.pos⟩
    ({a, b} : Finset (Fin m)))
  have hcover : (Finset.univ : Finset (Fin m)).powersetCard 2 ⊆ Pairs ∪ (Bad1 ∪ Bad2) := by
    intro p hp
    rw [Finset.mem_powersetCard] at hp
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hp.2
    let c : Fin m := ⟨(m - (a.val + b.val) % m) % m, Nat.mod_lt _ a.pos⟩
    have hc_sum : (c.val + a.val + b.val) % m = 0 := by
      dsimp [c]
      rw [add_assoc, Nat.mod_add_mod, ← Nat.add_mod_mod,
        Nat.sub_add_cancel (Nat.mod_lt _ a.pos).le, Nat.mod_self]
    by_cases hca : c = a
    · simp only [Finset.mem_union]; right; left
      rw [Finset.mem_image]
      refine ⟨a, Finset.mem_univ a, ?_⟩
      have hbmod : b.val = (m - (2 * a.val) % m) % m := by
        have h1 : (2 * a.val + b.val) % m = 0 := by
          simpa [hca, two_mul, add_assoc] using hc_sum
        exact mod_eq_sub_mod a.pos b.isLt h1
      have hb_eq : b = ⟨(m - (2 * a.val) % m) % m, Nat.mod_lt _ a.pos⟩ := Fin.ext hbmod
      rw [← hb_eq]
    · by_cases hcb : c = b
      · simp only [Finset.mem_union]; right; right
        rw [Finset.mem_image]
        refine ⟨b, Finset.mem_univ b, ?_⟩
        have hamod : a.val = (m - (2 * b.val) % m) % m := by
          have h1 : (2 * b.val + a.val) % m = 0 := by
            have h' : (b.val + a.val + b.val) % m = 0 := by simpa [hcb] using hc_sum
            simpa [two_mul, add_assoc, add_comm, add_left_comm] using h'
          exact mod_eq_sub_mod b.pos a.isLt h1
        have ha_eq : a = ⟨(m - (2 * b.val) % m) % m, Nat.mod_lt _ b.pos⟩ := Fin.ext hamod
        rw [← ha_eq]
      · simp only [Finset.mem_union]; left
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_powersetCard.mpr hp, c, ?_, ?_⟩
        · simp [hca, hcb]
        · simpa [Finset.sum_pair hab, add_assoc] using hc_sum
  have hPairs_ge : m.choose 2 ≤ Pairs.card + 2 * m := by
    have h1 : ((Finset.univ : Finset (Fin m)).powersetCard 2).card ≤
        (Pairs ∪ (Bad1 ∪ Bad2)).card := Finset.card_le_card hcover
    have h2 : (Pairs ∪ (Bad1 ∪ Bad2)).card ≤ Pairs.card + Bad1.card + Bad2.card := by
      calc (Pairs ∪ (Bad1 ∪ Bad2)).card ≤ Pairs.card + (Bad1 ∪ Bad2).card := Finset.card_union_le _ _
        _ ≤ Pairs.card + (Bad1.card + Bad2.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
        _ = Pairs.card + Bad1.card + Bad2.card := by omega
    have hb1 : Bad1.card ≤ m := (Finset.card_image_le).trans (by simp)
    have hb2 : Bad2.card ≤ m := (Finset.card_image_le).trans (by simp)
    have hpc : ((Finset.univ : Finset (Fin m)).powersetCard 2).card = m.choose 2 := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    omega
  let toTriple : Finset (Fin m) → Finset (Fin m) := fun p =>
    if h : ∃ c : Fin m, c ∉ p ∧ (c.val + ∑ i ∈ p, i.val) % m = 0
    then insert (Classical.choose h) p
    else ∅
  have hmap : ∀ p ∈ Pairs, toTriple p ∈ Triples := by
    intro p hp
    have hfilt := (Finset.mem_filter.mp hp)
    have hp_pc := Finset.mem_powersetCard.mp hfilt.1
    have hEx := hfilt.2
    have hspec := Classical.choose_spec hEx
    dsimp [toTriple, Triples, triples]
    rw [dif_pos hEx, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · rw [Finset.card_insert_of_notMem hspec.1, hp_pc.2]
    · rw [Finset.sum_insert hspec.1]
      exact hspec.2
  have hPairs_le : Pairs.card ≤ 3 * Triples.card := by
    have hsub : Pairs ⊆ Triples.biUnion (fun t => t.powersetCard 2) := by
      intro p hp
      rw [Finset.mem_biUnion]
      refine ⟨toTriple p, hmap p hp, ?_⟩
      rw [Finset.mem_powersetCard]
      have hfilt := Finset.mem_filter.mp hp
      have hp_pc := Finset.mem_powersetCard.mp hfilt.1
      dsimp [toTriple]
      rw [dif_pos hfilt.2]
      exact ⟨Finset.subset_insert _ _, hp_pc.2⟩
    calc Pairs.card ≤ (Triples.biUnion (fun t => t.powersetCard 2)).card := Finset.card_le_card hsub
      _ ≤ ∑ t ∈ Triples, (t.powersetCard 2).card := Finset.card_biUnion_le
      _ = ∑ _t ∈ Triples, 3 := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have ht_pc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp ht).1).2
        rw [Finset.card_powersetCard, ht_pc]
        decide
      _ = 3 * Triples.card := by simp [mul_comm]
  dsimp [Triples] at hPairs_le
  omega

lemma lower_bound_odd_exactly {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    m.choose 2 ≤ 3 * maxLinesExactly 3 m + 2 * m := by
  classical
  let S : Finset ℝ² := Finset.univ.image (pt m)
  have hS_card : S.card = m := by
    rw [Finset.card_image_of_injective _ (pt_injective hm), Finset.card_univ, Fintype.card_fin]
  let Triples := triples m
  let lineOf : Finset (Fin m) → AffineSubspace ℝ ℝ² :=
    fun s => affineSpan ℝ ((s.image (pt m) : Finset ℝ²) : Set ℝ²)
  have hlineOf_mem : ∀ s ∈ Triples, lineOf s ∈ EuclideanGeometry.linesWithPointsFor 3 (S : Set ℝ²) := by
    intro s hs
    have hs_f := Finset.mem_filter.mp hs
    have hs_card := (Finset.mem_powersetCard.mp hs_f.1).2
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs_card
    have hsum : (a.val + b.val + c.val) % m = 0 := by
      have h1 : (∑ i ∈ ({a, b, c} : Finset (Fin m)), i.val) = a.val + b.val + c.val := by
        rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc]; ring
      simpa [h1] using hs_f.2
    have hcol : Collinear ℝ ({pt m a, pt m b, pt m c} : Set ℝ²) :=
      (collinear_pt_iff hm hab hac hbc).mpr hsum
    have hptab : pt m a ≠ pt m b := fun h => hab (pt_injective hm h)
    have hptac : pt m a ≠ pt m c := fun h => hac (pt_injective hm h)
    have hptbc : pt m b ≠ pt m c := fun h => hbc (pt_injective hm h)
    have hspan : lineOf {a, b, c} = affineSpan ℝ {pt m a, pt m b} := by
      dsimp [lineOf]
      have hcoe : (({a, b, c} : Finset (Fin m)).image (pt m) : Set ℝ²) =
          {pt m a, pt m b, pt m c} := by
        ext x; simp
      rw [hcoe]
      exact (hcol.affineSpan_eq_of_ne (by simp) (by simp) hptab).symm
    refine ⟨?_, ?_⟩
    · refine ⟨pt m a, by simp [S], pt m b, by simp [S], hptab, hspan.symm⟩
    · have hinter_eq : ↑(lineOf {a, b, c}) ∩ (S : Set ℝ²) =
          (({pt m a, pt m b, pt m c} : Finset ℝ²) : Set ℝ²) := by
        ext p
        simp only [Set.mem_inter_iff, SetLike.mem_coe, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hpL, hpS⟩
          simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hpS
          rcases hpS with ⟨x, rfl⟩
          by_cases hx_mem : x ∈ ({a, b, c} : Finset (Fin m))
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hx_mem
            rcases hx_mem with rfl | rfl | rfl <;> simp
          · exfalso
            have hxa : x ≠ a := fun h => hx_mem (by simp [h])
            have hxb : x ≠ b := fun h => hx_mem (by simp [h])
            have hxc : x ≠ c := fun h => hx_mem (by simp [h])
            rw [hspan] at hpL
            have hcol_x : Collinear ℝ ({pt m a, pt m b, pt m x} : Set ℝ²) := by
              have h1 : Collinear ℝ ({pt m x, pt m a, pt m b} : Set ℝ²) :=
                (collinear_insert_iff_of_mem_affineSpan hpL).2 (collinear_pair ℝ _ _)
              refine h1.subset ?_
              intro z hz
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
              tauto
            have hsum_x : (a.val + b.val + x.val) % m = 0 :=
              (collinear_pt_iff hm hab hxa.symm hxb.symm).mp hcol_x
            exact hxc (Fin.ext (mod_add_cancel x.pos x.isLt c.isLt hsum_x hsum))
        · intro hp
          refine ⟨?_, ?_⟩
          · dsimp [lineOf]
            refine subset_affineSpan ℝ _ ?_
            simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_insert,
              Finset.mem_singleton]
            rcases hp with rfl | rfl | rfl
            · exact ⟨a, Or.inl rfl, rfl⟩
            · exact ⟨b, Or.inr (Or.inl rfl), rfl⟩
            · exact ⟨c, Or.inr (Or.inr rfl), rfl⟩
          · rcases hp with rfl | rfl | rfl <;> simp [S]
      have hcard3 : ({pt m a, pt m b, pt m c} : Finset ℝ²).card = 3 := by
        simp [hptab, hptac, hptbc]
      rw [hinter_eq, Set.ncard_coe_finset, hcard3]
  have hlineOf_inj : Set.InjOn lineOf (Triples : Set (Finset (Fin m))) := by
    intro s₁ hs₁ s₂ hs₂ heq
    have hs₁' := Finset.mem_filter.mp hs₁
    have hs₂' := Finset.mem_filter.mp hs₂
    have hs₁_card := (Finset.mem_powersetCard.mp hs₁'.1).2
    have hs₂_card := (Finset.mem_powersetCard.mp hs₂'.1).2
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs₁_card
    have hsum1 : (a.val + b.val + c.val) % m = 0 := by
      have h1 : (∑ i ∈ ({a, b, c} : Finset (Fin m)), i.val) = a.val + b.val + c.val := by
        rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc]; ring
      simpa [h1] using hs₁'.2
    have hsub21 : s₂ ⊆ {a, b, c} := by
      intro x hx
      by_contra hx_not
      have hxa : x ≠ a := fun h => hx_not (by simp [h])
      have hxb : x ≠ b := fun h => hx_not (by simp [h])
      have hxc : x ≠ c := fun h => hx_not (by simp [h])
      have hx_mem : pt m x ∈ lineOf s₂ := by
        dsimp [lineOf]
        exact subset_affineSpan ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))
      rw [← heq] at hx_mem
      have hcol1 : Collinear ℝ ({pt m a, pt m b, pt m c} : Set ℝ²) :=
        (collinear_pt_iff hm hab hac hbc).mpr hsum1
      have hptab : pt m a ≠ pt m b := fun h => hab (pt_injective hm h)
      have hspan1 : lineOf {a, b, c} = affineSpan ℝ {pt m a, pt m b} := by
        dsimp [lineOf]
        have hcoe : (({a, b, c} : Finset (Fin m)).image (pt m) : Set ℝ²) =
            {pt m a, pt m b, pt m c} := by ext z; simp
        rw [hcoe]
        exact (hcol1.affineSpan_eq_of_ne (by simp) (by simp) hptab).symm
      rw [hspan1] at hx_mem
      have hcol_x : Collinear ℝ ({pt m a, pt m b, pt m x} : Set ℝ²) := by
        have h1 : Collinear ℝ ({pt m x, pt m a, pt m b} : Set ℝ²) :=
          (collinear_insert_iff_of_mem_affineSpan hx_mem).2 (collinear_pair ℝ _ _)
        refine h1.subset ?_
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
        tauto
      have hsum_x : (a.val + b.val + x.val) % m = 0 :=
        (collinear_pt_iff hm hab hxa.symm hxb.symm).mp hcol_x
      have hx_eq_c : x = c := Fin.ext (mod_add_cancel x.pos x.isLt c.isLt hsum_x hsum1)
      exact hxc hx_eq_c
    have hcard_eq : s₂.card = ({a, b, c} : Finset (Fin m)).card := by
      rw [hs₂_card, Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
    exact (Finset.eq_of_subset_of_card_le hsub21 hcard_eq.ge).symm
  have hncard_le : Triples.card ≤ (EuclideanGeometry.linesWithPointsFor 3 (S : Set ℝ²)).ncard := by
    have hfin : (EuclideanGeometry.linesWithPointsFor 3 (S : Set ℝ²)).Finite := by
      refine ((S.finite_toSet.prod S.finite_toSet).image
        (fun pq : ℝ² × ℝ² => affineSpan ℝ {pq.1, pq.2})).subset ?_
      rintro L ⟨⟨p, hp, q, hq, -, rfl⟩, -⟩
      exact ⟨(p, q), Set.mk_mem_prod hp hq, rfl⟩
    rw [← Set.ncard_coe_finset Triples]
    calc (Triples : Set (Finset (Fin m))).ncard
        = (lineOf '' (Triples : Set (Finset (Fin m)))).ncard :=
          (hlineOf_inj.ncard_image).symm
      _ ≤ (EuclideanGeometry.linesWithPointsFor 3 (S : Set ℝ²)).ncard := by
          refine Set.ncard_le_ncard ?_ hfin
          rintro L ⟨s, hs, rfl⟩
          exact hlineOf_mem s (Finset.mem_coe.mp hs)
  have hmax : (EuclideanGeometry.linesWithPointsFor 3 (S : Set ℝ²)).ncard ≤ maxLinesExactly 3 m :=
    le_csSup (lineCountsExactly_bddAbove 3 m) ⟨S, hS_card, rfl⟩
  have htri := triples_card_lower hm hm3
  dsimp [Triples] at hncard_le
  omega

noncomputable def parabola (t : ℝ) : ℝ² := !₂[t, t ^ 2]

lemma parabola_injective : Function.Injective parabola := by
  intro t₁ t₂ h
  exact congrArg (fun p : ℝ² => p 0) h

lemma parabola_not_collinear {t₁ t₂ t₃ : ℝ} (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃) :
    ¬ Collinear ℝ ({parabola t₁, parabola t₂, parabola t₃} : Set ℝ²) := by
  have hab : parabola t₁ ≠ parabola t₂ := fun h => h12 (parabola_injective h)
  rw [collinear_iff_det_zero hab]
  dsimp [parabola]
  intro hdet
  have hfac : (t₂ - t₁) * (t₃ - t₁) * (t₃ - t₂) = 0 := by
    have : (t₂ - t₁) * (t₃ - t₁) * (t₃ - t₂) =
        (t₂ - t₁) * (t₃ ^ 2 - t₁ ^ 2) - (t₂ ^ 2 - t₁ ^ 2) * (t₃ - t₁) := by ring
    linarith
  rcases mul_eq_zero.mp hfac with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact h12 (sub_eq_zero.mp h'').symm
    · exact h13 (sub_eq_zero.mp h'').symm
  · exact h23 (sub_eq_zero.mp h').symm

lemma maxLinesExactly_le_succ (k m : ℕ) :
    maxLinesExactly k m ≤ maxLinesExactly k (m + 1) := by
  classical
  refine csSup_le' ?_
  rintro c ⟨S, rfl, rfl⟩
  have hfin : (EuclideanGeometry.linesWithPointsFor k (S : Set ℝ²)).Finite := by
    refine ((S.finite_toSet.prod S.finite_toSet).image
      (fun pq : ℝ² × ℝ² => affineSpan ℝ {pq.1, pq.2})).subset ?_
    rintro L ⟨⟨p, hp, q, hq, -, rfl⟩, -⟩
    exact ⟨(p, q), Set.mk_mem_prod hp hq, rfl⟩
  let TF : Finset (AffineSubspace ℝ ℝ²) := hfin.toFinset
  let N := 2 * TF.card + S.card + 1
  let badS : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => parabola (i.val : ℝ) ∈ S)
  let badL : AffineSubspace ℝ ℝ² → Finset (Fin N) :=
    fun L => Finset.univ.filter (fun i : Fin N => parabola (i.val : ℝ) ∈ (L : Set ℝ²))
  have hbadS : badS.card ≤ S.card := by
    refine Finset.card_le_card_of_injOn (fun i => parabola (i.val : ℝ)) ?_ ?_
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i _ j _ hij
      exact Fin.ext (by exact_mod_cast parabola_injective hij)
  have hbadL : ∀ L ∈ TF, (badL L).card ≤ 2 := by
    intro L hL
    by_contra! hgt
    obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hgt)
    obtain ⟨i₁, i₂, i₃, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp ht_card
    have hi₁ : parabola (i₁.val : ℝ) ∈ (L : Set ℝ²) :=
      (Finset.mem_filter.mp (ht_sub (by simp))).2
    have hi₂ : parabola (i₂.val : ℝ) ∈ (L : Set ℝ²) :=
      (Finset.mem_filter.mp (ht_sub (by simp))).2
    have hi₃ : parabola (i₃.val : ℝ) ∈ (L : Set ℝ²) :=
      (Finset.mem_filter.mp (ht_sub (by simp))).2
    have hLT := hfin.mem_toFinset.mp hL
    rcases hLT.1 with ⟨p, -, q, -, hpq, rfl⟩
    have hp12 : parabola (i₁.val : ℝ) ≠ parabola (i₂.val : ℝ) :=
      fun h => h12 (Fin.ext (by exact_mod_cast parabola_injective h))
    have hsp : line[ℝ, parabola (i₁.val : ℝ), parabola (i₂.val : ℝ)] = line[ℝ, p, q] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hi₁ hi₂ hp12
    rw [← hsp] at hi₃
    have hcol : Collinear ℝ ({parabola (i₁.val : ℝ), parabola (i₂.val : ℝ),
        parabola (i₃.val : ℝ)} : Set ℝ²) := by
      refine ((collinear_insert_iff_of_mem_affineSpan hi₃).2 (collinear_pair ℝ _ _)).subset ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
    have hn12 : (i₁.val : ℝ) ≠ (i₂.val : ℝ) := by
      intro h; exact h12 (Fin.ext (by exact_mod_cast h))
    have hn13 : (i₁.val : ℝ) ≠ (i₃.val : ℝ) := by
      intro h; exact h13 (Fin.ext (by exact_mod_cast h))
    have hn23 : (i₂.val : ℝ) ≠ (i₃.val : ℝ) := by
      intro h; exact h23 (Fin.ext (by exact_mod_cast h))
    exact parabola_not_collinear hn12 hn13 hn23 hcol
  let badAll : Finset (Fin N) := badS ∪ TF.biUnion badL
  have hbadAll : badAll.card < N := by
    calc badAll.card ≤ badS.card + (TF.biUnion badL).card := Finset.card_union_le _ _
      _ ≤ S.card + ∑ L ∈ TF, (badL L).card := Nat.add_le_add hbadS Finset.card_biUnion_le
      _ ≤ S.card + ∑ _L ∈ TF, 2 := Nat.add_le_add_left (Finset.sum_le_sum hbadL) _
      _ = S.card + 2 * TF.card := by simp [mul_comm]
      _ < N := by omega
  have hne_univ : badAll ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ, Fintype.card_fin] at hbadAll
    omega
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin N, i₀ ∉ badAll := by
    by_contra hc
    push Not at hc
    apply hne_univ
    ext x
    simp [hc x]
  let q := parabola (i₀.val : ℝ)
  have hqS : q ∉ S := by
    intro h
    apply hi₀
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hqL : ∀ L ∈ TF, q ∉ (L : Set ℝ²) := by
    intro L hL hmem
    apply hi₀
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨L, hL,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩⟩)
  let T : Finset ℝ² := insert q S
  have hT_card : T.card = S.card + 1 := Finset.card_insert_of_notMem hqS
  have hsub : EuclideanGeometry.linesWithPointsFor k (S : Set ℝ²) ⊆
      EuclideanGeometry.linesWithPointsFor k (T : Set ℝ²) := by
    intro L hL
    have hL_TF : L ∈ TF := hfin.mem_toFinset.mpr hL
    have hq_not_L : q ∉ (L : Set ℝ²) := hqL L hL_TF
    rcases hL with ⟨⟨p, hp, r, hr, hpr, rfl⟩, hnc⟩
    refine ⟨⟨p, Finset.mem_coe.mpr (Finset.mem_insert_of_mem hp),
        r, Finset.mem_coe.mpr (Finset.mem_insert_of_mem hr), hpr, rfl⟩, ?_⟩
    have hinter : ↑(affineSpan ℝ {p, r}) ∩ (T : Set ℝ²) =
        ↑(affineSpan ℝ {p, r}) ∩ (S : Set ℝ²) := by
      ext z
      simp only [Set.mem_inter_iff, SetLike.mem_coe, T, Finset.mem_insert]
      constructor
      · rintro ⟨hzL, rfl | hzS⟩
        · exact absurd hzL hq_not_L
        · exact ⟨hzL, hzS⟩
      · rintro ⟨hzL, hzS⟩
        exact ⟨hzL, Or.inr hzS⟩
    rw [hinter]
    exact hnc
  have hfinT : (EuclideanGeometry.linesWithPointsFor k (T : Set ℝ²)).Finite := by
    refine ((T.finite_toSet.prod T.finite_toSet).image
      (fun pq : ℝ² × ℝ² => affineSpan ℝ {pq.1, pq.2})).subset ?_
    rintro L ⟨⟨p, hp, r, hr, -, rfl⟩, -⟩
    exact ⟨(p, r), Set.mk_mem_prod hp hr, rfl⟩
  exact le_csSup_of_le (lineCountsExactly_bddAbove k (S.card + 1)) ⟨T, hT_card, rfl⟩
    (Set.ncard_le_ncard hsub hfinT)

end OrchardProof

theorem OMA.solution : type_of% @Erdos669.erdos_669.variants.burr_grunbaum_sloane_exactly := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨4, Filter.eventually_atTop.mpr ⟨4, fun n hn => ?_⟩⟩
  have hup_nat : 3 * Erdos669.maxLinesExactly 3 n ≤ n.choose 2 := by
    have h1 := Erdos669.erdos_669.variants.exactly_le_atLeast 3 n
    have h2 := OrchardProof.three_mul_maxLinesAtLeast_le n
    omega
  have hlow_nat : (n - 1).choose 2 ≤ 3 * Erdos669.maxLinesExactly 3 n + 2 * n := by
    rcases Nat.even_or_odd n with hev | hod
    · have hod' : Odd (n - 1) := by
        rcases hev with ⟨k, rfl⟩
        refine ⟨k - 1, ?_⟩
        omega
      have h1 : (n - 1).choose 2 ≤ 3 * Erdos669.maxLinesExactly 3 (n - 1) + 2 * (n - 1) :=
        OrchardProof.lower_bound_odd_exactly hod' (by omega)
      have hmono := OrchardProof.maxLinesExactly_le_succ 3 (n - 1)
      have hsub : n - 1 + 1 = n := by omega
      rw [hsub] at hmono
      omega
    · have h1 : n.choose 2 ≤ 3 * Erdos669.maxLinesExactly 3 n + 2 * n :=
        OrchardProof.lower_bound_odd_exactly hod (by omega)
      have h2 : (n - 1).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 (Nat.sub_le n 1)
      omega
  have hup : (Erdos669.maxLinesExactly 3 n : ℝ) ≤ (n : ℝ) ^ 2 / 6 := by
    have h1 : (3 * Erdos669.maxLinesExactly 3 n : ℝ) ≤ ((n.choose 2 : ℕ) : ℝ) := by
      exact_mod_cast hup_nat
    rw [Nat.cast_choose_two] at h1
    nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hlow : (n : ℝ) ^ 2 / 6 - 2 * (n : ℝ) ≤ (Erdos669.maxLinesExactly 3 n : ℝ) := by
    have h1 : (((n - 1).choose 2 : ℕ) : ℝ) ≤ (3 * Erdos669.maxLinesExactly 3 n + 2 * n : ℝ) := by
      exact_mod_cast hlow_nat
    rw [Nat.cast_choose_two] at h1
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hn1] at h1
    linarith
  conv_rhs => rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith
