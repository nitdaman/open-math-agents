import FormalConjectures.Books.UniformDistributionOfSequences.Equidistribution
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Non-equidistributed transcendental multiples of `(3/2)^n`

We prove `¬ ∀ x : ℝ, Transcendental ℚ x → IsEquidistributedModuloOne (fun n ↦ x * (3 / 2) ^ n)`
using an elementary Cantor-set construction of nested closed intervals:
1. Setting `B = (3 / 2) ^ 8 > 25`, for each binary sequence `w : ℕ → Bool` we inductively build
   nested closed intervals `I_w j = [a_w j / B ^ j, (a_w j + 1 / 10) / B ^ j]` with `a_w j : ℤ`,
   branching into two disjoint subintervals at each step according to `w j`.
2. The limit point `x_w = ⨆ j, a_w j / B ^ j` satisfies `Int.fract (x_w * (3 / 2) ^ (8 * j)) ∈ [0, 1 / 10]`
   for every `j : ℕ`, and `w ↦ x_w` is injective.
3. Since `ℕ → Bool` is uncountable while the set of real numbers algebraic over `ℚ` is countable,
   there exists `w` with `Transcendental ℚ x_w`.
4. For `x_w`, at every `n = 8 * N` (`N ≥ 1`), at least `N` of the first `8 * N` fractional parts
   lie in `[0, 1 / 10]`, giving density `≥ 1 / 8 > 1 / 10`, which rules out equidistribution mod `1`.
-/

open Filter Finset Set
open scoped Topology

namespace OMAEquidist

private noncomputable abbrev B : ℝ := (3 / 2 : ℝ) ^ 8

private lemma B_pos : (0 : ℝ) < B := by unfold B; positivity

private lemma B_gt_twentyfive : (25 : ℝ) < B := by unfold B; norm_num

/-- Integer left-endpoint sequence defining the nested intervals for a binary sequence `w`. -/
private noncomputable def seqA (w : ℕ → Bool) : ℕ → ℤ
  | 0 => 0
  | j + 1 => ⌈B * (seqA w j : ℝ)⌉ + if w j then 1 else 0

private lemma seqA_agree {w₁ w₂ : ℕ → Bool} {j : ℕ}
    (h : ∀ i < j, w₁ i = w₂ i) : seqA w₁ j = seqA w₂ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [seqA]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h j (Nat.lt_succ_self j)]

private noncomputable def lo (w : ℕ → Bool) (j : ℕ) : ℝ :=
  (seqA w j : ℝ) / B ^ j

private noncomputable def hi (w : ℕ → Bool) (j : ℕ) : ℝ :=
  ((seqA w j : ℝ) + 1 / 10) / B ^ j

private lemma lo_le_hi (w : ℕ → Bool) (j : ℕ) : lo w j ≤ hi w j := by
  unfold lo hi
  have hBp : (0 : ℝ) < B ^ j := pow_pos B_pos j
  exact div_le_div_of_nonneg_right (by linarith) hBp.le

private lemma lo_le_lo_succ (w : ℕ → Bool) (j : ℕ) : lo w j ≤ lo w (j + 1) := by
  unfold lo
  have hBp : (0 : ℝ) < B ^ j := pow_pos B_pos j
  have hBp1 : (0 : ℝ) < B ^ (j + 1) := pow_pos B_pos (j + 1)
  rw [div_le_div_iff₀ hBp hBp1, pow_succ]
  have hceil : B * (seqA w j : ℝ) ≤ (⌈B * (seqA w j : ℝ)⌉ : ℝ) := Int.le_ceil _
  have hstep : B * (seqA w j : ℝ) ≤ (seqA w (j + 1) : ℝ) := by
    simp only [seqA, Int.cast_add]
    split_ifs <;> push_cast <;> linarith
  have : (seqA w j : ℝ) * (B ^ j * B) = B ^ j * (B * (seqA w j : ℝ)) := by ring
  rw [this]
  nlinarith

private lemma hi_succ_le_hi (w : ℕ → Bool) (j : ℕ) : hi w (j + 1) ≤ hi w j := by
  unfold hi
  have hBp : (0 : ℝ) < B ^ j := pow_pos B_pos j
  have hBp1 : (0 : ℝ) < B ^ (j + 1) := pow_pos B_pos (j + 1)
  rw [div_le_div_iff₀ hBp1 hBp, pow_succ]
  have hceil : (⌈B * (seqA w j : ℝ)⌉ : ℝ) < B * (seqA w j : ℝ) + 1 := Int.ceil_lt_add_one _
  have hB10 : (5 / 2 : ℝ) < B * (1 / 10) := by unfold B; norm_num
  have hstep : (seqA w (j + 1) : ℝ) + 1 / 10 ≤ B * ((seqA w j : ℝ) + 1 / 10) := by
    simp only [seqA, Int.cast_add]
    rw [mul_add]
    split_ifs <;> push_cast
    · calc (⌈B * (seqA w j : ℝ)⌉ : ℝ) + 1 + 1 / 10
          ≤ (B * (seqA w j : ℝ) + 1) + 1 + 1 / 10 := by gcongr
        _ ≤ B * (seqA w j : ℝ) + B * (1 / 10) := by linarith
    · calc (⌈B * (seqA w j : ℝ)⌉ : ℝ) + 0 + 1 / 10
          ≤ (B * (seqA w j : ℝ) + 1) + 0 + 1 / 10 := by gcongr
        _ ≤ B * (seqA w j : ℝ) + B * (1 / 10) := by linarith
  have : ((seqA w j : ℝ) + 1 / 10) * (B ^ j * B) =
      (B * ((seqA w j : ℝ) + 1 / 10)) * B ^ j := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right hstep hBp.le

private lemma lo_mono (w : ℕ → Bool) : Monotone (lo w) :=
  monotone_nat_of_le_succ (lo_le_lo_succ w)

private lemma hi_anti (w : ℕ → Bool) : Antitone (hi w) :=
  antitone_nat_of_succ_le (hi_succ_le_hi w)

private lemma lo_le_hi_any (w : ℕ → Bool) (j k : ℕ) : lo w j ≤ hi w k := by
  rcases le_total j k with hjk | hkj
  · exact (lo_mono w hjk).trans (lo_le_hi w k)
  · exact (lo_le_hi w j).trans (hi_anti w hkj)

/-- The Cantor-set real number associated with `w : ℕ → Bool`. -/
private noncomputable def cantorPt (w : ℕ → Bool) : ℝ :=
  ⨆ j : ℕ, lo w j

private lemma cantorPt_mem_Icc (w : ℕ → Bool) (k : ℕ) :
    lo w k ≤ cantorPt w ∧ cantorPt w ≤ hi w k := by
  have hbdd : BddAbove (Set.range (lo w)) := ⟨hi w 0, by rintro _ ⟨j, rfl⟩; exact lo_le_hi_any w j 0⟩
  exact ⟨le_ciSup hbdd k, ciSup_le fun j => lo_le_hi_any w j k⟩

private lemma cantorPt_injective : Function.Injective cantorPt := by
  intro w₁ w₂ heq
  by_contra hne
  have hex : ∃ j : ℕ, w₁ j ≠ w₂ j := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  classical
  let j := Nat.find hex
  have hj_ne : w₁ j ≠ w₂ j := Nat.find_spec hex
  have hj_eq : ∀ i < j, w₁ i = w₂ i := fun i hi => by
    by_contra h
    exact Nat.find_min hex hi h
  have hprev : seqA w₁ j = seqA w₂ j := seqA_agree hj_eq
  have h1 := cantorPt_mem_Icc w₁ (j + 1)
  have h2 := cantorPt_mem_Icc w₂ (j + 1)
  rw [heq] at h1
  have hBp1 : (0 : ℝ) < B ^ (j + 1) := pow_pos B_pos (j + 1)
  cases hw1 : w₁ j <;> cases hw2 : w₂ j
  · exact hj_ne (hw1.trans hw2.symm)
  · -- w₁ j = false, w₂ j = true: hi w₁ (j+1) < lo w₂ (j+1)
    have hlt : hi w₁ (j + 1) < lo w₂ (j + 1) := by
      unfold hi lo
      apply div_lt_div_of_pos_right _ hBp1
      simp only [seqA, hw1, hw2, hprev, Bool.false_eq_true, ↓reduceIte, add_zero, Int.cast_add,
        Int.cast_one]
      linarith
    linarith [h1.2, h2.1]
  · -- w₁ j = true, w₂ j = false: hi w₂ (j+1) < lo w₁ (j+1)
    have hlt : hi w₂ (j + 1) < lo w₁ (j + 1) := by
      unfold hi lo
      apply div_lt_div_of_pos_right _ hBp1
      simp only [seqA, hw1, hw2, hprev, Bool.false_eq_true, ↓reduceIte, add_zero, Int.cast_add,
        Int.cast_one]
      linarith
    linarith [h2.2, h1.1]
  · exact hj_ne (hw1.trans hw2.symm)

private lemma cantorPt_fract_mem (w : ℕ → Bool) (j : ℕ) :
    Int.fract (cantorPt w * (3 / 2 : ℝ) ^ (8 * j)) ∈ Set.Icc (0 : ℝ) (1 / 10) := by
  have hpow : (3 / 2 : ℝ) ^ (8 * j) = B ^ j := by
    unfold B
    rw [pow_mul]
  rw [hpow]
  have hmem := cantorPt_mem_Icc w j
  have hBp : (0 : ℝ) < B ^ j := pow_pos B_pos j
  have hlo : (seqA w j : ℝ) ≤ cantorPt w * B ^ j := by
    have := hmem.1
    unfold lo at this
    exact (div_le_iff₀ hBp).mp this
  have hhi : cantorPt w * B ^ j ≤ (seqA w j : ℝ) + 1 / 10 := by
    have := hmem.2
    unfold hi at this
    exact (le_div_iff₀ hBp).mp this
  have hfloor : ⌊cantorPt w * B ^ j⌋ = seqA w j := by
    rw [Int.floor_eq_iff]
    refine ⟨hlo, lt_of_le_of_lt hhi ?_⟩
    exact add_lt_add_right (by norm_num : (1 / 10 : ℝ) < 1) (seqA w j : ℝ) |> fun h => by
      simpa [add_comm] using h
  rw [Int.fract, hfloor]
  exact ⟨by linarith, by linarith⟩

private lemma cantorPt_not_equidistributed (w : ℕ → Bool) :
    ¬ IsEquidistributedModuloOne (fun n => cantorPt w * (3 / 2 : ℝ) ^ n) := by
  intro heq
  have hlim := heq 0 (1 / 10) (by norm_num) (Set.Icc_subset_Icc (by norm_num) (by norm_num))
  have htarget : ((1 / 10 : ℝ) - 0) / (1 - 0) = 1 / 10 := by norm_num
  rw [htarget] at hlim
  have hev : ∀ᶠ n : ℕ in atTop,
      (((Finset.range n).filter
        (fun m => Int.fract (cantorPt w * (3 / 2 : ℝ) ^ m) ∈ Set.Icc (0 : ℝ) (1 / 10))).card : ℝ) /
        (n : ℝ) < 1 / 8 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (1 / 10 : ℝ) < 1 / 8))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  let N := max N₀ 1
  have h8N : N₀ ≤ 8 * N := by omega
  have hlt := hN₀ (8 * N) h8N
  have hcard_ge : N ≤ ((Finset.range (8 * N)).filter
      (fun m => Int.fract (cantorPt w * (3 / 2 : ℝ) ^ m) ∈ Set.Icc (0 : ℝ) (1 / 10))).card := by
    have hsub : (Finset.range N).image (fun j => 8 * j) ⊆
        (Finset.range (8 * N)).filter
          (fun m => Int.fract (cantorPt w * (3 / 2 : ℝ) ^ m) ∈ Set.Icc (0 : ℝ) (1 / 10)) := by
      intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨j, hj, rfl⟩ := hm
      rw [Finset.mem_range] at hj
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, cantorPt_fract_mem w j⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (fun a b hab => by omega), Finset.card_range] at h1
    exact h1
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hcard_real : (N : ℝ) ≤ (((Finset.range (8 * N)).filter
      (fun m => Int.fract (cantorPt w * (3 / 2 : ℝ) ^ m) ∈ Set.Icc (0 : ℝ) (1 / 10))).card : ℝ) := by
    exact_mod_cast hcard_ge
  have hge : (1 / 8 : ℝ) ≤
      (((Finset.range (8 * N)).filter
        (fun m => Int.fract (cantorPt w * (3 / 2 : ℝ) ^ m) ∈ Set.Icc (0 : ℝ) (1 / 10))).card : ℝ) /
        ((8 * N : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, le_div_iff₀ (by positivity)]
    linarith
  linarith

private lemma countable_poly_rat : Countable (Polynomial ℚ) := by
  let enc : Polynomial ℚ → List ℚ := fun p =>
    List.ofFn (fun i : Fin (p.natDegree + 1) => p.coeff i)
  refine Function.Injective.countable (f := enc) fun p q hpq => ?_
  have hlen : p.natDegree + 1 = q.natDegree + 1 := by
    have := congr_arg List.length hpq
    simpa [enc] using this
  ext k
  by_cases hk : k < p.natDegree + 1
  · have hget := congr_arg (fun l : List ℚ => l[k]?) hpq
    have hk' : k < q.natDegree + 1 := by omega
    simp only [enc, List.getElem?_ofFn, hk, hk', ↓reduceDIte, Option.some.injEq] at hget
    exact hget
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

private lemma countable_isAlgebraic_rat : Set.Countable {x : ℝ | IsAlgebraic ℚ x} := by
  have : Countable (Polynomial ℚ) := countable_poly_rat
  have hsub : {x : ℝ | IsAlgebraic ℚ x} ⊆
      ⋃ p ∈ {p : Polynomial ℚ | p ≠ 0}, {x : ℝ | Polynomial.aeval x p = 0} := by
    intro x ⟨p, hp0, hpx⟩
    exact Set.mem_biUnion hp0 hpx
  refine (Set.Countable.biUnion (Set.to_countable _) fun p hp => ?_).mono hsub
  have hp0 : p ≠ 0 := hp
  have hp_map : p.map (algebraMap ℚ ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hp0
  have hfin : ((p.map (algebraMap ℚ ℝ)).roots.toFinset : Set ℝ).Finite := Finset.finite_toSet _
  refine (hfin.subset ?_).countable
  intro x hx
  change Polynomial.aeval x p = 0 at hx
  rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp_map, Polynomial.IsRoot]
  simpa [Polynomial.aeval_def, Polynomial.eval_map] using hx

private lemma exists_transcendental_cantorPt :
    ∃ w : ℕ → Bool, Transcendental ℚ (cantorPt w) := by
  by_contra hall
  push Not at hall
  have hrange : Set.range cantorPt ⊆ {x : ℝ | IsAlgebraic ℚ x} := by
    rintro _ ⟨w, rfl⟩
    exact not_not.mp (hall w)
  have hcount_range : (Set.range cantorPt).Countable := countable_isAlgebraic_rat.mono hrange
  have hcount_fn : Countable (ℕ → Bool) := by
    have : Countable (Set.range cantorPt) := hcount_range.to_subtype
    exact Function.Injective.countable (f := fun w => (⟨cantorPt w, ⟨w, rfl⟩⟩ : Set.range cantorPt))
      fun w₁ w₂ h => cantorPt_injective (congr_arg Subtype.val h)
  -- Cantor diagonalization: `ℕ → Bool` is not countable
  obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ → Bool)
  let g : ℕ → Bool := fun n => !(f n n)
  obtain ⟨n, hn⟩ := hf g
  have hdiag := congr_fun hn n
  simp only [g] at hdiag
  cases h : f n n <;> simp [h] at hdiag

end OMAEquidist

theorem OMA.solution :
    type_of% @Equidistribution.isEquidistributedModuloOne_transcendental_three_halves_pow := by
  intro hall
  obtain ⟨w, hw_trans⟩ := OMAEquidist.exists_transcendental_cantorPt
  exact OMAEquidist.cantorPt_not_equidistributed w (hall (OMAEquidist.cantorPt w) hw_trans)
