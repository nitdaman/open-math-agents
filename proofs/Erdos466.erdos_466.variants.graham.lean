import FormalConjectures.ErdosProblems.«466»

-- Problem: Erdős Problem 466 — graham
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/466.lean:71 (declaration Erdos466.erdos_466.variants.graham)
-- Credit: @timlantin (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Written with Claude Code (AI-assisted).
-- The parabola construction (points (2^m, 4^m)) and the distance and compactness lemmas are
-- adapted from the Apache-2.0 formalization of erdos_466 in plby/lean-proofs
-- (src/latest/ErdosProblems/Erdos466.lean, formal authors Codex and GPT-5.6 Sol), ported to the
-- upstream definition of N. The quantitative bound log X / 10 < N X (1/10) is new here.

open Metric

namespace OMA.E466

/-- Graham's points on the parabola y = x². -/
noncomputable def gp (m : ℕ) : EuclideanSpace ℝ (Fin 2) := !₂[(2 : ℝ) ^ m, (4 : ℝ) ^ m]

theorem gp_zero (m : ℕ) : gp m 0 = (2 : ℝ) ^ m := by simp [gp]

theorem gp_one (m : ℕ) : gp m 1 = (4 : ℝ) ^ m := by simp [gp]

theorem gp_injective : Function.Injective gp := by
  intro i j hij
  have hcoord := congrArg (fun p : EuclideanSpace ℝ (Fin 2) ↦ p 0) hij
  simp only [gp_zero] at hcoord
  exact (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).injective hcoord

theorem dist_round_le (x : ℝ) (z : ℤ) : distToNearestInt x ≤ |x - (z : ℝ)| := by
  unfold distToNearestInt
  exact round_le x z

theorem dist_round_le_self {x : ℝ} (hx : 0 ≤ x) : distToNearestInt x ≤ x := by
  simpa [abs_of_nonneg hx] using dist_round_le x 0

theorem gt_of_between {x δ : ℝ} (a : ℤ)
    (hleft : (a : ℝ) + δ < x) (hright : x < (a : ℝ) + 1 - δ) :
    δ < distToNearestInt x := by
  unfold distToNearestInt
  have hz : round x ≤ a ∨ a + 1 ≤ round x := by omega
  rcases hz with hza | haz
  · have hza' : ((round x : ℤ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hza
    calc δ < x - (round x : ℝ) := by linarith
      _ ≤ |x - (round x : ℝ)| := le_abs_self _
  · have haz' : (a : ℝ) + 1 ≤ ((round x : ℤ) : ℝ) := by exact_mod_cast haz
    calc δ < -(x - (round x : ℝ)) := by linarith
      _ ≤ |x - (round x : ℝ)| := neg_le_abs _

theorem sqrt_away (a : ℤ) (r : ℝ) (ha : 1 ≤ a)
    (hlo : (3 / 10 : ℝ) * a ≤ r) (hhi : r ≤ (9 / 5 : ℝ) * a) :
    (1 / 10 : ℝ) < distToNearestInt (Real.sqrt ((a : ℝ) ^ 2 + r)) := by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hr : 0 ≤ r := by nlinarith
  have hbase : 0 ≤ (a : ℝ) ^ 2 + r := by positivity
  have hs0 : 0 ≤ Real.sqrt ((a : ℝ) ^ 2 + r) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt ((a : ℝ) ^ 2 + r) ^ 2 = (a : ℝ) ^ 2 + r := Real.sq_sqrt hbase
  apply gt_of_between a
  · nlinarith
  · nlinarith

theorem gp_dist {i j : ℕ} :
    dist (gp i) (gp j) =
      Real.sqrt ((((4 : ℤ) ^ j - (4 : ℤ) ^ i : ℤ) : ℝ) ^ 2 + ((2 : ℝ) ^ j - (2 : ℝ) ^ i) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, gp_zero, gp_one, Real.dist_eq]
  rw [sq_abs, sq_abs]
  norm_num
  ring_nf

theorem gp_away {i j : ℕ} (hij : i < j) :
    (1 / 10 : ℝ) < distToNearestInt (dist (gp i) (gp j)) := by
  set a : ℤ := (4 : ℤ) ^ j - (4 : ℤ) ^ i with ha_def
  set u : ℝ := (2 : ℝ) ^ i with hu_def
  set v : ℝ := (2 : ℝ) ^ j with hv_def
  have hp4 : (4 : ℤ) ^ i < (4 : ℤ) ^ j :=
    (pow_right_strictMono₀ (by norm_num : (1 : ℤ) < 4)) hij
  have ha : 1 ≤ a := by rw [ha_def]; omega
  have hu0 : 0 ≤ u := by positivity
  have huv : 2 * u ≤ v := by
    rw [hu_def, hv_def]
    calc 2 * (2 : ℝ) ^ i = (2 : ℝ) ^ (i + 1) := by rw [pow_succ]; ring
      _ ≤ (2 : ℝ) ^ j :=
        (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).monotone (Nat.succ_le_iff.2 hij)
  have hpow (k : ℕ) : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have ha_real : (a : ℝ) = v ^ 2 - u ^ 2 := by
    rw [ha_def, hu_def, hv_def]; push_cast; rw [hpow, hpow]
  have hdiff : 0 ≤ v - u := by linarith
  have hlinear : 0 ≤ 7 * v - 13 * u := by linarith
  rw [gp_dist]
  change (1 / 10 : ℝ) < distToNearestInt (Real.sqrt ((a : ℝ) ^ 2 + (v - u) ^ 2))
  apply sqrt_away a ((v - u) ^ 2) ha
  · rw [ha_real]; nlinarith [mul_nonneg hdiff hlinear]
  · rw [ha_real]
    have hprod : 0 ≤ u * (v - u) := mul_nonneg hu0 hdiff
    nlinarith

theorem gp_mem_closedBall {m n : ℕ} (hmn : m < n) :
    gp m ∈ closedBall (gp 0) (2 * (4 : ℝ) ^ n) := by
  have hm4 : (4 : ℝ) ^ m ≤ (4 : ℝ) ^ n :=
    (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 4)).monotone hmn.le
  have h24 : (2 : ℝ) ^ m ≤ (4 : ℝ) ^ m := by gcongr; norm_num
  have h2m1 : 1 ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have h4m1 : 1 ≤ (4 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have h4n0 : 0 ≤ (4 : ℝ) ^ n := by positivity
  have h2sq : ((2 : ℝ) ^ m - 1) ^ 2 ≤ ((4 : ℝ) ^ n) ^ 2 := by
    have hleft : 0 ≤ (4 : ℝ) ^ n - ((2 : ℝ) ^ m - 1) := by linarith
    have hright : 0 ≤ (4 : ℝ) ^ n + ((2 : ℝ) ^ m - 1) := by linarith
    nlinarith [mul_nonneg hleft hright]
  have h4sq : ((4 : ℝ) ^ m - 1) ^ 2 ≤ ((4 : ℝ) ^ n) ^ 2 := by
    have hleft : 0 ≤ (4 : ℝ) ^ n - ((4 : ℝ) ^ m - 1) := by linarith
    have hright : 0 ≤ (4 : ℝ) ^ n + ((4 : ℝ) ^ m - 1) := by linarith
    nlinarith [mul_nonneg hleft hright]
  rw [mem_closedBall, gp_dist]
  norm_num
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith

/-- The set whose supremum defines `Erdos466.N X δ`. -/
def S (X δ : ℝ) : Set ℕ :=
  {n | ∃ (c : EuclideanSpace ℝ (Fin 2)) (P : Finset (EuclideanSpace ℝ (Fin 2))),
    P.card = n ∧ ↑P ⊆ closedBall c X ∧
      (P : Set (EuclideanSpace ℝ (Fin 2))).Pairwise fun x y => δ ≤ distToNearestInt (dist x y)}

theorem N_eq (X δ : ℝ) : Erdos466.N X δ = sSup (S X δ) := rfl

/-- Compactness: for `δ > 0` the admissible sizes are bounded (via a finite `δ/3`-net). -/
theorem S_bddAbove (X : ℝ) {δ : ℝ} (hδ : 0 < δ) : BddAbove (S X δ) := by
  obtain ⟨t, _htsub, htfin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) X)
      (by positivity : 0 < δ / 3)
  refine ⟨htfin.toFinset.card, ?_⟩
  rintro n ⟨c, P, rfl, hPsub, hsep⟩
  have hchoice : ∀ x ∈ P, ∃ y ∈ t, dist (x - c) y < δ / 3 := by
    intro x hx
    have hx' : x - c ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) X := by
      rw [mem_closedBall]
      simpa [dist_eq_norm] using hPsub hx
    rcases Set.mem_iUnion.mp (hcover hx') with ⟨y, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hyt, hyball⟩
    exact ⟨y, hyt, hyball⟩
  classical
  let f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun x =>
    if hx : x ∈ P then (hchoice x hx).choose else 0
  have hf_mem : ∀ x ∈ P, f x ∈ htfin.toFinset := by
    intro x hx
    simp only [f, dif_pos hx, Set.Finite.mem_toFinset]
    exact (hchoice x hx).choose_spec.1
  have hf_close : ∀ x ∈ P, dist (x - c) (f x) < δ / 3 := by
    intro x hx
    simp only [f, dif_pos hx]
    exact (hchoice x hx).choose_spec.2
  apply Finset.card_le_card_of_injOn f (fun x hx => hf_mem x hx)
  intro x hx y hy hxy
  by_contra hne
  have hlt : dist x y < δ := by
    calc dist x y = dist (x - c) (y - c) := by rw [dist_sub_right]
      _ ≤ dist (x - c) (f x) + dist (f x) (y - c) := dist_triangle _ _ _
      _ < δ / 3 + δ / 3 := by
        apply add_lt_add (hf_close x hx)
        rw [dist_comm, hxy]
        exact hf_close y hy
      _ < δ := by linarith
  have hge : δ ≤ dist x y := (hsep hx hy hne).trans (dist_round_le_self dist_nonneg)
  exact absurd hge (not_le.mpr hlt)

/-- Graham's first `n` points give `n ≤ N X (1/10)` once `2 * 4^n ≤ X`. -/
theorem le_N_of_radius {X : ℝ} (n : ℕ) (hX : 2 * (4 : ℝ) ^ n ≤ X) :
    n ≤ Erdos466.N X (1 / 10) := by
  rw [N_eq]
  refine le_csSup (S_bddAbove X (by norm_num)) ?_
  refine ⟨gp 0, (Finset.range n).image gp, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ gp_injective, Finset.card_range]
  · intro x hx
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact closedBall_subset_closedBall hX (gp_mem_closedBall hm)
  · intro x hx y hy hxy
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx hy
    obtain ⟨i, -, rfl⟩ := hx
    obtain ⟨j, -, rfl⟩ := hy
    have hij : i ≠ j := fun h => hxy (h ▸ rfl)
    rcases lt_or_gt_of_ne hij with h | h
    · exact (gp_away h).le
    · rw [dist_comm]; exact (gp_away h).le

/-- One point fits in any disc of nonnegative radius. -/
theorem one_le_N {X : ℝ} (hX : 0 ≤ X) : 1 ≤ Erdos466.N X (1 / 10) := by
  rw [N_eq]
  refine le_csSup (S_bddAbove X (by norm_num)) ?_
  refine ⟨0, {0}, Finset.card_singleton _, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx
    rw [hx, mem_closedBall, dist_self]; exact hX
  · simp

end OMA.E466

theorem OMA.solution : type_of% @Erdos466.erdos_466.variants.graham := by
  intro X hX
  have hX0 : 0 < X := by linarith
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  by_cases hsmall : Real.log X < 10
  · have h1 := OMA.E466.one_le_N hX0.le
    have : Real.log X / 10 < 1 := by linarith
    exact lt_of_lt_of_le this (by exact_mod_cast h1)
  replace hsmall : 10 ≤ Real.log X := not_lt.mp hsmall
  set L := Real.log X with hL
  have hlog4pos : 0 < Real.log 4 := by rw [hlog4]; linarith
  set y : ℝ := Real.log (X / 2) / Real.log 4 with hy
  have hlogX2 : Real.log (X / 2) = L - Real.log 2 := by
    rw [Real.log_div hX0.ne' (by norm_num)]
  have hy0 : 0 ≤ y := by
    rw [hy, hlogX2]; apply div_nonneg <;> linarith
  set n : ℕ := ⌊y⌋₊ with hn
  have hny : (n : ℝ) ≤ y := Nat.floor_le hy0
  have hyn : y < n + 1 := Nat.lt_floor_add_one y
  -- 2 * 4^n ≤ X
  have hpow : 2 * (4 : ℝ) ^ n ≤ X := by
    have h1 : Real.log ((4 : ℝ) ^ n) ≤ Real.log (X / 2) := by
      rw [Real.log_pow]
      have : (n : ℝ) * Real.log 4 ≤ y * Real.log 4 := by gcongr
      rwa [hy, div_mul_cancel₀ _ hlog4pos.ne'] at this
    have h2 : (4 : ℝ) ^ n ≤ X / 2 :=
      (Real.log_le_log_iff (by positivity) (by positivity)).mp h1
    linarith
  have hkey : L / 10 + 1 ≤ y := by
    rw [hy, hlogX2, le_div_iff₀ hlog4pos, hlog4]
    nlinarith
  have hN := OMA.E466.le_N_of_radius n hpow
  have : L / 10 < (n : ℝ) := by linarith
  exact lt_of_lt_of_le this (by exact_mod_cast hN)
