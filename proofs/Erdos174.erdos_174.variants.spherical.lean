import FormalConjectures.ErdosProblems.«174»

/-! A finite coloring excludes every congruent image of a noncospherical set. -/

namespace OMA.Spherical

open Finset

lemma functional_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) →ₗ[ℝ] ℝ) (x : ι → ℝ) :
    f x = ∑ i, f (Pi.single i 1) * x i := by
  calc
    f x = f (∑ i, Pi.single i (x i)) := congrArg f (Finset.univ_sum_single x).symm
    _ = ∑ i, f (Pi.single i 1) * x i := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      have he : Pi.single i (x i) = x i • Pi.single i (1 : ℝ) := by
        funext j
        by_cases h : j = i <;> simp [h]
      rw [he, map_smul, smul_eq_mul, mul_comm]

lemma separating_weights {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : Set E} [Fintype A] (o : A) (hA : ¬ EuclideanGeometry.Cospherical A) :
    ∃ w : A → ℝ,
      (∀ z : E, ∑ i, w i * inner ℝ ((i : E) - o) z = 0) ∧
      ∑ i, w i * ‖(i : E) - o‖ ^ 2 = 1 := by
  classical
  let T : E →ₗ[ℝ] (A → ℝ) :=
    LinearMap.pi fun i => (2 : ℝ) • (innerSL ℝ ((i : E) - o)).toLinearMap
  let b : A → ℝ := fun i => ‖(i : E) - o‖ ^ 2
  have hTa (z : E) (i : A) : T z i = 2 * inner ℝ ((i : E) - o) z := by
    simp [T, smul_eq_mul, inner_sub_left]
  have hbr : b ∉ LinearMap.range T := by
    rintro ⟨z, hz⟩
    apply hA
    refine ⟨(o : E) + z, ‖z‖, fun a ha => ?_⟩
    have hr := congrFun hz ⟨a, ha⟩
    rw [hTa] at hr
    change 2 * inner ℝ (a - (o : E)) z = ‖a - (o : E)‖ ^ 2 at hr
    rw [dist_eq_norm, show a - ((o : E) + z) = a - (o : E) - z by abel]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sub_sq_real]
    linarith
  obtain ⟨f, hrestrict, hf⟩ := LinearMap.exists_extend_of_notMem
    (0 : LinearMap.range T →ₗ[ℝ] ℝ) hbr 1
  let w (i : A) := f (Pi.single i 1)
  refine ⟨w, fun z => ?_, (functional_sum f b).symm.trans hf⟩
  have hzero : f (T z) = 0 := by
    have he := congrArg (fun g : LinearMap.range T →ₗ[ℝ] ℝ => g ⟨T z, ⟨z, rfl⟩⟩) hrestrict
    simpa using he
  have hs := (functional_sum f (T z)).symm.trans hzero
  change (∑ i, w i * T z i) = 0 at hs
  simp_rw [hTa] at hs
  have he : (∑ i, w i * (2 * inner ℝ ((i : E) - o) z)) =
      2 * ∑ i, w i * inner ℝ ((i : E) - o) z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hs
  linarith

lemma anchored_inner {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {a : ι → E} {p : ι → F} (h : ∀ i j, dist (a i) (a j) = dist (p i) (p j))
    (o i j : ι) :
    inner ℝ (a i - a o) (a j - a o) = inner ℝ (p i - p o) (p j - p o) := by
  have hi := h i o
  have hj := h j o
  have hij := h i j
  simp only [dist_eq_norm] at hi hj hij
  have ha := norm_sub_sq_real (a i - a o) (a j - a o)
  have hp := norm_sub_sq_real (p i - p o) (p j - p o)
  rw [show (a i - a o) - (a j - a o) = a i - a j by abel, hi, hj, hij] at ha
  rw [show (p i - p o) - (p j - p o) = p i - p j by abel] at hp
  linarith

lemma transported_sum {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {a : ι → E} {p : ι → F} (h : ∀ i j, dist (a i) (a j) = dist (p i) (p j))
    (o : ι) (w : ι → ℝ)
    (hw : ∀ z : E, ∑ i, w i * inner ℝ (a i - a o) z = 0)
    (hs : ∑ i, w i * ‖a i - a o‖ ^ 2 = 1) :
    ∑ i, w i * (‖p i‖ ^ 2 - ‖p o‖ ^ 2) = 1 := by
  let v (i : ι) := p i - p o
  let vSum : F := ∑ i, w i • v i
  have hv (j : ι) : inner ℝ vSum (v j) = 0 := by
    simp only [vSum, sum_inner, real_inner_smul_left, v]
    simp_rw [← anchored_inner h o]
    exact hw (a j - a o)
  have hzero : vSum = 0 := by
    apply (@inner_self_eq_zero ℝ F _ _ _).mp
    change inner ℝ vSum (∑ i, w i • v i) = 0
    simp [inner_sum, real_inner_smul_right, hv]
  have horth : (∑ i, w i * inner ℝ (v i) (p o)) = 0 := by
    have hh := congrArg (fun y : F => inner ℝ y (p o)) hzero
    simpa only [vSum, sum_inner, real_inner_smul_left, inner_zero_left] using hh
  have hshift (i : ι) : ‖p i‖ ^ 2 - ‖p o‖ ^ 2 =
      ‖v i‖ ^ 2 + 2 * inner ℝ (v i) (p o) := by
    have hh := norm_add_sq_real (v i) (p o)
    rw [show v i + p o = p i by simp [v]] at hh
    linarith
  have hn (i : ι) : ‖v i‖ = ‖a i - a o‖ := by
    simpa only [v, dist_eq_norm] using (h i o).symm
  calc
    (∑ i, w i * (‖p i‖ ^ 2 - ‖p o‖ ^ 2)) =
      (∑ i, w i * ‖v i‖ ^ 2) + 2 * (∑ i, w i * inner ℝ (v i) (p o)) := by
        simp_rw [hshift, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = 1 := by simpa [hn, horth] using hs

noncomputable def bin (m : ℕ) (hm : 0 < m) (t : ℝ) : Fin m :=
  ⟨Nat.floor ((m : ℝ) * Int.fract t),
    (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg m) (Int.fract_nonneg t))).mpr (by
      have hmr : (0 : ℝ) < m := by exact_mod_cast hm
      simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one t) hmr)⟩

lemma bin_bound {m : ℕ} {hm : 0 < m} {s t : ℝ} (h : bin m hm s = bin m hm t) :
    |Int.fract s - Int.fract t| ≤ 1 / (m : ℝ) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have he : Nat.floor ((m : ℝ) * Int.fract s) = Nat.floor ((m : ℝ) * Int.fract t) :=
    congrArg Fin.val h
  have hs₁ := Nat.floor_le (mul_nonneg (Nat.cast_nonneg m) (Int.fract_nonneg s))
  have hs₂ := Nat.lt_floor_add_one ((m : ℝ) * Int.fract s)
  have ht₁ := Nat.floor_le (mul_nonneg (Nat.cast_nonneg m) (Int.fract_nonneg t))
  have ht₂ := Nat.lt_floor_add_one ((m : ℝ) * Int.fract t)
  rw [he] at hs₁ hs₂
  apply abs_le.mpr
  constructor
  · rw [← neg_div]
    apply (div_le_iff₀ hmr).mpr
    linarith
  · apply (le_div_iff₀ hmr).mpr
    linarith

lemma no_half_sum {ι : Type*} [Fintype ι] {s t : ι → ℝ}
    (h : ∑ i, (s i - t i) = 1 / 2)
    (hb : ∀ i, |Int.fract (s i) - Int.fract (t i)| ≤
      1 / ((2 * Fintype.card ι + 1 : ℕ) : ℝ)) : False := by
  let m : ℕ := 2 * Fintype.card ι + 1
  have hm : (0 : ℝ) < m := by positivity
  have hbound : |∑ i, (Int.fract (s i) - Int.fract (t i))| < 1 / 2 := by
    calc
      _ ≤ ∑ i, |Int.fract (s i) - Int.fract (t i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, (1 / (m : ℝ)) := Finset.sum_le_sum (fun i _ => hb i)
      _ < 1 / 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
        apply (div_lt_iff₀ hm).mpr
        push_cast [m]
        linarith
  let z : ℤ := ∑ i, (Int.floor (s i) - Int.floor (t i))
  have hz : (∑ i, (Int.fract (s i) - Int.fract (t i))) = 1 / 2 - (z : ℝ) := by
    calc
      _ = (∑ i, (s i - t i)) - (z : ℝ) := by
        simp only [z, Int.cast_sum, Int.cast_sub, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        unfold Int.fract
        ring
      _ = _ := by rw [h]
  rw [hz] at hbound
  obtain ⟨hl, hu⟩ := abs_lt.mp hbound
  have hpos : (0 : ℤ) < z := by exact_mod_cast (show (0 : ℝ) < (z : ℝ) by linarith)
  have hone : z < 1 := by exact_mod_cast (show (z : ℝ) < (1 : ℝ) by linarith)
  omega

end OMA.Spherical

open OMA.Spherical in
theorem OMA.solution : type_of% @Erdos174.erdos_174.variants.spherical := by
  classical
  intro n A hA
  obtain ⟨hfinite, hRamsey⟩ := hA
  by_contra hnot
  have hnon : A.Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    exact hnot ⟨0, 0, by simp [he]⟩
  obtain ⟨a₀, ha₀⟩ := hnon
  let o : A := ⟨a₀, ha₀⟩
  let _ : Fintype A := hfinite.fintype
  obtain ⟨w, hw, hs⟩ := separating_weights o hnot
  let m : ℕ := 2 * Fintype.card A + 1
  have hm : 0 < m := by positivity
  let k := Fintype.card (A → Fin m)
  let e := Fintype.equivFin (A → Fin m)
  have hk : 1 ≤ k := by
    let _ : Nonempty (A → Fin m) := ⟨fun _ => ⟨0, hm⟩⟩
    exact Fintype.card_pos
  obtain ⟨d, hd⟩ := hRamsey k hk
  let F (i : A) (x : EuclideanSpace ℝ (Fin d)) := w i * ‖x‖ ^ 2 / 2
  let c (x : EuclideanSpace ℝ (Fin d)) := e (fun i => bin m hm (F i x))
  obtain ⟨p, hp, color, hc⟩ := hd c
  have hsum :
      ∑ i, (F i (p i) - F i (p o)) = 1 / 2 := by
    have hh := transported_sum hp.dist_eq o w hw hs
    calc
      _ = (∑ i, w i * (‖p i‖ ^ 2 - ‖p o‖ ^ 2)) / 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [F]
        ring
      _ = _ := by rw [hh]
  apply no_half_sum hsum
  intro i
  apply bin_bound (m := m) (hm := hm)
  have hh := (hc i).trans (hc o).symm
  exact congrFun (e.injective hh) i
