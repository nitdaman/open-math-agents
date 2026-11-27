import FormalConjectures.ErdosProblems.«756»
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Infinite

/-!
Bhowmick's rich-distance bound, following the reflected and rotated polygon
construction in Theorem 1.2 of [A problem of Erdős about rich distances](https://arxiv.org/abs/2407.01174).
-/

open Finset
open scoped Classical

private noncomputable def unitCircle (t : ℝ) : ℂ := circleMap 0 1 t

private theorem unitCircle_norm (t : ℝ) : ‖unitCircle t‖ = 1 := by
  simp [unitCircle]

private theorem unitCircle_add (t u : ℝ) : unitCircle (t + u) = unitCircle t * unitCircle u := by
  symm
  simpa [unitCircle] using circleMap_zero_mul 1 1 t u

private theorem unitCircle_sub_period (t : ℝ) :
    unitCircle (t - 2 * Real.pi) = unitCircle t := by
  simpa only [unitCircle, sub_add_cancel] using (periodic_circleMap 0 1 (t - 2 * Real.pi)).symm

private theorem unitCircle_re (t : ℝ) : (unitCircle t).re = Real.cos t := by
  simpa [unitCircle] using circleMap_zero_re 1 t

private theorem unitCircle_im (t : ℝ) : (unitCircle t).im = Real.sin t := by
  simpa [unitCircle] using circleMap_zero_im 1 t

private noncomputable def polygonVertex (k : ℕ) (i : Fin k) : ℂ :=
  unitCircle ((2 * (i.val : ℝ) + 1) * (Real.pi / k))

private theorem polygonVertex_norm (k : ℕ) (i : Fin k) : ‖polygonVertex k i‖ = 1 :=
  unitCircle_norm _

private theorem polygonVertex_injective (k : ℕ) : Function.Injective (polygonVertex k) := by
  intro i j heq
  have hk : 0 < (k : ℝ) := by exact_mod_cast (i.isLt.trans_le' (Nat.zero_le _))
  let t := Real.pi / (k : ℝ)
  have ht : 0 < t := div_pos Real.pi_pos hk
  have hπ : (k : ℝ) * t = Real.pi := by dsimp [t]; field_simp
  have hi : (i.val : ℝ) < k := by exact_mod_cast i.isLt
  have hj : (j.val : ℝ) < k := by exact_mod_cast j.isLt
  have habs : |(2 * (i.val : ℝ) + 1) * t - (2 * (j.val : ℝ) + 1) * t| < 2 * Real.pi := by
    rw [abs_lt]
    have h₁ := mul_lt_mul_of_pos_right hi ht
    have h₂ := mul_lt_mul_of_pos_right hj ht
    have h₃ : 0 ≤ (i.val : ℝ) * t := by positivity
    have h₄ : 0 ≤ (j.val : ℝ) * t := by positivity
    constructor <;> nlinarith only [h₁, h₂, h₃, h₄, hπ]
  have harg := eq_of_circleMap_eq (R := 1) (by norm_num) habs heq
  apply Fin.ext
  have hval : (i.val : ℝ) = j.val := by
    apply mul_right_cancel₀ ht.ne'
    nlinarith only [harg]
  exact_mod_cast hval

private theorem polygonVertex_shift (k : ℕ) (i j : Fin k) :
    polygonVertex k (i + j) = unitCircle (2 * (j.val : ℝ) * (Real.pi / k)) * polygonVertex k i := by
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  let t := Real.pi / (k : ℝ)
  have hπ : (k : ℝ) * t = Real.pi := by dsimp [t]; field_simp
  change unitCircle ((2 * ((i + j).val : ℝ) + 1) * t) =
    unitCircle (2 * (j.val : ℝ) * t) * unitCircle ((2 * (i.val : ℝ) + 1) * t)
  rw [← unitCircle_add, Fin.val_add_eq_ite]
  split
  · rename_i h
    rw [Nat.cast_sub h, Nat.cast_add]
    rw [show (2 * ((i.val : ℝ) + (j.val : ℝ) - k) + 1) * t =
      2 * (j.val : ℝ) * t + (2 * (i.val : ℝ) + 1) * t - 2 * Real.pi by
        nlinarith only [hπ], unitCircle_sub_period]
  · rw [Nat.cast_add]
    congr 1
    ring

private noncomputable def polygon (k : ℕ) : Finset ℂ :=
  univ.image (polygonVertex k)

private theorem card_polygon (k : ℕ) : (polygon k).card = k := by
  rw [polygon, card_image_of_injective _ (polygonVertex_injective _)]
  simp

private theorem norm_mem_polygon {k : ℕ} {z : ℂ} (h : z ∈ polygon k) : ‖z‖ = 1 := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp h
  exact polygonVertex_norm _ _

private noncomputable def chordLength (k j : ℕ) : ℝ :=
  ‖unitCircle (2 * (j : ℝ) * (Real.pi / k)) - 1‖

private theorem polygon_chord_eq (k : ℕ) (i j : Fin k) :
    dist (polygonVertex k i) (polygonVertex k (i + j)) = chordLength k j.val := by
  rw [dist_comm, dist_eq_norm, chordLength, polygonVertex_shift, ← sub_one_mul, norm_mul,
    polygonVertex_norm, mul_one]

private theorem square_chordLength (k j : ℕ) :
    chordLength k j ^ 2 = 2 - 2 * Real.cos (2 * (j : ℝ) * (Real.pi / k)) := by
  let t := 2 * (j : ℝ) * (Real.pi / k)
  have hnorm : Complex.normSq (unitCircle t) = 1 := by
    rw [Complex.normSq_eq_norm_sq, unitCircle_norm, one_pow]
  change ‖unitCircle t - 1‖ ^ 2 = 2 - 2 * Real.cos t
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    unitCircle_re] at hnorm ⊢
  nlinarith only [hnorm]

private theorem chordLength_inj {k a b : ℕ} (hk : 0 < k) (ha : 2 * a < k) (hb : 2 * b < k)
    (heq : chordLength k a = chordLength k b) : a = b := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  let t := Real.pi / (k : ℝ)
  have ht : 0 < t := div_pos Real.pi_pos hkR
  have hπ : (k : ℝ) * t = Real.pi := by dsimp [t]; field_simp
  have haR : 2 * (a : ℝ) < k := by exact_mod_cast ha
  have hbR : 2 * (b : ℝ) < k := by exact_mod_cast hb
  have hamem : 2 * (a : ℝ) * t ∈ Set.Icc 0 Real.pi :=
    ⟨by positivity, by rw [← hπ]; exact mul_le_mul_of_nonneg_right haR.le ht.le⟩
  have hbmem : 2 * (b : ℝ) * t ∈ Set.Icc 0 Real.pi :=
    ⟨by positivity, by rw [← hπ]; exact mul_le_mul_of_nonneg_right hbR.le ht.le⟩
  have hsq := congrArg (fun x : ℝ => x ^ 2) heq
  rw [square_chordLength, square_chordLength] at hsq
  have hcos : Real.cos (2 * (a : ℝ) * t) = Real.cos (2 * (b : ℝ) * t) := by
    change 2 - 2 * Real.cos (2 * (a : ℝ) * t) = 2 - 2 * Real.cos (2 * (b : ℝ) * t) at hsq
    linarith only [hsq]
  have harg := Real.strictAntiOn_cos.injOn hamem hbmem hcos
  have hval : (a : ℝ) = b := by
    apply mul_right_cancel₀ ht.ne'
    linarith only [harg]
  exact_mod_cast hval

private theorem card_two_chord_orientations {k : ℕ} (hk : 0 < k)
    (v : Fin k → ℂ) (hv : Function.Injective v) (j : Fin k) (hj : 0 < j.val)
    (hj2 : 2 * j.val < k) (d : ℝ)
    (hd : ∀ i, dist (v i) (v (i + j)) = d) :
    k ≤ distanceMultiplicity (univ.image v) d := by
  let _ : NeZero k := ⟨hk.ne'⟩
  let S := (univ : Finset (Fin k)).image (fun i => (v i, v (i + j)))
  let T := (univ : Finset (Fin k)).image (fun i => (v (i + j), v i))
  let D := (univ.image v).offDiag.filter (fun p => dist p.1 p.2 = d)
  have hj0 : j ≠ 0 := by
    intro he
    have he' := congrArg Fin.val he
    simp only [Fin.val_zero] at he'
    omega
  have htwo : j + j ≠ 0 := by
    intro he
    have he' := congrArg Fin.val he
    simp only [Fin.val_add, Fin.val_zero, Nat.mod_eq_of_lt (show j.val + j.val < k by omega)] at he'
    omega
  have hne (i : Fin k) : v i ≠ v (i + j) := by
    intro he
    have he' : i + j = i + 0 := by simpa using (hv he).symm
    exact hj0 (add_left_cancel he')
  have hS : S.card = k := by
    dsimp only [S]
    rw [card_image_of_injective _ (fun _ _ h => hv (congrArg Prod.fst h))]
    simp
  have hT : T.card = k := by
    dsimp only [T]
    rw [card_image_of_injective _ (fun _ _ h => hv (congrArg Prod.snd h))]
    simp
  have hST : Disjoint S T := by
    refine disjoint_left.mpr fun p h₁ h₂ => ?_
    obtain ⟨a, _, rfl⟩ := mem_image.mp h₁
    obtain ⟨b, _, heq⟩ := mem_image.mp h₂
    have hab : b + j = a := hv (congrArg Prod.fst heq)
    have hba : b = a + j := hv (congrArg Prod.snd heq)
    have he : b + (j + j) = b + 0 := by rw [← add_assoc, hab, ← hba, add_zero]
    exact htwo (add_left_cancel he)
  have hSD : S ⊆ D := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_image_of_mem _ (mem_univ _),
      mem_image_of_mem _ (mem_univ _), hne i⟩, hd i⟩
  have hTD : T ⊆ D := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_image_of_mem _ (mem_univ _),
      mem_image_of_mem _ (mem_univ _), (hne i).symm⟩, (dist_comm _ _).trans (hd i)⟩
  have hcard := card_le_card (union_subset hSD hTD)
  rw [card_union_of_disjoint hST, hS, hT] at hcard
  change k ≤ D.card / 2
  omega

private noncomputable def edgeRe (k : ℕ) : ℝ := Real.cos (Real.pi / k)

private theorem card_polygon_reflection_inter (k : ℕ) (hk : 2 ≤ k) (hs : 0 < edgeRe k) :
    ((polygon k) ∩ (polygon k).image (fun z => ((2 * edgeRe k : ℝ) : ℂ) - z)).card = 2 := by
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨k - 1, by omega⟩
  let x := polygonVertex k i
  let y := polygonVertex k j
  let t := Real.pi / (k : ℝ)
  let S : ℂ := ((2 * edgeRe k : ℝ) : ℂ)
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hπ : (k : ℝ) * t = Real.pi := by dsimp [t]; field_simp
  have hx : x = unitCircle t := by simp [x, i, polygonVertex, t]
  have hy : y = unitCircle (2 * Real.pi - t) := by
    change unitCircle ((2 * ((k - 1 : ℕ) : ℝ) + 1) * t) = _
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    congr 1
    nlinarith only [hπ]
  have hxRe : x.re = edgeRe k := by simp [hx, unitCircle_re, t, edgeRe]
  have hyRe : y.re = edgeRe k := by simp [hy, unitCircle_re, Real.cos_two_pi_sub, t, edgeRe]
  have hyIm : y.im = -x.im := by simp [hx, hy, unitCircle_im, Real.sin_two_pi_sub]
  have hxy : x ≠ y := by
    intro h
    have he := congrArg Fin.val (polygonVertex_injective k h)
    dsimp [i, j] at he
    omega
  have hxP : x ∈ polygon k := mem_image_of_mem _ (mem_univ i)
  have hyP : y ∈ polygon k := mem_image_of_mem _ (mem_univ j)
  have hflip : S - x = y := by
    apply Complex.ext
    · simp only [S, Complex.sub_re, Complex.ofReal_re, hxRe, hyRe]
      ring
    · simp [S, hyIm]
  have hflip' : S - y = x := by rw [← hflip]; ring
  change ((polygon k) ∩ (polygon k).image (fun z => S - z)).card = 2
  have hset : (polygon k) ∩ (polygon k).image (fun z => S - z) = {x, y} := by
    ext z
    simp only [mem_inter, mem_image, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hz, w, hw, hwz⟩
      have hwEq : w = S - z := by rw [← hwz]; ring
      have hNz : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, norm_mem_polygon hz, one_pow]
      have hNw : Complex.normSq (S - z) = 1 := by
        rw [← hwEq, Complex.normSq_eq_norm_sq, norm_mem_polygon hw, one_pow]
      have hNx : Complex.normSq x = 1 := by rw [Complex.normSq_eq_norm_sq, norm_mem_polygon hxP, one_pow]
      simp only [Complex.normSq_apply] at hNz hNx
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, S, Complex.ofReal_re,
        Complex.ofReal_im, zero_sub] at hNw
      have hprod : edgeRe k * (z.re - edgeRe k) = 0 := by nlinarith only [hNz, hNw]
      have hzRe : z.re = edgeRe k :=
        sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hs.ne')
      have hprod' : (z.im - x.im) * (z.im + x.im) = 0 := by
        rw [hxRe] at hNx
        rw [hzRe] at hNz
        nlinarith only [hNx, hNz]
      rcases mul_eq_zero.mp hprod' with h | h
      · exact Or.inl (Complex.ext (hzRe.trans hxRe.symm) (sub_eq_zero.mp h))
      · exact Or.inr (Complex.ext (hzRe.trans hyRe.symm) (by rw [hyIm]; linarith only [h]))
    · rintro (rfl | rfl)
      · exact ⟨hxP, y, hyP, hflip'⟩
      · exact ⟨hyP, x, hxP, hflip⟩
  rw [hset, card_insert_of_notMem (by simpa using hxy), card_singleton]

private noncomputable def chainPhase (k : ℕ) : ℝ :=
  2 * ((k / 2 : ℕ) : ℝ) * (Real.pi / k) - Real.pi

private theorem phase_abs_le (k : ℕ) (hk : 0 < k) :
    |chainPhase k| ≤ Real.pi / k := by
  let t := Real.pi / (k : ℝ)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have ht : 0 < t := div_pos Real.pi_pos hkR
  have hπ : (k : ℝ) * t = Real.pi := by dsimp [t]; field_simp
  have hlo : (k : ℝ) ≤ 2 * ((k / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show k ≤ 2 * (k / 2) + 1 by omega)
  have hhi : 2 * ((k / 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast (show 2 * (k / 2) ≤ k by omega)
  change |2 * ((k / 2 : ℕ) : ℝ) * t - Real.pi| ≤ t
  rw [abs_le]
  constructor <;>
    nlinarith only [hπ, mul_le_mul_of_nonneg_right hlo ht.le, mul_le_mul_of_nonneg_right hhi ht.le]

private theorem unitCircle_pi : unitCircle Real.pi = -1 := by
  simp [unitCircle, circleMap_zero, Complex.exp_pi_mul_I]

private theorem phase_rotates_polygon (k : ℕ) (hk : 0 < k) :
    (polygon k).image (fun z => unitCircle (chainPhase k) * z) =
      (polygon k).image Neg.neg := by
  let j : Fin k := ⟨k / 2, by omega⟩
  let a := 2 * ((k / 2 : ℕ) : ℝ) * (Real.pi / k)
  have hphase : unitCircle (chainPhase k) = -(unitCircle a) := by
    change unitCircle (a - Real.pi) = _
    rw [show a - Real.pi = a + Real.pi - 2 * Real.pi by ring,
      unitCircle_sub_period, unitCircle_add, unitCircle_pi]
    ring
  have hshift : (polygon k).image (fun z => unitCircle a * z) = polygon k := by
    apply eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      obtain ⟨i, _, rfl⟩ := mem_image.mp hw
      exact mem_image.mpr ⟨i + j, mem_univ _, polygonVertex_shift k i j⟩
    · have hne : unitCircle a ≠ 0 := by
        intro h
        have hnorm := unitCircle_norm a
        simp [h] at hnorm
      rw [card_image_of_injective _ (mul_right_injective₀ hne)]
  calc
    _ = (polygon k).image (fun z => -(unitCircle a * z)) := by simp [hphase]
    _ = ((polygon k).image (fun z => unitCircle a * z)).image Neg.neg := by rw [image_image]; rfl
    _ = _ := by rw [hshift]

private theorem unitCircle_pow (t : ℝ) (i : ℕ) :
    unitCircle t ^ i = unitCircle ((i : ℝ) * t) := by
  simpa [unitCircle, one_pow] using circleMap_zero_pow i 1 t

private theorem unitCircle_re_gt {t : ℝ} (ht : |t| ≤ Real.pi / 6) :
    3 / 4 < (unitCircle t).re := by
  rw [unitCircle_re]
  have hcos : Real.cos (Real.pi / 6) ≤ Real.cos |t| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) ht
  rw [show Real.cos |t| = Real.cos t by
    by_cases h : 0 ≤ t
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), Real.cos_neg]] at hcos
  have hstrict : 3 / 4 < Real.cos (Real.pi / 6) := by
    rw [Real.cos_pi_div_six]
    have h : (3 / 2 : ℝ) < Real.sqrt 3 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    linarith
  exact hstrict.trans_le hcos

private theorem long_polygon_shift_re {k m : ℕ} (hk : 8 * (m + 1) ≤ k) {i : ℕ} (hi : i ≤ m) :
    1 < (((2 * edgeRe k : ℝ) : ℂ) * unitCircle (chainPhase k) ^ i).re := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  let t := Real.pi / (k : ℝ)
  have ht : 0 < t := div_pos Real.pi_pos hkR
  have hπ : (k : ℝ) * t = Real.pi := by dsimp [t]; field_simp
  have hki : (i : ℝ) ≤ (k : ℝ) / 6 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
    exact_mod_cast (show i * 6 ≤ k by omega)
  have hkt : t ≤ Real.pi / 6 := by
    have hh : (1 : ℝ) ≤ (k : ℝ) / 6 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
      exact_mod_cast (show 1 * 6 ≤ k by omega)
    nlinarith only [mul_le_mul_of_nonneg_right hh ht.le, hπ]
  have hposS : 3 / 4 < edgeRe k := by
    have h := unitCircle_re_gt (show |t| ≤ Real.pi / 6 by rwa [abs_of_pos ht])
    simpa only [unitCircle_re, edgeRe, t] using h
  have hphase : |(i : ℝ) * chainPhase k| ≤ Real.pi / 6 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (i : ℝ))]
    calc
      _ ≤ (i : ℝ) * t := mul_le_mul_of_nonneg_left
        (phase_abs_le k (by omega)) (by positivity)
      _ ≤ (k : ℝ) / 6 * t := mul_le_mul_of_nonneg_right hki ht.le
      _ = _ := by nlinarith only [hπ]
  have hposRot : 3 / 4 < (unitCircle (chainPhase k) ^ i).re := by
    rw [unitCircle_pow]
    exact unitCircle_re_gt hphase
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    1 < 2 * (3 / 4 : ℝ) * (3 / 4 : ℝ) := by norm_num
    _ ≤ _ := by gcongr

private theorem OMA.distanceMultiplicityUnion {X : Type*} [MetricSpace X] [DecidableEq X]
    (A B : Finset X) (d : ℝ) (t : ℕ)
    (hi : (A ∩ B).card = 1 ∨ (A ∩ B).card = 2)
    (hA : A.card + t ≤ distanceMultiplicity A d)
    (hB : B.card ≤ distanceMultiplicity B d) :
    (A ∪ B).card + t + 1 ≤ distanceMultiplicity (A ∪ B) d := by
  classical
  let pairs (S : Finset X) := S.offDiag.filter fun p => dist p.1 p.2 = d
  have hsubset : pairs A ∪ pairs B ⊆ pairs (A ∪ B) := by
    apply Finset.union_subset
    · exact Finset.filter_subset_filter _ (Finset.offDiag_mono Finset.subset_union_left)
    · exact Finset.filter_subset_filter _ (Finset.offDiag_mono Finset.subset_union_right)
  have hinter : pairs A ∩ pairs B ⊆ (A ∩ B).offDiag := by
    intro p hp
    obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hp
    obtain ⟨ha₁, ha₂, hne⟩ := Finset.mem_offDiag.mp (Finset.mem_filter.mp ha).1
    obtain ⟨hb₁, hb₂, _⟩ := Finset.mem_offDiag.mp (Finset.mem_filter.mp hb).1
    exact Finset.mem_offDiag.mpr
      ⟨Finset.mem_inter.mpr ⟨ha₁, hb₁⟩, Finset.mem_inter.mpr ⟨ha₂, hb₂⟩, hne⟩
  have hle := Finset.card_le_card hsubset
  have hleInter := Finset.card_le_card hinter
  rw [Finset.offDiag_card] at hleInter
  have hpoints := Finset.card_union_add_card_inter A B
  have hpairs := Finset.card_union_add_card_inter (pairs A) (pairs B)
  change A.card + t ≤ (pairs A).card / 2 at hA
  change B.card ≤ (pairs B).card / 2 at hB
  change (A ∪ B).card + t + 1 ≤ (pairs (A ∪ B)).card / 2
  rcases hi with hi | hi <;> rw [hi] at hleInter hpoints <;> omega

private noncomputable def planeMove (c q z : ℂ) : ℂ := c + q * z

private theorem planeMove_inj (c : ℂ) {q : ℂ} (hq : ‖q‖ = 1) :
    Function.Injective (planeMove c q) := by
  intro z w he
  have hne : q ≠ 0 := fun h => by simp [h] at hq
  exact mul_left_cancel₀ hne (add_left_cancel he)

private theorem planeMove_dist (c : ℂ) {q : ℂ} (hq : ‖q‖ = 1) (x y : ℂ) :
    dist (planeMove c q x) (planeMove c q y) = dist x y := by
  simp only [dist_eq_norm]
  rw [show planeMove c q x - planeMove c q y = q * (x - y) by unfold planeMove; ring,
    norm_mul, hq, one_mul]

private noncomputable def movedPolygon (k : ℕ) (c q : ℂ) : Finset ℂ :=
  (polygon k).image (planeMove c q)

private theorem card_movedPolygon (k : ℕ) (c : ℂ) {q : ℂ} (hq : ‖q‖ = 1) :
    (movedPolygon k c q).card = k := by
  rw [movedPolygon, card_image_of_injective _ (planeMove_inj c hq), card_polygon]

private theorem norm_of_mem_movedPolygon {k : ℕ} {c q z : ℂ} (hq : ‖q‖ = 1)
    (hz : z ∈ movedPolygon k c q) : ‖z - c‖ = 1 := by
  obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
  rw [planeMove, add_sub_cancel_left, norm_mul, hq, one_mul, norm_mem_polygon hw]

private theorem movedPolygon_multiplicity {k j : ℕ} (hj : 0 < j) (hj' : 2 * j < k)
    (c : ℂ) {q : ℂ} (hq : ‖q‖ = 1) :
    k ≤ distanceMultiplicity (movedPolygon k c q) (chordLength k j) := by
  rw [movedPolygon, polygon, image_image]
  let J : Fin k := ⟨j, by omega⟩
  refine card_two_chord_orientations (by omega) _ ((planeMove_inj c hq).comp
    (polygonVertex_injective k)) J hj hj' _ ?_
  intro i
  change dist (planeMove c q (polygonVertex k i)) (planeMove c q (polygonVertex k (i + J))) = _
  rw [planeMove_dist c hq]
  exact polygon_chord_eq k i J

private noncomputable def chainCenter (k : ℕ) : ℕ → ℂ
  | 0 => 0
  | i + 1 => chainCenter k i + ((2 * edgeRe k : ℝ) : ℂ) * unitCircle (chainPhase k) ^ i

private noncomputable def chainPolygon (k i : ℕ) : Finset ℂ :=
  movedPolygon k (chainCenter k i) (unitCircle (chainPhase k) ^ i)

private theorem chain_unit_rotation (k i : ℕ) : ‖unitCircle (chainPhase k) ^ i‖ = 1 := by
  rw [norm_pow, unitCircle_norm, one_pow]

private theorem chain_consecutive_overlap {k : ℕ} (hk : 2 ≤ k) (hs : 0 < edgeRe k) (i : ℕ) :
    (chainPolygon k i ∩ chainPolygon k (i + 1)).card = 2 := by
  let c := chainCenter k i
  let l := unitCircle (chainPhase k)
  let q := l ^ i
  let S : ℂ := ((2 * edgeRe k : ℝ) : ℂ)
  have hnext : chainPolygon k (i + 1) = ((polygon k).image (fun z => S - z)).image (planeMove c q) := by
    calc
      _ = ((polygon k).image (fun z => l * z)).image (fun z => planeMove c q (S + z)) := by
        unfold chainPolygon movedPolygon
        rw [image_image]
        apply image_congr
        intro z _
        simp only [Function.comp_apply, planeMove, chainCenter, pow_succ]
        dsimp [c, q, l, S]
        ring
      _ = ((polygon k).image Neg.neg).image (fun z => planeMove c q (S + z)) := by
        rw [phase_rotates_polygon k (by omega)]
      _ = _ := by
        rw [image_image, image_image]
        apply image_congr
        intro z _
        simp only [Function.comp_apply, sub_eq_add_neg]
  have hq : ‖q‖ = 1 := chain_unit_rotation k i
  change ((polygon k).image (planeMove c q) ∩ chainPolygon k (i + 1)).card = 2
  rw [hnext, ← image_inter _ _ (planeMove_inj c hq),
    card_image_of_injective _ (planeMove_inj c hq)]
  exact card_polygon_reflection_inter k hk hs

private theorem chain_center_growth {k m : ℕ} (hk : 8 * (m + 1) ≤ k) {i : ℕ} (hi : i ≤ m) :
    (chainCenter k i).re + 1 < (chainCenter k (i + 1)).re := by
  simp only [chainCenter, Complex.add_re]
  linarith only [long_polygon_shift_re hk hi]

private theorem chain_nonconsecutive_disjoint {k m a b : ℕ}
    (hk : 8 * (m + 1) ≤ k) (hab : a + 1 < b) (hb : b ≤ m) :
    Disjoint (chainPolygon k a) (chainPolygon k b) := by
  have hmon (j l : ℕ) (hjl : j ≤ l) (hl : l ≤ m) :
      (chainCenter k j).re ≤ (chainCenter k l).re := by
    induction l with
    | zero =>
      have he : j = 0 := by omega
      simp [he]
    | succ l ih =>
      by_cases he : j = l + 1
      · subst j
        exact le_rfl
      · have h₁ := ih (by omega) (by omega)
        have h₂ := chain_center_growth hk (show l ≤ m by omega)
        linarith only [h₁, h₂]
  have hbound : (chainCenter k a).re + 2 < (chainCenter k b).re := by
    have ha₀ := chain_center_growth hk (show a ≤ m by omega)
    have ha₁ := chain_center_growth hk (show a + 1 ≤ m by omega)
    have ha₂ := hmon (a + 2) b (by omega) hb
    linarith only [ha₀, ha₁, ha₂]
  refine disjoint_left.mpr fun z hza hzb => ?_
  have hclose (i : ℕ) (hzi : z ∈ chainPolygon k i) :
      |z.re - (chainCenter k i).re| ≤ 1 := by
    have hh := Complex.abs_re_le_norm (z - chainCenter k i)
    rwa [norm_of_mem_movedPolygon (chain_unit_rotation k i) hzi, Complex.sub_re] at hh
  have h₁ := (abs_le.mp (hclose a hza)).2
  have h₂ := (abs_le.mp (hclose b hzb)).1
  linarith only [hbound, h₁, h₂]

private noncomputable def chainUnion (k i : ℕ) : Finset ℂ :=
  (range (i + 1)).biUnion (chainPolygon k)

private theorem chainUnion_succ (k i : ℕ) :
    chainUnion k (i + 1) = chainUnion k i ∪ chainPolygon k (i + 1) := by
  rw [chainUnion, range_add_one, biUnion_insert, union_comm]
  rfl

private theorem chainUnion_overlap {k m i : ℕ} (hk : 8 * (m + 1) ≤ k) (hi : i + 1 ≤ m) :
    (chainUnion k i ∩ chainPolygon k (i + 1)).card = 2 := by
  have heq : chainUnion k i ∩ chainPolygon k (i + 1) =
      chainPolygon k i ∩ chainPolygon k (i + 1) := by
    ext z
    simp only [chainUnion, mem_inter, mem_biUnion, mem_range]
    constructor
    · rintro ⟨⟨j, hj, hz⟩, hnext⟩
      by_cases hji : j = i
      · exact ⟨hji ▸ hz, hnext⟩
      · exact ((disjoint_left.mp (chain_nonconsecutive_disjoint hk (by omega) hi)) hz hnext).elim
    · rintro ⟨hz, hnext⟩
      exact ⟨⟨i, by omega, hz⟩, hnext⟩
  rw [heq]
  apply chain_consecutive_overlap (by omega)
  have h := long_polygon_shift_re hk (Nat.zero_le m)
  simp only [pow_zero, mul_one, Complex.ofReal_re] at h
  linarith

private theorem chainUnion_card_multiplicity {k m : ℕ} (hk : 8 * (m + 1) ≤ k) (i : ℕ)
    (hi : i ≤ m) :
    (chainUnion k i).card = k + i * (k - 2) ∧
      ∀ j : ℕ, 0 < j → 2 * j < k →
        (chainUnion k i).card + i ≤ distanceMultiplicity (chainUnion k i) (chordLength k j) := by
  induction i with
  | zero =>
    have heq : chainUnion k 0 = chainPolygon k 0 := by simp [chainUnion]
    have hcard : (chainPolygon k 0).card = k :=
      card_movedPolygon k _ (chain_unit_rotation k 0)
    constructor
    · simp [heq, hcard]
    · intro j hj hj'
      rw [heq, hcard, add_zero]
      exact movedPolygon_multiplicity hj hj' (chainCenter k 0) (chain_unit_rotation k 0)
  | succ i ih =>
    obtain ⟨hcard, hrich⟩ := ih (by omega)
    have h := chainUnion_overlap hk hi
    have hnextCard : (chainPolygon k (i + 1)).card = k :=
      card_movedPolygon k _ (chain_unit_rotation k (i + 1))
    have hsum := card_union_add_card_inter (chainUnion k i) (chainPolygon k (i + 1))
    rw [h, hcard, hnextCard, ← chainUnion_succ] at hsum
    constructor
    · rw [Nat.succ_mul]
      omega
    · intro j hj hj'
      rw [chainUnion_succ]
      have hstep := OMA.distanceMultiplicityUnion _ _ (chordLength k j) i (Or.inr h)
        (hrich j hj hj') (by rw [hnextCard]; exact movedPolygon_multiplicity hj hj' _ (chain_unit_rotation k (i + 1)))
      simpa only [Nat.add_assoc] using hstep

private theorem attach_at_vertex (k : ℕ) (hk : 0 < k) (A : Finset ℂ) (a : ℂ) (ha : a ∈ A) :
    ∃ B : Finset ℂ, B.card = k ∧ (A ∩ B).card = 1 ∧
      ∀ j : ℕ, 0 < j → 2 * j < k → k ≤ distanceMultiplicity B (chordLength k j) := by
  let i : Fin k := ⟨0, hk⟩
  let p := polygonVertex k i
  have hp : p ∈ polygon k := mem_image_of_mem _ (mem_univ i)
  let forbidden := (A.product ((polygon k).erase p)).image (fun xy => (xy.1 - a) / (xy.2 - p))
  have hInterval : (Set.Ioo (0 : ℝ) (2 * Real.pi)).Infinite := Set.Ioo_infinite (by positivity)
  have hInj : (Set.Ioo (0 : ℝ) (2 * Real.pi)).InjOn unitCircle :=
    (injOn_circleMap_of_abs_sub_le' (c := 0) (R := 1) (by norm_num)
      (show 2 * Real.pi - 0 ≤ 2 * Real.pi by simp)).mono Set.Ioo_subset_Ico_self
  obtain ⟨q, hqImage, hqNot⟩ := (hInterval.image hInj).exists_notMem_finset forbidden
  obtain ⟨t, _, ht⟩ := hqImage
  have hqNorm : ‖q‖ = 1 := by rw [← ht]; exact unitCircle_norm t
  let c := a - q * p
  let B := movedPolygon k c q
  have hinter : A ∩ B = {a} := by
    ext x
    simp only [mem_inter, mem_singleton]
    constructor
    · rintro ⟨hx, hxB⟩
      obtain ⟨y, hy, hxy⟩ := mem_image.mp hxB
      by_cases h : y = p
      · rw [h, planeMove] at hxy
        rw [← hxy]
        dsimp [c]
        ring
      · have hturn : q = (x - a) / (y - p) := by
          apply (eq_div_iff (sub_ne_zero.mpr h)).mpr
          rw [← hxy, planeMove]
          dsimp [c]
          ring
        exact (hqNot (mem_image.mpr ⟨(x, y), mem_product.mpr ⟨hx, mem_erase.mpr ⟨h, hy⟩⟩,
          hturn.symm⟩)).elim
    · rintro rfl
      refine ⟨ha, mem_image.mpr ⟨p, hp, ?_⟩⟩
      dsimp [planeMove, c]
      ring
  refine ⟨B, card_movedPolygon k c hqNorm, by simp [hinter], ?_⟩
  intro j hj hj'
  exact movedPolygon_multiplicity hj hj' c hqNorm

private theorem add_single_vertex_polygons (k : ℕ) (hk : 0 < k) (A : Finset ℂ) (a : ℂ) (ha : a ∈ A)
    (t r : ℕ) (hA : ∀ j : ℕ, 0 < j → 2 * j < k →
      A.card + t ≤ distanceMultiplicity A (chordLength k j)) :
    ∃ B : Finset ℂ, a ∈ B ∧ B.card = A.card + r * (k - 1) ∧
      ∀ j : ℕ, 0 < j → 2 * j < k →
        B.card + t + r ≤ distanceMultiplicity B (chordLength k j) := by
  induction r with
  | zero => exact ⟨A, ha, by simp, fun j hj hj' => by simpa using hA j hj hj'⟩
  | succ r ih =>
    obtain ⟨B, haB, hBcard, hB⟩ := ih
    obtain ⟨P, hPk, hBP, hP⟩ := attach_at_vertex k hk B a haB
    refine ⟨B ∪ P, mem_union_left _ haB, ?_, ?_⟩
    · have hcard := card_union_add_card_inter B P
      rw [hBcard, hPk, hBP] at hcard
      rw [Nat.succ_mul]
      omega
    · intro j hj hj'
      have hstep := OMA.distanceMultiplicityUnion B P (chordLength k j) (t + r) (Or.inl hBP)
        (by simpa only [Nat.add_assoc] using hB j hj hj') (by rw [hPk]; exact hP j hj hj')
      simpa only [Nat.add_assoc] using hstep

private theorem le_distanceMultiplicity_map {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (A : Finset X) (d : ℝ) (f : X ↪ Y) (hf : Isometry f) :
    distanceMultiplicity A d ≤ distanceMultiplicity (A.map f) d := by
  unfold distanceMultiplicity
  apply Nat.div_le_div_right
  apply card_le_card_of_injOn (fun p : X × X => (f p.1, f p.2))
  · intro p hp
    obtain ⟨hp, hd⟩ := mem_filter.mp hp
    obtain ⟨h₁, h₂, hne⟩ := mem_offDiag.mp hp
    exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_map_of_mem _ h₁, mem_map_of_mem _ h₂,
      f.injective.ne hne⟩, (hf.dist_eq _ _).trans hd⟩
  · intro x _ y _ h
    exact Prod.ext (f.injective (congrArg Prod.fst h)) (f.injective (congrArg Prod.snd h))

private theorem mem_distanceSet_of_pos {X : Type*} [MetricSpace X] {A : Finset X} {d : ℝ}
    (h : 0 < distanceMultiplicity A d) : d ∈ distanceSet A := by
  unfold distanceMultiplicity at h
  obtain ⟨p, hp⟩ := card_pos.mp (Nat.pos_of_ne_zero (by
    intro e
    rw [e, Nat.zero_div] at h
    omega))
  obtain ⟨hoff, hd⟩ := mem_filter.mp hp
  exact mem_image.mpr ⟨p, hoff, hd⟩

theorem OMA.solution : type_of% @Erdos756.erdos_756.variants.bhowmick_general := by
  intro m hm
  refine Filter.eventually_atTop.mpr ⟨(8 * (m + 1)) * (m + 1) + 2, ?_⟩
  intro n hN
  let k := (n - 2) / (m + 1)
  let r := (n - 2) % (m + 1)
  let e := m - r
  have hr : r < m + 1 := Nat.mod_lt _ (by omega)
  have her : e + r = m := by dsimp [e]; omega
  have hk : 8 * (m + 1) ≤ k := by
    rw [show k = (n - 2) / (m + 1) from rfl, Nat.le_div_iff_mul_le (by omega : 0 < m + 1)]
    omega
  have hdiv : n = (m + 1) * k + 2 + r := by
    have h := Nat.div_add_mod (n - 2) (m + 1)
    change (m + 1) * k + r = n - 2 at h
    omega
  let A := chainUnion (k + 2) e
  have hEdge := chainUnion_card_multiplicity (m := m) (k := k + 2) (by omega) e (by omega)
  have hPosCard : 0 < A.card := by
    change 0 < (chainUnion (k + 2) e).card
    rw [hEdge.1]
    omega
  obtain ⟨a, ha⟩ := card_pos.mp hPosCard
  obtain ⟨B, _, hBcard, hBrich⟩ :=
    add_single_vertex_polygons (k + 2) (by omega) A a ha e r hEdge.2
  have hcard : B.card = n := by
    have hAcard : A.card = k + 2 + e * k := by simpa using hEdge.1
    have hsum : e * k + r * k = m * k := by rw [← add_mul, her]
    have hmK : (m + 1) * k = m * k + k := by ring
    rw [hBcard, hAcard, show k + 2 - 1 = k + 1 by omega, mul_add, mul_one]
    omega
  let E := Complex.orthonormalBasisOneI.repr
  let P := B.map E.toEquiv.toEmbedding
  refine ⟨P, (card_map _).trans hcard, ?_⟩
  let J := Finset.Icc 1 ((k + 1) / 2)
  have hJ {j : ℕ} (hj : j ∈ J) : 0 < j ∧ 2 * j < k + 2 := by
    obtain ⟨h₁, h₂⟩ := mem_Icc.mp hj
    omega
  have hJcard : J.card = (k + 1) / 2 := by
    dsimp [J]
    rw [Nat.card_Icc]
    omega
  have hnum : n / (2 * (m + 1)) ≤ (k + 1) / 2 := by
    rw [Nat.mul_comm 2 (m + 1), ← Nat.div_div_eq_div_mul]
    apply Nat.div_le_div_right
    have hnlt : n < (k + 2) * (m + 1) := by
      have ht : 2 + r < 2 * (m + 1) := by omega
      rw [hdiv, Nat.mul_comm (k + 2) (m + 1), Nat.mul_add]
      omega
    have hle := (Nat.div_lt_iff_lt_mul (by omega : 0 < m + 1)).mpr hnlt
    omega
  have hinj : (J : Set ℕ).InjOn (chordLength (k + 2)) := by
    intro x hx y hy heq
    exact chordLength_inj (by omega) (hJ hx).2 (hJ hy).2 heq
  have hsubset : J.image (chordLength (k + 2)) ⊆ Erdos756.richDistances P (n + m) := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hd
    have hj' := hJ hj
    have hMult : n + m ≤ distanceMultiplicity B (chordLength (k + 2) j) := by
      simpa only [hcard, Nat.add_assoc, her] using hBrich j hj'.1 hj'.2
    have hTransport := le_distanceMultiplicity_map B (chordLength (k + 2) j)
      E.toEquiv.toEmbedding E.isometry
    have hRich : n + m ≤ distanceMultiplicity P (chordLength (k + 2) j) := hMult.trans hTransport
    exact mem_filter.mpr ⟨mem_distanceSet_of_pos (by omega), hRich⟩
  rw [← hJcard] at hnum
  rw [← card_image_of_injOn hinj] at hnum
  exact hnum.trans (card_le_card hsubset)