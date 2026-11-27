import FormalConjectures.Wikipedia.SquarePacking

-- Problem: Packing — seventeen square packing in square bound
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/SquarePacking.lean:132 (declaration SquarePacking.seventeen_square_packing_in_square_bound)
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Explicit rational packing of 17 unit squares into `Square 4.6756`. -/

namespace Sq17Proof

open EuclideanGeometry SquarePacking

def S : ℤ := 2000000

def sqData (i : Fin 17) : ℤ × ℤ × ℤ × ℤ × ℤ :=
  match i.val with
  | 0 => (1, 0, 1, 26, 26)
  | 1 => (1, 0, 1, 2000050, 26)
  | 2 => (1, 0, 1, 26, 2000050)
  | 3 => (1, 0, 1, 26, 7351174)
  | 4 => (1, 0, 1, 7351174, 26)
  | 5 => (1, 0, 1, 5351150, 26)
  | 6 => (1, 0, 1, 7351174, 2000050)
  | 7 => (1, 0, 1, 7351174, 7351174)
  | 8 => (178313, 148584, 232105, 297176037780, 928439178820)
  | 9 => (178313, 148584, 232105, 636908126280, 1245888723110)
  | 10 => (178313, 148584, 232105, 692935952230, 653963875280)
  | 11 => (178313, 148584, 232105, 1032668040730, 971413883780)
  | 12 => (178313, 148584, 232105, 1035781961410, 335395120680)
  | 13 => (178313, 148584, 232105, 1375514049910, 652844664970)
  | 14 => (1, 0, 1, 3694720, 7351174)
  | 15 => (103415, 139128, 173353, 1160815574720, 926737199946)
  | 16 => (1, 0, 1, 7351174, 4226996)
  | _ => (1, 0, 1, 0, 0)

def axisData (k : Fin 12) : ℤ × ℤ × ℤ :=
  match k.val with
  | 0 => (1, 0, 1)
  | 1 => (0, 1, 1)
  | 2 => (178313, 148584, 232105)
  | 3 => (-148584, 178313, 232105)
  | 4 => (103415, 139128, 173353)
  | 5 => (-139128, 103415, 173353)
  | 6 => (-1, 0, 1)
  | 7 => (0, -1, 1)
  | 8 => (-178313, -148584, 232105)
  | 9 => (148584, -178313, 232105)
  | 10 => (-103415, -139128, 173353)
  | 11 => (139128, -103415, 173353)
  | _ => (1, 0, 1)

def sepIdx (i j : Fin 17) : Fin 12 :=
  match i.val, j.val with
  | 0, 1 => 0
  | 0, 2 => 1
  | 0, 3 => 1
  | 0, 4 => 0
  | 0, 5 => 0
  | 0, 6 => 0
  | 0, 7 => 2
  | 0, 8 => 1
  | 0, 9 => 1
  | 0, 10 => 2
  | 0, 11 => 2
  | 0, 12 => 2
  | 0, 13 => 2
  | 0, 14 => 1
  | 0, 15 => 4
  | 0, 16 => 2
  | 1, 2 => 3
  | 1, 3 => 1
  | 1, 4 => 0
  | 1, 5 => 0
  | 1, 6 => 0
  | 1, 7 => 4
  | 1, 8 => 1
  | 1, 9 => 1
  | 1, 10 => 1
  | 1, 11 => 1
  | 1, 12 => 2
  | 1, 13 => 2
  | 1, 14 => 1
  | 1, 15 => 4
  | 1, 16 => 2
  | 2, 3 => 1
  | 2, 4 => 0
  | 2, 5 => 0
  | 2, 6 => 0
  | 2, 7 => 2
  | 2, 8 => 1
  | 2, 9 => 4
  | 2, 10 => 2
  | 2, 11 => 2
  | 2, 12 => 0
  | 2, 13 => 0
  | 2, 14 => 4
  | 2, 15 => 2
  | 2, 16 => 0
  | 3, 4 => 9
  | 3, 5 => 9
  | 3, 6 => 11
  | 3, 7 => 0
  | 3, 8 => 7
  | 3, 9 => 9
  | 3, 10 => 9
  | 3, 11 => 9
  | 3, 12 => 9
  | 3, 13 => 9
  | 3, 14 => 0
  | 3, 15 => 0
  | 3, 16 => 0
  | 4, 5 => 6
  | 4, 6 => 1
  | 4, 7 => 1
  | 4, 8 => 5
  | 4, 9 => 3
  | 4, 10 => 5
  | 4, 11 => 3
  | 4, 12 => 5
  | 4, 13 => 3
  | 4, 14 => 1
  | 4, 15 => 1
  | 4, 16 => 1
  | 5, 6 => 2
  | 5, 7 => 1
  | 5, 8 => 3
  | 5, 9 => 3
  | 5, 10 => 3
  | 5, 11 => 3
  | 5, 12 => 3
  | 5, 13 => 1
  | 5, 14 => 1
  | 5, 15 => 1
  | 5, 16 => 1
  | 6, 7 => 1
  | 6, 8 => 6
  | 6, 9 => 5
  | 6, 10 => 6
  | 6, 11 => 3
  | 6, 12 => 6
  | 6, 13 => 3
  | 6, 14 => 3
  | 6, 15 => 3
  | 6, 16 => 1
  | 7, 8 => 8
  | 7, 9 => 6
  | 7, 10 => 8
  | 7, 11 => 8
  | 7, 12 => 10
  | 7, 13 => 10
  | 7, 14 => 6
  | 7, 15 => 10
  | 7, 16 => 7
  | 8, 9 => 2
  | 8, 10 => 9
  | 8, 11 => 2
  | 8, 12 => 9
  | 8, 13 => 11
  | 8, 14 => 2
  | 8, 15 => 2
  | 8, 16 => 0
  | 9, 10 => 9
  | 9, 11 => 9
  | 9, 12 => 9
  | 9, 13 => 9
  | 9, 14 => 2
  | 9, 15 => 0
  | 9, 16 => 0
  | 10, 11 => 2
  | 10, 12 => 9
  | 10, 13 => 2
  | 10, 14 => 1
  | 10, 15 => 2
  | 10, 16 => 0
  | 11, 12 => 9
  | 11, 13 => 9
  | 11, 14 => 1
  | 11, 15 => 2
  | 11, 16 => 0
  | 12, 13 => 2
  | 12, 14 => 1
  | 12, 15 => 4
  | 12, 16 => 2
  | 13, 14 => 1
  | 13, 15 => 4
  | 13, 16 => 2
  | 14, 15 => 11
  | 14, 16 => 11
  | 15, 16 => 11
  | _, _ => 0

def insideCheck (i : Fin 17) : Bool :=
  let (cn, sn, d, x0n, y0n) := sqData i
  decide (0 < d) &&
  decide (0 ≤ x0n + S * min cn 0 + S * min (-sn) 0) &&
  decide (10000 * (x0n + S * max cn 0 + S * max (-sn) 0) ≤ 46756 * (S * d)) &&
  decide (0 ≤ y0n + S * min sn 0 + S * min cn 0) &&
  decide (10000 * (y0n + S * max sn 0 + S * max cn 0) ≤ 46756 * (S * d))

def sepCheck (i j : Fin 17) : Bool :=
  let (ci, si, di, x0i, y0i) := sqData i
  let (cj, sj, dj, x0j, y0j) := sqData j
  let (nx, ny, dk) := axisData (sepIdx i j)
  let ai := nx * ci + ny * si
  let bi := -nx * si + ny * ci
  let aj := nx * cj + ny * sj
  let bj := -nx * sj + ny * cj
  decide (0 < dk) &&
  decide (dj * (nx * x0i + ny * y0i + S * max ai 0 + S * max bi 0) ≤
          di * (nx * x0j + ny * y0j + S * min aj 0 + S * min bj 0))

lemma sqData_unit : ∀ i : Fin 17, (sqData i).1 ^ 2 + (sqData i).2.1 ^ 2 = (sqData i).2.2.1 ^ 2 := by
  decide

lemma axisData_unit : ∀ k : Fin 12, (axisData k).1 ^ 2 + (axisData k).2.1 ^ 2 = (axisData k).2.2 ^ 2 := by
  decide

lemma insideCheck_all : ∀ i : Fin 17, insideCheck i = true := by
  decide

lemma sepCheck_all : ∀ i j : Fin 17, i < j → sepCheck i j = true := by
  decide

noncomputable def mkSqIso (c s x0 y0 : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) : ℝ² ≃ᵢ ℝ² where
  toFun p := !₂[x0 + c * p 0 - s * p 1, y0 + s * p 0 + c * p 1]
  invFun q := !₂[c * (q 0 - x0) + s * (q 1 - y0), -s * (q 0 - x0) + c * (q 1 - y0)]
  left_inv p := by
    ext i
    fin_cases i
    · dsimp
      linear_combination (p 0) * hcs
    · dsimp
      linear_combination (p 1) * hcs
  right_inv q := by
    ext i
    fin_cases i
    · dsimp
      linear_combination (q 0 - x0) * hcs
    · dsimp
      linear_combination (q 1 - y0) * hcs
  isometry_toFun := by
    refine Isometry.of_dist_eq fun x y => ?_
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    congr 1
    simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.dist_eq, sq_abs]
    linear_combination ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) * hcs

lemma dot_lt_max_of_unitSquare {A B u v : ℝ} (hAB : A ≠ 0 ∨ B ≠ 0)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) :
    A * u + B * v < max A 0 + max B 0 := by
  have hAle : A * u ≤ max A 0 := by
    rcases le_total A 0 with h | h
    · exact (mul_nonpos_of_nonpos_of_nonneg h hu0.le).trans (le_max_right _ _)
    · exact (mul_le_of_le_one_right h hu1.le).trans (le_max_left _ _)
  have hBle : B * v ≤ max B 0 := by
    rcases le_total B 0 with h | h
    · exact (mul_nonpos_of_nonpos_of_nonneg h hv0.le).trans (le_max_right _ _)
    · exact (mul_le_of_le_one_right h hv1.le).trans (le_max_left _ _)
  rcases hAB with hA | hB
  · have hAlt : A * u < max A 0 := by
      rcases lt_or_gt_of_ne hA with h | h
      · exact (mul_neg_of_neg_of_pos h hu0).trans_le (le_max_right _ _)
      · exact (mul_lt_of_lt_one_right h hu1).trans_le (le_max_left _ _)
    linarith
  · have hBlt : B * v < max B 0 := by
      rcases lt_or_gt_of_ne hB with h | h
      · exact (mul_neg_of_neg_of_pos h hv0).trans_le (le_max_right _ _)
      · exact (mul_lt_of_lt_one_right h hv1).trans_le (le_max_left _ _)
    linarith

lemma min_lt_dot_of_unitSquare {A B u v : ℝ} (hAB : A ≠ 0 ∨ B ≠ 0)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) :
    min A 0 + min B 0 < A * u + B * v := by
  have hneg : -A ≠ 0 ∨ -B ≠ 0 := by
    rcases hAB with h | h
    · exact Or.inl (neg_ne_zero.mpr h)
    · exact Or.inr (neg_ne_zero.mpr h)
  have h := dot_lt_max_of_unitSquare hneg hu0 hu1 hv0 hv1
  have h1 : max (-A) 0 = - min A 0 := by
    rcases le_total A 0 with ha | ha <;> simp [ha]
  have h2 : max (-B) 0 = - min B 0 := by
    rcases le_total B 0 with hb | hb <;> simp [hb]
  linarith

lemma ne_zero_or_of_sq_add_sq_eq_one {A B : ℝ} (h : A ^ 2 + B ^ 2 = 1) : A ≠ 0 ∨ B ≠ 0 := by
  by_contra hc
  simp only [not_or, not_not] at hc
  rcases hc with ⟨rfl, rfl⟩
  norm_num at h

lemma int_min_div {a d : ℝ} (hd : 0 < d) : min (a / d) 0 = min a 0 / d := by
  rcases le_total a 0 with h | h
  · have hd0 : a / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hd.le
    rw [min_eq_left hd0, min_eq_left h]
  · have hd0 : 0 ≤ a / d := div_nonneg h hd.le
    rw [min_eq_right hd0, min_eq_right h, zero_div]

lemma int_max_div {a d : ℝ} (hd : 0 < d) : max (a / d) 0 = max a 0 / d := by
  rcases le_total a 0 with h | h
  · have hd0 : a / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hd.le
    rw [max_eq_right hd0, max_eq_right h, zero_div]
  · have hd0 : 0 ≤ a / d := div_nonneg h hd.le
    rw [max_eq_left hd0, max_eq_left h]

noncomputable def sqC (i : Fin 17) : ℝ := (sqData i).1 / (sqData i).2.2.1
noncomputable def sqS (i : Fin 17) : ℝ := (sqData i).2.1 / (sqData i).2.2.1
noncomputable def sqX0 (i : Fin 17) : ℝ := (sqData i).2.2.2.1 / ((S : ℝ) * (sqData i).2.2.1)
noncomputable def sqY0 (i : Fin 17) : ℝ := (sqData i).2.2.2.2 / ((S : ℝ) * (sqData i).2.2.1)

lemma sqD_pos (i : Fin 17) : (0 : ℝ) < (sqData i).2.2.1 := by
  have h := insideCheck_all i
  simp only [insideCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact_mod_cast h.1.1.1.1

lemma sq_cs (i : Fin 17) : sqC i ^ 2 + sqS i ^ 2 = 1 := by
  have hd : ((sqData i).2.2.1 : ℝ) ≠ 0 := (sqD_pos i).ne'
  have hu : ((sqData i).1 : ℝ) ^ 2 + ((sqData i).2.1 : ℝ) ^ 2 = ((sqData i).2.2.1 : ℝ) ^ 2 := by
    exact_mod_cast sqData_unit i
  dsimp [sqC, sqS]
  field_simp
  exact hu

noncomputable def embed (i : Fin 17) : ℝ² ≃ᵢ ℝ² :=
  mkSqIso (sqC i) (sqS i) (sqX0 i) (sqY0 i) (sq_cs i)

lemma embed_inside (i : Fin 17) : embed i '' UnitSquare ⊆ Square 4.6756 := by
  have hchk := insideCheck_all i
  simp only [insideCheck, Bool.and_eq_true, decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨hd, hx0⟩, hx1⟩, hy0⟩, hy1⟩
  have hd_r : (0 : ℝ) < (sqData i).2.2.1 := by exact_mod_cast hd
  have hS_r : (0 : ℝ) < (S : ℝ) := by norm_num [S]
  have hSd_r : (0 : ℝ) < (S : ℝ) * (sqData i).2.2.1 := mul_pos hS_r hd_r
  have hx0i : (0 : ℝ) ≤ ((sqData i).2.2.2.1 : ℝ) + (S : ℝ) * min ((sqData i).1 : ℝ) 0 +
      (S : ℝ) * min (-((sqData i).2.1 : ℝ)) 0 := by exact_mod_cast hx0
  have hx1i : 10000 * (((sqData i).2.2.2.1 : ℝ) + (S : ℝ) * max ((sqData i).1 : ℝ) 0 +
      (S : ℝ) * max (-((sqData i).2.1 : ℝ)) 0) ≤ 46756 * ((S : ℝ) * (sqData i).2.2.1) := by
    exact_mod_cast hx1
  have hy0i : (0 : ℝ) ≤ ((sqData i).2.2.2.2 : ℝ) + (S : ℝ) * min ((sqData i).2.1 : ℝ) 0 +
      (S : ℝ) * min ((sqData i).1 : ℝ) 0 := by exact_mod_cast hy0
  have hy1i : 10000 * (((sqData i).2.2.2.2 : ℝ) + (S : ℝ) * max ((sqData i).2.1 : ℝ) 0 +
      (S : ℝ) * max ((sqData i).1 : ℝ) 0) ≤ 46756 * ((S : ℝ) * (sqData i).2.2.1) := by
    exact_mod_cast hy1
  have hx0r : 0 ≤ sqX0 i + min (sqC i) 0 + min (-sqS i) 0 := by
    dsimp [sqX0, sqC, sqS]
    rw [← neg_div, int_min_div hd_r, int_min_div hd_r]
    rw [show ((sqData i).2.2.2.1 : ℝ) / ((S : ℝ) * (sqData i).2.2.1) +
        min ((sqData i).1 : ℝ) 0 / (sqData i).2.2.1 +
        min (-((sqData i).2.1 : ℝ)) 0 / (sqData i).2.2.1 =
        (((sqData i).2.2.2.1 : ℝ) + (S : ℝ) * min ((sqData i).1 : ℝ) 0 +
          (S : ℝ) * min (-((sqData i).2.1 : ℝ)) 0) / ((S : ℝ) * (sqData i).2.2.1) by
      field_simp]
    exact div_nonneg hx0i hSd_r.le
  have hx1r : sqX0 i + max (sqC i) 0 + max (-sqS i) 0 ≤ 4.6756 := by
    dsimp [sqX0, sqC, sqS]
    rw [← neg_div, int_max_div hd_r, int_max_div hd_r]
    rw [show ((sqData i).2.2.2.1 : ℝ) / ((S : ℝ) * (sqData i).2.2.1) +
        max ((sqData i).1 : ℝ) 0 / (sqData i).2.2.1 +
        max (-((sqData i).2.1 : ℝ)) 0 / (sqData i).2.2.1 =
        (((sqData i).2.2.2.1 : ℝ) + (S : ℝ) * max ((sqData i).1 : ℝ) 0 +
          (S : ℝ) * max (-((sqData i).2.1 : ℝ)) 0) / ((S : ℝ) * (sqData i).2.2.1) by
      field_simp]
    rw [div_le_iff₀ hSd_r]
    linarith
  have hy0r : 0 ≤ sqY0 i + min (sqS i) 0 + min (sqC i) 0 := by
    dsimp [sqY0, sqS, sqC]
    rw [int_min_div hd_r, int_min_div hd_r]
    rw [show ((sqData i).2.2.2.2 : ℝ) / ((S : ℝ) * (sqData i).2.2.1) +
        min ((sqData i).2.1 : ℝ) 0 / (sqData i).2.2.1 +
        min ((sqData i).1 : ℝ) 0 / (sqData i).2.2.1 =
        (((sqData i).2.2.2.2 : ℝ) + (S : ℝ) * min ((sqData i).2.1 : ℝ) 0 +
          (S : ℝ) * min ((sqData i).1 : ℝ) 0) / ((S : ℝ) * (sqData i).2.2.1) by
      field_simp]
    exact div_nonneg hy0i hSd_r.le
  have hy1r : sqY0 i + max (sqS i) 0 + max (sqC i) 0 ≤ 4.6756 := by
    dsimp [sqY0, sqS, sqC]
    rw [int_max_div hd_r, int_max_div hd_r]
    rw [show ((sqData i).2.2.2.2 : ℝ) / ((S : ℝ) * (sqData i).2.2.1) +
        max ((sqData i).2.1 : ℝ) 0 / (sqData i).2.2.1 +
        max ((sqData i).1 : ℝ) 0 / (sqData i).2.2.1 =
        (((sqData i).2.2.2.2 : ℝ) + (S : ℝ) * max ((sqData i).2.1 : ℝ) 0 +
          (S : ℝ) * max ((sqData i).1 : ℝ) 0) / ((S : ℝ) * (sqData i).2.2.1) by
      field_simp]
    rw [div_le_iff₀ hSd_r]
    linarith
  have hcs := sq_cs i
  have hcs1 : sqC i ≠ 0 ∨ -sqS i ≠ 0 := by
    refine ne_zero_or_of_sq_add_sq_eq_one ?_; nlinarith
  have hcs2 : sqS i ≠ 0 ∨ sqC i ≠ 0 := by
    refine ne_zero_or_of_sq_add_sq_eq_one ?_; nlinarith
  rintro q ⟨p, hp, rfl⟩
  rcases hp with ⟨hp00, hp01, hp10, hp11⟩
  have hminx := min_lt_dot_of_unitSquare hcs1 hp00 hp01 hp10 hp11
  have hmaxx := dot_lt_max_of_unitSquare hcs1 hp00 hp01 hp10 hp11
  have hminy := min_lt_dot_of_unitSquare hcs2 hp00 hp01 hp10 hp11
  have hmaxy := dot_lt_max_of_unitSquare hcs2 hp00 hp01 hp10 hp11
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [embed, mkSqIso]; linarith
  · dsimp [embed, mkSqIso]; linarith
  · dsimp [embed, mkSqIso]; linarith
  · dsimp [embed, mkSqIso]; linarith

lemma embed_disjoint_lt {i j : Fin 17} (hij : i < j) :
    Disjoint (embed i '' UnitSquare) (embed j '' UnitSquare) := by
  have hsep := sepCheck_all i j hij
  simp only [sepCheck, Bool.and_eq_true, decide_eq_true_eq] at hsep
  rcases hsep with ⟨hdk, hle⟩
  let k := sepIdx i j
  have hdk_r : (0 : ℝ) < (axisData k).2.2 := by exact_mod_cast hdk
  have hdi_r : (0 : ℝ) < (sqData i).2.2.1 := sqD_pos i
  have hdj_r : (0 : ℝ) < (sqData j).2.2.1 := sqD_pos j
  have hS_r : (0 : ℝ) < (S : ℝ) := by norm_num [S]
  have hax_u : ((axisData k).1 : ℝ) ^ 2 + ((axisData k).2.1 : ℝ) ^ 2 = ((axisData k).2.2 : ℝ) ^ 2 := by
    exact_mod_cast axisData_unit k
  set nx : ℝ := ((axisData k).1 : ℝ) / ((axisData k).2.2 : ℝ)
  set ny : ℝ := ((axisData k).2.1 : ℝ) / ((axisData k).2.2 : ℝ)
  have hax : nx ^ 2 + ny ^ 2 = 1 := by
    dsimp [nx, ny]
    have hne : ((axisData k).2.2 : ℝ) ≠ 0 := hdk_r.ne'
    field_simp
    exact hax_u
  set ai : ℝ := nx * sqC i + ny * sqS i
  set bi : ℝ := -nx * sqS i + ny * sqC i
  set aj : ℝ := nx * sqC j + ny * sqS j
  set bj : ℝ := -nx * sqS j + ny * sqC j
  have hai : ai ^ 2 + bi ^ 2 = 1 := by
    dsimp [ai, bi]
    linear_combination (nx ^ 2 + ny ^ 2) * sq_cs i + hax
  have haj : aj ^ 2 + bj ^ 2 = 1 := by
    dsimp [aj, bj]
    linear_combination (nx ^ 2 + ny ^ 2) * sq_cs j + hax
  have hle_r : ((sqData j).2.2.1 : ℝ) * (((axisData k).1 : ℝ) * (sqData i).2.2.2.1 +
      ((axisData k).2.1 : ℝ) * (sqData i).2.2.2.2 +
      (S : ℝ) * max (((axisData k).1 : ℝ) * (sqData i).1 + ((axisData k).2.1 : ℝ) * (sqData i).2.1) 0 +
      (S : ℝ) * max (-((axisData k).1 : ℝ) * (sqData i).2.1 + ((axisData k).2.1 : ℝ) * (sqData i).1) 0) ≤
      ((sqData i).2.2.1 : ℝ) * (((axisData k).1 : ℝ) * (sqData j).2.2.2.1 +
      ((axisData k).2.1 : ℝ) * (sqData j).2.2.2.2 +
      (S : ℝ) * min (((axisData k).1 : ℝ) * (sqData j).1 + ((axisData k).2.1 : ℝ) * (sqData j).2.1) 0 +
      (S : ℝ) * min (-((axisData k).1 : ℝ) * (sqData j).2.1 + ((axisData k).2.1 : ℝ) * (sqData j).1) 0) := by
    exact_mod_cast hle
  have hdki_pos : (0 : ℝ) < (axisData k).2.2 * (sqData i).2.2.1 := mul_pos hdk_r hdi_r
  have hdkj_pos : (0 : ℝ) < (axisData k).2.2 * (sqData j).2.2.1 := mul_pos hdk_r hdj_r
  have hai_eq : ai = (((axisData k).1 : ℝ) * (sqData i).1 + ((axisData k).2.1 : ℝ) * (sqData i).2.1) /
      (((axisData k).2.2 : ℝ) * (sqData i).2.2.1) := by
    dsimp [ai, nx, ny, sqC, sqS]; field_simp
  have hbi_eq : bi = (-((axisData k).1 : ℝ) * (sqData i).2.1 + ((axisData k).2.1 : ℝ) * (sqData i).1) /
      (((axisData k).2.2 : ℝ) * (sqData i).2.2.1) := by
    dsimp [bi, nx, ny, sqC, sqS]; field_simp
  have haj_eq : aj = (((axisData k).1 : ℝ) * (sqData j).1 + ((axisData k).2.1 : ℝ) * (sqData j).2.1) /
      (((axisData k).2.2 : ℝ) * (sqData j).2.2.1) := by
    dsimp [aj, nx, ny, sqC, sqS]; field_simp
  have hbj_eq : bj = (-((axisData k).1 : ℝ) * (sqData j).2.1 + ((axisData k).2.1 : ℝ) * (sqData j).1) /
      (((axisData k).2.2 : ℝ) * (sqData j).2.2.1) := by
    dsimp [bj, nx, ny, sqC, sqS]; field_simp
  have hsep_r : nx * sqX0 i + ny * sqY0 i + max ai 0 + max bi 0 ≤
      nx * sqX0 j + ny * sqY0 j + min aj 0 + min bj 0 := by
    rw [hai_eq, hbi_eq, haj_eq, hbj_eq,
      int_max_div hdki_pos, int_max_div hdki_pos,
      int_min_div hdkj_pos, int_min_div hdkj_pos]
    have hden_pos : (0 : ℝ) < (S : ℝ) * ((axisData k).2.2 : ℝ) * (sqData i).2.2.1 * (sqData j).2.2.1 := by
      positivity
    have hL : nx * sqX0 i + ny * sqY0 i +
        max (((axisData k).1 : ℝ) * (sqData i).1 + ((axisData k).2.1 : ℝ) * (sqData i).2.1) 0 /
          (((axisData k).2.2 : ℝ) * (sqData i).2.2.1) +
        max (-((axisData k).1 : ℝ) * (sqData i).2.1 + ((axisData k).2.1 : ℝ) * (sqData i).1) 0 /
          (((axisData k).2.2 : ℝ) * (sqData i).2.2.1) =
        (((sqData j).2.2.1 : ℝ) * (((axisData k).1 : ℝ) * (sqData i).2.2.2.1 +
          ((axisData k).2.1 : ℝ) * (sqData i).2.2.2.2 +
          (S : ℝ) * max (((axisData k).1 : ℝ) * (sqData i).1 + ((axisData k).2.1 : ℝ) * (sqData i).2.1) 0 +
          (S : ℝ) * max (-((axisData k).1 : ℝ) * (sqData i).2.1 + ((axisData k).2.1 : ℝ) * (sqData i).1) 0)) /
          ((S : ℝ) * ((axisData k).2.2 : ℝ) * (sqData i).2.2.1 * (sqData j).2.2.1) := by
      dsimp [nx, ny, sqX0, sqY0]
      have hne1 : ((sqData i).2.2.1 : ℝ) ≠ 0 := hdi_r.ne'
      have hne2 : ((sqData j).2.2.1 : ℝ) ≠ 0 := hdj_r.ne'
      have hne3 : ((axisData k).2.2 : ℝ) ≠ 0 := hdk_r.ne'
      have hne4 : (S : ℝ) ≠ 0 := hS_r.ne'
      field_simp
    have hR : nx * sqX0 j + ny * sqY0 j +
        min (((axisData k).1 : ℝ) * (sqData j).1 + ((axisData k).2.1 : ℝ) * (sqData j).2.1) 0 /
          (((axisData k).2.2 : ℝ) * (sqData j).2.2.1) +
        min (-((axisData k).1 : ℝ) * (sqData j).2.1 + ((axisData k).2.1 : ℝ) * (sqData j).1) 0 /
          (((axisData k).2.2 : ℝ) * (sqData j).2.2.1) =
        (((sqData i).2.2.1 : ℝ) * (((axisData k).1 : ℝ) * (sqData j).2.2.2.1 +
          ((axisData k).2.1 : ℝ) * (sqData j).2.2.2.2 +
          (S : ℝ) * min (((axisData k).1 : ℝ) * (sqData j).1 + ((axisData k).2.1 : ℝ) * (sqData j).2.1) 0 +
          (S : ℝ) * min (-((axisData k).1 : ℝ) * (sqData j).2.1 + ((axisData k).2.1 : ℝ) * (sqData j).1) 0)) /
          ((S : ℝ) * ((axisData k).2.2 : ℝ) * (sqData i).2.2.1 * (sqData j).2.2.1) := by
      dsimp [nx, ny, sqX0, sqY0]
      have hne1 : ((sqData i).2.2.1 : ℝ) ≠ 0 := hdi_r.ne'
      have hne2 : ((sqData j).2.2.1 : ℝ) ≠ 0 := hdj_r.ne'
      have hne3 : ((axisData k).2.2 : ℝ) ≠ 0 := hdk_r.ne'
      have hne4 : (S : ℝ) ≠ 0 := hS_r.ne'
      field_simp
    rw [hL, hR]
    exact div_le_div_of_nonneg_right hle_r hden_pos.le
  rw [Set.disjoint_left]
  rintro z ⟨p, hp, hzp⟩ ⟨q, hq, hzq⟩
  rcases hp with ⟨hp00, hp01, hp10, hp11⟩
  rcases hq with ⟨hq00, hq01, hq10, hq11⟩
  have hpi := dot_lt_max_of_unitSquare (ne_zero_or_of_sq_add_sq_eq_one hai) hp00 hp01 hp10 hp11
  have hqj := min_lt_dot_of_unitSquare (ne_zero_or_of_sq_add_sq_eq_one haj) hq00 hq01 hq10 hq11
  have hz0i : z 0 = sqX0 i + sqC i * p 0 - sqS i * p 1 := by rw [← hzp]; rfl
  have hz1i : z 1 = sqY0 i + sqS i * p 0 + sqC i * p 1 := by rw [← hzp]; rfl
  have hz0j : z 0 = sqX0 j + sqC j * q 0 - sqS j * q 1 := by rw [← hzq]; rfl
  have hz1j : z 1 = sqY0 j + sqS j * q 0 + sqC j * q 1 := by rw [← hzq]; rfl
  have hi_eq : nx * z 0 + ny * z 1 = nx * sqX0 i + ny * sqY0 i + (ai * p 0 + bi * p 1) := by
    rw [hz0i, hz1i]; dsimp [ai, bi]; ring
  have hj_eq : nx * z 0 + ny * z 1 = nx * sqX0 j + ny * sqY0 j + (aj * q 0 + bj * q 1) := by
    rw [hz0j, hz1j]; dsimp [aj, bj]; ring
  linarith

end Sq17Proof

theorem OMA.solution : type_of% @SquarePacking.seventeen_square_packing_in_square_bound := by
  refine ⟨⟨Sq17Proof.embed, ?_, Sq17Proof.embed_inside⟩⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact Sq17Proof.embed_disjoint_lt h
  · exact (Sq17Proof.embed_disjoint_lt h).symm
