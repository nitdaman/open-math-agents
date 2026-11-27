import FormalConjectures.Arxiv.«2607.27197».MaxwellConjecture

open Matrix
open Arxiv.«2607.27197»
open scoped Gradient

namespace MaxwellScratch

abbrev E := EuclideanSpace ℝ (Fin 3)

private noncomputable abbrev coord (i : Fin 3) : E →L[ℝ] ℝ :=
  EuclideanSpace.proj i

private theorem coord_apply (i : Fin 3) (p : E) : coord i p = p.ofLp i := rfl

private theorem fderiv_phi (p v : E) :
    let x := p.ofLp 0
    let y := p.ofLp 1
    let z := p.ofLp 2
    let H := 5 + 36 * (x ^ 2 + y ^ 2) - 144 * z ^ 2
    16 * fderiv ℝ phiZero p v =
      (x * H + 90 * (x ^ 2 - y ^ 2)) * v.ofLp 0 +
      (y * (H - 180 * x)) * v.ofLp 1 +
      (z * (-10 - 144 * (x ^ 2 + y ^ 2) + 96 * z ^ 2)) * v.ofLp 2 := by
  change 16 * fderiv ℝ (fun q : E =>
      5 / 32 * ((coord 0 q ^ 2 + coord 1 q ^ 2) - 2 * coord 2 q ^ 2) +
      15 / 8 * (coord 0 q ^ 3 - 3 * coord 0 q * coord 1 q ^ 2) +
      3 / 16 * (3 * (coord 0 q ^ 2 + coord 1 q ^ 2) ^ 2 -
        24 * (coord 0 q ^ 2 + coord 1 q ^ 2) * coord 2 q ^ 2 +
        8 * coord 2 q ^ 4)) p v = _
  simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul, fderiv_const_apply, ContinuousLinearMap.zero_apply,
    fderiv_fun_pow, ContinuousLinearMap.fderiv, _root_.add_apply,
    _root_.sub_apply, _root_.smul_apply, smul_eq_mul]
  simp only [coord_apply]
  ring

theorem critical_iff (p : E) :
    ∇ phiZero p = 0 ↔
      let x := p.ofLp 0
      let y := p.ofLp 1
      let z := p.ofLp 2
      let H := 5 + 36 * (x ^ 2 + y ^ 2) - 144 * z ^ 2
      x * H + 90 * (x ^ 2 - y ^ 2) = 0 ∧
      y * (H - 180 * x) = 0 ∧
      z * (-10 - 144 * (x ^ 2 + y ^ 2) + 96 * z ^ 2) = 0 := by
  have hgrad : ∇ phiZero p = 0 ↔ fderiv ℝ phiZero p = 0 := by
    rw [← toDual_gradient]
    exact (InnerProductSpace.toDual ℝ E).map_eq_zero_iff.symm
  rw [hgrad]
  constructor
  · intro h
    have atVec (v : E) := fderiv_phi p v
    simp only [h, ContinuousLinearMap.zero_apply, mul_zero] at atVec
    exact ⟨by simpa using (atVec (WithLp.toLp 2 ![1, 0, 0])).symm,
      by simpa using (atVec (WithLp.toLp 2 ![0, 1, 0])).symm,
      by simpa using (atVec (WithLp.toLp 2 ![0, 0, 1])).symm⟩
  · dsimp only
    rintro ⟨hx, hy, hz⟩
    ext v
    have heq := fderiv_phi p v
    dsimp only at heq
    rw [hx, hy, hz] at heq
    simpa using heq

noncomputable def hessianMatrix (p : E) : Matrix (Fin 3) (Fin 3) ℝ :=
  let x := p.ofLp 0
  let y := p.ofLp 1
  let z := p.ofLp 2
  let H := 5 + 36 * (x ^ 2 + y ^ 2) - 144 * z ^ 2
  let a := H + 72 * x ^ 2 + 180 * x
  let b := 72 * x * y - 180 * y
  let c := -288 * x * z
  let d := H + 72 * y ^ 2 - 180 * x
  let e := -288 * y * z
  let f := -10 - 144 * (x ^ 2 + y ^ 2) + 288 * z ^ 2
  !![a, b, c; b, d, e; c, e, f]

private theorem fderiv_smul_coord (f : E → ℝ) (p v w : E) (i : Fin 3)
    (hf : DifferentiableAt ℝ f p) :
    fderiv ℝ (fun q => f q • coord i) p v w = fderiv ℝ f p v * coord i w := by
  rw [fderiv_fun_smul hf (differentiableAt_const (coord i)), fderiv_const_apply, smul_zero, zero_add,
    ContinuousLinearMap.smulRight_apply, _root_.smul_apply, smul_eq_mul]

private theorem second_derivative (p v w : E) :
    16 * iteratedFDeriv ℝ 2 phiZero p ![v, w] =
      w.ofLp ⬝ᵥ (hessianMatrix p *ᵥ v.ofLp) := by
  have heq : fderiv ℝ phiZero = fun q : E =>
      let x := coord 0 q
      let y := coord 1 q
      let z := coord 2 q
      let H := 5 + 36 * (x ^ 2 + y ^ 2) - 144 * z ^ 2
      ((x * H + 90 * (x ^ 2 - y ^ 2)) / 16) • coord 0 +
      ((y * (H - 180 * x)) / 16) • coord 1 +
      ((z * (-10 - 144 * (x ^ 2 + y ^ 2) + 96 * z ^ 2)) / 16) • coord 2 := by
    funext q
    ext u
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    have h := fderiv_phi q u
    dsimp only at h ⊢
    simp only [coord_apply]
    linear_combination h / 16
  rw [iteratedFDeriv_two_apply, heq]
  simp only [div_eq_mul_inv]
  simp (disch := fun_prop) only [Matrix.cons_val_zero, Matrix.cons_val_one,
    fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul, fderiv_fun_pow, fderiv_smul_coord,
    fderiv_const_apply, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.smulRight_apply,
    _root_.add_apply, _root_.sub_apply, _root_.smul_apply, smul_eq_mul, zero_add, add_zero, smul_zero,
    hessianMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons]
  simp only [coord_apply]
  ring


def radial (x y z : ℝ) : ℝ := 5 + 36 * (x ^ 2 + y ^ 2) - 144 * z ^ 2

def stationary (x y z : ℝ) : Prop :=
  x * radial x y z + 90 * (x ^ 2 - y ^ 2) = 0 ∧
  y * (radial x y z - 180 * x) = 0 ∧
  z * (-10 - 144 * (x ^ 2 + y ^ 2) + 96 * z ^ 2) = 0

def direction (s x y : ℝ) : Prop :=
  (x = s ∧ y = 0) ∨ (x = -s / 2 ∧ y ^ 2 = 3 * s ^ 2 / 4)

theorem radial_classification {x y z : ℝ} (h : stationary x y z) :
    (x = 0 ∧ y = 0 ∧ (z = 0 ∨ z ^ 2 = 5 / 48)) ∨
    ∃ s ≠ 0, direction s x y ∧
      ((z = 0 ∧ 36 * s ^ 2 + 90 * s + 5 = 0) ∨
        (z ^ 2 = 5 / 48 + 3 / 2 * s ^ 2 ∧ (s = 1 / 6 ∨ s = 1 / 3))) := by
  rcases h with ⟨hx, hy, hz⟩
  have hreduce (s : ℝ) (hs : s ≠ 0) (hdir : direction s x y)
      (hr : x ^ 2 + y ^ 2 = s ^ 2) (hlin : radial x y z + 90 * s = 0) :
      ∃ s ≠ 0, direction s x y ∧
        ((z = 0 ∧ 36 * s ^ 2 + 90 * s + 5 = 0) ∨
          (z ^ 2 = 5 / 48 + 3 / 2 * s ^ 2 ∧ (s = 1 / 6 ∨ s = 1 / 3))) := by
    refine ⟨s, hs, hdir, ?_⟩
    rw [radial, hr] at hlin
    rcases mul_eq_zero.mp hz with hz0 | hzn
    · exact Or.inl ⟨hz0, by rw [hz0] at hlin; linarith⟩
    · rw [hr] at hzn
      have hzsq : z ^ 2 = 5 / 48 + 3 / 2 * s ^ 2 := by linarith
      have hprod : (s - 1 / 6) * (s - 1 / 3) = 0 := by
        linear_combination (hlin + 144 * hzsq) * (-1 / 180)
      exact Or.inr ⟨hzsq, (mul_eq_zero.mp hprod).imp (by intro h; linarith)
        (by intro h; linarith)⟩
  by_cases hy0 : y = 0
  · subst y
    by_cases hx0 : x = 0
    · subst x
      refine Or.inl ⟨rfl, rfl, (mul_eq_zero.mp hz).imp id ?_⟩
      intro h
      norm_num at h
      linarith
    · apply Or.inr
      apply hreduce x hx0 (Or.inl ⟨rfl, rfl⟩) (by ring)
      apply (mul_eq_zero.mp (show x * (radial x 0 z + 90 * x) = 0 by
        linear_combination hx)).resolve_left hx0
  · have hrad : radial x y z - 180 * x = 0 := (mul_eq_zero.mp hy).resolve_left hy0
    have hyx : y ^ 2 = 3 * x ^ 2 := by linear_combination - hx / 90 + x * hrad / 90
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hyx
      exact hy0 (by nlinarith [sq_nonneg y])
    apply Or.inr
    refine hreduce (-2 * x) (by intro h; apply hx0; linarith) ?_ ?_ ?_
    · exact Or.inr ⟨by ring, by linarith [hyx, show 3 * (-2 * x) ^ 2 / 4 = 3 * x ^ 2 by ring]⟩
    · linear_combination hyx
    · linear_combination hrad

theorem stationary_of_direction {s x y z : ℝ} (hdir : direction s x y)
    (hz : (z = 0 ∧ 36 * s ^ 2 + 90 * s + 5 = 0) ∨
      (z ^ 2 = 5 / 48 + 3 / 2 * s ^ 2 ∧ (s = 1 / 6 ∨ s = 1 / 3))) :
    stationary x y z := by
  have hr : x ^ 2 + y ^ 2 = s ^ 2 := by
    rcases hdir with ⟨rfl, rfl⟩ | ⟨hx, hy⟩
    · ring
    · rw [hx, hy]
      ring
  have hrad : radial x y z = -90 * s := by
    rw [radial, hr]
    rcases hz with ⟨rfl, hp⟩ | ⟨hz, hs | hs⟩
    · linarith
    · rw [hz, hs]
      norm_num
    · rw [hz, hs]
      norm_num
  unfold stationary
  rw [hrad, hr]
  refine ⟨?_, ?_, ?_⟩
  · rcases hdir with ⟨rfl, rfl⟩ | ⟨hx, hy⟩
    · ring
    · rw [hx, hy]
      ring
  · rcases hdir with ⟨rfl, rfl⟩ | ⟨hx, _⟩
    · ring
    · rw [hx]
      ring
  · rcases hz with ⟨rfl, _⟩ | ⟨hz, _⟩
    · ring
    · rw [hz]
      ring

def hessianDet (x y z : ℝ) : ℝ :=
  let a := radial x y z + 72 * x ^ 2 + 180 * x
  let b := 72 * x * y - 180 * y
  let c := -288 * x * z
  let d := radial x y z + 72 * y ^ 2 - 180 * x
  let e := -288 * y * z
  let f := -10 - 144 * (x ^ 2 + y ^ 2) + 288 * z ^ 2
  a * d * f + 2 * b * c * e - a * e ^ 2 - d * c ^ 2 - f * b ^ 2

theorem hessianDet_radial {s x y z : ℝ}
    (hdir : direction s x y) (hlin : radial x y z = -90 * s) :
    hessianDet x y z = (-270 * s) *
      ((72 * s ^ 2 + 90 * s) * (-10 - 144 * s ^ 2 + 288 * z ^ 2) -
        (-288 * s * z) ^ 2) := by
  rcases hdir with ⟨rfl, rfl⟩ | ⟨hx, hy⟩
  · simp only [hessianDet, hlin, zero_pow, Nat.succ_ne_zero, add_zero, mul_zero,
      zero_mul, sub_zero]
    ring
  · have hr : x ^ 2 + y ^ 2 = s ^ 2 := by rw [hx, hy]; ring
    unfold hessianDet
    dsimp only
    rw [hlin, hr, hx, hy]
    calc
      _ = (y ^ 2) *
          (2 * (-36 * s - 180) * (144 * s * z) * (-288 * z) -
            (18 * s ^ 2 - 180 * s) * (-288 * z) ^ 2 -
            (-10 - 144 * s ^ 2 + 288 * z ^ 2) * (-36 * s - 180) ^ 2) +
          (18 * s ^ 2 - 180 * s) * (54 * s ^ 2) *
            (-10 - 144 * s ^ 2 + 288 * z ^ 2) -
          (54 * s ^ 2) * (144 * s * z) ^ 2 := by ring
      _ = _ := by rw [hy]; ring

theorem hessianDet_ne_zero {x y z : ℝ} (h : stationary x y z) :
    hessianDet x y z ≠ 0 := by
  rcases radial_classification h with ⟨rfl, rfl, hz | hz⟩ | ⟨s, hs, hdir, hz⟩
  · norm_num [hz, hessianDet, radial]
  · simp [hessianDet, radial, hz]
    norm_num
  · have hlin : radial x y z = -90 * s := by
      rcases hdir with ⟨rfl, rfl⟩ | ⟨hx, hy⟩
      · have hfactor : x * (radial x 0 z + 90 * x) = 0 := by
          linear_combination h.1
        have := (mul_eq_zero.mp hfactor).resolve_left hs
        linarith
      · have hy' : y ≠ 0 := by
          intro hy0
          rw [hy0] at hy
          have hs' : s ^ 2 = 0 := by linarith
          exact hs (by nlinarith [hs'])
        have hfactor := (mul_eq_zero.mp h.2.1).resolve_left hy'
        linarith
    rw [hessianDet_radial hdir hlin]
    apply mul_ne_zero (mul_ne_zero (by norm_num) hs)
    rcases hz with ⟨rfl, hp⟩ | ⟨hz, hs' | hs'⟩
    · have hpos : 0 < 10 + 144 * s ^ 2 := by positivity
      have hprod : (72 * s ^ 2 + 90 * s) ≠ 0 := by
        intro heq
        have hfactor : s * (72 * s + 90) = 0 := by linear_combination heq
        have hsval : s = -5 / 4 := by
          have := (mul_eq_zero.mp hfactor).resolve_left hs
          linarith
        rw [hsval] at hp
        norm_num at hp
      have hneg : -10 - 144 * s ^ 2 ≠ 0 := by linarith
      simpa using mul_ne_zero hprod hneg
    · rw [hs'] at hz ⊢
      have heq : z ^ 2 = (7 / 48 : ℝ) := by linear_combination hz
      ring_nf
      rw [heq]
      norm_num
    · rw [hs'] at hz ⊢
      have heq : z ^ 2 = (13 / 48 : ℝ) := by linear_combination hz
      ring_nf
      rw [heq]
      norm_num


private noncomputable def planarRadii : Bool → ℝ
  | false => (-90 - Real.sqrt 7380) / 72
  | true => (-90 + Real.sqrt 7380) / 72

private theorem planarRadii_spec (s : ℝ) :
    36 * s ^ 2 + 90 * s + 5 = 0 ↔ ∃ b, s = planarRadii b := by
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7380)
  have hf : 36 * s ^ 2 + 90 * s + 5 =
      36 * (s - planarRadii false) * (s - planarRadii true) := by
    dsimp [planarRadii]
    linear_combination hsqrt / 144
  rw [hf, mul_eq_zero, mul_eq_zero]
  simp only [OfNat.ofNat_ne_zero, false_or, sub_eq_zero, Bool.exists_bool]

private theorem planarRadii_neg (b : Bool) : planarRadii b < 0 := by
  have hpos := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 7380)
  have hlt : Real.sqrt 7380 < 90 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7380)
    nlinarith
  cases b <;> simp only [planarRadii] <;> linarith

private theorem planarRadii_inj : Function.Injective planarRadii := by
  have hpos := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 7380)
  intro a b h
  cases a <;> cases b <;> simp [planarRadii] at h ⊢ <;> linarith only [h, hpos]

private noncomputable def angular (s : ℝ) : Fin 3 → ℝ × ℝ :=
  ![(s, 0), (-s / 2, Real.sqrt 3 * s / 2), (-s / 2, -(Real.sqrt 3 * s / 2))]

private theorem square_eq_sq_iff (a b : ℝ) : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  have h : (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring
  rw [← sub_eq_zero, ← h, mul_eq_zero]
  constructor
  · rintro (h' | h')
    · exact Or.inl (by linarith only [h'])
    · exact Or.inr (by linarith only [h'])
  · rintro (h' | h')
    · exact Or.inl (by linarith only [h'])
    · exact Or.inr (by linarith only [h'])

private theorem angular_spec (s x y : ℝ) :
    ((x = s ∧ y = 0) ∨ (x = -s / 2 ∧ y ^ 2 = 3 * s ^ 2 / 4)) ↔
      ∃ i, (x, y) = angular s i := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h : 3 * s ^ 2 / 4 = (Real.sqrt 3 * s / 2) ^ 2 := by
    linear_combination -s ^ 2 / 4 * hsq
  rw [h, square_eq_sq_iff]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp [angular] at hi <;> simp [hi.1, hi.2]

private theorem angular_inj {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0)
    {i j : Fin 3} (h : angular s i = angular t j) : s = t ∧ i = j := by
  have hpos := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)
  have helim (u : ℝ) (hu : u ≠ 0) : Real.sqrt 3 * u / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hpos.ne' hu) (by norm_num)
  fin_cases i <;> fin_cases j <;> simp [angular] at h ⊢
  all_goals
    first
    | exact h.1
    | exact h
    | exact False.elim (hs h.2)
    | exact False.elim (ht h.2)
    | exact False.elim (helim t ht (by linarith only [h.2]))
    | exact False.elim (helim s hs (by linarith only [h.2]))
    | exfalso
      apply helim s hs
      have heq : s = t := by linarith only [h.1]
      rw [← heq] at h
      linarith only [h.2]

private noncomputable def signedRoot (r : ℝ) (b : Bool) : ℝ :=
  if b then Real.sqrt r else -Real.sqrt r

private theorem signedRoot_spec (r z : ℝ) (hr : 0 ≤ r) :
    z ^ 2 = r ↔ ∃ b, z = signedRoot r b := by
  rw [← Real.sq_sqrt hr, square_eq_sq_iff]
  simp [signedRoot, Bool.exists_bool, or_comm]

private theorem signedRoot_inj {r : ℝ} (hr : 0 < r) : Function.Injective (signedRoot r) := by
  have hpos := Real.sqrt_pos.2 hr
  intro a b h
  cases a <;> cases b <;> simp [signedRoot] at h ⊢ <;> linarith only [h, hpos]

private theorem signedRoot_ne_zero {r : ℝ} (hr : 0 < r) (b : Bool) :
    signedRoot r b ≠ 0 := by
  have hpos := Real.sqrt_pos.2 hr
  cases b <;> simp [signedRoot, hpos.ne']

private noncomputable def axialHeight : Fin 3 → ℝ :=
  ![0, signedRoot (5 / 48) false, signedRoot (5 / 48) true]

private theorem axialHeight_spec (z : ℝ) :
    z = 0 ∨ z ^ 2 = 5 / 48 ↔ ∃ i, z = axialHeight i := by
  rw [signedRoot_spec _ _ (by norm_num)]
  constructor
  · rintro (rfl | ⟨b, rfl⟩)
    · exact ⟨0, rfl⟩
    · cases b
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr ⟨false, rfl⟩
    · exact Or.inr ⟨true, rfl⟩

private theorem axialHeight_inj : Function.Injective axialHeight := by
  intro i j h
  have hp : 0 < Real.sqrt (5 / 48 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  fin_cases i <;> fin_cases j <;> simp [axialHeight, signedRoot] at h ⊢ <;>
    linarith only [h, hp, show 0 < Real.sqrt 5 / Real.sqrt 48 by positivity]

private noncomputable def offRadius (b : Bool) : ℝ := if b then 1 / 3 else 1 / 6

private theorem offRadius_pos (b : Bool) : 0 < offRadius b := by
  cases b <;> norm_num [offRadius]

private theorem offRadius_inj : Function.Injective offRadius := by
  intro a b h
  cases a <;> cases b <;> norm_num [offRadius] at *

private noncomputable def offHeightSq (s : ℝ) : ℝ := 5 / 48 + 3 / 2 * s ^ 2

private theorem offHeightSq_pos (s : ℝ) : 0 < offHeightSq s := by
  unfold offHeightSq
  positivity

private theorem angular_ne_origin {s : ℝ} (hs : s ≠ 0) (i : Fin 3) : angular s i ≠ (0, 0) := by
  intro h
  have hx := congrArg Prod.fst h
  fin_cases i <;> simp [angular] at hx <;> exact hs hx

private abbrev CriticalIndex := Fin 3 ⊕ ((Bool × Fin 3) ⊕ (Bool × Bool × Fin 3))

private noncomputable def criticalCoordinates : CriticalIndex → (ℝ × ℝ) × ℝ
  | .inl i => ((0, 0), axialHeight i)
  | .inr (.inl (b, i)) => (angular (planarRadii b) i, 0)
  | .inr (.inr (b, e, i)) =>
      (angular (offRadius b) i, signedRoot (offHeightSq (offRadius b)) e)

private theorem criticalCoordinates_inj : Function.Injective criticalCoordinates := by
  intro a b h
  rcases a with a | (⟨a, i⟩ | ⟨a, e, i⟩) <;>
    rcases b with b | (⟨b, j⟩ | ⟨b, f, j⟩) <;>
    simp only [criticalCoordinates, Prod.mk.injEq] at h
  · exact congrArg Sum.inl (axialHeight_inj h.2)
  · exact False.elim (angular_ne_origin (planarRadii_neg b).ne j h.1.symm)
  · exact False.elim (angular_ne_origin (offRadius_pos b).ne' j h.1.symm)
  · exact False.elim (angular_ne_origin (planarRadii_neg a).ne i h.1)
  · obtain ⟨hab, hij⟩ := angular_inj (planarRadii_neg a).ne (planarRadii_neg b).ne h.1
    rw [planarRadii_inj hab, hij]
  · exact False.elim (signedRoot_ne_zero (offHeightSq_pos _) f h.2.symm)
  · exact False.elim (angular_ne_origin (offRadius_pos a).ne' i h.1)
  · exact False.elim (signedRoot_ne_zero (offHeightSq_pos _) e h.2)
  · obtain ⟨hab, hij⟩ := angular_inj (offRadius_pos a).ne' (offRadius_pos b).ne' h.1
    obtain rfl := offRadius_inj hab
    obtain rfl := signedRoot_inj (offHeightSq_pos _) h.2
    rw [hij]


private theorem stationary_iff_coordinates (x y z : ℝ) :
    stationary x y z ↔ ∃ i, ((x, y), z) = criticalCoordinates i := by
  constructor
  · intro h
    rcases radial_classification h with ⟨rfl, rfl, hz⟩ | ⟨s, _, hdir, hz⟩
    · obtain ⟨i, hi⟩ := (axialHeight_spec z).mp hz
      exact ⟨Sum.inl i, by simp [criticalCoordinates, hi]⟩
    · obtain ⟨i, hi⟩ := (angular_spec s x y).mp hdir
      rcases hz with ⟨rfl, hp⟩ | ⟨hz, hs | hs⟩
      · obtain ⟨b, rfl⟩ := (planarRadii_spec s).mp hp
        exact ⟨Sum.inr (Sum.inl (b, i)), by simp [criticalCoordinates, hi]⟩
      · have he : s = offRadius false := hs
        obtain ⟨b, hb⟩ := (signedRoot_spec (offHeightSq s) z (offHeightSq_pos s).le).mp hz
        exact ⟨Sum.inr (Sum.inr (false, b, i)), by rw [criticalCoordinates, ← he, ← hi, ← hb]⟩
      · have he : s = offRadius true := hs
        obtain ⟨b, hb⟩ := (signedRoot_spec (offHeightSq s) z (offHeightSq_pos s).le).mp hz
        exact ⟨Sum.inr (Sum.inr (true, b, i)), by rw [criticalCoordinates, ← he, ← hi, ← hb]⟩
  · rintro ⟨i, hi⟩
    rcases i with i | (⟨b, i⟩ | ⟨b, e, i⟩) <;>
      simp only [criticalCoordinates, Prod.mk.injEq] at hi
    · rcases hi with ⟨⟨rfl, rfl⟩, hz⟩
      rcases (axialHeight_spec z).mpr ⟨i, hz⟩ with rfl | hz
      · norm_num [stationary, radial]
      · unfold stationary radial
        rw [hz]
        norm_num
    · apply stationary_of_direction ((angular_spec _ _ _).mpr ⟨i, hi.1⟩)
      exact Or.inl ⟨hi.2, (planarRadii_spec _).mpr ⟨b, rfl⟩⟩
    · apply stationary_of_direction ((angular_spec _ _ _).mpr ⟨i, hi.1⟩)
      refine Or.inr ⟨(signedRoot_spec _ _ (offHeightSq_pos _).le).mpr ⟨e, hi.2⟩, ?_⟩
      cases b <;> norm_num [offRadius]

private noncomputable def criticalPoint (i : CriticalIndex) : E :=
  let p := criticalCoordinates i
  WithLp.toLp 2 ![p.1.1, p.1.2, p.2]

private theorem criticalPoint_inj : Function.Injective criticalPoint := by
  intro i j h
  apply criticalCoordinates_inj
  apply Prod.ext
  · apply Prod.ext
    · exact congrArg (fun p : E => p.ofLp 0) h
    · exact congrArg (fun p : E => p.ofLp 1) h
  · exact congrArg (fun p : E => p.ofLp 2) h

private theorem criticalPoint_range :
    {p : E | ∇ phiZero p = 0} = Set.range criticalPoint := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_range, critical_iff]
  change stationary (p.ofLp 0) (p.ofLp 1) (p.ofLp 2) ↔ _
  rw [stationary_iff_coordinates]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply WithLp.ofLp_injective
    funext j
    rcases Prod.mk.inj hi with ⟨hxy, hz⟩
    rcases Prod.mk.inj hxy with ⟨hx, hy⟩
    fin_cases j
    · exact hx.symm
    · exact hy.symm
    · exact hz.symm
  · rintro ⟨i, rfl⟩
    exact ⟨i, by cases h : criticalCoordinates i with | mk xy z => cases xy; simp [criticalPoint, h]⟩

private theorem nondegenerate_at_critical (p : E) (hp : ∇ phiZero p = 0) :
    HasNondegenerateHessianAt phiZero p := by
  have hstat : stationary (p.ofLp 0) (p.ofLp 1) (p.ofLp 2) := (critical_iff p).mp hp
  have hdet : (hessianMatrix p).det ≠ 0 := by
    have hval : (hessianMatrix p).det = hessianDet (p.ofLp 0) (p.ofLp 1) (p.ofLp 2) := by
      simp only [hessianMatrix, Matrix.det_fin_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons, hessianDet, radial]
      ring
    exact hval.symm ▸ hessianDet_ne_zero hstat
  have hmul := Matrix.mulVec_injective_iff_isUnit.mpr
    ((hessianMatrix p).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet))
  intro v hv
  let u := hessianMatrix p *ᵥ v.ofLp
  have hu : u ≠ 0 := by
    intro h
    apply hv
    apply WithLp.ofLp_injective
    apply hmul
    simpa [u] using h
  refine ⟨WithLp.toLp 2 u, ?_⟩
  intro h
  have hh := second_derivative p v (WithLp.toLp 2 u)
  rw [h, mul_zero] at hh
  apply hu
  exact dotProduct_self_eq_zero.mp hh.symm

end MaxwellScratch

open MaxwellScratch in
theorem OMA.solution : type_of% @Arxiv.«2607.27197».maxwell_conjecture.phiZero_critical_points := by
  constructor
  · rw [criticalPoint_range, ← Set.image_univ, criticalPoint_inj.encard_image, Set.encard_univ]
    norm_num [ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card, CriticalIndex]
  · exact nondegenerate_at_critical
