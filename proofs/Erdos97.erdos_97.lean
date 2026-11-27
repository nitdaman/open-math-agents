import FormalConjectures.ErdosProblems.«97»
import Mathlib

/-!
# A convex polygon with at least four unit-distance neighbors at each vertex

The seed geometry uses the middle levels graph and the construction of Liam Kruer, Jensen
Kohlmeyer, and Liam Price in Unit distances in convex polygons
(https://github.com/lkruer/erdos-96-97-proof). Finite sets of products of small rotations
have at most polynomial growth. An overlap bound on a suitable set of products gives
enough unit edges even when different products coincide.
-/


open Filter
open scoped Topology

namespace OMA.Erdos97Seed

noncomputable def lowerHeight (x t : ℝ) : ℝ := x ^ 2 + t / 2

noncomputable def upperHeight (x t : ℝ) : ℝ := -(x ^ 2) + t / 2

def complexPoint (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * Complex.I

@[simp]
lemma complexPoint_re (x y : ℝ) : (complexPoint x y).re = x := by
  simp [complexPoint, Complex.mul_re]

@[simp]
lemma complexPoint_im (x y : ℝ) : (complexPoint x y).im = y := by
  simp [complexPoint, Complex.mul_im]

noncomputable def lowerPoint (x t e : ℝ) : ℂ :=
  complexPoint (e * x) (-(1 / 2) + e ^ 2 * lowerHeight x t)

noncomputable def upperPoint (x t e : ℝ) : ℂ :=
  complexPoint (-(e * x)) (1 / 2 + e ^ 2 * upperHeight x t)

lemma continuous_lowerPoint (x t : ℝ) : Continuous (lowerPoint x t) := by
  unfold lowerPoint complexPoint
  fun_prop

lemma continuous_upperPoint (x t : ℝ) : Continuous (upperPoint x t) := by
  unfold upperPoint complexPoint
  fun_prop

lemma lowerPoint_zero (x t : ℝ) : lowerPoint x t 0 = -(Complex.I / 2) := by
  apply Complex.ext <;> simp [lowerPoint, div_eq_mul_inv, Complex.mul_re, Complex.mul_im]

lemma upperPoint_zero (x t : ℝ) : upperPoint x t 0 = Complex.I / 2 := by
  apply Complex.ext <;> simp [upperPoint, div_eq_mul_inv, Complex.mul_re, Complex.mul_im]

def radial (a b : ℂ) : ℝ := (star a * b).re - Complex.normSq a

lemma radial_coords (a b : ℂ) :
    radial a b = a.re * (b.re - a.re) + a.im * (b.im - a.im) := by
  simp [radial, Complex.mul_re, Complex.normSq_apply]
  ring

lemma lower_radial (x t y u e : ℝ) :
    radial (lowerPoint x t e) (lowerPoint y u e) = e ^ 2 *
      (-(y - x) ^ 2 / 2 - (u - t) / 4 +
        e ^ 2 * (lowerHeight x t * (lowerHeight y u - lowerHeight x t))) := by
  rw [radial_coords]
  simp [lowerPoint, lowerHeight]
  ring

lemma upper_radial (x t y u e : ℝ) :
    radial (upperPoint x t e) (upperPoint y u e) = e ^ 2 *
      (-(y - x) ^ 2 / 2 + (u - t) / 4 +
        e ^ 2 * (upperHeight x t * (upperHeight y u - upperHeight x t))) := by
  rw [radial_coords]
  simp [upperPoint, upperHeight]
  ring

lemma eventually_radial_small {p q : ℝ → ℂ} (hp : ContinuousAt p 0) (hq : ContinuousAt q 0)
    (hgap : radial (p 0) (q 0) < 0) :
    ∀ᶠ e : ℝ in 𝓝 0, radial (p e) (q e) ≤ -(e ^ 2) := by
  have hRad : ContinuousAt (fun e ↦ radial (p e) (q e)) 0 := by
    simp only [radial_coords]
    fun_prop
  have hs : ContinuousAt (fun (e : ℝ) ↦ -(e ^ 2)) 0 := by fun_prop
  apply (hRad.eventually_lt hs (by simpa using hgap)).mono
  exact fun _ h ↦ h.le

lemma eventually_factor_small {a b : ℝ} (ha : a < 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ e : ℝ in 𝓝 0, e ^ 2 * (a + e ^ 2 * b) ≤ -(c * e ^ 2) := by
  refine ⟨-a / 2, by linarith, ?_⟩
  have hpoly : ContinuousAt (fun (e : ℝ) ↦ a + e ^ 2 * b) 0 := by fun_prop
  filter_upwards [hpoly.eventually_lt continuousAt_const (by simp; linarith : a + (0 : ℝ)^2*b < -(-a/2))] with e he
  calc
    e ^ 2 * (a + e ^ 2 * b) ≤ e ^ 2 * (-(-a / 2)) :=
      mul_le_mul_of_nonneg_left he.le (sq_nonneg e)
    _ = -(-a / 2 * e ^ 2) := by ring

noncomputable def seedPoint {L R : Type*} (X T : L ⊕ R → ℝ) (e : ℝ) : L ⊕ R → ℂ
  | .inl i => lowerPoint (X (.inl i)) (T (.inl i)) e
  | .inr i => upperPoint (X (.inr i)) (T (.inr i)) e

lemma seed_norm {L R : Type*} (X T : L ⊕ R → ℝ) (i : L ⊕ R) :
    ∀ᶠ e : ℝ in 𝓝 0, seedPoint X T e i ≠ 0 ∧ ‖seedPoint X T e i‖ ≤ 1 := by
  have hcont : Continuous (fun e ↦ seedPoint X T e i) := by
    cases i
    · exact continuous_lowerPoint _ _
    · exact continuous_upperPoint _ _
  have hhalf : ‖seedPoint X T 0 i‖ = 1 / 2 := by
    cases i <;> simp [seedPoint, lowerPoint_zero, upperPoint_zero]
  have hnorm : ∀ᶠ e : ℝ in 𝓝 0, (0 : ℝ) < ‖seedPoint X T e i‖ :=
    continuousAt_const.eventually_lt hcont.norm.continuousAt (by rw [hhalf]; norm_num)
  have hbound : ∀ᶠ e : ℝ in 𝓝 0, ‖seedPoint X T e i‖ < 1 :=
    hcont.norm.continuousAt.eventually_lt continuousAt_const (by rw [hhalf]; norm_num)
  filter_upwards [hnorm, hbound] with e h₁ h₂
  exact ⟨norm_pos_iff.mp h₁, h₂.le⟩

lemma seed_pair {L R : Type*} (X T : L ⊕ R → ℝ) (i j : L ⊕ R)
    (hspread : |T j - T i| < 2 * (X j - X i) ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ e : ℝ in 𝓝 0,
      radial (seedPoint X T e i) (seedPoint X T e j) ≤ -(c * e ^ 2) := by
  cases i <;> cases j
  · simp only [seedPoint, lower_radial]
    have h := (abs_lt.mp hspread).1
    exact eventually_factor_small (by linarith)
  · refine ⟨1, zero_lt_one, ?_⟩
    simp only [one_mul, seedPoint]
    apply eventually_radial_small (continuous_lowerPoint _ _).continuousAt
      (continuous_upperPoint _ _).continuousAt
    rw [lowerPoint_zero, upperPoint_zero, radial_coords]
    norm_num [div_eq_mul_inv, Complex.mul_re, Complex.mul_im]
  · refine ⟨1, zero_lt_one, ?_⟩
    simp only [one_mul, seedPoint]
    apply eventually_radial_small (continuous_upperPoint _ _).continuousAt
      (continuous_lowerPoint _ _).continuousAt
    rw [upperPoint_zero, lowerPoint_zero, radial_coords]
    norm_num [div_eq_mul_inv, Complex.mul_re, Complex.mul_im]
  · simp only [seedPoint, upper_radial]
    have h := (abs_lt.mp hspread).2
    exact eventually_factor_small (by linarith)


lemma sqrt_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) :
    a = b := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact h
  · linarith

lemma normSq_sub_conj (a b : ℂ) :
    Complex.normSq (a - b) = Complex.normSq a + Complex.normSq b - 2 * (star a * b).re := by
  simp [Complex.normSq_apply, Complex.mul_re]
  ring

lemma lower_upper_distSq (x t y u e : ℝ) (hedge : u - t = (y - x) ^ 2) :
    Complex.normSq (lowerPoint x t e - upperPoint y u e) =
      1 + e ^ 4 * (upperHeight y u - lowerHeight x t) ^ 2 := by
  have hzero : (x + y) ^ 2 + 2 * (upperHeight y u - lowerHeight x t) = 0 := by
    unfold upperHeight lowerHeight
    linarith only [hedge]
  simp [Complex.normSq_apply, lowerPoint, upperPoint]
  linear_combination e ^ 2 * hzero

lemma eventually_correct (x t y u : ℝ) (hxy : x < y) (hedge : u - t = (y - x) ^ 2)
    (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ e : ℝ in 𝓝 0, ∃ w : ℂ, ‖w‖ = 1 ∧
      ‖lowerPoint x t e - upperPoint y u e * w‖ = 1 ∧ ‖w - 1‖ ≤ θ * e ^ 2 := by
  let C := lowerHeight x t
  let D := upperHeight y u
  let M := D - C
  let Z (e : ℝ) := star (lowerPoint x t e) * upperPoint y u e
  let τ (e : ℝ) := (x - y) / 2 + e ^ 2 * (x * D + y * C)
  -- Shift the real part of Z to fix the squared distance and retain its squared norm.
  let G (e : ℝ) := -(M ^ 2 * (Z e).re) - e ^ 4 * M ^ 4 / 4
  let F (e : ℝ) := τ e ^ 2 + e ^ 2 * G e
  let U (e : ℝ) := complexPoint ((Z e).re + e ^ 4 * M ^ 2 / 2) (-(e * √(F e)))
  -- Rationalizing the imaginary correction shows that U - Z is divisible by e ^ 3.
  let B (e : ℝ) := complexPoint (e * M ^ 2 / 2) (-(G e / (√(F e) - τ e)))
  have hZ : Continuous Z :=
    (continuous_lowerPoint x t).star.mul (continuous_upperPoint y u)
  have hτ : Continuous τ := by dsimp only [τ]; fun_prop
  have hG : Continuous G := by dsimp only [G]; fun_prop
  have hF : Continuous F := by dsimp only [F]; fun_prop
  have hZzero : Z 0 = -(1 / 4 : ℂ) := by
    simp only [Z, lowerPoint_zero, upperPoint_zero]
    apply Complex.ext <;> norm_num [div_eq_mul_inv, Complex.mul_re, Complex.mul_im]
  have hZne := hZ.continuousAt.eventually_ne (y := 0) (by rw [hZzero]; norm_num)
  have hFzero : 0 < F 0 := by
    simp only [F, τ, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero]
    exact sq_pos_of_ne_zero (by linarith)
  have hFpos : ∀ᶠ e : ℝ in 𝓝 0, 0 < F e :=
    continuousAt_const.eventually_lt hF.continuousAt hFzero
  have hτneg : ∀ᶠ e : ℝ in 𝓝 0, τ e < 0 := by
    apply hτ.continuousAt.eventually_lt continuousAt_const
    dsimp [τ]
    simp
    linarith
  have hB : ContinuousAt B 0 := by
    have hden : √(F 0) - τ 0 ≠ 0 := by
      have htzero : τ 0 < 0 := by dsimp [τ]; simp; linarith
      linarith [Real.sqrt_nonneg (F 0)]
    have hquot : ContinuousAt (fun e ↦ G e / (√(F e) - τ e)) 0 :=
      hG.continuousAt.div ((hF.continuousAt.sqrt).sub hτ.continuousAt) hden
    dsimp only [B, complexPoint]
    fun_prop
  have hratio : ContinuousAt (fun e : ℝ ↦ |e| * ‖B e‖ / ‖Z e‖) 0 := by
    have hz : ‖Z 0‖ ≠ 0 := norm_ne_zero_iff.mpr (by rw [hZzero]; norm_num)
    exact (continuousAt_id.abs.mul hB.norm).div hZ.norm.continuousAt hz
  have hsmall : ∀ᶠ e : ℝ in 𝓝 0, |e| * ‖B e‖ / ‖Z e‖ < θ := by
    apply hratio.eventually_lt continuousAt_const
    simpa using hθ
  filter_upwards [hZne, hFpos, hτneg, hsmall] with e hZne' hFpos' hτneg' hsmall'
  have hZim : (Z e).im = e * τ e := by
    simp [Z, τ, lowerPoint, upperPoint, C, D, Complex.mul_im]
    ring
  have hUre : (U e).re = (Z e).re + e ^ 4 * M ^ 2 / 2 := complexPoint_re _ _
  have hUim : (U e).im = -(e * √(F e)) := complexPoint_im _ _
  have hSqrt : √(F e) ^ 2 = F e := Real.sq_sqrt hFpos'.le
  have hFform : √(F e) ^ 2 = τ e ^ 2 + e ^ 2 * G e := hSqrt
  have hUsq : Complex.normSq (U e) = Complex.normSq (Z e) := by
    simp only [Complex.normSq_apply, hUre, hUim, hZim]
    linear_combination e ^ 2 * hFform
  let w := U e / Z e
  have hwSq : Complex.normSq w = 1 := by
    rw [Complex.normSq_div, hUsq, div_self (Complex.normSq_pos.mpr hZne').ne']
  have hwr : Z e * w = U e := by dsimp [w]; field_simp
  have hErr : (U e - Z e) = ((e ^ 3 : ℝ) : ℂ) * B e := by
    have hden' : 0 < √(F e) - τ e := by linarith [Real.sqrt_nonneg (F e)]
    have hrational : √(F e) + τ e = (e ^ 2 * G e) / (√(F e) - τ e) := by
      apply (eq_div_iff hden'.ne').mpr
      linarith only [hFform]
    apply Complex.ext
    · simp only [Complex.sub_re, hUre, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        B, complexPoint_re, complexPoint_im]
      ring
    · simp only [Complex.sub_im, hUim, hZim, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        B, complexPoint_re, complexPoint_im]
      calc
        -(e * √(F e)) - e * τ e = -(e * (√(F e) + τ e)) := by ring
        _ = _ := by rw [hrational]; ring
  refine ⟨w, sqrt_sq_eq (norm_nonneg _) zero_le_one (by simpa [Complex.sq_norm] using hwSq),
    ?_, ?_⟩
  · apply sqrt_sq_eq (norm_nonneg _) zero_le_one
    rw [Complex.sq_norm]
    have hOld := lower_upper_distSq x t y u e hedge
    change Complex.normSq (lowerPoint x t e - upperPoint y u e) =
      1 + e ^ 4 * M ^ 2 at hOld
    rw [normSq_sub_conj, Complex.normSq_mul, hwSq, mul_one, ← mul_assoc]
    change Complex.normSq (lowerPoint x t e) + Complex.normSq (upperPoint y u e) -
      2 * (Z e * w).re = _
    rw [hwr, hUre]
    rw [normSq_sub_conj] at hOld
    change Complex.normSq (lowerPoint x t e) + Complex.normSq (upperPoint y u e) -
      2 * (Z e).re = _ at hOld
    linarith only [hOld]
  · have hwSub : w - 1 = (U e - Z e) / Z e := by
      dsimp only [w]
      field_simp
    rw [hwSub, hErr, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow]
    have habs : |e| ^ 3 = e ^ 2 * |e| := by
      rw [pow_succ, sq_abs]
    rw [habs, mul_assoc, mul_div_assoc, mul_comm θ]
    exact mul_le_mul_of_nonneg_left hsmall'.le (sq_nonneg e)


/-- Construct seed points and small edge rotations with a common strict support margin. -/
theorem exists_seeds {L R E : Type*} [Finite L] [Finite R] [Finite E]
    (left : E → L) (right : E → R) (X T : L ⊕ R → ℝ)
    (hspread : ∀ i j, i ≠ j → |T j - T i| < 2 * (X j - X i) ^ 2)
    (hedge : ∀ e, X (.inl (left e)) < X (.inr (right e)) ∧
      T (.inr (right e)) - T (.inl (left e)) = (X (.inr (right e)) - X (.inl (left e))) ^ 2)
    (C : ℕ) :
    ∃ (b : L ⊕ R → ℂ) (w : E → ℂ) (σ : ℝ),
      0 < σ ∧ (∀ i, b i ≠ 0 ∧ ‖b i‖ ≤ 1) ∧
      (∀ i j, i ≠ j → (star (b i) * b j).re + σ ≤ Complex.normSq (b i)) ∧
      ∀ e, ‖w e‖ = 1 ∧ ‖b (.inl (left e)) - b (.inr (right e)) * w e‖ = 1 ∧
        (C : ℝ) * ‖w e - 1‖ ≤ σ / 4 := by
  classical
  let P := { p : (L ⊕ R) × (L ⊕ R) // p.1 ≠ p.2 }
  have hPairs (p : P) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ e : ℝ in 𝓝 0,
      radial (seedPoint X T e p.1.1) (seedPoint X T e p.1.2) ≤ -(c * e ^ 2) :=
    seed_pair X T p.1.1 p.1.2 (hspread _ _ p.2)
  choose margins hPos hMargin using hPairs
  let : Fintype P := Fintype.ofFinite P
  let s : Finset ℝ := insert 1 (Finset.univ.image margins)
  have hs : s.Nonempty := ⟨1, by simp [s]⟩
  let c := s.inf' hs id
  have hc : 0 < c := by
    change 0 < s.inf' hs id
    apply (Finset.lt_inf'_iff (H := hs)).mpr
    intro z hz
    have hz' : z = 1 ∨ ∃ p, margins p = z := by simpa [s] using hz
    rcases hz' with rfl | ⟨p, rfl⟩
    · exact zero_lt_one
    · exact hPos p
  have hCommon (p : P) : c ≤ margins p := by
    exact Finset.inf'_le id (by simp [s] : margins p ∈ s)
  have hN := eventually_all.mpr (seed_norm X T)
  have hM := eventually_all.mpr hMargin
  let θ : ℝ := c / (4 * ((C : ℝ) + 1))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hE : ∀ᶠ a : ℝ in 𝓝 0, ∀ e : E, ∃ z : ℂ, ‖z‖ = 1 ∧
      ‖seedPoint X T a (.inl (left e)) - seedPoint X T a (.inr (right e)) * z‖ = 1 ∧
      ‖z - 1‖ ≤ θ * a ^ 2 := by
    apply eventually_all.mpr
    intro e
    exact eventually_correct _ _ _ _ (hedge e).1 (hedge e).2 θ hθ
  have hAll : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ),
      0 < e ∧
      (∀ i, seedPoint X T e i ≠ 0 ∧ ‖seedPoint X T e i‖ ≤ 1) ∧
      (∀ p : P, radial (seedPoint X T e p.1.1) (seedPoint X T e p.1.2) ≤
        -(margins p * e ^ 2)) ∧
      ∀ f : E, ∃ z : ℂ, ‖z‖ = 1 ∧
        ‖seedPoint X T e (.inl (left f)) - seedPoint X T e (.inr (right f)) * z‖ = 1 ∧
        ‖z - 1‖ ≤ θ * e ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, (hN.and (hM.and hE)).filter_mono nhdsWithin_le_nhds]
      with e he hn
    exact ⟨he, hn⟩
  obtain ⟨ε, hε, hNε, hMε, hEε⟩ := hAll.exists
  choose w hW hUnit hClose using hEε
  refine ⟨seedPoint X T ε, w, c * ε ^ 2, by positivity, hNε, ?_, ?_⟩
  · intro i j hij
    let p : P := ⟨(i, j), hij⟩
    have h := (hMε p).trans (neg_le_neg (mul_le_mul_of_nonneg_right (hCommon p) (sq_nonneg ε)))
    change radial (seedPoint X T ε i) (seedPoint X T ε j) ≤ -(c * ε ^ 2) at h
    unfold radial at h
    linarith only [h]
  · intro f
    refine ⟨hW f, hUnit f, ?_⟩
    have hbase : θ * (4 * ((C : ℝ) + 1)) = c := by
      dsimp [θ]
      field_simp
    have hθC : (C : ℝ) * θ ≤ c / 4 := by
      have hnonneg : 0 ≤ θ := hθ.le
      nlinarith only [hbase, hnonneg]
    calc
      (C : ℝ) * ‖w f - 1‖ ≤ (C : ℝ) * (θ * ε ^ 2) :=
        mul_le_mul_of_nonneg_left (hClose f) (Nat.cast_nonneg C)
      _ = ((C : ℝ) * θ) * ε ^ 2 := by ring
      _ ≤ (c / 4) * ε ^ 2 := mul_le_mul_of_nonneg_right hθC (sq_nonneg ε)
      _ = c * ε ^ 2 / 4 := by ring

end OMA.Erdos97Seed


namespace OMA97

open Finset

abbrev MiddleLeft (n k : ℕ) := {s : Finset (Fin n) // s.card = k}
abbrev MiddleRight (n k : ℕ) := {s : Finset (Fin n) // s.card = k + 1}
abbrev MiddleEdge (n k : ℕ) := (s : MiddleLeft n k) × {i : Fin n // i ∉ s.val}

def middleLeft {n k : ℕ} (e : MiddleEdge n k) : MiddleLeft n k :=
  e.1

def middleRight {n k : ℕ} (e : MiddleEdge n k) : MiddleRight n k :=
  ⟨insert e.2.val e.1.val, by rw [Finset.card_insert_of_notMem e.2.prop, e.1.prop]⟩

lemma middleEndpoints_injective (n k : ℕ) :
    Function.Injective (fun e : MiddleEdge n k ↦ (middleLeft e, middleRight e)) := by
  rintro ⟨A, i⟩ ⟨B, j⟩ heq
  have hA : A = B := congrArg Prod.fst heq
  subst B
  have hinsert : insert i.val A.val = insert j.val A.val :=
    congrArg (fun p ↦ p.2.val) heq
  have hi : i.val ∈ insert j.val A.val := hinsert ▸ mem_insert_self _ _
  have hij : i.val = j.val := (mem_insert.mp hi).resolve_right i.prop
  have hij' : i = j := Subtype.ext hij
  subst j
  rfl

lemma card_middle_level (n k : ℕ) :
    Fintype.card (MiddleLeft n k) = Nat.choose n k := by
  unfold MiddleLeft
  rw [Fintype.card_subtype]
  have h : (univ.filter fun s : Finset (Fin n) ↦ s.card = k) =
      (univ : Finset (Fin n)).powersetCard k := by
    ext s
    simp
  rw [h, card_powersetCard]
  simp

lemma card_middle_extensions {n k : ℕ} (A : MiddleLeft n k) :
    Fintype.card {i : Fin n // i ∉ A.val} = n - k := by
  rw [Fintype.card_subtype_compl]
  have h : Fintype.card {i : Fin n // i ∈ A.val} = k := by
    simpa using A.prop
  rw [h, Fintype.card_fin]

lemma middle_density (k : ℕ) :
    (k + 1) * (Fintype.card (MiddleLeft (2 * k + 1) k) +
      Fintype.card (MiddleRight (2 * k + 1) k)) =
      2 * Fintype.card (MiddleEdge (2 * k + 1) k) := by
  have hn : 2 * k + 1 - k = k + 1 := by omega
  have h :
      Fintype.card (MiddleLeft (2 * k + 1) k) = Fintype.card (MiddleRight (2 * k + 1) k) := by
    change _ = Fintype.card (MiddleLeft _ (k + 1))
    rw [card_middle_level, card_middle_level, ← hn, Nat.choose_symm (by omega)]
  rw [Fintype.card_sigma]
  simp only [card_middle_extensions, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, hn]
  rw [← h]
  ring

lemma middle_nonempty {n k : ℕ} (hkn : k ≤ n) : Nonempty (MiddleLeft n k ⊕ MiddleRight n k) := by
  have h : 0 < Fintype.card (MiddleLeft n k) := by
    rw [card_middle_level]
    exact Nat.choose_pos hkn
  exact Fintype.card_pos_iff.mp (by rw [Fintype.card_sum]; omega)

end OMA97

namespace OMA97

open Finset

lemma digit_difference_bounds {n : ℕ} (x : ℝ) (hx : 0 ≤ x) {S T : Finset (Fin n)}
    {j : Fin n} (hj : j ∈ (S \ T) ∪ (T \ S))
    (hmax : ∀ i ∈ (S \ T) ∪ (T \ S), i ≤ j) :
    let difference := (∑ i ∈ S, x ^ i.val) - ∑ i ∈ T, x ^ i.val
    let earlier := ∑ i ∈ range j.val, x ^ i
    x ^ j.val - earlier ≤ |difference| ∧ |difference| ≤ x ^ j.val + earlier := by
  classical
  let D := (S \ T) ∪ (T \ S)
  let w (i : Fin n) : ℝ := if i ∈ S then x ^ i.val else -(x ^ i.val)
  have hAbs (i : Fin n) : |w i| = x ^ i.val := by
    unfold w
    split_ifs <;> simp [abs_of_nonneg (pow_nonneg hx _)]
  have hSplit : ∑ i ∈ D, w i = (∑ i ∈ S, x ^ i.val) - ∑ i ∈ T, x ^ i.val := by
    have hDis : Disjoint (S \ T) (T \ S) :=
      disjoint_left.mpr fun i hi hj ↦ (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
    unfold D
    rw [sum_union hDis]
    have hS : ∑ i ∈ S \ T, w i = ∑ i ∈ S \ T, x ^ i.val :=
      sum_congr rfl fun i hi ↦ if_pos (mem_sdiff.mp hi).1
    have hT : ∑ i ∈ T \ S, w i = ∑ i ∈ T \ S, -(x ^ i.val) :=
      sum_congr rfl fun i hi ↦ if_neg (mem_sdiff.mp hi).2
    rw [hS, hT, sum_neg_distrib]
    have hSdiff : S \ T = S \ (S ∩ T) := by ext i; simp
    have hTdiff : T \ S = T \ (S ∩ T) := by ext i; simp
    rw [hSdiff, hTdiff, sum_sdiff_eq_sub inter_subset_left, sum_sdiff_eq_sub inter_subset_right]
    ring
  let rest := ∑ i ∈ D.erase j, w i
  have hRest : |rest| ≤ ∑ i ∈ range j.val, x ^ i := by
    have hSub : D.erase j ⊆ Iio j := by
      intro i hi
      obtain ⟨hij, hiD⟩ := mem_erase.mp hi
      exact mem_Iio.mpr (lt_of_le_of_ne (hmax i hiD) hij)
    calc
      |rest| ≤ ∑ i ∈ D.erase j, |w i| := abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ D.erase j, x ^ i.val := sum_congr rfl fun i _ ↦ hAbs i
      _ ≤ ∑ i ∈ Iio j, x ^ i.val :=
        sum_le_sum_of_subset_of_nonneg hSub fun i _ _ ↦ pow_nonneg hx _
      _ = ∑ i ∈ range j.val, x ^ i := by
        change (∑ i ∈ Iio j, x ^ (Fin.valEmbedding i)) = _
        rw [← sum_map, Fin.map_valEmbedding_Iio, Nat.Iio_eq_range]
  have hSum : rest + w j = (∑ i ∈ S, x ^ i.val) - ∑ i ∈ T, x ^ i.val :=
    (sum_erase_add D w hj).trans hSplit
  dsimp only
  rw [← hSum]
  constructor
  · have hTriangle : |w j| - |rest| ≤ |rest + w j| := by
      simpa [add_comm] using abs_sub_abs_le_abs_sub (w j) (-rest)
    rw [hAbs j] at hTriangle
    linarith
  · have hTriangle := abs_add_le rest (w j)
    rw [hAbs j] at hTriangle
    linarith

def digitX {n : ℕ} (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, (5 : ℝ) ^ i.val

def digitT {n : ℕ} (S : Finset (Fin n)) : ℝ :=
  1 + ∑ i ∈ S, (25 : ℝ) ^ i.val

lemma digitT_pos {n : ℕ} (S : Finset (Fin n)) : 0 < digitT S := by
  unfold digitT
  positivity

lemma digit_spread {n : ℕ} {S T : Finset (Fin n)} (hne : S ≠ T) :
    |digitT T - digitT S| < 2 * (digitX T - digitX S)^2 := by
  let D := (T \ S) ∪ (S \ T)
  have hD : D.Nonempty := by
    by_contra hd
    have h0 : D = ∅ := not_nonempty_iff_eq_empty.mp hd
    apply hne
    ext i
    have hNot : i ∉ D := by simp [h0]
    simp only [D, Finset.mem_union, Finset.mem_sdiff] at hNot
    tauto
  let j := D.max' hD
  have hj : j ∈ (T \ S) ∪ (S \ T) := D.max'_mem hD
  have hmax (i : Fin n) (hi : i ∈ (T \ S) ∪ (S \ T)) : i ≤ j := D.le_max' i hi
  have hX := (digit_difference_bounds 5 (by norm_num) hj hmax).1
  have hT := (digit_difference_bounds 25 (by norm_num) hj hmax).2
  rw [geom_sum_eq (by norm_num : (5 : ℝ) ≠ 1)] at hX
  rw [geom_sum_eq (by norm_num : (25 : ℝ) ≠ 1)] at hT
  have hX' : 3 / 4 * (5 : ℝ) ^ j.val ≤ |digitX T - digitX S| := by
    unfold digitX
    norm_num at hX
    linarith
  have hBase : (25 : ℝ) ^ j.val = ((5 : ℝ) ^ j.val)^2 := by
    rw [show (25 : ℝ) = 5 ^ (2 : ℕ) by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hT' : |digitT T - digitT S| ≤ 25 / 24 * (((5 : ℝ) ^ j.val)^2) := by
    unfold digitT
    rw [show (1 + ∑ i ∈ T, (25 : ℝ)^i.val) - (1 + ∑ i ∈ S, (25 : ℝ)^i.val) =
      (∑ i ∈ T, (25 : ℝ)^i.val) - ∑ i ∈ S, (25 : ℝ)^i.val by ring]
    norm_num at hT
    rw [hBase] at hT
    linarith
  have hP : 0 < (5 : ℝ) ^ j.val := by positivity
  have hSq : (3 / 4 * (5 : ℝ) ^ j.val)^2 ≤ (digitX T - digitX S)^2 := by
    rw [← sq_abs (digitX T - digitX S)]
    gcongr
  have hStrict : 25 / 24 * (((5 : ℝ) ^ j.val)^2) <
      2 * (3 / 4 * (5 : ℝ) ^ j.val)^2 := by
    nlinarith [sq_pos_of_pos hP]
  exact hT'.trans_lt (hStrict.trans_le (mul_le_mul_of_nonneg_left hSq (by norm_num)))

lemma digit_edge {n : ℕ} {S : Finset (Fin n)} {i : Fin n} (hi : i ∉ S) :
    digitX S < digitX (insert i S) ∧
      digitT (insert i S) - digitT S = (digitX (insert i S) - digitX S)^2 := by
  unfold digitX digitT
  simp only [sum_insert hi]
  constructor
  · have hp : 0 < (5 : ℝ) ^ i.val := by positivity
    linarith
  · rw [show (25 : ℝ) = 5 ^ (2 : ℕ) by norm_num, ← pow_mul]
    rw [show (5 : ℝ) ^ i.val + (∑ j ∈ S, (5 : ℝ) ^ j.val) -
      ∑ j ∈ S, (5 : ℝ) ^ j.val = (5 : ℝ) ^ i.val by ring]
    rw [← pow_mul, Nat.mul_comm]
    ring

end OMA97
namespace OMA97

def middleLabels {n k : ℕ} : MiddleLeft n k ⊕ MiddleRight n k → Finset (Fin n)
  | .inl s => s.val
  | .inr s => s.val

lemma middleLabels_injective (n k : ℕ) :
    Function.Injective (@middleLabels n k) := by
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (Subtype.ext hij)
    | inr j =>
      have h := congrArg Finset.card hij
      change i.val.card = j.val.card at h
      rw [i.prop, j.prop] at h
      omega
  | inr i =>
    cases j with
    | inl j =>
      have h := congrArg Finset.card hij
      change i.val.card = j.val.card at h
      rw [i.prop, j.prop] at h
      omega
    | inr j => exact congrArg Sum.inr (Subtype.ext hij)

lemma middle_spread {n k : ℕ} (i j : MiddleLeft n k ⊕ MiddleRight n k) (hij : i ≠ j) :
    |digitT (middleLabels j) - digitT (middleLabels i)| <
      2 * (digitX (middleLabels j) - digitX (middleLabels i)) ^ 2 :=
  digit_spread fun h ↦ hij (middleLabels_injective n k h)

lemma middle_coordinate_edge {n k : ℕ} (e : MiddleEdge n k) :
    digitX (middleLabels (.inl (middleLeft e))) <
        digitX (middleLabels (.inr (middleRight e))) ∧
      digitT (middleLabels (.inr (middleRight e))) -
        digitT (middleLabels (.inl (middleLeft e))) =
        (digitX (middleLabels (.inr (middleRight e))) -
          digitX (middleLabels (.inl (middleLeft e)))) ^ 2 :=
  digit_edge e.2.prop

lemma middle_density_seven {k : ℕ} (hk : 13 ≤ k) :
    7 * (Fintype.card (MiddleLeft (2 * k + 1) k) +
      Fintype.card (MiddleRight (2 * k + 1) k)) ≤ Fintype.card (MiddleEdge (2 * k + 1) k) := by
  have h₀ : 14 ≤ k + 1 := by omega
  have h := Nat.mul_le_mul_right
    (Fintype.card (MiddleLeft (2 * k + 1) k) +
      Fintype.card (MiddleRight (2 * k + 1) k)) h₀
  rw [middle_density] at h
  omega

end OMA97


/-!
# A localized rotation lift for a finite bipartite graph

Polynomial growth of finite rotation sets gives overlaps without requiring the rotations
to be multiplicatively independent.
-/

open scoped BigOperators Topology RealInnerProductSpace
open Finset Filter

namespace Erdos97Lift

noncomputable def rotationBox {E : Type*} [Fintype E] (w : E → ℂ) (n : ℕ) :
    Finset ℂ := by
  classical
  exact (univ : Finset (E → Fin (n + 1))).image (fun a ↦ ∏ e, w e ^ (a e).val)

lemma mem_rotationBox {E : Type*} [Fintype E] (w : E → ℂ) (n : ℕ) (z : ℂ) :
    z ∈ rotationBox w n ↔ ∃ a : E → Fin (n + 1), (∏ e, w e ^ (a e).val) = z := by
  classical
  simp [rotationBox]

lemma rotationBox_nonempty {E : Type*} [Fintype E] (w : E → ℂ) (n : ℕ) :
    (rotationBox w n).Nonempty := by
  use 1
  exact (mem_rotationBox w n 1).2 ⟨fun _ ↦ 0, by simp⟩

lemma rotationBox_card {E : Type*} [Fintype E] (w : E → ℂ) (n : ℕ) :
    (rotationBox w n).card ≤ (n + 1) ^ Fintype.card E := by
  classical
  unfold rotationBox
  exact (Finset.card_image_le).trans_eq (by simp)

lemma rotationBox_subset {E : Type*} [Fintype E] (w : E → ℂ) (n : ℕ) :
    rotationBox w n ⊆ rotationBox w (n + 1) := by
  intro z hz
  obtain ⟨a, rfl⟩ := (mem_rotationBox w n z).1 hz
  exact (mem_rotationBox w (n + 1) _).2 ⟨fun e ↦ ⟨(a e).val, by omega⟩, rfl⟩

lemma rotationBox_mul_mem {E : Type*} [Fintype E] (w : E → ℂ) (n : ℕ)
    (e : E) {z : ℂ} (hz : z ∈ rotationBox w n) :
    w e * z ∈ rotationBox w (n + 1) := by
  classical
  obtain ⟨a, rfl⟩ := (mem_rotationBox w n z).1 hz
  let a' (j : E) : Fin (n + 1 + 1) :=
    if h : j = e then ⟨(a j).val + 1, by omega⟩ else ⟨(a j).val, by omega⟩
  apply (mem_rotationBox w (n + 1) _).2
  refine ⟨a', ?_⟩
  rw [← prod_erase_mul _ _ (mem_univ e), ← prod_erase_mul _ (fun j : E ↦ w j ^ (a j).val)
    (mem_univ e)]
  have hprod : (∏ j ∈ (univ : Finset E).erase e, w j ^ (a' j).val) =
      ∏ j ∈ (univ : Finset E).erase e, w j ^ (a j).val := by
    apply prod_congr rfl
    intro j hj
    simp [a', (mem_erase.mp hj).1]
  rw [hprod]
  simp [a', pow_succ, mul_comm, mul_assoc]

lemma exists_growth_cutoff (m : ℕ) : ∃ N : ℕ, (N + 1 : ℝ) ^ m < (3 / 2 : ℝ) ^ N := by
  have hsmall := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) m
    (by norm_num : 1 < (3 / 2 : ℝ))
  have hn := (Asymptotics.isLittleO_iff.1 hsmall)
    (show 0 < (1 / (2 ^ (m + 1)) : ℝ) by positivity)
  obtain ⟨n, hn1, hn2⟩ := ((eventually_ge_atTop (1 : ℕ)).and hn).exists
  refine ⟨n, ?_⟩
  have hcast : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hr : 0 < (3 / 2 : ℝ) ^ n := by positivity
  simp only [Real.norm_of_nonneg (pow_nonneg hn0 _), Real.norm_of_nonneg hr.le] at hn2
  calc
    ((n : ℝ) + 1) ^ m ≤ (2 * (n : ℝ)) ^ m := by
      gcongr
      linarith
    _ = (2 : ℝ) ^ m * (n : ℝ) ^ m := mul_pow .. 
    _ ≤ (2 : ℝ) ^ m * (1 / 2 ^ (m + 1) * (3 / 2) ^ n) :=
      mul_le_mul_of_nonneg_left hn2 (by positivity)
    _ = (3 / 2 : ℝ) ^ n / 2 := by
      rw [pow_succ]
      field_simp
    _ < (3 / 2 : ℝ) ^ n := by linarith

lemma rotationBox_growth {E : Type*} [Fintype E] (w : E → ℂ) {N : ℕ}
    (hN : (N + 1 : ℝ) ^ Fintype.card E < (3 / 2 : ℝ) ^ N) :
    ∃ n < N, 2 * (rotationBox w (n + 1)).card ≤ 3 * (rotationBox w n).card := by
  by_contra! h
  have hlarge (n : ℕ) (hn : n ≤ N) : (3 / 2 : ℝ) ^ n ≤ (rotationBox w n).card := by
    induction n with
    | zero =>
      simp only [pow_zero]
      exact_mod_cast (rotationBox_nonempty w 0).card_pos
    | succ n ih =>
      have hs : 3 * (rotationBox w n).card < 2 * (rotationBox w (n + 1)).card :=
        h n (by omega)
      have hstep : (3 / 2 : ℝ) * (rotationBox w n).card ≤ (rotationBox w (n + 1)).card := by
        have hs' : (3 : ℝ) * (rotationBox w n).card < 2 * (rotationBox w (n + 1)).card := by
          exact_mod_cast hs
        linarith
      simpa [pow_succ, mul_comm] using
        (mul_le_mul_of_nonneg_left (ih (by omega)) (by norm_num : (0 : ℝ) ≤ 3 / 2)).trans hstep
  have hupper : ((rotationBox w N).card : ℝ) ≤ (N + 1 : ℝ) ^ Fintype.card E := by
    exact_mod_cast rotationBox_card w N
  exact (not_lt_of_ge ((hlarge N le_rfl).trans hupper)) hN

lemma norm_pow_sub_one_le {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ n * ‖z - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    have heq : z * z ^ n - 1 = z * (z ^ n - 1) + (z - 1) := by ring
    rw [heq]
    calc
      ‖z * (z ^ n - 1) + (z - 1)‖ ≤ ‖z * (z ^ n - 1)‖ + ‖z - 1‖ :=
        norm_add_le .. 
      _ = ‖z ^ n - 1‖ + ‖z - 1‖ := by rw [Complex.norm_mul, hz, one_mul]
      _ ≤ n * ‖z - 1‖ + ‖z - 1‖ := add_le_add_left ih _
      _ = (n.succ : ℝ) * ‖z - 1‖ := by push_cast; ring

lemma norm_prod_sub_one_le {E : Type*} (s : Finset E) (u : E → ℂ)
    (hu : ∀ e, ‖u e‖ = 1) :
    ‖(∏ e ∈ s, u e) - 1‖ ≤ ∑ e ∈ s, ‖u e - 1‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert e s he ih =>
    rw [prod_insert he, sum_insert he]
    have heq : u e * (∏ j ∈ s, u j) - 1 =
        u e * ((∏ j ∈ s, u j) - 1) + (u e - 1) := by ring
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_mul, hu, one_mul, add_comm]
    exact add_le_add_right ih _

lemma rotationBox_norm {E : Type*} [Fintype E] {w : E → ℂ}
    (hw : ∀ e, ‖w e‖ = 1) {n : ℕ} {z : ℂ} (hz : z ∈ rotationBox w n) : ‖z‖ = 1 := by
  obtain ⟨a, rfl⟩ := (mem_rotationBox w n z).1 hz
  simp [norm_prod, norm_pow, hw]

lemma rotationBox_small {E : Type*} [Fintype E] {w : E → ℂ}
    (hw : ∀ e, ‖w e‖ = 1) {D : ℝ} (hD : ∀ e, ‖w e - 1‖ ≤ D)
    {n : ℕ} {z : ℂ} (hz : z ∈ rotationBox w n) :
    ‖z - 1‖ ≤ Fintype.card E * n * D := by
  classical
  obtain ⟨a, rfl⟩ := (mem_rotationBox w n z).1 hz
  refine (norm_prod_sub_one_le univ _ (fun e ↦ by simp [norm_pow, hw])).trans ?_
  calc
    (∑ e : E, ‖w e ^ (a e).val - 1‖) ≤ ∑ e : E, n * D := by
      apply sum_le_sum
      intro e _
      refine (norm_pow_sub_one_le (hw e) _).trans ?_
      gcongr
      exact_mod_cast Nat.le_of_lt_succ (a e).isLt
      exact hD e
    _ = _ := by simp [mul_assoc]

lemma rotationBox_overlap {E : Type*} [Fintype E] {w : E → ℂ}
    (hw : ∀ e, ‖w e‖ = 1) {n : ℕ}
    (hG : 2 * (rotationBox w (n + 1)).card ≤ 3 * (rotationBox w n).card)
    (e : E) :
    (rotationBox w n).card ≤
      2 * ((rotationBox w n).filter fun z ↦ w e * z ∈ rotationBox w n).card := by
  classical
  let K := rotationBox w n
  let f (z : ℂ) := w e * z
  let T := K.image f
  have hne : w e ≠ 0 := by
    intro h
    simpa [h] using hw e
  have hInj : Function.Injective f := by
    intro x y h
    exact mul_left_cancel₀ hne h
  have hcardT : T.card = K.card := card_image_of_injective _ hInj
  have hUnion : K ∪ T ⊆ rotationBox w (n + 1) := by
    intro z hz
    rcases mem_union.mp hz with hz | hz
    · exact rotationBox_subset w n hz
    · obtain ⟨y, hy, hEq⟩ := mem_image.mp hz
      rw [← hEq]
      exact rotationBox_mul_mem w n e hy
  have hImage : (K.filter fun z ↦ f z ∈ K).image f = K ∩ T := by
    ext x
    constructor
    · rintro hx
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      obtain ⟨hz, hzK⟩ := mem_filter.mp hz
      exact mem_inter.mpr ⟨hzK, mem_image.mpr ⟨_, hz, rfl⟩⟩
    · intro hx
      obtain ⟨hxK, hxT⟩ := mem_inter.mp hx
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hxT
      exact mem_image.mpr ⟨z, mem_filter.mpr ⟨hz, hxK⟩, rfl⟩
  have hcardInter : (K ∩ T).card = (K.filter fun z ↦ f z ∈ K).card := by
    rw [← hImage, card_image_of_injective _ hInj]
  have hSum := card_inter_add_card_union K T
  have hU := card_le_card hUnion
  change 2 * (rotationBox w (n + 1)).card ≤ 3 * K.card at hG
  rw [hcardInter, hcardT] at hSum
  change K.card ≤ 2 * (K.filter fun z ↦ f z ∈ K).card
  omega

lemma card_neighbors_erase {X : Type*} [DecidableEq X] (r : X → X → Prop)
    [DecidableRel r] (P : Finset X) {p : X} (hp : p ∈ P) (x : X) :
    (P.filter (r x)).card = ((P.erase p).filter (r x)).card + if r x p then 1 else 0 := by
  simp only [Finset.card_filter]
  exact (P.sum_erase_add (fun y ↦ if r x y then 1 else 0) hp).symm

lemma sum_neighbors_erase {X : Type*} [DecidableEq X] (r : X → X → Prop)
    [DecidableRel r] (hsymm : ∀ {x y}, r x y → r y x) (hirr : ∀ x, ¬ r x x)
    (P : Finset X) {p : X} (hp : p ∈ P) :
    ∑ x ∈ P, (P.filter (r x)).card =
      (∑ x ∈ P.erase p, ((P.erase p).filter (r x)).card) + 2 * (P.filter (r p)).card := by
  rw [← P.sum_erase_add (fun x ↦ (P.filter (r x)).card) hp]
  have hOne : (∑ x ∈ P.erase p, (if r x p then 1 else 0 : ℕ)) = (P.filter (r p)).card := by
    have hCom : (∑ x ∈ P.erase p, (if r x p then 1 else 0 : ℕ)) =
        ∑ x ∈ P.erase p, (if r p x then 1 else 0 : ℕ) := by
      apply sum_congr rfl
      intro x _
      simp only [show r x p ↔ r p x from ⟨hsymm, hsymm⟩]
    rw [hCom, card_neighbors_erase r P hp p]
    simp [hirr]
  have hDistribute : ∑ x ∈ P.erase p, (P.filter (r x)).card =
      (∑ x ∈ P.erase p, ((P.erase p).filter (r x)).card) +
        (∑ x ∈ P.erase p, (if r x p then 1 else 0 : ℕ)) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun x _ ↦ card_neighbors_erase r P hp x)
  rw [hDistribute, hOne]
  omega

lemma dense_core {X : Type*} [DecidableEq X] (r : X → X → Prop)
    [DecidableRel r] (hsymm : ∀ {x y}, r x y → r y x) (hirr : ∀ x, ¬ r x x)
    (d : ℕ) (P : Finset X) (hP : 2 * d * P.card < ∑ x ∈ P, (P.filter (r x)).card) :
    ∃ Q ⊆ P, Q.Nonempty ∧ ∀ x ∈ Q, d + 1 ≤ (Q.filter (r x)).card := by
  induction P using Finset.strongInductionOn
  rename_i P ih
  by_cases h : ∀ x ∈ P, d + 1 ≤ (P.filter (r x)).card
  · have hne : P.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty.mp hne] at hP
      simp at hP
    exact ⟨P, subset_rfl, hne, h⟩
  · push Not at h
    obtain ⟨p, hp, hSmall⟩ := h
    have hDelete := sum_neighbors_erase r hsymm hirr P hp
    have hCard := card_erase_add_one hp
    have hDensity : 2 * d * (P.erase p).card <
        ∑ x ∈ P.erase p, ((P.erase p).filter (r x)).card := by
      rw [← hCard, mul_add, mul_one, hDelete] at hP
      omega
    obtain ⟨Q, hQ, hne, hMin⟩ := ih (P.erase p) (erase_ssubset hp) hDensity
    exact ⟨Q, hQ.trans (erase_subset _ _), hne, hMin⟩

lemma cardinal_ordered_edges {X : Type*} (P : Finset X) (r : X → X → Prop)
    [DecidableRel r] :
    ((P ×ˢ P).filter (fun q ↦ r q.1 q.2)).card = ∑ x ∈ P, (P.filter (r x)).card := by
  simp only [Finset.card_filter, Finset.sum_product]

lemma strict_support_of_equal_norm {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {a b : X} (hne : a ≠ b) (hNorm : ‖a‖ = ‖b‖) : inner ℝ a b < inner ℝ a a := by
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two a b,
    real_inner_self_eq_norm_mul_norm, hNorm]
  have hpos := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  nlinarith

lemma rotated_support {V : Type*} (b : V → ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hUnit : ∀ i, ‖b i‖ ≤ 1)
    (hSeed : ∀ i j, i ≠ j → (star (b i) * b j).re + σ ≤ Complex.normSq (b i))
    {i j : V} (hij : i ≠ j) {s t : ℂ}
    (hs : ‖s‖ = 1) (ht : ‖t‖ = 1) (hS : ‖s - 1‖ ≤ σ / 4) (hT : ‖t - 1‖ ≤ σ / 4) :
    inner ℝ (b i * s) (b j * t) < inner ℝ (b i * s) (b i * s) := by
  have hDiff (c v : ℂ) (hc : ‖c‖ ≤ 1) (hv : ‖v - 1‖ ≤ σ / 4) :
      ‖c * v - c‖ ≤ σ / 4 := by
    rw [show c * v - c = c * (v - 1) by ring, Complex.norm_mul]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by simpa using hv)
  have h1 : inner ℝ (b i * s - b i) (b j * t) ≤ σ / 4 := by
    calc
      inner ℝ (b i * s - b i) (b j * t) ≤ ‖b i * s - b i‖ * ‖b j * t‖ := real_inner_le_norm ..
      _ = ‖b i * s - b i‖ * ‖b j‖ := by rw [Complex.norm_mul, ht, mul_one]
      _ ≤ σ / 4 := by
        have hh := mul_le_mul_of_nonneg_left (hUnit j) (norm_nonneg (b i * s - b i))
        simpa only [mul_one] using hh.trans (by simpa using hDiff (b i) s (hUnit i) hS)
  have h2 : inner ℝ (b i) (b j * t - b j) ≤ σ / 4 := by
    calc
      inner ℝ (b i) (b j * t - b j) ≤ ‖b i‖ * ‖b j * t - b j‖ := real_inner_le_norm ..
      _ ≤ σ / 4 := by
        have hh := mul_le_mul_of_nonneg_right (hUnit i) (norm_nonneg (b j * t - b j))
        simpa only [one_mul] using hh.trans (by simpa using hDiff (b j) t (hUnit j) hT)
  have h3 : inner ℝ (b i) (b j) + σ ≤ inner ℝ (b i) (b i) := by
    rw [Complex.inner (b i) (b j), real_inner_self_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    change (b j * star (b i)).re + σ ≤ _
    rw [mul_comm]
    exact hSeed i j hij
  have h4 : inner ℝ (b i * s) (b i * s) = inner ℝ (b i) (b i) := by
    simp only [real_inner_self_eq_norm_sq, Complex.norm_mul, hs, mul_one]
  rw [inner_sub_left] at h1
  rw [inner_sub_right] at h2
  linarith

theorem exists_complex_core {L R E : Type*} [Fintype L] [Fintype R] [Fintype E]
    [Nonempty (L ⊕ R)] (left : E → L) (right : E → R)
    (hSimple : Function.Injective (fun e ↦ (left e, right e))) (d : ℕ)
    (hDense : (2 * d + 1) * (Fintype.card L + Fintype.card R) ≤ Fintype.card E)
    (hSeeds : ∀ C : ℕ, ∃ (b : L ⊕ R → ℂ) (w : E → ℂ) (σ : ℝ), 0 < σ ∧
      (∀ i, b i ≠ 0 ∧ ‖b i‖ ≤ 1) ∧
      (∀ i j, i ≠ j → (star (b i) * b j).re + σ ≤ Complex.normSq (b i)) ∧
      ∀ e, ‖w e‖ = 1 ∧ ‖b (.inl (left e)) - b (.inr (right e)) * w e‖ = 1 ∧
        (C : ℝ) * ‖w e - 1‖ ≤ σ / 4) :
    ∃ Q : Finset ℂ, Q.Nonempty ∧
      (∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → inner ℝ a b < inner ℝ a a) ∧
      ∀ a ∈ Q, d + 1 ≤ (Q.filter fun b ↦ dist a b = 1).card := by
  classical
  obtain ⟨N, hN⟩ := exists_growth_cutoff (Fintype.card E)
  let C := Fintype.card E * N + 1
  obtain ⟨b, w, σ, hσ, hb, hSupport, hw⟩ := hSeeds C
  have hW : ∀ e, ‖w e‖ = 1 := fun e ↦ (hw e).1
  obtain ⟨n, hnN, hGrowth⟩ := rotationBox_growth w hN
  let K := rotationBox w n
  have hKPos : 0 < K.card := (rotationBox_nonempty w n).card_pos
  have hCP : (0 : ℝ) < C := by
    exact_mod_cast (Nat.succ_pos (Fintype.card E * N))
  have hWK : ∀ e, ‖w e - 1‖ ≤ σ / 4 / C := by
    intro e
    exact (le_div_iff₀ hCP).2 (by simpa [mul_comm] using (hw e).2.2)
  have hKSmall (z : ℂ) (hz : z ∈ K) : ‖z - 1‖ ≤ σ / 4 := by
    have hh := rotationBox_small hW hWK hz
    have hcoef : (Fintype.card E : ℝ) * n ≤ C := by
      exact_mod_cast (show Fintype.card E * n ≤ C by
        exact (Nat.mul_le_mul_left _ hnN.le).trans (Nat.le_succ _))
    exact hh.trans <| (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans_eq <| by
      field_simp
  let I := (univ : Finset (L ⊕ R)) ×ˢ K
  let p (x : (L ⊕ R) × ℂ) : ℂ := b x.1 * x.2
  have hI (x : (L ⊕ R) × ℂ) : x ∈ I ↔ x.2 ∈ K := by simp [I]
  have hPS (x y : (L ⊕ R) × ℂ) (hx : x ∈ I) (hy : y ∈ I) (hxy : x ≠ y) :
      inner ℝ (p x) (p y) < inner ℝ (p x) (p x) := by
    have hxK := (hI x).1 hx
    have hyK := (hI y).1 hy
    have hxNorm := rotationBox_norm hW hxK
    have hyNorm := rotationBox_norm hW hyK
    by_cases he : x.1 = y.1
    · apply strict_support_of_equal_norm
      · intro hEq
        apply hxy
        refine Prod.ext he ?_
        change b x.1 * x.2 = b y.1 * y.2 at hEq
        rw [← he] at hEq
        exact mul_left_cancel₀ (hb x.1).1 hEq
      · simp [p, hxNorm, hyNorm, he]
    · exact rotated_support b hσ (fun i ↦ (hb i).2) hSupport he hxNorm hyNorm
        (hKSmall x.2 hxK) (hKSmall y.2 hyK)
  have hPointInj : Set.InjOn p (I : Set ((L ⊕ R) × ℂ)) := by
    intro x hx y hy hxy
    by_contra hne
    have hStrict := hPS x y hx hy hne
    rw [hxy] at hStrict
    exact (lt_irrefl _) hStrict
  let P := I.image p
  have hPCard : P.card = (Fintype.card L + Fintype.card R) * K.card := by
    change (I.image p).card = _
    rw [card_image_of_injOn hPointInj]
    simp [I]
  have hPStrict (x : ℂ) (hx : x ∈ P) (y : ℂ) (hy : y ∈ P) (hne : x ≠ y) :
      inner ℝ x y < inner ℝ x x := by
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hy
    exact hPS a c ha hc (fun he ↦ hne (congrArg p he))
  have hPPos : 0 < P.card := by
    rw [hPCard, ← Fintype.card_sum]
    exact Nat.mul_pos Fintype.card_pos hKPos
  let s (e : E) := K.filter fun z ↦ w e * z ∈ K
  let D := (univ : Finset E).sigma s
  have hChoice (x : Σ _ : E, ℂ) (hx : x ∈ D) : x.2 ∈ K ∧ w x.1 * x.2 ∈ K :=
    mem_filter.mp ((mem_sigma.mp hx).2)
  have hDCard : Fintype.card E * K.card ≤ 2 * D.card := by
    calc
      Fintype.card E * K.card = ∑ e : E, K.card := by simp
      _ ≤ ∑ e : E, 2 * (s e).card :=
        sum_le_sum fun e _ ↦ rotationBox_overlap hW hGrowth e
      _ = 2 * D.card := by simp [D, card_sigma, mul_sum]
  let a (x : Σ _ : E, ℂ) : (L ⊕ R) × ℂ := (.inl (left x.1), x.2)
  let c (x : Σ _ : E, ℂ) : (L ⊕ R) × ℂ := (.inr (right x.1), w x.1 * x.2)
  have hA (x : Σ _ : E, ℂ) (hx : x ∈ D) : a x ∈ I := (hI _).2 (hChoice x hx).1
  have hB (x : Σ _ : E, ℂ) (hx : x ∈ D) : c x ∈ I := (hI _).2 (hChoice x hx).2
  let f (x : Σ _ : E, ℂ) : ℂ × ℂ := (p (a x), p (c x))
  have hFInj : Set.InjOn f (D : Set (Σ _ : E, ℂ)) := by
    rintro ⟨e, z⟩ hz ⟨e', z'⟩ hz' hEq
    have hLeft := hPointInj (hA _ hz) (hA _ hz') (congrArg Prod.fst hEq)
    have hRight := hPointInj (hB _ hz) (hB _ hz') (congrArg Prod.snd hEq)
    have he : e = e' := hSimple <| Prod.ext (Sum.inl.inj (congrArg Prod.fst hLeft))
      (Sum.inr.inj (congrArg Prod.fst hRight))
    have hh : z = z' := congrArg Prod.snd hLeft
    subst e'
    subst z'
    rfl
  let F := D.image f
  let T := F.image Prod.swap
  have hFCard : F.card = D.card := card_image_of_injOn hFInj
  have hTCard : T.card = F.card := card_image_of_injective _ Prod.swap_injective
  have hDis : Disjoint F T := by
    rw [Finset.disjoint_left]
    intro z hz hzT
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    obtain ⟨u, hu, hEq⟩ := mem_image.mp hzT
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hu
    have hbad := hPointInj (hB _ hy) (hA _ hx) (congrArg Prod.fst hEq)
    cases congrArg Prod.fst hbad
  have hFEdges : F ⊆ (P ×ˢ P).filter (fun q ↦ dist q.1 q.2 = 1) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    rw [mem_filter, mem_product]
    refine ⟨⟨mem_image.mpr ⟨a x, hA _ hx, rfl⟩, mem_image.mpr ⟨c x, hB _ hx, rfl⟩⟩, ?_⟩
    change dist (b (.inl (left x.1)) * x.2) (b (.inr (right x.1)) * (w x.1 * x.2)) = 1
    rw [dist_eq_norm]
    rw [show b (.inl (left x.1)) * x.2 -
      b (.inr (right x.1)) * (w x.1 * x.2) =
      (b (.inl (left x.1)) - b (.inr (right x.1)) * w x.1) * x.2 by ring]
    rw [Complex.norm_mul, (hw x.1).2.1, rotationBox_norm hW (hChoice x hx).1, one_mul]
  have hUnion : F ∪ T ⊆ (P ×ˢ P).filter (fun q ↦ dist q.1 q.2 = 1) := by
    intro z hz
    rcases mem_union.mp hz with hzF | hzT
    · exact hFEdges hzF
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp hzT
      have hyE := hFEdges hy
      simp only [mem_filter, mem_product] at hyE ⊢
      exact ⟨⟨hyE.1.2, hyE.1.1⟩, (dist_comm ..).trans hyE.2⟩
  have hSum : (2 * d + 1) * P.card ≤ ∑ z ∈ P, (P.filter fun y ↦ dist z y = 1).card := by
    calc
      (2 * d + 1) * P.card = ((2 * d + 1) * (Fintype.card L + Fintype.card R)) * K.card := by
        rw [hPCard, mul_assoc]
      _ ≤ Fintype.card E * K.card := Nat.mul_le_mul_right _ hDense
      _ ≤ 2 * D.card := hDCard
      _ = (F ∪ T).card := by
        rw [card_union_of_disjoint hDis, hTCard, hFCard, two_mul]
      _ ≤ ((P ×ˢ P).filter (fun q ↦ dist q.1 q.2 = 1)).card := card_le_card hUnion
      _ = _ := cardinal_ordered_edges P (fun x y : ℂ ↦ dist x y = 1)
  have hDenseP : 2 * d * P.card < ∑ z ∈ P, (P.filter fun y ↦ dist z y = 1).card := by
    rw [add_mul, one_mul] at hSum
    omega
  obtain ⟨Q, hQP, hQ, hDegrees⟩ := dense_core (fun x y : ℂ ↦ dist x y = 1)
    (fun {_ _} h ↦ (dist_comm ..).trans h) (by simp) d P hDenseP
  exact ⟨Q, hQ, fun x hx y hy ↦ hPStrict x (hQP hx) y (hQP hy), hDegrees⟩

end Erdos97Lift


/-! # Transfer unit-distance configurations to the Euclidean plane -/

open EuclideanGeometry
open scoped InnerProductSpace

namespace OMA.Erdos97Seed

lemma convex_independent_of_inner {P : Finset ℝ²}
    (h : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ⟪x, y⟫_ℝ < ⟪x, x⟫_ℝ) : ConvexIndep P := by
  intro x hx hh
  let f := (innerSL ℝ x).toLinearMap
  have hc : Convex ℝ {y | f y < f x} := convex_halfSpace_lt f.isLinear _
  have hs : ((P : Set ℝ²) \ {x}) ⊆ {y | f y < f x} := by
    rintro y ⟨hy, hyx⟩
    exact h x hx y hy (fun hxy ↦ hyx (Set.mem_singleton_iff.mpr hxy.symm))
  have hfx := convexHull_min hs hc hh
  change f x < f x at hfx
  exact (lt_irrefl (f x)) hfx

lemma plane_of_complex (k : ℕ)
    (hex : ∃ Q : Finset ℂ, Q.Nonempty ∧
      (∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → ⟪x, y⟫_ℝ < ⟪x, x⟫_ℝ) ∧
      ∀ x ∈ Q, k ≤ (Q.filter fun y ↦ dist x y = 1).card) :
    ∃ P : Finset ℝ², P.Nonempty ∧ ConvexIndep P ∧ Erdos97.HasNEquidistantProperty k P := by
  classical
  rcases hex with ⟨Q, hQ, hSupport, hDegree⟩
  let e := Complex.orthonormalBasisOneI.repr
  let P := Q.image e
  refine ⟨P, hQ.image _, convex_independent_of_inner ?_, ?_⟩
  · rintro _ hx _ hy hxy
    obtain ⟨x, hxQ, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hyQ, rfl⟩ := Finset.mem_image.mp hy
    have hne : x ≠ y := fun heq ↦ hxy (congrArg e heq)
    rw [e.inner_map_map, e.inner_map_map]
    exact hSupport x hxQ y hyQ hne
  · intro p hp
    obtain ⟨x, hxQ, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨1, zero_lt_one, (hDegree x hxQ).trans ?_⟩
    have he : ((Q.filter fun y ↦ dist x y = 1).image e) ⊆
        P.filter (fun y ↦ dist (e x) y = 1) := by
      intro q hq
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hyQ, hyD⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem e hyQ, by rwa [e.isometry.dist_eq]⟩
    calc
      (Q.filter fun y ↦ dist x y = 1).card =
          ((Q.filter fun y ↦ dist x y = 1).image e).card :=
        (Finset.card_image_of_injective _ e.injective).symm
      _ ≤ _ := Finset.card_le_card he

end OMA.Erdos97Seed
namespace OMA97

lemma unit_degree_core (d : ℕ) :
    ∃ Q : Finset ℂ, Q.Nonempty ∧
      (∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → inner ℝ a b < inner ℝ a a) ∧
      ∀ a ∈ Q, d + 1 ≤ (Q.filter fun b ↦ dist a b = 1).card := by
  let k := 4 * d + 1
  let n := 2 * k + 1
  let : Nonempty (MiddleLeft n k ⊕ MiddleRight n k) := middle_nonempty (by dsimp [n]; omega)
  have hDensity :
      (2 * d + 1) * (Fintype.card (MiddleLeft n k) + Fintype.card (MiddleRight n k)) ≤
        Fintype.card (MiddleEdge n k) := by
    have h :
        (k + 1) * (Fintype.card (MiddleLeft n k) + Fintype.card (MiddleRight n k)) =
          2 * Fintype.card (MiddleEdge n k) := middle_density k
    have hk : k + 1 = 2 * (2 * d + 1) := by dsimp [k]; omega
    have hMul := congrArg (fun j : ℕ ↦ j *
      (Fintype.card (MiddleLeft n k) + Fintype.card (MiddleRight n k))) hk
    have h' := hMul.symm.trans h
    rw [mul_assoc] at h'
    omega
  exact Erdos97Lift.exists_complex_core (@middleLeft n k) (@middleRight n k)
    (middleEndpoints_injective n k) d hDensity
    (OMA.Erdos97Seed.exists_seeds middleLeft middleRight
      (fun i ↦ digitX (middleLabels i)) (fun i ↦ digitT (middleLabels i))
      middle_spread middle_coordinate_edge)

end OMA97
theorem OMA.disproof : ¬ (type_of% @Erdos97.erdos_97) := by
  obtain ⟨P, hP, hConvex, hNear⟩ := OMA.Erdos97Seed.plane_of_complex 4 (OMA97.unit_degree_core 3)
  exact fun h ↦ h P hP hConvex hNear
