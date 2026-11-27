import FormalConjectures.Other.VCDimConvex

/-!
# Infinite convex shattering in `ℝ³`

We prove `VCDimConvex.exists_infinite_convex_r3_shatters`: there exist an infinite set `A ⊆ ℝ³`
and a convex set `C ⊆ ℝ³` such that the translate family `{t +ᵥ C | t : ℝ³}` shatters `A`.

## Proof outline
1. Fix a bijection `e : Set ℕ ≃ ℝ` (since `|Set ℕ| = 2^ℵ₀ = |ℝ|`).
2. Let `Kopen = { p : ℝ³ | (p 0)^2 + (p 1)^2 < p 2 }` be the strict epigraph of the paraboloid,
   `A = { (0, k, k^2) | k : ℕ }`, and
   `E = { (e S, k, (e S)^2 + k^2) | S : Set ℕ, k ∈ S }` on the boundary of the paraboloid.
3. Put `C = Kopen ∪ E`. By strict convexity of `(x, y) ↦ x^2 + y^2`, every open line segment
   between two distinct points of `C` lies strictly in `Kopen ⊆ C`, so `C` is convex.
4. For any `B ⊆ A`, let `S = { k | (0, k, k^2) ∈ B }` and `t = (-e S, 0, -(e S)^2)`. Then for each
   `k : ℕ`, `(0, k, k^2) - t = (e S, k, (e S)^2 + k^2)` lies on the paraboloid boundary, so it
   belongs to `C` if and only if it belongs to `E`, which by injectivity of `e` holds if and only
   if `k ∈ S`, i.e., `(0, k, k^2) ∈ B`. Thus `A ∩ (t +ᵥ C) = B`.
-/

-- Problem: VCₙ dimension of convex sets in ℝⁿ, ℝⁿ⁺¹, ℝⁿ⁺² — exists infinite convex r3 shatters
-- Upstream: formal-conjectures FormalConjectures/Other/VCDimConvex.lean:47 (declaration VCDimConvex.exists_infinite_convex_r3_shatters)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace VCDimConvexR3Proof

open scoped EuclideanGeometry Pointwise

private def pt (x y z : ℝ) : ℝ³ := WithLp.toLp 2 ![x, y, z]

private lemma pt_0 (x y z : ℝ) : pt x y z 0 = x := rfl
private lemma pt_1 (x y z : ℝ) : pt x y z 1 = y := rfl
private lemma pt_2 (x y z : ℝ) : pt x y z 2 = z := rfl

private lemma eq_of_coords {p q : ℝ³} (h0 : p 0 = q 0) (h1 : p 1 = q 1) (h2 : p 2 = q 2) :
    p = q := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private lemma convex_paraboloid_union_boundary (E : Set ℝ³)
    (hE : ∀ p ∈ E, (p 0) ^ 2 + (p 1) ^ 2 = p 2) :
    Convex ℝ ({ p : ℝ³ | (p 0) ^ 2 + (p 1) ^ 2 < p 2 } ∪ E) := by
  intro p hp q hq a b ha hb hab
  by_cases ha0 : a = 0
  · subst ha0
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hq
  by_cases hb0 : b = 0
  · subst hb0
    have ha1 : a = 1 := by linarith
    subst ha1
    simpa using hp
  by_cases hpq : p = q
  · subst hpq
    rw [← add_smul, hab, one_smul]
    exact hp
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hp_le : (p 0) ^ 2 + (p 1) ^ 2 ≤ p 2 := by
    rcases hp with hp | hp
    · exact le_of_lt hp
    · exact le_of_eq (hE p hp)
  have hq_le : (q 0) ^ 2 + (q 1) ^ 2 ≤ q 2 := by
    rcases hq with hq | hq
    · exact le_of_lt hq
    · exact le_of_eq (hE q hq)
  left
  change ((a • p + b • q) 0) ^ 2 + ((a • p + b • q) 1) ^ 2 < (a • p + b • q) 2
  have h0 : (a • p + b • q) 0 = a * p 0 + b * q 0 := by simp
  have h1 : (a • p + b • q) 1 = a * p 1 + b * q 1 := by simp
  have h2 : (a • p + b • q) 2 = a * p 2 + b * q 2 := by simp
  rw [h0, h1, h2]
  have hid :
      (a * p 0 + b * q 0) ^ 2 + (a * p 1 + b * q 1) ^ 2 +
        a * b * ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) =
      a * ((p 0) ^ 2 + (p 1) ^ 2) + b * ((q 0) ^ 2 + (q 1) ^ 2) := by
    have h1a : a * (1 - a) = a * b := by nlinarith
    have h1b : b * (1 - b) = a * b := by nlinarith
    nlinarith
  by_cases hxy : p 0 = q 0 ∧ p 1 = q 1
  · have h2ne : p 2 ≠ q 2 := fun h2eq => hpq (eq_of_coords hxy.1 hxy.2 h2eq)
    have hstrict : (p 0) ^ 2 + (p 1) ^ 2 < p 2 ∨ (q 0) ^ 2 + (q 1) ^ 2 < q 2 := by
      rcases hp with hp | hp
      · exact Or.inl hp
      · rcases hq with hq | hq
        · exact Or.inr hq
        · exfalso
          have ep := hE p hp
          have eq_ := hE q hq
          rw [hxy.1, hxy.2] at ep
          exact h2ne (ep.symm.trans eq_)
    rcases hstrict with hlt | hlt
    · have h1' : a * ((p 0) ^ 2 + (p 1) ^ 2) < a * p 2 := mul_lt_mul_of_pos_left hlt ha_pos
      have h2' : b * ((q 0) ^ 2 + (q 1) ^ 2) ≤ b * q 2 := mul_le_mul_of_nonneg_left hq_le hb
      have h0diff : a * b * ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) = 0 := by
        rw [hxy.1, hxy.2]; ring
      linarith
    · have h1' : a * ((p 0) ^ 2 + (p 1) ^ 2) ≤ a * p 2 := mul_le_mul_of_nonneg_left hp_le ha
      have h2' : b * ((q 0) ^ 2 + (q 1) ^ 2) < b * q 2 := mul_lt_mul_of_pos_left hlt hb_pos
      have h0diff : a * b * ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) = 0 := by
        rw [hxy.1, hxy.2]; ring
      linarith
  · have hdiff_pos : 0 < (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
      by_cases hx : p 0 = q 0
      · have hy : p 1 ≠ q 1 := fun hy => hxy ⟨hx, hy⟩
        have hsq : 0 < (p 1 - q 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hy)
        nlinarith [sq_nonneg (p 0 - q 0)]
      · have hsq : 0 < (p 0 - q 0) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
        nlinarith [sq_nonneg (p 1 - q 1)]
    have hab_diff : 0 < a * b * ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) := by positivity
    have h1' : a * ((p 0) ^ 2 + (p 1) ^ 2) ≤ a * p 2 := mul_le_mul_of_nonneg_left hp_le ha
    have h2' : b * ((q 0) ^ 2 + (q 1) ^ 2) ≤ b * q 2 := mul_le_mul_of_nonneg_left hq_le hb
    linarith

end VCDimConvexR3Proof

open VCDimConvex VCDimConvexR3Proof
open scoped EuclideanGeometry Pointwise

theorem OMA.solution : type_of% @VCDimConvex.exists_infinite_convex_r3_shatters := by
  have hcard : Nonempty (Set ℕ ≃ ℝ) :=
    Cardinal.eq.mp (by
      rw [Cardinal.mk_set, Cardinal.mk_nat, Cardinal.two_power_aleph0, Cardinal.mk_real])
  rcases hcard with ⟨e⟩
  let a : ℕ → ℝ³ := fun k => pt 0 (k : ℝ) ((k : ℝ) ^ 2)
  let A : Set ℝ³ := Set.range a
  let E : Set ℝ³ := { p : ℝ³ | ∃ (S : Set ℕ) (k : ℕ),
    k ∈ S ∧ p = pt (e S) (k : ℝ) ((e S) ^ 2 + (k : ℝ) ^ 2) }
  let C : Set ℝ³ := { p : ℝ³ | (p 0) ^ 2 + (p 1) ^ 2 < p 2 } ∪ E
  refine ⟨A, C, ?_, ?_, ?_⟩
  · refine Set.infinite_range_of_injective fun k₁ k₂ h => ?_
    have h1 : (k₁ : ℝ) = (k₂ : ℝ) := by
      simpa [a, pt_1] using congr_arg (fun p : ℝ³ => p 1) h
    exact Nat.cast_injective h1
  · refine convex_paraboloid_union_boundary E ?_
    rintro p ⟨S, k, _, rfl⟩
    simp [pt_0, pt_1, pt_2]
  · intro B hBA
    let S : Set ℕ := { k : ℕ | a k ∈ B }
    let t : ℝ³ := pt (-e S) 0 (-(e S) ^ 2)
    refine ⟨t +ᵥ C, ⟨t, rfl⟩, ?_⟩
    ext x
    constructor
    · rintro ⟨⟨k, rfl⟩, hxC⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxC
      have hdiff : -t +ᵥ a k = pt (e S) (k : ℝ) ((e S) ^ 2 + (k : ℝ) ^ 2) := by
        apply eq_of_coords
        · simp [a, t, pt_0]
        · simp [a, t, pt_1]
        · simp [a, t, pt_2]
      rw [hdiff] at hxC
      rcases hxC with hlt | ⟨S', k', hk', heq⟩
      · exfalso
        simp [pt_0, pt_1, pt_2] at hlt
      · have h0 : e S = e S' := by
          simpa [pt_0] using congr_arg (fun p : ℝ³ => p 0) heq
        have h1 : (k : ℝ) = (k' : ℝ) := by
          simpa [pt_1] using congr_arg (fun p : ℝ³ => p 1) heq
        have hS : S = S' := e.injective h0
        have hk : k = k' := Nat.cast_injective h1
        rw [← hS, ← hk] at hk'
        exact hk'
    · intro hxB
      have hxA : x ∈ A := hBA hxB
      rcases hxA with ⟨k, rfl⟩
      refine ⟨⟨k, rfl⟩, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      have hdiff : -t +ᵥ a k = pt (e S) (k : ℝ) ((e S) ^ 2 + (k : ℝ) ^ 2) := by
        apply eq_of_coords
        · simp [a, t, pt_0]
        · simp [a, t, pt_1]
        · simp [a, t, pt_2]
      rw [hdiff]
      exact Or.inr ⟨S, k, hxB, rfl⟩
