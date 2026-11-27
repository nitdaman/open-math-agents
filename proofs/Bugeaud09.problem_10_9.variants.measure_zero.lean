import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_9

-- Problem: Bugeaud Collection of Conjectures and Open Questions: Mahler's Z-numbers — measure zero
-- Upstream: formal-conjectures FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_9.lean:64 (declaration Bugeaud09.problem_10_9.variants.measure_zero)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Proof idea (Mahler). Write `g = ⌊x⌋` and `k = ⌊3x/2⌋` for `x = ξ (3/2)^n`. If both fractional
parts are below `1/2` then `3g ≤ 2k ≤ 3g + 1`, so `k` is determined by `g`. Hence for a Z-number
all the floors `⌊ξ (3/2)^n⌋` are determined by the first one. Two Z-numbers with the same first
floor then satisfy `|ξ - η| (3/2)^n < 1` for all `n ≥ 1`, so they are equal. The set of
Z-numbers therefore injects into `ℤ`, is countable, and has Lebesgue measure zero.
-/

namespace OMAQ

theorem floor_bounds (z : ℝ) (h1 : Int.fract z < 1 / 2) (h2 : Int.fract (z * (3 / 2)) < 1 / 2) :
    3 * ⌊z⌋ ≤ 2 * ⌊z * (3 / 2)⌋ ∧ 2 * ⌊z * (3 / 2)⌋ ≤ 3 * ⌊z⌋ + 1 := by
  rw [Int.fract] at h1 h2
  have a1 := Int.floor_le z
  have a2 := Int.floor_le (z * (3 / 2))
  constructor
  · have h : (3 * ⌊z⌋ : ℝ) < 2 * ⌊z * (3 / 2)⌋ + 1 := by linarith
    have h3 : 3 * ⌊z⌋ < 2 * ⌊z * (3 / 2)⌋ + 1 := by exact_mod_cast h
    omega
  · have h : (2 * ⌊z * (3 / 2)⌋ : ℝ) < 3 * ⌊z⌋ + 2 := by linarith
    have h3 : 2 * ⌊z * (3 / 2)⌋ < 3 * ⌊z⌋ + 2 := by exact_mod_cast h
    omega

theorem step (x y : ℝ) (h : ⌊x⌋ = ⌊y⌋) (hx : Int.fract x < 1 / 2) (hy : Int.fract y < 1 / 2)
    (hx' : Int.fract (x * (3 / 2)) < 1 / 2) (hy' : Int.fract (y * (3 / 2)) < 1 / 2) :
    ⌊x * (3 / 2)⌋ = ⌊y * (3 / 2)⌋ := by
  have a := floor_bounds x hx hx'
  have b := floor_bounds y hy hy'
  rw [h] at a
  omega

theorem zinj (ξ η : ℝ) (hξ : IsZNumber ξ) (hη : IsZNumber η)
    (h1 : ⌊ξ * (3 / 2 : ℝ) ^ 1⌋ = ⌊η * (3 / 2 : ℝ) ^ 1⌋) : ξ = η := by
  have hfl : ∀ n, 1 ≤ n → ⌊ξ * (3 / 2 : ℝ) ^ n⌋ = ⌊η * (3 / 2 : ℝ) ^ n⌋ := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact h1
    | succ n hn ih =>
      have e1 : ξ * (3 / 2 : ℝ) ^ (n + 1) = ξ * (3 / 2) ^ n * (3 / 2) := by ring
      have e2 : η * (3 / 2 : ℝ) ^ (n + 1) = η * (3 / 2) ^ n * (3 / 2) := by ring
      rw [e1, e2]
      refine step _ _ ih (hξ.2 n hn) (hη.2 n hn) ?_ ?_
      · rw [← e1]; exact hξ.2 (n + 1) (by omega)
      · rw [← e2]; exact hη.2 (n + 1) (by omega)
  have hb : ∀ n, 1 ≤ n → |ξ - η| * (3 / 2 : ℝ) ^ n < 1 := by
    intro n hn
    have hx := hξ.2 n hn
    have hy := hη.2 n hn
    rw [Int.fract] at hx hy
    have e := hfl n hn
    have a := Int.floor_le (ξ * (3 / 2 : ℝ) ^ n)
    have b := Int.floor_le (η * (3 / 2 : ℝ) ^ n)
    rw [e] at hx a
    have hp : (0 : ℝ) < (3 / 2) ^ n := by positivity
    rw [← abs_of_pos hp, ← abs_mul, sub_mul, abs_lt]
    constructor <;> linarith
  by_contra hne
  have hpos : 0 < |ξ - η| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / |ξ - η|) (by norm_num : (1 : ℝ) < 3 / 2)
  have h' := hb (n + 1) (by omega)
  have hmono : (3 / 2 : ℝ) ^ n ≤ (3 / 2) ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [div_lt_iff₀ hpos] at hn
  nlinarith

end OMAQ

theorem OMA.solution : type_of% @Bugeaud09.problem_10_9.variants.measure_zero := by
  apply Set.Countable.measure_zero
  have hi : Function.Injective
      (fun x : {ξ : ℝ | IsZNumber ξ} => ⌊x.1 * (3 / 2 : ℝ) ^ 1⌋) := by
    intro a b h
    exact Subtype.ext (OMAQ.zinj a.1 b.1 a.2 b.2 h)
  exact Set.countable_coe_iff.1 hi.countable
