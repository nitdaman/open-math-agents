import FormalConjectures.ErdosProblems.«482»

/-! Closed forms for both parities of Stoll's recurrence in base g. -/

namespace OMA.StollDigits

def repunit (g : ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => g * repunit g n + 1

lemma repunit_identity (g : ℤ) (n : ℕ) : (g - 1) * repunit g n + 1 = g ^ n := by
  induction n with
  | zero => simp [repunit]
  | succ n ih =>
    rw [repunit, pow_succ, ← ih]
    ring

-- The possible error in replacing x by its floor is less than one.
-- After rescaling, the hypotheses on ε keep this step in the interval [q,q+1).
lemma odd_floor (g t ε x : ℝ) (q : ℤ) (hg : 2 ≤ g) (ht : 1 ≤ t)
    (hlo : -1 ≤ ε * g) (hhi : ε * g < (g + 1) * (g - 2))
    (hx : g * x = ((g - 1) * q + 1) * (t + g)) :
    ⌊g / ((g - 1) * (t + g)) * ((⌊x⌋ : ℝ) + ε)⌋ = q := by
  have hg₀ : 0 < g := by linarith
  have hden : 0 < (g - 1) * (t + g) := mul_pos (by linarith) (by linarith)
  rw [div_mul_eq_mul_div]
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ hden).2
    have hfloor := mul_lt_mul_of_pos_left (Int.sub_one_lt_floor x) hg₀
    nlinarith only [hx, hlo, ht, hfloor]
  · apply (div_lt_iff₀ hden).2
    have hfloor := mul_le_mul_of_nonneg_left (Int.floor_le x) hg₀.le
    have ht' := mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hg)
    nlinarith only [hx, hhi, hfloor, ht']

end OMA.StollDigits

open OMA.StollDigits Erdos482

theorem OMA.solution : type_of% @Erdos482.erdos_482.variants.stoll_explicit := by
  intro g hg t ht htg ε hlo hhi
  let a := (g : ℝ) / (((g : ℝ) - 1) * (t + g))
  let b := ((g : ℝ) - 1) * (t + g)
  let u := generalRecurrence g a b ε
  let x (n : ℕ) := (t + g) * (g : ℝ) ^ n / g
  have hg₂ : 2 ≤ (g : ℝ) := by exact_mod_cast hg
  have hg₀ : 0 < (g : ℝ) := by linarith
  have hgm : (g : ℝ) - 1 ≠ 0 := by linarith
  have geo (n : ℕ) : ((g : ℝ) - 1) * (repunit g n : ℝ) + 1 = (g : ℝ) ^ n := by
    exact_mod_cast repunit_identity (g : ℤ) n
  have scaled (n : ℕ) : (g : ℝ) * x n =
      (((g : ℝ) - 1) * (repunit g n : ℝ) + 1) * (t + g) := by
    rw [geo]
    dsimp [x]
    field_simp [hg₀.ne'] <;> ring
  have first (n : ℕ) : u (2 * n + 1) = ⌊a * ((u (2 * n) : ℝ) + ε)⌋ := by
    change generalRecurrence g a b ε (2 * n + 1) = _
    rw [generalRecurrence, if_pos (even_two_mul n)]
  have second (n : ℕ) : u (2 * n + 2) =
      ⌊b * ((u (2 * n + 1) : ℝ) + 1 / ((g : ℝ) - 1))⌋ := by
    change generalRecurrence g a b ε ((2 * n + 1) + 1) = _
    rw [generalRecurrence, if_neg (by simp : ¬ Even (2 * n + 1))]
  have even_value (n : ℕ) : u (2 * n) = ⌊x n⌋ := by
    induction n with
    | zero =>
      change (1 : ℤ) = ⌊(t + g) * (g : ℝ) ^ 0 / g⌋
      rw [pow_zero, mul_one]
      symm
      apply Int.floor_eq_iff.mpr
      constructor
      · apply (le_div_iff₀ hg₀).2
        norm_num
        linarith
      · apply (div_lt_iff₀ hg₀).2
        norm_num
        linarith
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, second]
      have odd_value : u (2 * n + 1) = repunit g n := by
        rw [first, ih]
        exact odd_floor g t ε (x n) (repunit g n) hg₂ ht
          ((div_le_iff₀ hg₀).mp hlo) ((lt_div_iff₀ hg₀).mp hhi) (scaled n)
      rw [odd_value]
      apply congrArg Int.floor
      calc
        b * ((repunit g n : ℝ) + 1 / ((g : ℝ) - 1)) =
            (t + g) * (((g : ℝ) - 1) * (repunit g n : ℝ) + 1) := by
              dsimp [b]
              field_simp [hgm] <;> ring
        _ = (t + g) * (g : ℝ) ^ n := by rw [geo]
        _ = x (n + 1) := by
          dsimp [x]
          rw [pow_succ]
          field_simp [hg₀.ne'] <;> ring
  change ∀ n : ℕ, u (2 * n + 2) - (g : ℤ) * u (2 * n) =
    ⌊t * (g : ℝ) ^ n⌋ - (g : ℤ) * ⌊t * (g : ℝ) ^ n / g⌋
  intro n
  rw [show 2 * n + 2 = 2 * (n + 1) by omega, even_value, even_value]
  have hnext : x (n + 1) = t * (g : ℝ) ^ n + (((g : ℤ) ^ (n + 1) : ℤ) : ℝ) := by
    dsimp [x]
    push_cast
    rw [pow_succ]
    field_simp [hg₀.ne'] <;> ring
  have hcurr : x n = t * (g : ℝ) ^ n / g + (((g : ℤ) ^ n : ℤ) : ℝ) := by
    dsimp [x]
    push_cast
    field_simp [hg₀.ne'] <;> ring
  rw [hnext, hcurr, Int.floor_add_intCast, Int.floor_add_intCast, pow_succ]
  ring
