import FormalConjectures.OEIS.«166944»

/-! A square-root interval before a main increment detects small divisors of both candidates. -/

-- Credit: @desenyon
open OeisA166944

namespace OMA.R_OeisA166944_conjecture_R1

/-- Each large record occurs at the main increment following a fundamental point. -/
def H1 : Prop := ∀ R, 5 < R → IsDifferenceRecord R →
  R % 2 = 1 ∧ a (R + 1) = 2 * R

/-- At such a crossing, the final square-root length interval is a run of unit increments.
The affine formula specifies this run backwards from its endpoint. -/
def H2 : Prop := ∀ R, 13 < R → R % 2 = 1 → a (R + 1) = 2 * R →
  ∀ k, 2 ≤ k → k ≤ R + 1 → R + 1 ≤ k + 2 * R.sqrt + 4 → a k = k + R - 1

private theorem obstruction {k R p : ℕ} (hk : 2 ≤ k) (hp : 1 < p)
    (left : a (k - 1) = k + R - 2) (right : a k = k + R - 1)
    (hdiv : p ∣ k + R - 2)
    (hidx : p ∣ (if k % 2 = 0 then k else k - 2)) : False := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simp only [Nat.add_sub_cancel] at *
  rw [a] at right
  split at right <;> rename_i h
  all_goals
    first | rw [if_pos h] at hidx | rw [if_neg h] at hidx
    try simp only [Nat.add_sub_cancel] at *
    simp at left
    rw [left] at right
    have hg := Nat.dvd_gcd hidx hdiv
    have lower := Nat.le_of_dvd (by omega) hg
    omega

theorem main : H1 → H2 → type_of% @OeisA166944.conjecture := by
  intro align run R hR rec
  obtain ⟨odd, cross⟩ := align R hR rec
  by_cases small : R ≤ 13
  · unfold IsGreaterTwinPrime
    interval_cases R <;> first | decide | contradiction
  have window := run R (by omega) odd cross
  constructor <;> by_contra hn
  · let p := R.minFac
    have pd : p ∣ R := Nat.minFac_dvd _
    have hp : 2 ≤ p := Nat.minFac_prime (by omega : R ≠ 1) |>.two_le
    have sq := Nat.minFac_sq_le_self (by omega : 0 < R) hn
    have bound : p ≤ R.sqrt := Nat.le_sqrt.mpr (by simpa [p, pow_two] using sq)
    have room : 2*p + 3 ≤ R := by change p^2 ≤ R at sq; nlinarith
    let k := R + 2 - 2*p
    have eqk : k + 2*p = R+2 := by dsimp [k]; omega
    apply obstruction (k := k) (R := R) (p := p) (by omega) (by omega)
    · rw [window (k-1) (by omega) (by omega) (by omega)]; omega
    · exact window k (by omega) (by omega) (by omega)
    · have he : k+R-2 = (R+R) - 2*p := by omega
      rw [he]; exact Nat.dvd_sub (dvd_add pd pd) (dvd_mul_left ..)
    · rw [if_neg (by omega)]
      have he : k-2 = R-2*p := by omega
      rw [he]; exact Nat.dvd_sub pd (dvd_mul_left ..)
  · let p := (R-2).minFac
    have pd : p ∣ R-2 := Nat.minFac_dvd _
    have hp : 2 ≤ p := Nat.minFac_prime (by omega : R-2 ≠ 1) |>.two_le
    have sq := Nat.minFac_sq_le_self (by omega : 0 < R-2) hn
    change p^2 ≤ R-2 at sq
    have bound : p ≤ R.sqrt := Nat.le_sqrt.mpr (by rw [← pow_two]; omega)
    have room : p+5 ≤ R := by nlinarith [Nat.sub_le R 2]
    have po : p % 2 = 1 := by
      by_contra h
      have he : 2 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
      have := Nat.mod_eq_zero_of_dvd (he.trans pd)
      omega
    let k := R-2-p
    have eqk : k+p+2 = R := by dsimp [k]; omega
    apply obstruction (k := k) (R := R) (p := p) (by omega) (by omega)
    · rw [window (k-1) (by omega) (by omega) (by omega)]; omega
    · exact window k (by omega) (by omega) (by omega)
    · have he : k+R-2 = k+(R-2) := by omega
      rw [he]; exact dvd_add (Nat.dvd_sub pd (dvd_refl p)) pd
    · rw [if_pos (by omega)]; exact Nat.dvd_sub pd (dvd_refl p)

end OMA.R_OeisA166944_conjecture_R1
