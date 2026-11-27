import FormalConjectures.ErdosProblems.«962»

/-!
# A square-root bound for Erdős 962

If m < k², the first multiple of k strictly above m has the form kq with
1 ≤ q ≤ k. It belongs to the interval from m+1 to m+k, yet every prime
factor divides k or q and is consequently at most k.
-/

namespace Erdos962Bound

lemma square_le {n k : ℕ} (h : Erdos962.Erdos962Prop n k) : k ^ 2 ≤ n := by
  obtain ⟨m, hmn, hall⟩ := h
  by_cases hzero : k = 0
  · simp [hzero]
  have hk : 0 < k := Nat.pos_of_ne_zero hzero
  suffices hkm : k^2 ≤ m by exact hkm.trans hmn
  by_contra! hsmall
  have hq : m / k < k := (Nat.div_lt_iff_lt_mul hk).mpr (by simpa [pow_two] using hsmall)
  have hr := Nat.mod_lt m hk
  have hd := Nat.mod_add_div m k
  obtain ⟨p, hp, hpk, hdiv⟩ := hall (k - m % k) ⟨by omega, by omega⟩
  have heq : m + (k - m % k) = k * (m / k + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [heq] at hdiv
  rcases hp.dvd_mul.mp hdiv with h | h
  · exact (not_lt_of_ge (Nat.le_of_dvd hk h)) hpk
  · have hpq := Nat.le_of_dvd (Nat.succ_pos (m / k)) h
    omega

end Erdos962Bound

theorem OMA.solution : type_of% @Erdos962.erdos_962.variants.tao_upper_bound := by
  classical
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro δ hδ
    exact Filter.Eventually.of_forall fun _ => by simpa using hδ
  · apply Filter.Eventually.of_forall
    intro n
    simp only [add_zero, one_mul]
    apply Real.le_sqrt_of_sq_le
    have hz : Erdos962.Erdos962Prop n 0 := ⟨0, Nat.zero_le _, by simp⟩
    have hk : Erdos962.Erdos962Prop n (Erdos962.k n) :=
      Nat.findGreatest_spec (Nat.zero_le n) hz
    exact_mod_cast Erdos962Bound.square_le hk
