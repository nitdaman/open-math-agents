import FormalConjectures.Wikipedia.Catalan

/-! Descent to prime exponents and fourth powers for the weighted Pillai equation. -/

namespace OMA.R_Catalan_pillais_conjecture_R1

/-- Bound the power values when a square faces a fourth power or an odd prime power. -/
def H1 : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → ∃ B : ℕ,
    ∀ x y m n : ℕ, 1 < x → 1 < y →
    ((m = 2 ∧ 2 < n ∧ (n.Prime ∨ n = 4)) ∨
     (n = 2 ∧ 2 < m ∧ (m.Prime ∨ m = 4))) →
    a * x^n - b * y^m = c → x^n + y^m ≤ B

/-- Bound the power values when both exponents are odd primes or four. -/
def H2 : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → ∃ B : ℕ,
    ∀ x y m n : ℕ, 1 < x → 1 < y → 2 < m → 2 < n →
    (m.Prime ∨ m = 4) → (n.Prime ∨ n = 4) →
    a * x^n - b * y^m = c → x^n + y^m ≤ B

private theorem compress {e : ℕ} (he : 1 < e) :
    ∃ d k : ℕ, e = k*d ∧ 0 < k ∧ 1 < d ∧ (d.Prime ∨ d = 4) ∧ (d = 2 → e = 2) := by
  by_cases h : e = 2
  · exact ⟨2, 1, by omega, by decide, by decide, Or.inl Nat.prime_two, fun _ => h⟩
  by_cases hf : 4 ∣ e
  · obtain ⟨k, hk⟩ := hf
    exact ⟨4, k, by omega, by omega, by decide, Or.inr rfl, by omega⟩
  let t := if 2 ∣ e then e / 2 else e
  have ht : 1 < t ∧ ¬ 2 ∣ t ∧ t ∣ e := by
    dsimp [t]
    split_ifs with htwo
    · refine ⟨by omega, by omega, 2, by omega⟩
    · exact ⟨he, htwo, dvd_rfl⟩
  obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd (by omega : t ≠ 1)
  obtain ⟨k, hk⟩ := dvd_trans hpt ht.2.2
  refine ⟨p, k, hk.trans (Nat.mul_comm ..), ?_, hp.one_lt, Or.inl hp, ?_⟩
  · by_contra! hz
    simp [Nat.eq_zero_of_le_zero hz] at hk
    omega
  · rintro rfl
    exact (ht.2.1 hpt).elim

theorem main : H1 → H2 → type_of% @Catalan.pillais_conjecture := by
  intro hsq hlarge a b c ha hb hc
  obtain ⟨S, hS⟩ := hsq a b c ha hb hc
  obtain ⟨L, hL⟩ := hlarge a b c ha hb hc
  apply ((Set.finite_Iic (S + L)).prod ((Set.finite_Iic (S + L)).prod
    ((Set.finite_Iic (S + L)).prod (Set.finite_Iic (S + L))))).subset
  rintro ⟨x,y,m,n⟩ ⟨hx,hy,hm,hn,hpair,heq⟩
  obtain ⟨p,i,hmi,hi,hp,hpc,hp2⟩ := compress hm
  obtain ⟨q,j,hnj,hj,hq,hqc,hq2⟩ := compress hn
  have hxj := one_lt_pow₀ hx hj.ne'
  have hyi := one_lt_pow₀ hy hi.ne'
  have ex : (x^j)^q = x^n := by rw [← pow_mul, ← hnj]
  have ey : (y^i)^p = y^m := by rw [← pow_mul, ← hmi]
  have eqn : a * (x^j)^q - b * (y^i)^p = c := by rwa [ex, ey]
  have bound : x^n + y^m ≤ S + L := by
    by_cases hs : p = 2 ∨ q = 2
    · have hboth : ¬ (p = 2 ∧ q = 2) := fun h => hpair (Prod.ext (hp2 h.1) (hq2 h.2))
      have H := hS _ _ p q hxj hyi (by
        rcases hs with h|h
        · exact Or.inl ⟨h, by omega, hqc⟩
        · exact Or.inr ⟨h, by omega, hpc⟩) eqn
      rw [ex, ey] at H
      omega
    · have H := hL _ _ p q hxj hyi (by omega) (by omega) hpc hqc eqn
      rw [ex, ey] at H
      omega
  have bx := le_self_pow hx.le (by omega : n ≠ 0)
  have by' := le_self_pow hy.le (by omega : m ≠ 0)
  have bn : n < x^n := Nat.lt_pow_self hx
  have bm : m < y^m := Nat.lt_pow_self hy
  change x ≤ S + L ∧ y ≤ S + L ∧ m ≤ S + L ∧ n ≤ S + L
  omega

end OMA.R_Catalan_pillais_conjecture_R1
