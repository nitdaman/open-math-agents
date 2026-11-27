import FormalConjectures.OEIS.«245211»

/-! Removing two primes of multiplicity one turns the remaining search into a divisor test. -/

open Finset OeisA245211

namespace OMA.R_OeisA245211_conjecture_R1

private theorem full {m : ℕ} (hm : m ≠ 0) :
    (∑ d ∈ m.divisors, d * d.divisors.card) = a m + m * m.divisors.card := by
  conv_lhs => rw [← Nat.insert_self_properDivisors hm, sum_insert Nat.self_notMem_properDivisors]
  simp [a, add_comm]

private theorem full_mul {m n : ℕ} (h : m.Coprime n) :
    (∑ d ∈ (m*n).divisors, d * d.divisors.card) =
    (∑ d ∈ m.divisors, d * d.divisors.card) * ∑ d ∈ n.divisors, d * d.divisors.card := by
  rw [h.divisors_mul, sum_map]
  change (∑ x ∈ (m.divisors ×ˢ n.divisors).attach, x.val.1*x.val.2*(x.val.1*x.val.2).divisors.card) = _
  rw [sum_attach (f := fun x : ℕ × ℕ => x.1*x.2*(x.1*x.2).divisors.card)]
  rw [sum_product, sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [((h.coprime_dvd_left (Nat.dvd_of_mem_divisors hi)).coprime_dvd_right
    (Nat.dvd_of_mem_divisors hj)).card_divisors_mul]
  ring

private theorem prime_sum {p : ℕ} (hp : p.Prime) :
    (∑ d ∈ p.divisors, d * d.divisors.card) = 1+2*p := by
  simp [hp.divisors, Ne.symm hp.ne_one, two_mul]
  omega

/-- A fixed point has two distinct prime factors of multiplicity one. -/
def H1 : Prop := ∀ n : ℕ, 0 < n → a n = n →
  ∃ m p q : ℕ, n = m*p*q ∧ p.Prime ∧ q.Prime ∧ m.Coprime p ∧ (m*p).Coprime q

/-- For a nontrivial cofactor, complementary divisors cannot reconstruct two
distinct primes coprime to the cofactor. The search in u is finite for each m. -/
def H2 : Prop := ∀ m : ℕ, 1 < m → 4*a m < m →
  let F := a m + m*m.divisors.card
  let D := m - 4*a m
  let C := F*m*(4*m.divisors.card+1)
  ∀ u ∈ C.divisors,
    let v := C/u
    let p := (u+2*F)/D
    let q := (v+2*F)/D
    D ∣ u+2*F → D ∣ v+2*F → p.Prime → q.Prime →
      m.Coprime p → ¬ (m*p).Coprime q

theorem main : H1 → H2 → type_of% @OeisA245211.conjecture := by
  intro h1 h2 n hn
  constructor
  · intro h
    obtain ⟨m,p,q,rfl,hp,hq,hmp,hmq⟩ := h1 n hn h
    have hm : m ≠ 0 := by rintro rfl; simp at hn
    have ht : 0 < m.divisors.card := Finset.card_pos.mpr ⟨m, Nat.mem_divisors.mpr ⟨dvd_refl _,hm⟩⟩
    have hs := full (Nat.ne_of_gt hn)
    rw [full_mul hmq, full_mul hmp, prime_sum hp, prime_sum hq, full hm, h,
      hmq.card_divisors_mul, hmp.card_divisors_mul] at hs
    have cp : p.divisors.card = 2 := by simp [hp.divisors, Ne.symm hp.ne_one]
    have cq : q.divisors.card = 2 := by simp [hq.divisors, Ne.symm hq.ne_one]
    rw [cp,cq] at hs
    let F := a m + m*m.divisors.card
    have hF : 0 < F := by dsimp [F]; positivity
    have key : m*(p*q) = 4*a m*(p*q) + F*(2*p+2*q+1) := by
      dsimp [F]; linarith only [hs]
    have small : 4*a m < m := by
      by_contra! hh
      have := Nat.mul_le_mul_right (p*q) hh
      have : 0 < F*(2*p+2*q+1) := by positivity
      omega
    let D := m-4*a m
    have hd : 0 < D := Nat.sub_pos_of_lt small
    have hdadd : D+4*a m = m := Nat.sub_add_cancel small.le
    have rel : D*p*q = F*(2*p+2*q+1) := by
      nth_rw 1 [← hdadd] at key
      linarith only [key]
    have bounds (x y : ℕ) (he : D*x*y = F*(2*x+2*y+1)) : 2*F < D*x := by
      by_contra! hh
      have := Nat.mul_le_mul_right y hh
      nlinarith only [this,he,hF,Nat.zero_le (2*F*x)]
    have bp := bounds p q rel
    have bq := bounds q p (by linarith only [rel])
    let u := D*p-2*F
    let v := D*q-2*F
    have hu : u+2*F = D*p := Nat.sub_add_cancel bp.le
    have hv : v+2*F = D*q := Nat.sub_add_cancel bq.le
    have huv : u*v = F*m*(4*m.divisors.card+1) := by
      have fac : u*v + 2*F*(D*p+D*q) = D*(D*p*q) + 4*F*F := by
        calc
          _ = (u+2*F)*(v+2*F)+4*F*F := by rw [← hu, ← hv]; ring
          _ = _ := by rw [hu,hv]; ring
      rw [rel] at fac
      dsimp [F] at *
      nlinarith only [fac, congrArg ((a m + m*m.divisors.card)*·) hdadd]
    have mone : m = 1 := by
      by_contra hh
      have hc : 0 < F*m*(4*m.divisors.card+1) := by positivity
      have step := h2 m (by omega) small u (Nat.mem_divisors.mpr ⟨⟨v,huv.symm⟩, hc.ne'⟩)
      change (D ∣ u+2*F) → (D ∣ (F*m*(4*m.divisors.card+1))/u+2*F) → _ at step
      change (D ∣ u+2*F) → (D ∣ (F*m*(4*m.divisors.card+1))/u+2*F) →
        ((u+2*F)/D).Prime → (((F*m*(4*m.divisors.card+1))/u+2*F)/D).Prime →
        m.Coprime ((u+2*F)/D) → ¬ (m*((u+2*F)/D)).Coprime (((F*m*(4*m.divisors.card+1))/u+2*F)/D) at step
      rw [← huv, Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt bp), hu,hv,
        Nat.mul_div_cancel_left _ hd,Nat.mul_div_cancel_left _ hd] at step
      exact step (dvd_mul_right ..) (dvd_mul_right ..) hp hq hmp hmq
    have f1 : F = 1 := by simp [F,mone,a]
    have d1 : D = 1 := by simp [D,mone,a]
    rw [mone] at ⊢
    norm_num [f1,d1,mone] at huv hu hv
    have cases : u = 1 ∨ u = 5 := (Nat.dvd_prime (by decide : Nat.Prime 5)).mp ⟨v,huv.symm⟩
    rcases cases with h | h
    all_goals
      rw [h] at hu huv
      norm_num at hu huv
      rw [huv] at hv
      norm_num at hv
      rw [← hu, ← hv]
  · rintro rfl
    decide

end OMA.R_OeisA245211_conjecture_R1
