import FormalConjectures.OEIS.«228304»
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.Matrix.Block

/-! Lucas cancellation makes the Hankel matrix triangular after reversing
its columns. The antidiagonal entries are all one modulo the prime. -/

open scoped BigOperators
open OeisA228304

namespace OMA

private theorem choose_lucas_cast {p : ℕ} [Fact p.Prime] (n k : ℕ) :
    (n.choose k : ZMod p) = ((n % p).choose (k % p) : ZMod p) *
        ((n / p).choose (k / p) : ZMod p) := by
  exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ p).mpr
    (Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k))

private theorem a_large_zero {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (r : ℕ) (hr : r < p) : (a (p + r) : ZMod p) = 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let term (k : ℕ) : ZMod p := (-1) ^ k * ((p + r).choose k : ZMod p) ^ 4
  have hchoose (k : ℕ) (hk : k < p) :
      ((p + r).choose k : ZMod p) = (r.choose k : ZMod p) := by
    rw [choose_lucas_cast, Nat.add_mod, Nat.mod_self, zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hk,
      Nat.div_eq_of_lt hk, Nat.choose_zero_right, Nat.cast_one, mul_one]
  have hshift (k : ℕ) (hk : k < p) :
      ((p + r).choose (p + k) : ZMod p) = (r.choose k : ZMod p) := by
    have hdiv (t : ℕ) (ht : t < p) : (p + t) / p = 1 := by
      rw [Nat.add_comm, Nat.add_div_right _ hp, Nat.div_eq_of_lt ht, zero_add]
    have hmod (t : ℕ) (ht : t < p) : (p + t) % p = t := by
      simp [Nat.mod_eq_of_lt ht]
    rw [choose_lucas_cast, hdiv r hr, hdiv k hk, hmod r hr, hmod k hk]
    simp
  have hpair (k : ℕ) (hk : k ∈ Finset.range (r + 1)) :
      term (p + k) = -term k := by
    have hk' : k < p := by
      have := Finset.mem_range.mp hk
      omega
    simp [term, hchoose k hk', hshift k hk', pow_add, hpodd.neg_one_pow]
  have hprefix : ∑ k ∈ Finset.range p, term k = ∑ k ∈ Finset.range (r + 1), term k := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k hk hn
    have hlt := Finset.mem_range.mp hk
    have hgt : r < k := by simpa using hn
    simp [term, hchoose k hlt, Nat.choose_eq_zero_of_lt hgt]
  have hsplit : p + r + 1 = p + (r + 1) := by omega
  unfold a
  push_cast
  change ∑ k ∈ Finset.range (p + r + 1), term k = 0
  rw [hsplit, Finset.sum_range_add, hprefix]
  have hs : (∑ k ∈ Finset.range (r + 1), term (p + k)) =
      ∑ k ∈ Finset.range (r + 1), -term k := Finset.sum_congr rfl hpair
  rw [hs, Finset.sum_neg_distrib, add_neg_cancel]

private theorem choose_pred_cast {p : ℕ} [Fact p.Prime] (k : ℕ) (hk : k < p) :
    ((p - 1).choose k : ZMod p) = (-1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hrec := congrArg (fun n : ℕ => (n : ZMod p))
      (Nat.choose_succ_right_eq (p - 1) k)
    push_cast at hrec
    have hsub : ((p - 1 - k : ℕ) : ZMod p) = -(k + 1 : ℕ) := by
      rw [show p - 1 - k = p - (k + 1) by omega, Nat.cast_sub (by omega),
        ZMod.natCast_self, zero_sub]
    have hne : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro hz
      have hz' := (ZMod.natCast_eq_natCast_iff' (k + 1) 0 p).mp (by simpa using hz)
      simp [Nat.mod_eq_of_lt hk] at hz'
    apply mul_right_cancel₀ hne
    rw [hsub, ih (by omega)] at hrec
    rw [Nat.cast_add, Nat.cast_one, hrec, pow_succ, Nat.cast_add, Nat.cast_one]
    ring

private theorem a_pred_one {p : ℕ} [Fact p.Prime] (hpodd : Odd p) :
    (a (p - 1) : ZMod p) = 1 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  unfold a
  push_cast
  rw [show p - 1 + 1 = p by omega]
  have hsum : (∑ k ∈ Finset.range p, (-1 : ZMod p) ^ k * ((p - 1).choose k : ZMod p) ^ 4) =
      ∑ k ∈ Finset.range p, (-1 : ZMod p) ^ k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [choose_pred_cast k (Finset.mem_range.mp hk), ← pow_mul, mul_comm k 4, pow_mul]
    norm_num
  rw [hsum, ← Fin.sum_univ_eq_sum_range, Fin.sum_neg_one_pow]
  simp [Nat.not_even_iff_odd.mpr hpodd]

private theorem rev_sign (p : ℕ) (hp : Odd p) :
    Equiv.Perm.sign (Fin.revPerm (n := p)) = (-1) ^ ((p - 1) / 2) := by
  have hpow : (Fin.revPerm (n := p)) ^ 2 = 1 := by
    ext i
    simp [pow_two, Equiv.Perm.mul_apply]
  have hpp : 0 < p := by obtain ⟨k, hk⟩ := hp; omega
  let m : Fin p := ⟨p / 2, by omega⟩
  have heq : Function.fixedPoints (Fin.revPerm (n := p)) = {m} := by
    ext i
    have hodd : p % 2 = 1 := Nat.odd_iff.mp hp
    change Fin.rev i = i ↔ i = m
    rw [← Fin.val_inj, ← Fin.val_inj]
    simp only [Fin.val_rev, m]
    omega
  rw [Equiv.Perm.sign_of_pow_two_eq_one hpow, Fintype.card_fin, ← Nat.card_eq_fintype_card, heq]
  simp

end OMA

open OMA in
theorem OMA.solution : type_of% @OeisA228304.conjecture_1 := by
  intro p hp hodd
  let : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hodd
  let A : Matrix (Fin p) (Fin p) ℤ := fun i j => a (i.val + j.val)
  let B : Matrix (Fin p) (Fin p) (ZMod p) := A.map (Int.castRingHom (ZMod p))
  let C := B.submatrix id Fin.revPerm
  have htri : C.IsUpperTriangular := by
    intro i j hij
    change (a (i.val + (Fin.rev j).val) : ZMod p) = 0
    have hi := i.isLt
    have hj := j.isLt
    have hji : j.val < i.val := hij
    rw [Fin.val_rev]
    let r := i.val + (p - (j.val + 1)) - p
    have heq : i.val + (p - (j.val + 1)) = p + r := by dsimp [r]; omega
    rw [heq]
    exact a_large_zero hpodd r (by dsimp [r]; omega)
  have hdiag (i : Fin p) : C i i = 1 := by
    change (a (i.val + (Fin.rev i).val) : ZMod p) = 1
    rw [Fin.val_rev, show i.val + (p - (i.val + 1)) = p - 1 by have := i.isLt; omega]
    exact a_pred_one hpodd
  have hdet : C.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular htri]
    simp [hdiag]
  change A.det ≡ (-1 : ℤ) ^ ((p - 1) / 2) [ZMOD p]
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  change B.det = _
  have hsign : (↑(Equiv.Perm.sign (Fin.revPerm (n := p))) : ZMod p) =
      (-1) ^ ((p - 1) / 2) := by
    rw [rev_sign p hpodd]
    simp
  rw [Matrix.det_permute', hsign] at hdet
  calc
    B.det = (-1 : ZMod p) ^ ((p - 1) / 2) *
        ((-1 : ZMod p) ^ ((p - 1) / 2) * B.det) := by
      rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    _ = _ := by rw [hdet, mul_one]
