import FormalConjectures.OEIS.«228304»
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# OEIS A228304 determinant for the auxiliary sequence

Lucas's congruence makes the Hankel matrix anti-triangular modulo an odd prime.
Reversing the columns then gives the determinant from the diagonal entries.
-/

open scoped BigOperators

namespace OMA

private lemma choose_cast_lucas (p n k : ℕ) [Fact p.Prime] :
    (n.choose k : ZMod p) =
      ((n % p).choose (k % p) : ZMod p) * ((n / p).choose (k / p) : ZMod p) := by
  rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat

private lemma shift_mod (p k : ℕ) (hk : k < p) : (p + k) % p = k := by
  simp [Nat.add_mod_left, Nat.mod_eq_of_lt hk]

private lemma shift_div (p k : ℕ) (hk : k < p) : (p + k) / p = 1 := by
  have hp : 0 < p := by omega
  calc
    (p + k) / p = (k + p * 1) / p := by simp [Nat.add_comm]
    _ = 1 := by rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hk, zero_add]

private lemma choose_shift_low (p d k : ℕ) [Fact p.Prime] (hd : d < p) (hk : k < p) :
    ((p + d).choose k : ZMod p) = (d.choose k : ZMod p) := by
  rw [choose_cast_lucas, shift_mod p d hd, Nat.mod_eq_of_lt hk, Nat.div_eq_of_lt hk]
  simp

private lemma choose_shift_high (p d k : ℕ) [Fact p.Prime] (hd : d < p) (hk : k < p) :
    ((p + d).choose (p + k) : ZMod p) = (d.choose k : ZMod p) := by
  rw [choose_cast_lucas, shift_mod p d hd, shift_mod p k hk, shift_div p d hd, shift_div p k hk]
  simp

private def central (p k : ℕ) : ZMod p := ((2 * k).choose k : ℕ)

-- A carry in the low digit of 2k forces the corresponding binomial coefficient to vanish.
private lemma central_zero (p k : ℕ) [Fact p.Prime] (hk : k < p) (hc : p ≤ 2 * k) :
    central p k = 0 := by
  have hmod : (2 * k) % p = 2 * k - p := by
    rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)]
  unfold central
  rw [choose_cast_lucas, hmod, Nat.mod_eq_of_lt hk, Nat.choose_eq_zero_of_lt (by omega)]
  simp

private lemma central_shift (p k : ℕ) [Fact p.Prime] (hk : k < p) :
    central p (p + k) = 2 * central p k := by
  have hp : 0 < p := by omega
  have hdouble : 2 * (p + k) = 2 * k + p * 2 := by omega
  have hmod : 2 * (p + k) % p = (2 * k) % p := by
    rw [hdouble, Nat.add_mul_mod_self_left]
  have hdiv : 2 * (p + k) / p = (2 * k) / p + 2 := by
    rw [hdouble, Nat.add_mul_div_left _ _ hp]
  change (((2 * (p + k)).choose (p + k) : ℕ) : ZMod p) = 2 * central p k
  rw [choose_cast_lucas, hmod, shift_mod p k hk, shift_div p k hk, hdiv]
  by_cases h : 2 * k < p
  · rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]
    simp [central, mul_comm]
  · have hc : p ≤ 2 * k := by omega
    have hmod' : (2 * k) % p = 2 * k - p := by
      rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)]
    rw [hmod', Nat.choose_eq_zero_of_lt (by omega), central_zero p k hk hc]
    simp

private def summand (p n k : ℕ) : ZMod p :=
  (-1) ^ k * (n.choose k : ZMod p) ^ 2 * central p k * central p (n - k)

private lemma c_cast (p n : ℕ) :
    (OeisA228304.c n : ZMod p) = ∑ k ∈ Finset.range (n + 1), summand p n k := by
  simp [OeisA228304.c, summand, central]

private lemma choose_pred (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : k < p) :
    ((p - 1).choose k : ZMod p) = (-1 : ZMod p) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := congrArg (fun n : ℕ => (n : ZMod p)) (Nat.choose_succ_right_eq (p - 1) k)
    simp only [Nat.cast_mul] at h
    have hzero : ((p - 1 - k : ℕ) : ZMod p) + ((k + 1 : ℕ) : ZMod p) = 0 := by
      rw [← Nat.cast_add, show p - 1 - k + (k + 1) = p by omega, ZMod.natCast_self]
    have hne : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt (by omega) hk
    have hneg : ((p - 1 - k : ℕ) : ZMod p) = -((k + 1 : ℕ) : ZMod p) :=
      eq_neg_of_add_eq_zero_left hzero
    rw [ih (by omega), hneg] at h
    apply mul_right_cancel₀ hne
    rw [pow_succ]
    linear_combination h

-- At p − 1, both central binomial coefficients can be nonzero only at the midpoint.
private lemma c_diagonal (p : ℕ) [Fact p.Prime] (hpodd : p % 2 = 1) :
    (OeisA228304.c (p - 1) : ZMod p) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
  let m := (p - 1) / 2
  have hm : 2 * m = p - 1 := by dsimp [m]; omega
  have hmp : m < p := by omega
  have hc : ((p - 1).choose m : ZMod p) = (-1 : ZMod p) ^ m := choose_pred p m hmp
  have hs : ((-1 : ZMod p) ^ m) ^ 2 = 1 := by
    rw [← pow_mul]
    exact (show Even (m * 2) from ⟨m, by omega⟩).neg_one_pow
  have hmid : summand p (p - 1) m = (-1 : ZMod p) ^ m := by
    unfold summand central
    rw [show p - 1 - m = m by omega, hm, hc, hs, mul_one, mul_assoc, ← pow_two, hs, mul_one]
  rw [c_cast, Finset.sum_eq_single m]
  · exact hmid
  · intro k hk hkm
    simp only [Finset.mem_range] at hk
    unfold summand
    rcases lt_or_gt_of_ne hkm with hlt | hlt
    · rw [central_zero p (p - 1 - k) (by omega) (by omega), mul_zero]
    · rw [central_zero p k (by omega) (by omega), mul_zero, zero_mul]
  · intro hn
    exact (hn (Finset.mem_range.mpr (by omega))).elim

-- Pair the summands with indices k and p + k after removing the zero terms.
private lemma c_vanish (p : ℕ) [Fact p.Prime] (hpodd : Odd p) (d : ℕ) (hd : d < p) :
    (OeisA228304.c (p + d) : ZMod p) = 0 := by
  have hcut : ∑ k ∈ Finset.range (d + 1), summand p (p + d) k =
      ∑ k ∈ Finset.range p, summand p (p + d) k := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k hk hk'
    simp only [Finset.mem_range, not_lt] at hk hk'
    unfold summand
    rw [choose_shift_low p d k hd hk, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hpair (k : ℕ) (hk : k < d + 1) :
      summand p (p + d) (p + k) = -summand p (p + d) k := by
    unfold summand
    rw [choose_shift_high p d k hd (by omega), choose_shift_low p d k hd (by omega),
      show p + d - (p + k) = d - k by omega, show p + d - k = p + (d - k) by omega,
      central_shift p k (by omega), central_shift p (d - k) (by omega), pow_add, hpodd.neg_one_pow]
    ring
  rw [c_cast, Nat.add_assoc, Finset.sum_range_add, ← hcut, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun k hk => by rw [hpair k (Finset.mem_range.mp hk), add_neg_cancel]

private lemma reversal_sign (p : ℕ) (hpodd : p % 2 = 1) :
    Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin p)) = (-1 : ℤˣ) ^ ((p - 1) / 2) := by
  classical
  have hs : (Fin.revPerm : Equiv.Perm (Fin p)) ^ 2 = 1 := by
    ext i
    simp [pow_two]
  let mid : Fin p := ⟨(p - 1) / 2, by omega⟩
  have hfix (i : Function.fixedPoints (Fin.revPerm : Equiv.Perm (Fin p))) : i.val = mid := by
    apply Fin.ext
    have h := congrArg Fin.val i.property
    change (Fin.rev (i.val : Fin p)).val = i.val.val at h
    rw [Fin.val_rev] at h
    change i.val.val = (p - 1) / 2
    have hi := i.val.isLt
    omega
  let inst : Unique (Function.fixedPoints (Fin.revPerm : Equiv.Perm (Fin p))) :=
    { default := ⟨mid, by
        change Fin.rev mid = mid
        apply Fin.ext
        rw [Fin.val_rev]
        change p - ((p - 1) / 2 + 1) = (p - 1) / 2
        omega⟩
      uniq := fun i => Subtype.ext (hfix i) }
  rw [Equiv.Perm.sign_of_pow_two_eq_one hs, Fintype.card_fin, Fintype.card_unique]

end OMA

theorem OMA.solution : type_of% @OeisA228304.conjecture_2 := by
  classical
  intro p hp hodd
  let inst : Fact p.Prime := ⟨hp⟩
  have hodd' : Odd p := hp.odd_of_ne_two hodd
  have hmod : p % 2 = 1 := Nat.odd_iff.mp hodd'
  let C : Matrix (Fin p) (Fin p) ℤ := fun i j => OeisA228304.c (i.val + j.val)
  let D := C.map (Int.castRingHom (ZMod p))
  change C.det ≡ 1 [ZMOD p]
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_one]
  change (Int.castRingHom (ZMod p)) C.det = 1
  rw [RingHom.map_det]
  change D.det = 1
  -- Reversing the columns places the anti-diagonal on the ordinary diagonal.
  let T := D.submatrix id (Fin.revPerm : Equiv.Perm (Fin p))
  have hT : T.IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    have hj := j.isLt
    have hi := i.isLt
    change j.val < i.val at hij
    change (OeisA228304.c (i.val + (Fin.rev j).val) : ZMod p) = 0
    rw [Fin.val_rev]
    have he : i.val + (p - (j.val + 1)) = p + (i.val - (j.val + 1)) := by omega
    rw [he]
    exact OMA.c_vanish p hodd' _ (by omega)
  let a : ZMod p := (-1 : ZMod p) ^ ((p - 1) / 2)
  have hdiag (i : Fin p) : T i i = a := by
    change (OeisA228304.c (i.val + (Fin.rev i).val) : ZMod p) = a
    have hi := i.isLt
    rw [Fin.val_rev, show i.val + (p - (i.val + 1)) = p - 1 by omega]
    exact OMA.c_diagonal p hmod
  have hdet : T.det = a := by
    rw [Matrix.det_of_isUpperTriangular hT]
    simp_rw [hdiag]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    change ((-1 : ZMod p) ^ ((p - 1) / 2)) ^ p = a
    rw [← pow_mul, Nat.mul_comm ((p - 1) / 2) p, pow_mul, hodd'.neg_one_pow]
  have hs : (↑((Fin.revPerm : Equiv.Perm (Fin p)).sign : ℤ) : ZMod p) = a := by
    rw [OMA.reversal_sign p hmod]
    simp [a]
  change (D.submatrix id (Fin.revPerm : Equiv.Perm (Fin p))).det = a at hdet
  rw [Matrix.det_permute', hs] at hdet
  apply mul_left_cancel₀ (show a ≠ 0 by simp [a])
  simpa using hdet

