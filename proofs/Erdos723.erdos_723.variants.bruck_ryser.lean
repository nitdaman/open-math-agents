import FormalConjectures.ErdosProblems.«723»
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Combinatorics.Configuration

/-!
# Proof of the Bruck–Ryser Theorem (`Erdos723.erdos_723.variants.bruck_ryser`)

If a finite projective plane has order `n` with `n ≡ 1 [MOD 4]` or `n ≡ 2 [MOD 4]`, then `n` is
a sum of two squares.
-/

-- Problem: Erdős Problem 723: The prime power conjecture. — bruck ryser
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/723.lean:72 (declaration Erdos723.erdos_723.variants.bruck_ryser)
-- Credit: @Dugongue (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Configuration

namespace OMA.BruckRyser

private lemma nat_eq_sq_add_sq_of_rat {n : ℕ} {q₁ q₂ : ℚ} (h : (n : ℚ) = q₁ ^ 2 + q₂ ^ 2) :
    ∃ a b : ℕ, n = a ^ 2 + b ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact ⟨0, 0, rfl⟩
  let d : ℕ := q₁.den * q₂.den
  have hd0 : d ≠ 0 := mul_ne_zero q₁.den_nz q₂.den_nz
  let x : ℕ := (q₁.num * (q₂.den : ℤ)).natAbs
  let y : ℕ := (q₂.num * (q₁.den : ℤ)).natAbs
  have hq₁d : q₁ * (d : ℚ) = (q₁.num * (q₂.den : ℤ) : ℤ) := by
    dsimp [d]
    rw [Nat.cast_mul, ← mul_assoc, Rat.mul_den_eq_num]
    push_cast
    ring
  have hq₂d : q₂ * (d : ℚ) = (q₂.num * (q₁.den : ℤ) : ℤ) := by
    dsimp [d]
    rw [Nat.cast_mul, mul_comm (q₁.den : ℚ), ← mul_assoc, Rat.mul_den_eq_num]
    push_cast
    ring
  have hnd_rat : ((n * d ^ 2 : ℕ) : ℚ) = ((x ^ 2 + y ^ 2 : ℕ) : ℚ) := by
    have hx : ((x : ℚ)) ^ 2 = ((q₁.num * (q₂.den : ℤ) : ℤ) : ℚ) ^ 2 := by
      dsimp [x]
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]
    have hy : ((y : ℚ)) ^ 2 = ((q₂.num * (q₁.den : ℤ) : ℤ) : ℚ) ^ 2 := by
      dsimp [y]
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]
    push_cast
    rw [h, hx, hy, ← hq₁d, ← hq₂d]
    ring
  have hnd : n * d ^ 2 = x ^ 2 + y ^ 2 := Nat.cast_injective hnd_rat
  rw [Nat.eq_sq_add_sq_iff]
  intro q hq hq4
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have : Fact q.Prime := ⟨hq_prime⟩
  have hnd_ne : n * d ^ 2 ≠ 0 := mul_ne_zero hn0 (pow_ne_zero 2 hd0)
  have hq_nd : q ∈ (n * d ^ 2).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hq_prime, dvd_mul_of_dvd_left (Nat.dvd_of_mem_primeFactors hq) _, hnd_ne⟩
  have hev : Even (padicValNat q (n * d ^ 2)) :=
    Nat.eq_sq_add_sq_iff.mp ⟨x, y, hnd⟩ q hq_nd hq4
  rw [padicValNat.mul hn0 (pow_ne_zero 2 hd0), sq d, padicValNat.mul hd0 hd0, ← two_mul] at hev
  rw [Nat.even_add] at hev
  exact hev.mpr (even_two_mul _)

private lemma sign_elimination : ∀ (k : ℕ) (f : Fin k → (Fin (k + 1) → ℚ) →ₗ[ℚ] ℚ),
    ∃ z : Fin (k + 1) → ℚ, z (Fin.last k) = 1 ∧ ∀ i : Fin k, (f i z) ^ 2 = (z i.castSucc) ^ 2
  | 0, _ => ⟨fun _ => 1, rfl, fun i => Fin.elim0 i⟩
  | k + 1, f => by
    let c : ℚ := f 0 (Pi.single 0 1)
    let ε : ℚ := if c = 1 then -1 else 1
    have hε_sq : ε ^ 2 = 1 := by
      dsimp [ε]
      split_ifs <;> norm_num
    have hcε : c - ε ≠ 0 := by
      dsimp [ε]
      split_ifs with h
      · intro h0
        linarith
      · intro h0
        exact h (sub_eq_zero.mp h0)
    let cons0 : (Fin (k + 1) → ℚ) →ₗ[ℚ] (Fin (k + 2) → ℚ) :=
      { toFun := fun u => Fin.cons 0 u
        map_add' := fun u v => by
          ext i
          refine Fin.cases ?_ ?_ i <;> simp
        map_smul' := fun r u => by
          ext i
          refine Fin.cases ?_ ?_ i <;> simp }
    let α : (Fin (k + 1) → ℚ) →ₗ[ℚ] ℚ := (-(c - ε)⁻¹) • ((f 0).comp cons0)
    let φ : (Fin (k + 1) → ℚ) →ₗ[ℚ] (Fin (k + 2) → ℚ) :=
      { toFun := fun u => Fin.cons (α u) u
        map_add' := fun u v => by
          ext i
          refine Fin.cases ?_ ?_ i <;> simp
        map_smul' := fun r u => by
          ext i
          refine Fin.cases ?_ ?_ i <;> simp }
    have hφ_decomp : ∀ u : Fin (k + 1) → ℚ, φ u = α u • Pi.single 0 1 + cons0 u := by
      intro u
      ext i
      refine Fin.cases ?_ ?_ i
      · simp [φ, cons0]
      · intro j
        simp [φ, cons0]
    have hf0 : ∀ u : Fin (k + 1) → ℚ, f 0 (φ u) = ε * φ u 0 := by
      intro u
      conv_lhs => rw [hφ_decomp u]
      rw [map_add, map_smul, smul_eq_mul]
      change α u * c + f 0 (cons0 u) = ε * α u
      have hα : α u = -(c - ε)⁻¹ * f 0 (cons0 u) := rfl
      rw [hα]
      field_simp [hcε]
      ring
    obtain ⟨u, hu_last, hu_sq⟩ := sign_elimination k (fun i => (f i.succ).comp φ)
    refine ⟨φ u, ?_, ?_⟩
    · have hlast : Fin.last (k + 1) = (Fin.last k).succ := by
        ext
        simp
      rw [hlast]
      simpa [φ] using hu_last
    · intro i
      refine Fin.cases ?_ ?_ i
      · have h0 : (0 : Fin (k + 1)).castSucc = 0 := rfl
        rw [h0, hf0 u, mul_pow, hε_sq, one_mul]
      · intro j
        have hs : j.succ.castSucc = j.castSucc.succ := rfl
        rw [hs]
        simpa [φ] using hu_sq j

private noncomputable def fourBlockLin (n : ℕ) (a b c d : ℚ) :
    (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) :=
  { toFun := fun z =>
      ![(a * z 0 + b * z 1 + c * z 2 + d * z 3) / (n : ℚ),
        (-b * z 0 + a * z 1 + d * z 2 - c * z 3) / (n : ℚ),
        (-c * z 0 - d * z 1 + a * z 2 + b * z 3) / (n : ℚ),
        (-d * z 0 + c * z 1 - b * z 2 + a * z 3) / (n : ℚ)]
    map_add' := fun u v => by
      ext i
      fin_cases i <;> simp <;> ring
    map_smul' := fun r u => by
      ext i
      fin_cases i <;> simp <;> ring }

private lemma fourBlockLin_sum_sq {n : ℕ} (hn : n ≠ 0) {a b c d : ℚ}
    (habcd : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = (n : ℚ)) (z : Fin 4 → ℚ) :
    (n : ℚ) * ∑ j : Fin 4, (fourBlockLin n a b c d z j) ^ 2 = ∑ j : Fin 4, (z j) ^ 2 := by
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h0 : fourBlockLin n a b c d z 0 = (a * z 0 + b * z 1 + c * z 2 + d * z 3) / (n : ℚ) := rfl
  have h1 : fourBlockLin n a b c d z 1 = (-b * z 0 + a * z 1 + d * z 2 - c * z 3) / (n : ℚ) := rfl
  have h2 : fourBlockLin n a b c d z 2 = (-c * z 0 - d * z 1 + a * z 2 + b * z 3) / (n : ℚ) := rfl
  have h3 : fourBlockLin n a b c d z 3 = (-d * z 0 + c * z 1 - b * z 2 + a * z 3) / (n : ℚ) := rfl
  rw [Fin.sum_univ_four, Fin.sum_univ_four, h0, h1, h2, h3]
  field_simp [hnq]
  rw [← habcd]
  ring

private noncomputable def multFourLin (m n : ℕ) (a b c d : ℚ) :
    (Fin (m * 4) → ℚ) →ₗ[ℚ] (Fin (m * 4) → ℚ) :=
  { toFun := fun z i =>
      let p := finProdFinEquiv.symm i
      fourBlockLin n a b c d (fun j => z (finProdFinEquiv (p.1, j))) p.2
    map_add' := fun u v => by
      ext i
      simp only [Pi.add_apply]
      have h : (fun j : Fin 4 => u (finProdFinEquiv ((finProdFinEquiv.symm i).1, j)) +
          v (finProdFinEquiv ((finProdFinEquiv.symm i).1, j))) =
          (fun j => u (finProdFinEquiv ((finProdFinEquiv.symm i).1, j))) +
          (fun j => v (finProdFinEquiv ((finProdFinEquiv.symm i).1, j))) := rfl
      rw [h, map_add, Pi.add_apply]
    map_smul' := fun r u => by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      have h : (fun j : Fin 4 => r * u (finProdFinEquiv ((finProdFinEquiv.symm i).1, j))) =
          r • (fun j => u (finProdFinEquiv ((finProdFinEquiv.symm i).1, j))) := rfl
      rw [h, map_smul, Pi.smul_apply, smul_eq_mul] }

private lemma multFourLin_sum_sq {m n : ℕ} (hn : n ≠ 0) {a b c d : ℚ}
    (habcd : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = (n : ℚ)) (z : Fin (m * 4) → ℚ) :
    (n : ℚ) * ∑ i : Fin (m * 4), (multFourLin m n a b c d z i) ^ 2 =
      ∑ i : Fin (m * 4), (z i) ^ 2 := by
  rw [← Fintype.sum_equiv finProdFinEquiv
        (fun p : Fin m × Fin 4 => (multFourLin m n a b c d z (finProdFinEquiv p)) ^ 2)
        (fun i => (multFourLin m n a b c d z i) ^ 2) (fun _ => rfl)]
  rw [← Fintype.sum_equiv finProdFinEquiv
        (fun p : Fin m × Fin 4 => (z (finProdFinEquiv p)) ^ 2)
        (fun i => (z i) ^ 2) (fun _ => rfl)]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : ∀ j : Fin 4,
      multFourLin m n a b c d z (finProdFinEquiv (k, j)) =
        fourBlockLin n a b c d (fun j' => z (finProdFinEquiv (k, j'))) j := by
    intro j
    simp only [multFourLin, LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply]
  simp_rw [h1]
  exact fourBlockLin_sum_sq hn habcd _

open Classical in
private lemma incidence_sum_sq {P L : Type} [Membership P L] [Fintype P] [Fintype L]
    [Configuration.ProjectivePlane P L] (x : P → ℚ) :
    ∑ l : L, (∑ p : P, if p ∈ l then x p else 0) ^ 2 =
      (Configuration.ProjectivePlane.order P L : ℚ) * ∑ p : P, (x p) ^ 2 +
        (∑ p : P, x p) ^ 2 := by
  have hcount : ∀ p q : P,
      ((Finset.univ.filter fun l : L => p ∈ l ∧ q ∈ l).card : ℚ) =
        (if p = q then (Configuration.ProjectivePlane.order P L : ℚ) else 0) + 1 := by
    intro p q
    by_cases hpq : p = q
    · subst hpq
      simp only [and_self, ↓reduceIte]
      have hcard : (Finset.univ.filter fun l : L => p ∈ l).card =
          Configuration.ProjectivePlane.order P L + 1 := by
        rw [← Configuration.ProjectivePlane.lineCount_eq L p, Configuration.lineCount,
          Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact_mod_cast hcard
    · simp only [hpq, ↓reduceIte, zero_add]
      obtain ⟨l₀, hl₀, huniq⟩ := @Configuration.HasLines.existsUnique_line P L _ _ p q hpq
      have hfilt : (Finset.univ.filter fun l : L => p ∈ l ∧ q ∈ l) = {l₀} := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => huniq l h, fun h => h ▸ hl₀⟩
      rw [hfilt, Finset.card_singleton, Nat.cast_one]
  calc
    ∑ l : L, (∑ p : P, if p ∈ l then x p else 0) ^ 2
        = ∑ l : L, ∑ p : P, ∑ q : P,
            (if p ∈ l then x p else 0) * (if q ∈ l then x q else 0) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [sq, Finset.sum_mul_sum]
    _ = ∑ p : P, ∑ q : P, ∑ l : L,
          if p ∈ l ∧ q ∈ l then x p * x q else 0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun q _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          by_cases hp : p ∈ l <;> by_cases hq : q ∈ l <;> simp [hp, hq]
    _ = ∑ p : P, ∑ q : P,
          ((Finset.univ.filter fun l : L => p ∈ l ∧ q ∈ l).card : ℚ) * (x p * x q) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ = ∑ p : P, ∑ q : P,
          ((if p = q then (Configuration.ProjectivePlane.order P L : ℚ) else 0) * (x p * x q) +
            x p * x q) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          rw [hcount p q, add_mul, one_mul]
    _ = (∑ p : P, ∑ q : P,
          (if p = q then (Configuration.ProjectivePlane.order P L : ℚ) else 0) * (x p * x q)) +
        ∑ p : P, ∑ q : P, x p * x q := by
          simp_rw [Finset.sum_add_distrib]
    _ = (Configuration.ProjectivePlane.order P L : ℚ) * ∑ p : P, (x p) ^ 2 +
        (∑ p : P, x p) ^ 2 := by
          congr 1
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => ?_
            simp [sq]
          · rw [sq, Finset.sum_mul_sum]

end OMA.BruckRyser

open Classical in
theorem OMA.solution : type_of% @Erdos723.erdos_723.variants.bruck_ryser := by
  intro P L _ _ _ n pp hpp hmod
  let : Configuration.ProjectivePlane P L := pp
  subst hpp
  set n := Configuration.ProjectivePlane.order P L
  have hn1 : 1 < n := Configuration.ProjectivePlane.one_lt_order P L
  have hn0 : n ≠ 0 := by omega
  set v := n ^ 2 + n + 1
  have hP : Fintype.card P = v := Configuration.ProjectivePlane.card_points P L
  have hL : Fintype.card L = v := Configuration.ProjectivePlane.card_lines P L
  have hdiv4 : 4 ∣ v + 1 := by
    have hv1 : v + 1 = n ^ 2 + n + 2 := rfl
    rw [hv1, Nat.dvd_iff_mod_eq_zero]
    rcases hmod with h | h
    · have h2 : n ^ 2 + n + 2 ≡ 1 ^ 2 + 1 + 2 [MOD 4] :=
        ((h.pow 2).add h).add_right 2
      simpa [Nat.ModEq] using h2
    · have h2 : n ^ 2 + n + 2 ≡ 2 ^ 2 + 2 + 2 [MOD 4] :=
        ((h.pow 2).add h).add_right 2
      simpa [Nat.ModEq] using h2
  set m := (v + 1) / 4
  have hm : m * 4 = v + 1 := Nat.div_mul_cancel hdiv4
  obtain ⟨a, b, c, d, habcd_nat⟩ := Nat.sum_four_squares n
  have habcd : (a : ℚ) ^ 2 + (b : ℚ) ^ 2 + (c : ℚ) ^ 2 + (d : ℚ) ^ 2 = (n : ℚ) := by
    exact_mod_cast habcd_nat
  let eP : P ≃ Fin v := Fintype.equivFinOfCardEq hP
  let eL : L ≃ Fin v := Fintype.equivFinOfCardEq hL
  let e4 : Fin (v + 1) ≃ Fin (m * 4) := finCongr hm.symm
  let e4Lin : (Fin (v + 1) → ℚ) ≃ₗ[ℚ] (Fin (m * 4) → ℚ) :=
    LinearEquiv.funCongrLeft ℚ ℚ e4.symm
  let X : (Fin (v + 1) → ℚ) →ₗ[ℚ] (Fin (v + 1) → ℚ) :=
    e4Lin.symm.toLinearMap.comp
      ((OMA.BruckRyser.multFourLin m n a b c d).comp e4Lin.toLinearMap)
  have hX_sum : ∀ z : Fin (v + 1) → ℚ,
      (n : ℚ) * ∑ i : Fin (v + 1), (X z i) ^ 2 = ∑ i : Fin (v + 1), (z i) ^ 2 := by
    intro z
    have h1 : ∑ i : Fin (v + 1), (X z i) ^ 2 =
        ∑ j : Fin (m * 4), (OMA.BruckRyser.multFourLin m n a b c d (e4Lin z) j) ^ 2 := by
      refine Fintype.sum_equiv e4 _ _ fun i => ?_
      simp [X, e4Lin]
    have h2 : ∑ i : Fin (v + 1), (z i) ^ 2 = ∑ j : Fin (m * 4), (e4Lin z j) ^ 2 := by
      refine Fintype.sum_equiv e4 _ _ fun i => ?_
      simp [e4Lin]
    rw [h1, h2]
    exact OMA.BruckRyser.multFourLin_sum_sq hn0 habcd (e4Lin z)
  let f : Fin v → (Fin (v + 1) → ℚ) →ₗ[ℚ] ℚ := fun j =>
    { toFun := fun z => ∑ i : Fin v, if eP.symm i ∈ eL.symm j then X z i.castSucc else 0
      map_add' := fun u v' => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
      map_smul' := fun r u => by
        simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp }
  obtain ⟨z, hz_last, hz_sq⟩ := OMA.BruckRyser.sign_elimination v f
  let x : P → ℚ := fun p => X z (eP p).castSucc
  have hinc := OMA.BruckRyser.incidence_sum_sq (L := L) x
  change _ = (n : ℚ) * _ + _ at hinc
  have hlhs : ∑ l : L, (∑ p : P, if p ∈ l then x p else 0) ^ 2 =
      ∑ j : Fin v, (z j.castSucc) ^ 2 := by
    calc
      ∑ l : L, (∑ p : P, if p ∈ l then x p else 0) ^ 2
          = ∑ j : Fin v, (∑ p : P, if p ∈ eL.symm j then x p else 0) ^ 2 :=
            Fintype.sum_equiv eL _ _ fun l => by simp
      _ = ∑ j : Fin v, (f j z) ^ 2 := by
            refine Finset.sum_congr rfl fun j _ => ?_
            congr 1
            exact Fintype.sum_equiv eP _ _ fun p => by simp [x]
      _ = ∑ j : Fin v, (z j.castSucc) ^ 2 :=
            Finset.sum_congr rfl fun j _ => hz_sq j
  have hsum_x : ∑ p : P, (x p) ^ 2 = ∑ i : Fin v, (X z i.castSucc) ^ 2 :=
    Fintype.sum_equiv eP _ _ fun p => by simp [x]
  have hXz := hX_sum z
  have hXz_lhs : ∑ i : Fin (v + 1), (X z i) ^ 2 =
      ∑ i : Fin v, (X z i.castSucc) ^ 2 + (X z (Fin.last v)) ^ 2 := Fin.sum_univ_castSucc _
  have hXz_rhs : ∑ i : Fin (v + 1), (z i) ^ 2 =
      ∑ i : Fin v, (z i.castSucc) ^ 2 + (z (Fin.last v)) ^ 2 := Fin.sum_univ_castSucc _
  rw [hXz_lhs, hXz_rhs, hz_last, mul_add] at hXz
  rw [hlhs, hsum_x] at hinc
  set r : ℚ := X z (Fin.last v)
  set w : ℚ := ∑ p : P, x p
  have hkey : (n : ℚ) * r ^ 2 = 1 + w ^ 2 := by linarith
  have hr : r ≠ 0 := by
    intro hr0
    rw [hr0] at hkey
    nlinarith
  have hn_rat : (n : ℚ) = (1 / r) ^ 2 + (w / r) ^ 2 := by
    field_simp [hr]
    linarith
  exact OMA.BruckRyser.nat_eq_sq_add_sq_of_rat hn_rat
