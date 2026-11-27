import FormalConjectures.Wikipedia.Kaplansky

/-!
# Counterexample to Kaplansky's Unit Conjecture in every prime characteristic

We prove `Kaplansky.UnitConjecture.counterexamples.i`: for every prime `p`, the group ring
`MonoidAlgebra (ZMod p) PromislowGroup` contains a non-trivial unit.

## Proof outline
1. Let `gA, gB` be the generators of `PromislowGroup = ⟨a, b | b⁻¹a²ba², a⁻¹b²ab²⟩`, and set
   `gX = gA²`, `gY = gB²`, `gAB = gA * gB`, `gZ = gAB²`. From the two defining relations, `gX, gY, gZ`
   pairwise commute and are inverted/fixed under conjugation by `gA, gB, gAB`.
2. Let `N = Multiplicative (ℤ × ℤ × ℤ)` and `R = MonoidAlgebra (ZMod p) N` (a commutative ring of
   characteristic `p`). The group homomorphism `ι : N →* PromislowGroup` induces a ring embedding
   `embed : R →+* MonoidAlgebra (ZMod p) PromislowGroup` intertwined with three coordinate-flip
   automorphisms `σA, σB, σC` of `R`.
3. Following Murray (2021) and Passman (2021), put `H = (1 - Z) ^ (p - 2)` and
   `Ha = (1 - Z⁻¹) ^ (p - 2)` in `R`, and define `U = P + Q a + R b + S ab` and
   `V = P' + Q' a + R' b + S' ab` with `P' = X⁻¹ σA(P)`, `Q' = -X⁻¹ Q`, `R' = -Y⁻¹ R`,
   `S' = Z⁻¹ σA(S)`. The single Frobenius identity `(1 - Z)(Z - 1) H Ha = -Z² H - Ha` in
   characteristic `p` collapses all four components of `U * V` and `V * U` to `1` via cleared
   polynomial identities.
4. A concrete 4×4 integer matrix representation `φ : PromislowGroup →* (Matrix (Fin 4) (Fin 4) ℤ)ˣ`
   separates the four `N`-cosets and acts injectively on `N`, showing that the image of `U` has
   coefficient `1 ≠ 0` at both `φ(gX * gAB)` and `φ(gY * gAB)`. Hence `U` is not a trivial unit.
-/

-- Problem: Kaplansky's Conjectures — i
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/Kaplansky.lean:114 (declaration Kaplansky.UnitConjecture.counterexamples.i)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace KaplanskyUnitCharP

open Kaplansky

noncomputable section

/- ### Relations in `PromislowGroup` -/

private abbrev P := PromislowGroup

private def gA : P := PresentedGroup.of (0 : Fin 2)
private def gB : P := PresentedGroup.of (1 : Fin 2)
private def gX : P := gA * gA
private def gY : P := gB * gB
private def gAB : P := gA * gB
private def gZ : P := gAB * gAB

private lemma rel_b_a2 : gB⁻¹ * gA * gA * gB * gA * gA = 1 := by
  let fa := FreeGroup.of (0 : Fin 2)
  let fb := FreeGroup.of (1 : Fin 2)
  have hmem : fb⁻¹ * fa * fa * fb * fa * fa ∈
      ({fb⁻¹ * fa * fa * fb * fa * fa, fa⁻¹ * fb * fb * fa * fb * fb} : Set (FreeGroup (Fin 2))) :=
    Set.mem_insert _ _
  have h := PresentedGroup.one_of_mem hmem
  simpa [gA, gB, fa, fb, PresentedGroup.of, map_mul, map_inv] using h

private lemma rel_a_b2 : gA⁻¹ * gB * gB * gA * gB * gB = 1 := by
  let fa := FreeGroup.of (0 : Fin 2)
  let fb := FreeGroup.of (1 : Fin 2)
  have hmem : fa⁻¹ * fb * fb * fa * fb * fb ∈
      ({fb⁻¹ * fa * fa * fb * fa * fa, fa⁻¹ * fb * fb * fa * fb * fb} : Set (FreeGroup (Fin 2))) :=
    Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have h := PresentedGroup.one_of_mem hmem
  simpa [gA, gB, fa, fb, PresentedGroup.of, map_mul, map_inv] using h

private lemma gB_mul_gX : gB * gX = gX⁻¹ * gB := by
  have h : gB⁻¹ * gX * gB * gX = 1 := by
    simpa [gX, mul_assoc] using rel_b_a2
  calc
    gB * gX = gX⁻¹ * (gB * (gB⁻¹ * gX * gB * gX)) := by group
    _ = gX⁻¹ * (gB * 1) := by rw [h]
    _ = gX⁻¹ * gB := by group

private lemma gB_mul_gX_inv : gB * gX⁻¹ = gX * gB := by
  calc
    gB * gX⁻¹ = gX * (gX⁻¹ * gB) * gX⁻¹ := by group
    _ = gX * (gB * gX) * gX⁻¹ := by rw [← gB_mul_gX]
    _ = gX * gB := by group

private lemma gA_mul_gY : gA * gY = gY⁻¹ * gA := by
  have h : gA⁻¹ * gY * gA * gY = 1 := by
    simpa [gY, mul_assoc] using rel_a_b2
  calc
    gA * gY = gY⁻¹ * (gA * (gA⁻¹ * gY * gA * gY)) := by group
    _ = gY⁻¹ * (gA * 1) := by rw [h]
    _ = gY⁻¹ * gA := by group

private lemma gA_mul_gY_inv : gA * gY⁻¹ = gY * gA := by
  calc
    gA * gY⁻¹ = gY * (gY⁻¹ * gA) * gY⁻¹ := by group
    _ = gY * (gA * gY) * gY⁻¹ := by rw [← gA_mul_gY]
    _ = gY * gA := by group

private lemma gA_mul_gX : gA * gX = gX * gA := by
  simp only [gX, mul_assoc]

private lemma gA_mul_gX_inv : gA * gX⁻¹ = gX⁻¹ * gA := by
  calc
    gA * gX⁻¹ = gX⁻¹ * (gX * gA) * gX⁻¹ := by group
    _ = gX⁻¹ * (gA * gX) * gX⁻¹ := by rw [← gA_mul_gX]
    _ = gX⁻¹ * gA := by group

private lemma gB_mul_gY : gB * gY = gY * gB := by
  simp only [gY, mul_assoc]

private lemma gB_mul_gY_inv : gB * gY⁻¹ = gY⁻¹ * gB := by
  calc
    gB * gY⁻¹ = gY⁻¹ * (gY * gB) * gY⁻¹ := by group
    _ = gY⁻¹ * (gB * gY) * gY⁻¹ := by rw [← gB_mul_gY]
    _ = gY⁻¹ * gB := by group

private lemma gX_mul_gY : gX * gY = gY * gX := by
  calc
    gX * gY = gA * (gA * gY) := by simp only [gX, mul_assoc]
    _ = gA * (gY⁻¹ * gA) := by rw [gA_mul_gY]
    _ = (gA * gY⁻¹) * gA := by simp only [mul_assoc]
    _ = (gY * gA) * gA := by rw [gA_mul_gY_inv]
    _ = gY * gX := by simp only [gX, mul_assoc]

private lemma gA_mul_gZ : gA * gZ = gZ⁻¹ * gA := by
  have hprod : (gA * gZ * gA⁻¹) * gZ = 1 := by
    calc
      gA * gZ * gA⁻¹ * gZ
        = gX * gB * (gA * gY) * gA * gB := by simp only [gZ, gAB, gX, gY, mul_assoc]; group
      _ = gX * gB * (gY⁻¹ * gA) * gA * gB := by rw [gA_mul_gY]
      _ = gX * (gB * gY⁻¹) * gX * gB := by simp only [gX, mul_assoc]
      _ = gX * (gY⁻¹ * gB) * gX * gB := by rw [gB_mul_gY_inv]
      _ = gX * gY⁻¹ * (gB * gX) * gB := by simp only [mul_assoc]
      _ = gX * gY⁻¹ * (gX⁻¹ * gB) * gB := by rw [gB_mul_gX]
      _ = gX * gY⁻¹ * gX⁻¹ * gY := by simp only [gY, mul_assoc]
      _ = gX * gY⁻¹ * gX⁻¹ * (gX * gY * gX⁻¹) := by rw [gX_mul_gY]; group
      _ = 1 := by group
  calc
    gA * gZ = (gA * gZ * gA⁻¹ * gZ) * gZ⁻¹ * gA := by group
    _ = 1 * gZ⁻¹ * gA := by rw [hprod]
    _ = gZ⁻¹ * gA := by group

private lemma gB_mul_gZ : gB * gZ = gZ⁻¹ * gB := by
  have hprod : (gB * gZ * gB⁻¹) * gZ = 1 := by
    calc
      gB * gZ * gB⁻¹ * gZ
        = gB * gA * (gB * gX) * gB * gA * gB := by simp only [gZ, gAB, gX, mul_assoc]; group
      _ = gB * gA * (gX⁻¹ * gB) * gB * gA * gB := by rw [gB_mul_gX]
      _ = gB * (gA * gX⁻¹) * gY * gA * gB := by simp only [gY, mul_assoc]
      _ = gB * (gX⁻¹ * gA) * gY * gA * gB := by rw [gA_mul_gX_inv]
      _ = gB * gX⁻¹ * (gA * gY) * gA * gB := by simp only [mul_assoc]
      _ = gB * gX⁻¹ * (gY⁻¹ * gA) * gA * gB := by rw [gA_mul_gY]
      _ = (gB * gX⁻¹) * gY⁻¹ * gX * gB := by simp only [gX, mul_assoc]
      _ = (gX * gB) * gY⁻¹ * gX * gB := by rw [gB_mul_gX_inv]
      _ = gX * (gB * gY⁻¹) * gX * gB := by simp only [mul_assoc]
      _ = gX * (gY⁻¹ * gB) * gX * gB := by rw [gB_mul_gY_inv]
      _ = gX * gY⁻¹ * (gB * gX) * gB := by simp only [mul_assoc]
      _ = gX * gY⁻¹ * (gX⁻¹ * gB) * gB := by rw [gB_mul_gX]
      _ = gX * gY⁻¹ * gX⁻¹ * gY := by simp only [gY, mul_assoc]
      _ = gX * gY⁻¹ * gX⁻¹ * (gX * gY * gX⁻¹) := by rw [gX_mul_gY]; group
      _ = 1 := by group
  calc
    gB * gZ = (gB * gZ * gB⁻¹ * gZ) * gZ⁻¹ * gB := by group
    _ = 1 * gZ⁻¹ * gB := by rw [hprod]
    _ = gZ⁻¹ * gB := by group

private lemma gA_mul_gZ_inv : gA * gZ⁻¹ = gZ * gA := by
  calc
    gA * gZ⁻¹ = gZ * (gZ⁻¹ * gA) * gZ⁻¹ := by group
    _ = gZ * (gA * gZ) * gZ⁻¹ := by rw [← gA_mul_gZ]
    _ = gZ * gA := by group

private lemma gB_mul_gZ_inv : gB * gZ⁻¹ = gZ * gB := by
  calc
    gB * gZ⁻¹ = gZ * (gZ⁻¹ * gB) * gZ⁻¹ := by group
    _ = gZ * (gB * gZ) * gZ⁻¹ := by rw [← gB_mul_gZ]
    _ = gZ * gB := by group

private lemma gX_mul_gZ : gX * gZ = gZ * gX := by
  calc
    gX * gZ = gA * (gA * gZ) := by simp only [gX, mul_assoc]
    _ = gA * (gZ⁻¹ * gA) := by rw [gA_mul_gZ]
    _ = (gA * gZ⁻¹) * gA := by simp only [mul_assoc]
    _ = (gZ * gA) * gA := by rw [gA_mul_gZ_inv]
    _ = gZ * gX := by simp only [gX, mul_assoc]

private lemma gY_mul_gZ : gY * gZ = gZ * gY := by
  calc
    gY * gZ = gB * (gB * gZ) := by simp only [gY, mul_assoc]
    _ = gB * (gZ⁻¹ * gB) := by rw [gB_mul_gZ]
    _ = (gB * gZ⁻¹) * gB := by simp only [mul_assoc]
    _ = (gZ * gB) * gB := by rw [gB_mul_gZ_inv]
    _ = gZ * gY := by simp only [gY, mul_assoc]

private lemma gB_mul_gA : gB * gA = gX⁻¹ * gY * gZ⁻¹ * gAB := by
  have h1 : gA⁻¹ = gX⁻¹ * gA := by simp only [gX]; group
  have h2 : gB⁻¹ = gY⁻¹ * gB := by simp only [gY]; group
  calc
    gB * gA = gA⁻¹ * gZ * gB⁻¹ := by simp only [gZ, gAB, mul_assoc]; group
    _ = gX⁻¹ * (gA * gZ) * (gY⁻¹ * gB) := by rw [h1, h2]; simp only [mul_assoc]
    _ = gX⁻¹ * (gZ⁻¹ * gA) * (gY⁻¹ * gB) := by rw [gA_mul_gZ]
    _ = gX⁻¹ * gZ⁻¹ * (gA * gY⁻¹) * gB := by simp only [mul_assoc]
    _ = gX⁻¹ * gZ⁻¹ * (gY * gA) * gB := by rw [gA_mul_gY_inv]
    _ = gX⁻¹ * (gZ⁻¹ * gY) * gAB := by simp only [gAB, mul_assoc]
    _ = gX⁻¹ * (gY * gZ⁻¹) * gAB := by
          have hzy : gZ⁻¹ * gY = gY * gZ⁻¹ := by
            calc
              gZ⁻¹ * gY = gZ⁻¹ * (gY * gZ) * gZ⁻¹ := by group
              _ = gZ⁻¹ * (gZ * gY) * gZ⁻¹ := by rw [gY_mul_gZ]
              _ = gY * gZ⁻¹ := by group
          rw [hzy]
    _ = gX⁻¹ * gY * gZ⁻¹ * gAB := by simp only [mul_assoc]

private lemma gA_mul_gAB : gA * gAB = gX * gB := by
  simp only [gAB, gX, mul_assoc]

private lemma gB_mul_gAB : gB * gAB = gX⁻¹ * gZ⁻¹ * gA := by
  calc
    gB * gAB = (gB * gA) * gB := by simp only [gAB, mul_assoc]
    _ = (gX⁻¹ * gY * gZ⁻¹ * gAB) * gB := by rw [gB_mul_gA]
    _ = gX⁻¹ * gY * gZ⁻¹ * (gA * gY) := by simp only [gAB, gY, mul_assoc]
    _ = gX⁻¹ * gY * gZ⁻¹ * (gY⁻¹ * gA) := by rw [gA_mul_gY]
    _ = gX⁻¹ * gY * (gZ⁻¹ * gY⁻¹) * gA := by simp only [mul_assoc]
    _ = gX⁻¹ * gY * (gY⁻¹ * gZ⁻¹) * gA := by
          have h : gZ⁻¹ * gY⁻¹ = gY⁻¹ * gZ⁻¹ := by
            calc
              gZ⁻¹ * gY⁻¹ = (gY * gZ)⁻¹ := by group
              _ = (gZ * gY)⁻¹ := by rw [gY_mul_gZ]
              _ = gY⁻¹ * gZ⁻¹ := by group
          rw [h]
    _ = gX⁻¹ * gZ⁻¹ * gA := by group

private lemma gAB_mul_gA : gAB * gA = gY⁻¹ * gZ * gB := by
  calc
    gAB * gA = gA * (gB * gA) := by simp only [gAB, mul_assoc]
    _ = gA * (gX⁻¹ * gY * gZ⁻¹ * gAB) := by rw [gB_mul_gA]
    _ = (gA * gX⁻¹) * gY * gZ⁻¹ * gAB := by simp only [mul_assoc]
    _ = (gX⁻¹ * gA) * gY * gZ⁻¹ * gAB := by rw [gA_mul_gX_inv]
    _ = gX⁻¹ * (gA * gY) * gZ⁻¹ * gAB := by simp only [mul_assoc]
    _ = gX⁻¹ * (gY⁻¹ * gA) * gZ⁻¹ * gAB := by rw [gA_mul_gY]
    _ = gX⁻¹ * gY⁻¹ * (gA * gZ⁻¹) * gAB := by simp only [mul_assoc]
    _ = gX⁻¹ * gY⁻¹ * (gZ * gA) * gAB := by rw [gA_mul_gZ_inv]
    _ = gX⁻¹ * gY⁻¹ * gZ * (gA * gAB) := by simp only [mul_assoc]
    _ = gX⁻¹ * gY⁻¹ * gZ * (gX * gB) := by rw [gA_mul_gAB]
    _ = gX⁻¹ * gY⁻¹ * (gZ * gX) * gB := by simp only [mul_assoc]
    _ = gX⁻¹ * gY⁻¹ * (gX * gZ) * gB := by rw [gX_mul_gZ]
    _ = gX⁻¹ * (gY⁻¹ * gX) * gZ * gB := by simp only [mul_assoc]
    _ = gX⁻¹ * (gX * gY⁻¹) * gZ * gB := by
          have h : gY⁻¹ * gX = gX * gY⁻¹ := by
            calc
              gY⁻¹ * gX = gY⁻¹ * (gX * gY) * gY⁻¹ := by group
              _ = gY⁻¹ * (gY * gX) * gY⁻¹ := by rw [gX_mul_gY]
              _ = gX * gY⁻¹ := by group
          rw [h]
    _ = gY⁻¹ * gZ * gB := by group

private lemma gAB_mul_gB : gAB * gB = gY⁻¹ * gA := by
  calc
    gAB * gB = gA * gY := by simp only [gAB, gY, mul_assoc]
    _ = gY⁻¹ * gA := gA_mul_gY

private lemma gAB_mul_gAB : gAB * gAB = gZ := rfl

/- ### Commutative Laurent-polynomial subring `R` and coordinate-flip automorphisms -/

private abbrev N := Multiplicative (ℤ × ℤ × ℤ)

private def mkN (i j k : ℤ) : N := Multiplicative.ofAdd (i, j, k)

private lemma mkN_mul (i₁ j₁ k₁ i₂ j₂ k₂ : ℤ) :
    mkN i₁ j₁ k₁ * mkN i₂ j₂ k₂ = mkN (i₁ + i₂) (j₁ + j₂) (k₁ + k₂) := rfl

private lemma mkN_one : mkN 0 0 0 = 1 := rfl

private lemma commute_zpow {G : Type*} [Group G] {a b : G} (h : a * b = b * a) (m n : ℤ) :
    a ^ m * b ^ n = b ^ n * a ^ m :=
  (Commute.zpow_right (Commute.zpow_left h m) n).eq

private lemma conj_zpow_inv {G : Type*} [Group G] {g a : G} (h : g * a = a⁻¹ * g) (n : ℤ) :
    g * a ^ n = a ^ (-n) * g := by
  have h1 : g * a * g⁻¹ = a⁻¹ := by rw [h]; group
  have h2 : g * a ^ n * g⁻¹ = a ^ (-n) := by
    rw [← conj_zpow, h1, inv_zpow, zpow_neg]
  calc
    g * a ^ n = (g * a ^ n * g⁻¹) * g := by group
    _ = a ^ (-n) * g := by rw [h2]

private lemma conj_zpow_eq {G : Type*} [Group G] {g a : G} (h : g * a = a * g) (n : ℤ) :
    g * a ^ n = a ^ n * g :=
  (Commute.zpow_right h n).eq

private def ι : N →* P where
  toFun n :=
    let v := Multiplicative.toAdd n
    gX ^ v.1 * gY ^ v.2.1 * gZ ^ v.2.2
  map_one' := by simp
  map_mul' n₁ n₂ := by
    rcases n₁ with ⟨i₁, j₁, k₁⟩
    rcases n₂ with ⟨i₂, j₂, k₂⟩
    change gX ^ (i₁ + i₂) * gY ^ (j₁ + j₂) * gZ ^ (k₁ + k₂) =
      (gX ^ i₁ * gY ^ j₁ * gZ ^ k₁) * (gX ^ i₂ * gY ^ j₂ * gZ ^ k₂)
    have hxy := commute_zpow gX_mul_gY
    have hxz := commute_zpow gX_mul_gZ
    have hyz := commute_zpow gY_mul_gZ
    rw [zpow_add, zpow_add, zpow_add]
    calc
      gX ^ i₁ * gX ^ i₂ * (gY ^ j₁ * gY ^ j₂) * (gZ ^ k₁ * gZ ^ k₂)
        = gX ^ i₁ * (gX ^ i₂ * gY ^ j₁) * gY ^ j₂ * gZ ^ k₁ * gZ ^ k₂ := by simp only [mul_assoc]
      _ = gX ^ i₁ * (gY ^ j₁ * gX ^ i₂) * gY ^ j₂ * gZ ^ k₁ * gZ ^ k₂ := by rw [hxy i₂ j₁]
      _ = gX ^ i₁ * gY ^ j₁ * gX ^ i₂ * (gY ^ j₂ * gZ ^ k₁) * gZ ^ k₂ := by simp only [mul_assoc]
      _ = gX ^ i₁ * gY ^ j₁ * gX ^ i₂ * (gZ ^ k₁ * gY ^ j₂) * gZ ^ k₂ := by rw [hyz j₂ k₁]
      _ = gX ^ i₁ * gY ^ j₁ * (gX ^ i₂ * gZ ^ k₁) * gY ^ j₂ * gZ ^ k₂ := by simp only [mul_assoc]
      _ = gX ^ i₁ * gY ^ j₁ * (gZ ^ k₁ * gX ^ i₂) * gY ^ j₂ * gZ ^ k₂ := by rw [hxz i₂ k₁]
      _ = (gX ^ i₁ * gY ^ j₁ * gZ ^ k₁) * (gX ^ i₂ * gY ^ j₂ * gZ ^ k₂) := by simp only [mul_assoc]

private def flipA : N →* N where
  toFun n := let v := Multiplicative.toAdd n; mkN v.1 (-v.2.1) (-v.2.2)
  map_one' := rfl
  map_mul' n₁ n₂ := by
    rcases n₁ with ⟨i₁, j₁, k₁⟩; rcases n₂ with ⟨i₂, j₂, k₂⟩
    change mkN (i₁ + i₂) (-(j₁ + j₂)) (-(k₁ + k₂)) =
      mkN (i₁ + i₂) (-j₁ + -j₂) (-k₁ + -k₂)
    congr 1; ring; ring

private def flipB : N →* N where
  toFun n := let v := Multiplicative.toAdd n; mkN (-v.1) v.2.1 (-v.2.2)
  map_one' := rfl
  map_mul' n₁ n₂ := by
    rcases n₁ with ⟨i₁, j₁, k₁⟩; rcases n₂ with ⟨i₂, j₂, k₂⟩
    change mkN (-(i₁ + i₂)) (j₁ + j₂) (-(k₁ + k₂)) =
      mkN (-i₁ + -i₂) (j₁ + j₂) (-k₁ + -k₂)
    congr 1; ring; ring

private def flipC : N →* N where
  toFun n := let v := Multiplicative.toAdd n; mkN (-v.1) (-v.2.1) v.2.2
  map_one' := rfl
  map_mul' n₁ n₂ := by
    rcases n₁ with ⟨i₁, j₁, k₁⟩; rcases n₂ with ⟨i₂, j₂, k₂⟩
    change mkN (-(i₁ + i₂)) (-(j₁ + j₂)) (k₁ + k₂) =
      mkN (-i₁ + -i₂) (-j₁ + -j₂) (k₁ + k₂)
    congr 1; ring; ring

private lemma gA_mul_ι (n : N) : gA * ι n = ι (flipA n) * gA := by
  rcases n with ⟨i, j, k⟩
  change gA * (gX ^ i * gY ^ j * gZ ^ k) = gX ^ i * gY ^ (-j) * gZ ^ (-k) * gA
  calc
    gA * (gX ^ i * gY ^ j * gZ ^ k)
      = (gA * gX ^ i) * gY ^ j * gZ ^ k := by simp only [mul_assoc]
    _ = (gX ^ i * gA) * gY ^ j * gZ ^ k := by rw [conj_zpow_eq gA_mul_gX i]
    _ = gX ^ i * (gA * gY ^ j) * gZ ^ k := by simp only [mul_assoc]
    _ = gX ^ i * (gY ^ (-j) * gA) * gZ ^ k := by rw [conj_zpow_inv gA_mul_gY j]
    _ = gX ^ i * gY ^ (-j) * (gA * gZ ^ k) := by simp only [mul_assoc]
    _ = gX ^ i * gY ^ (-j) * (gZ ^ (-k) * gA) := by rw [conj_zpow_inv gA_mul_gZ k]
    _ = gX ^ i * gY ^ (-j) * gZ ^ (-k) * gA := by simp only [mul_assoc]

private lemma gB_mul_ι (n : N) : gB * ι n = ι (flipB n) * gB := by
  rcases n with ⟨i, j, k⟩
  change gB * (gX ^ i * gY ^ j * gZ ^ k) = gX ^ (-i) * gY ^ j * gZ ^ (-k) * gB
  calc
    gB * (gX ^ i * gY ^ j * gZ ^ k)
      = (gB * gX ^ i) * gY ^ j * gZ ^ k := by simp only [mul_assoc]
    _ = (gX ^ (-i) * gB) * gY ^ j * gZ ^ k := by rw [conj_zpow_inv gB_mul_gX i]
    _ = gX ^ (-i) * (gB * gY ^ j) * gZ ^ k := by simp only [mul_assoc]
    _ = gX ^ (-i) * (gY ^ j * gB) * gZ ^ k := by rw [conj_zpow_eq gB_mul_gY j]
    _ = gX ^ (-i) * gY ^ j * (gB * gZ ^ k) := by simp only [mul_assoc]
    _ = gX ^ (-i) * gY ^ j * (gZ ^ (-k) * gB) := by rw [conj_zpow_inv gB_mul_gZ k]
    _ = gX ^ (-i) * gY ^ j * gZ ^ (-k) * gB := by simp only [mul_assoc]

private lemma gAB_mul_ι (n : N) : gAB * ι n = ι (flipC n) * gAB := by
  rcases n with ⟨i, j, k⟩
  have hflip : flipA (flipB (mkN i j k)) = flipC (mkN i j k) := by
    change mkN (-i) (-j) (-(-k)) = mkN (-i) (-j) k
    simp
  calc
    gAB * ι (mkN i j k) = gA * (gB * ι (mkN i j k)) := by simp only [gAB, mul_assoc]
    _ = gA * (ι (flipB (mkN i j k)) * gB) := by rw [gB_mul_ι]
    _ = (gA * ι (flipB (mkN i j k))) * gB := by simp only [mul_assoc]
    _ = (ι (flipA (flipB (mkN i j k))) * gA) * gB := by rw [gA_mul_ι]
    _ = ι (flipC (mkN i j k)) * gAB := by rw [hflip]; simp only [gAB, mul_assoc]

/- ### Group algebra over `ZMod p` -/

section RingAlgebra

variable (p : ℕ) [hp : Fact p.Prime]

private abbrev R (p : ℕ) := MonoidAlgebra (ZMod p) N
private abbrev A (p : ℕ) := MonoidAlgebra (ZMod p) P

private def embed : R p →+* A p := MonoidAlgebra.mapDomainRingHom (ZMod p) ι
private def σA : R p →+* R p := MonoidAlgebra.mapDomainRingHom (ZMod p) flipA
private def σB : R p →+* R p := MonoidAlgebra.mapDomainRingHom (ZMod p) flipB
private def σC : R p →+* R p := MonoidAlgebra.mapDomainRingHom (ZMod p) flipC

private def eA : A p := MonoidAlgebra.single gA 1
private def eB : A p := MonoidAlgebra.single gB 1
private def eAB : A p := MonoidAlgebra.single gAB 1

private def rX : R p := MonoidAlgebra.single (mkN 1 0 0) 1
private def rXi : R p := MonoidAlgebra.single (mkN (-1) 0 0) 1
private def rY : R p := MonoidAlgebra.single (mkN 0 1 0) 1
private def rYi : R p := MonoidAlgebra.single (mkN 0 (-1) 0) 1
private def rZ : R p := MonoidAlgebra.single (mkN 0 0 1) 1
private def rZi : R p := MonoidAlgebra.single (mkN 0 0 (-1)) 1

private lemma rX_mul_rXi : rX p * rXi p = 1 := by
  simp [rX, rXi, MonoidAlgebra.single_mul_single, mkN_mul, mkN_one, MonoidAlgebra.one_def]

private lemma rY_mul_rYi : rY p * rYi p = 1 := by
  simp [rY, rYi, MonoidAlgebra.single_mul_single, mkN_mul, mkN_one, MonoidAlgebra.one_def]

private lemma rZ_mul_rZi : rZ p * rZi p = 1 := by
  simp [rZ, rZi, MonoidAlgebra.single_mul_single, mkN_mul, mkN_one, MonoidAlgebra.one_def]

private lemma embed_single (n : N) (c : ZMod p) :
    embed p (MonoidAlgebra.single n c) = MonoidAlgebra.single (ι n) c := by
  simp [embed]

private lemma σA_single (n : N) (c : ZMod p) :
    σA p (MonoidAlgebra.single n c) = MonoidAlgebra.single (flipA n) c := by
  simp [σA]

private lemma σB_single (n : N) (c : ZMod p) :
    σB p (MonoidAlgebra.single n c) = MonoidAlgebra.single (flipB n) c := by
  simp [σB]

private lemma σC_single (n : N) (c : ZMod p) :
    σC p (MonoidAlgebra.single n c) = MonoidAlgebra.single (flipC n) c := by
  simp [σC]

private lemma eA_mul_embed (f : R p) : eA p * embed p f = embed p (σA p f) * eA p := by
  refine MonoidAlgebra.induction_linear f ?_ ?_ ?_
  · simp
  · intro f₁ f₂ h₁ h₂
    simp only [map_add, mul_add, add_mul, h₁, h₂]
  · intro n c
    rw [embed_single, σA_single, embed_single]
    simp only [eA, MonoidAlgebra.single_mul_single, one_mul, mul_one, gA_mul_ι]

private lemma eB_mul_embed (f : R p) : eB p * embed p f = embed p (σB p f) * eB p := by
  refine MonoidAlgebra.induction_linear f ?_ ?_ ?_
  · simp
  · intro f₁ f₂ h₁ h₂
    simp only [map_add, mul_add, add_mul, h₁, h₂]
  · intro n c
    rw [embed_single, σB_single, embed_single]
    simp only [eB, MonoidAlgebra.single_mul_single, one_mul, mul_one, gB_mul_ι]

private lemma eAB_mul_embed (f : R p) : eAB p * embed p f = embed p (σC p f) * eAB p := by
  refine MonoidAlgebra.induction_linear f ?_ ?_ ?_
  · simp
  · intro f₁ f₂ h₁ h₂
    simp only [map_add, mul_add, add_mul, h₁, h₂]
  · intro n c
    rw [embed_single, σC_single, embed_single]
    simp only [eAB, MonoidAlgebra.single_mul_single, one_mul, mul_one, gAB_mul_ι]

private lemma eA_mul_eA : eA p * eA p = embed p (rX p) := by
  rw [rX, embed_single]
  simp only [eA, MonoidAlgebra.single_mul_single, one_mul, ι, mkN]
  simp [gX]

private lemma eA_mul_eB : eA p * eB p = eAB p := by
  simp [eA, eB, eAB, MonoidAlgebra.single_mul_single, gAB]

private lemma eA_mul_eAB : eA p * eAB p = embed p (rX p) * eB p := by
  rw [rX, embed_single]
  simp only [eA, eB, eAB, MonoidAlgebra.single_mul_single, one_mul, ι, mkN]
  simp [gA_mul_gAB]

private lemma eB_mul_eA : eB p * eA p = embed p (rXi p * rY p * rZi p) * eAB p := by
  have h1 : rXi p * rY p * rZi p = MonoidAlgebra.single (mkN (-1) 1 (-1)) 1 := by
    simp [rXi, rY, rZi, MonoidAlgebra.single_mul_single, mkN_mul]
  rw [h1, embed_single]
  simp only [eA, eB, eAB, MonoidAlgebra.single_mul_single, one_mul, ι, mkN]
  simp [gB_mul_gA]

private lemma eB_mul_eB : eB p * eB p = embed p (rY p) := by
  rw [rY, embed_single]
  simp only [eB, MonoidAlgebra.single_mul_single, one_mul, ι, mkN]
  simp [gY]

private lemma eB_mul_eAB : eB p * eAB p = embed p (rXi p * rZi p) * eA p := by
  have h1 : rXi p * rZi p = MonoidAlgebra.single (mkN (-1) 0 (-1)) 1 := by
    simp [rXi, rZi, MonoidAlgebra.single_mul_single, mkN_mul]
  rw [h1, embed_single]
  simp only [eA, eB, eAB, MonoidAlgebra.single_mul_single, one_mul, ι, mkN]
  simp [gB_mul_gAB]

private lemma eAB_mul_eA : eAB p * eA p = embed p (rYi p * rZ p) * eB p := by
  have h1 : rYi p * rZ p = MonoidAlgebra.single (mkN 0 (-1) 1) 1 := by
    simp [rYi, rZ, MonoidAlgebra.single_mul_single, mkN_mul]
  rw [h1, embed_single]
  simp only [eA, eB, eAB, MonoidAlgebra.single_mul_single, one_mul, ι, mkN]
  simp [gAB_mul_gA]

private lemma eAB_mul_eB : eAB p * eB p = embed p (rYi p) * eA p := by
  rw [rYi, embed_single]
  simp only [eA, eB, eAB, MonoidAlgebra.single_mul_single, one_mul, ι, mkN]
  simp [gAB_mul_gB]

private lemma eAB_mul_eAB : eAB p * eAB p = embed p (rZ p) := by
  rw [rZ, embed_single]
  simp only [eAB, MonoidAlgebra.single_mul_single, one_mul, ι, mkN]
  simp [gAB_mul_gAB]

private def quad (p1 q1 r1 s1 : R p) : A p :=
  embed p p1 + embed p q1 * eA p + embed p r1 * eB p + embed p s1 * eAB p

private lemma quad_one : quad p 1 0 0 0 = 1 := by
  simp [quad]

private lemma quad_mul (p1 q1 r1 s1 p2 q2 r2 s2 : R p) :
    quad p p1 q1 r1 s1 * quad p p2 q2 r2 s2 =
      quad p
        (p1 * p2 + q1 * σA p q2 * rX p + r1 * σB p r2 * rY p + s1 * σC p s2 * rZ p)
        (p1 * q2 + q1 * σA p p2 + r1 * σB p s2 * (rXi p * rZi p) + s1 * σC p r2 * rYi p)
        (p1 * r2 + q1 * σA p s2 * rX p + r1 * σB p p2 + s1 * σC p q2 * (rYi p * rZ p))
        (p1 * s2 + q1 * σA p r2 + r1 * σB p q2 * (rXi p * rY p * rZi p) + s1 * σC p p2) := by
  simp only [quad, add_mul, mul_add]
  have hA1 : ∀ f g : R p, embed p f * eA p * embed p g = embed p (f * σA p g) * eA p := by
    intro f g; rw [mul_assoc, eA_mul_embed, ← mul_assoc, ← map_mul]
  have hA2 : ∀ f g : R p, embed p f * eA p * (embed p g * eA p) = embed p (f * σA p g * rX p) := by
    intro f g
    rw [← mul_assoc, hA1, mul_assoc, eA_mul_eA, ← map_mul]
  have hA3 : ∀ f g : R p, embed p f * eA p * (embed p g * eB p) = embed p (f * σA p g) * eAB p := by
    intro f g
    rw [← mul_assoc, hA1, mul_assoc, eA_mul_eB]
  have hA4 : ∀ f g : R p, embed p f * eA p * (embed p g * eAB p) =
      embed p (f * σA p g * rX p) * eB p := by
    intro f g
    rw [← mul_assoc, hA1, mul_assoc, eA_mul_eAB, ← mul_assoc, ← map_mul]
  have hB1 : ∀ f g : R p, embed p f * eB p * embed p g = embed p (f * σB p g) * eB p := by
    intro f g; rw [mul_assoc, eB_mul_embed, ← mul_assoc, ← map_mul]
  have hB2 : ∀ f g : R p, embed p f * eB p * (embed p g * eA p) =
      embed p (f * σB p g * (rXi p * rY p * rZi p)) * eAB p := by
    intro f g
    rw [← mul_assoc, hB1, mul_assoc, eB_mul_eA, ← mul_assoc, ← map_mul]
  have hB3 : ∀ f g : R p, embed p f * eB p * (embed p g * eB p) = embed p (f * σB p g * rY p) := by
    intro f g
    rw [← mul_assoc, hB1, mul_assoc, eB_mul_eB, ← map_mul]
  have hB4 : ∀ f g : R p, embed p f * eB p * (embed p g * eAB p) =
      embed p (f * σB p g * (rXi p * rZi p)) * eA p := by
    intro f g
    rw [← mul_assoc, hB1, mul_assoc, eB_mul_eAB, ← mul_assoc, ← map_mul]
  have hC1 : ∀ f g : R p, embed p f * eAB p * embed p g = embed p (f * σC p g) * eAB p := by
    intro f g; rw [mul_assoc, eAB_mul_embed, ← mul_assoc, ← map_mul]
  have hC2 : ∀ f g : R p, embed p f * eAB p * (embed p g * eA p) =
      embed p (f * σC p g * (rYi p * rZ p)) * eB p := by
    intro f g
    rw [← mul_assoc, hC1, mul_assoc, eAB_mul_eA, ← mul_assoc, ← map_mul]
  have hC3 : ∀ f g : R p, embed p f * eAB p * (embed p g * eB p) =
      embed p (f * σC p g * rYi p) * eA p := by
    intro f g
    rw [← mul_assoc, hC1, mul_assoc, eAB_mul_eB, ← mul_assoc, ← map_mul]
  have hC4 : ∀ f g : R p, embed p f * eAB p * (embed p g * eAB p) =
      embed p (f * σC p g * rZ p) := by
    intro f g
    rw [← mul_assoc, hC1, mul_assoc, eAB_mul_eAB, ← map_mul]
  simp only [hA1, hA2, hA3, hA4, hB1, hB2, hB3, hB4, hC1, hC2, hC3, hC4,
    ← mul_assoc, ← map_mul, map_add, add_mul]
  abel

/- ### Murray–Passman unit in characteristic `p` -/

private lemma charP_R : CharP (R p) p := by
  have hinj : Function.Injective (algebraMap (ZMod p) (R p)) := by
    intro c₁ c₂ h
    have h1 := congr_arg (fun f : R p => f.coeff (1 : N)) h
    simpa [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.coeff_smul_apply,
      MonoidAlgebra.coeff_one_one] using h1
  refine ⟨fun n => ?_⟩
  rw [← map_natCast (algebraMap (ZMod p) (R p)), ← map_zero (algebraMap (ZMod p) (R p)),
    hinj.eq_iff, CharP.cast_eq_zero_iff (ZMod p) p n]

private def rH : R p := (1 - rZ p) ^ (p - 2)
private def rHa : R p := (1 - rZi p) ^ (p - 2)

private lemma σA_rX : σA p (rX p) = rX p := by simp [σA_single, rX, flipA, mkN]
private lemma σA_rXi : σA p (rXi p) = rXi p := by simp [σA_single, rXi, flipA, mkN]
private lemma σA_rY : σA p (rY p) = rYi p := by simp [σA_single, rY, rYi, flipA, mkN]
private lemma σA_rYi : σA p (rYi p) = rY p := by simp [σA_single, rY, rYi, flipA, mkN]
private lemma σA_rZ : σA p (rZ p) = rZi p := by simp [σA_single, rZ, rZi, flipA, mkN]
private lemma σA_rZi : σA p (rZi p) = rZ p := by simp [σA_single, rZ, rZi, flipA, mkN]

private lemma σB_rX : σB p (rX p) = rXi p := by simp [σB_single, rX, rXi, flipB, mkN]
private lemma σB_rXi : σB p (rXi p) = rX p := by simp [σB_single, rX, rXi, flipB, mkN]
private lemma σB_rY : σB p (rY p) = rY p := by simp [σB_single, rY, flipB, mkN]
private lemma σB_rYi : σB p (rYi p) = rYi p := by simp [σB_single, rYi, flipB, mkN]
private lemma σB_rZ : σB p (rZ p) = rZi p := by simp [σB_single, rZ, rZi, flipB, mkN]
private lemma σB_rZi : σB p (rZi p) = rZ p := by simp [σB_single, rZ, rZi, flipB, mkN]

private lemma σC_rX : σC p (rX p) = rXi p := by simp [σC_single, rX, rXi, flipC, mkN]
private lemma σC_rXi : σC p (rXi p) = rX p := by simp [σC_single, rX, rXi, flipC, mkN]
private lemma σC_rY : σC p (rY p) = rYi p := by simp [σC_single, rY, rYi, flipC, mkN]
private lemma σC_rYi : σC p (rYi p) = rY p := by simp [σC_single, rY, rYi, flipC, mkN]
private lemma σC_rZ : σC p (rZ p) = rZ p := by simp [σC_single, rZ, flipC, mkN]
private lemma σC_rZi : σC p (rZi p) = rZi p := by simp [σC_single, rZi, flipC, mkN]

private lemma σA_rH : σA p (rH p) = rHa p := by
  simp [rH, rHa, map_pow, map_sub, map_one, σA_rZ]

private lemma σA_rHa : σA p (rHa p) = rH p := by
  simp [rH, rHa, map_pow, map_sub, map_one, σA_rZi]

private lemma σB_rH : σB p (rH p) = rHa p := by
  simp [rH, rHa, map_pow, map_sub, map_one, σB_rZ]

private lemma σB_rHa : σB p (rHa p) = rH p := by
  simp [rH, rHa, map_pow, map_sub, map_one, σB_rZi]

private lemma σC_rH : σC p (rH p) = rH p := by
  simp [rH, map_pow, map_sub, map_one, σC_rZ]

private lemma σC_rHa : σC p (rHa p) = rHa p := by
  simp [rHa, map_pow, map_sub, map_one, σC_rZi]

private lemma neg_one_pow_sub_two : (-1 : R p) ^ (p - 2) = -1 := by
  have : CharP (R p) p := charP_R p
  by_cases hp2 : p = 2
  · subst hp2
    have h2 : (2 : R 2) = 0 := CharP.cast_eq_zero (R 2) 2
    have hneg : (-1 : R 2) = 1 := by
      linear_combination -h2
    simp [hneg]
  · have hodd : Odd (p - 2) := by
      have hpodd : Odd p := hp.out.odd_of_ne_two hp2
      rcases hpodd with ⟨k, hk⟩
      have hk1 : 1 ≤ k := by have := hp.out.two_le; omega
      exact ⟨k - 1, by omega⟩
    exact hodd.neg_one_pow

private lemma frobenius_H_Ha_poly :
    (1 - rZ p) * (rZ p - 1) * rH p * rHa p = - (rZ p) ^ 2 * rH p - rHa p := by
  have : CharP (R p) p := charP_R p
  have hp2 : 2 ≤ p := hp.out.two_le
  have hzz : rZ p * rZi p = 1 := rZ_mul_rZi p
  have h1mzi : 1 - rZi p = - rZi p * (1 - rZ p) := by
    calc
      1 - rZi p = rZ p * rZi p - rZi p := by rw [hzz]
      _ = - rZi p * (1 - rZ p) := by ring
  have hHa_rel : rHa p = - (rZi p) ^ (p - 2) * rH p := by
    rw [rHa, h1mzi, mul_pow, neg_mul, neg_pow, neg_one_pow_sub_two]
    change (-1 : R p) * (rZi p) ^ (p - 2) * rH p = _
    ring
  have hfrob : (1 - rZ p) ^ p = 1 - (rZ p) ^ p := by
    simpa [one_pow] using sub_pow_char (1 : R p) (rZ p)
  have hpow2 : (1 - rZ p) ^ 2 * rH p = (1 - rZ p) ^ p := by
    rw [rH, ← pow_add, Nat.add_sub_of_le hp2]
  have hz_cancel : (rZ p) ^ p * (rZi p) ^ (p - 2) = (rZ p) ^ 2 := by
    have h1 : (rZ p) ^ p = (rZ p) ^ 2 * (rZ p) ^ (p - 2) := by
      rw [← pow_add, Nat.add_sub_of_le hp2]
    rw [h1, mul_assoc, ← mul_pow, hzz, one_pow, mul_one]
  calc
    (1 - rZ p) * (rZ p - 1) * rH p * rHa p
      = - ((1 - rZ p) ^ 2 * rH p) * rHa p := by ring
    _ = - (1 - (rZ p) ^ p) * rHa p := by rw [hpow2, hfrob]
    _ = (rZ p) ^ p * rHa p - rHa p := by ring
    _ = (rZ p) ^ p * (- (rZi p) ^ (p - 2) * rH p) - rHa p := by rw [hHa_rel]
    _ = - ((rZ p) ^ p * (rZi p) ^ (p - 2)) * rH p - rHa p := by ring
    _ = - (rZ p) ^ 2 * rH p - rHa p := by rw [hz_cancel]

private def uP : R p := (1 + rX p) * (1 + rY p) * (1 + rZ p) * rH p
private def uQ : R p := ((1 + rX p) * (rXi p + rYi p) + (1 + rYi p) * (1 + rZi p)) * rH p
private def uR : R p := ((1 + rYi p) * (rX p + rY p) + (1 + rX p) * (1 + rZ p)) * rH p
private def uS : R p := rZi p + (4 + rX p + rXi p + rY p + rYi p) * rH p

private def vP : R p := rXi p * σA p (uP p)
private def vQ : R p := - rXi p * uQ p
private def vR : R p := - rYi p * uR p
private def vS : R p := rZi p * σA p (uS p)

private def unitU : A p := quad p (uP p) (uQ p) (uR p) (uS p)
private def unitV : A p := quad p (vP p) (vQ p) (vR p) (vS p)

private lemma cancel_xyz {a b : R p}
    (h : (rX p * rY p * rZ p) ^ 4 * a = (rX p * rY p * rZ p) ^ 4 * b) : a = b := by
  have hinv : (rXi p * rYi p * rZi p) ^ 4 * (rX p * rY p * rZ p) ^ 4 = 1 := by
    rw [← mul_pow]
    have h1 : (rXi p * rYi p * rZi p) * (rX p * rY p * rZ p) =
        (rX p * rXi p) * (rY p * rYi p) * (rZ p * rZi p) := by ring
    rw [h1, rX_mul_rXi, rY_mul_rYi, rZ_mul_rZi]
    ring
  calc
    a = 1 * a := (one_mul a).symm
    _ = ((rXi p * rYi p * rZi p) ^ 4 * (rX p * rY p * rZ p) ^ 4) * a := by rw [hinv]
    _ = (rXi p * rYi p * rZi p) ^ 4 * ((rX p * rY p * rZ p) ^ 4 * a) := by ring
    _ = (rXi p * rYi p * rZi p) ^ 4 * ((rX p * rY p * rZ p) ^ 4 * b) := by rw [h]
    _ = ((rXi p * rYi p * rZi p) ^ 4 * (rX p * rY p * rZ p) ^ 4) * b := by ring
    _ = 1 * b := by rw [hinv]
    _ = b := one_mul b

private lemma clear_uP :
    rX p * rY p * rZ p * uP p =
      rX p * rY p * rZ p * ((1 + rX p) * (1 + rY p) * (1 + rZ p) * rH p) := rfl

private lemma clear_uQ :
    rX p * rY p * rZ p * uQ p =
      ((1 + rX p) * (rY p + rX p) * rZ p + rX p * (rY p + 1) * (rZ p + 1)) * rH p := by
  have hx := rX_mul_rXi p; have hy := rY_mul_rYi p; have hz := rZ_mul_rZi p
  simp only [uQ]
  linear_combination
    (1 + rX p) * rY p * rZ p * rH p * hx +
    ((1 + rX p) * rX p * rZ p + rX p * (rZ p + 1)) * rH p * hy +
    rX p * (1 + rYi p) * rY p * rH p * hz

private lemma clear_uR :
    rX p * rY p * rZ p * uR p =
      rX p * rZ p * ((rY p + 1) * (rX p + rY p) + (1 + rX p) * (1 + rZ p) * rY p) * rH p := by
  have hy := rY_mul_rYi p
  simp only [uR]
  linear_combination rX p * rZ p * (rX p + rY p) * rH p * hy

private lemma clear_uS :
    rX p * rY p * rZ p * uS p =
      rX p * rY p + (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p) * rZ p * rH p := by
  have hx := rX_mul_rXi p; have hy := rY_mul_rYi p; have hz := rZ_mul_rZi p
  simp only [uS]
  linear_combination rX p * rY p * hz + rY p * rZ p * rH p * hx + rX p * rZ p * rH p * hy

private lemma clear_vP :
    rX p * rY p * rZ p * vP p = (1 + rX p) * (rY p + 1) * (rZ p + 1) * rHa p := by
  have hx := rX_mul_rXi p; have hy := rY_mul_rYi p; have hz := rZ_mul_rZi p
  simp only [vP, uP, map_mul, map_add, map_one, σA_rX, σA_rY, σA_rZ, σA_rH]
  linear_combination
    (1 + rX p) * (1 + rYi p) * rY p * (1 + rZi p) * rZ p * rHa p * hx +
    (1 + rX p) * (1 + rZi p) * rZ p * rHa p * hy +
    (1 + rX p) * (rY p + 1) * rHa p * hz

private lemma clear_vQ :
    rX p ^ 2 * rY p * rZ p * vQ p =
      - ((1 + rX p) * (rY p + rX p) * rZ p + rX p * (rY p + 1) * (rZ p + 1)) * rH p := by
  have hx := rX_mul_rXi p
  have hq := clear_uQ p
  simp only [vQ]
  linear_combination - rX p * rY p * rZ p * uQ p * hx - hq

private lemma clear_vR :
    rX p * rY p ^ 2 * rZ p * vR p =
      - rX p * rZ p * ((rY p + 1) * (rX p + rY p) + (1 + rX p) * (1 + rZ p) * rY p) * rH p := by
  have hy := rY_mul_rYi p
  have hr := clear_uR p
  simp only [vR]
  linear_combination - rX p * rY p * rZ p * uR p * hy - hr

private lemma clear_vS :
    rX p * rY p * rZ p * vS p =
      rX p * rY p * rZ p +
        (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p) * rHa p := by
  have hx := rX_mul_rXi p; have hy := rY_mul_rYi p; have hz := rZ_mul_rZi p
  simp only [vS, uS, map_mul, map_add, map_ofNat, σA_rX, σA_rXi, σA_rY, σA_rYi, σA_rZi, σA_rH]
  linear_combination
    rX p * rY p * rZ p * hz +
    rX p * rY p * (4 + rX p + rXi p + rYi p + rY p) * rHa p * hz +
    rY p * rHa p * hx + rX p * rHa p * hy

private lemma clear_σA_uP :
    rX p * rY p * rZ p * σA p (uP p) = rX p * (1 + rX p) * (rY p + 1) * (rZ p + 1) * rHa p := by
  have hy := rY_mul_rYi p; have hz := rZ_mul_rZi p
  simp only [uP, map_mul, map_add, map_one, σA_rX, σA_rY, σA_rZ, σA_rH]
  linear_combination
    rX p * (1 + rX p) * (1 + rZi p) * rZ p * rHa p * hy +
    rX p * (1 + rX p) * (rY p + 1) * rHa p * hz

private lemma clear_σA_uQ :
    rX p * rY p * rZ p * σA p (uQ p) =
      rY p * rZ p * ((1 + rX p) * (1 + rX p * rY p) + rX p * (1 + rY p) * (1 + rZ p)) * rHa p := by
  have hx := rX_mul_rXi p
  simp only [uQ, map_mul, map_add, map_one, σA_rX, σA_rXi, σA_rYi, σA_rZi, σA_rH]
  linear_combination rY p * rZ p * (1 + rX p) * rHa p * hx

private lemma clear_σA_uR :
    rX p * rY p * rZ p * σA p (uR p) =
      rX p * ((1 + rY p) * (rX p * rY p + 1) * rZ p + (1 + rX p) * (rZ p + 1) * rY p) * rHa p := by
  have hy := rY_mul_rYi p; have hz := rZ_mul_rZi p
  simp only [uR, map_mul, map_add, map_one, σA_rX, σA_rY, σA_rYi, σA_rZ, σA_rH]
  linear_combination
    rX p * rZ p * (1 + rY p) * rHa p * hy +
    rX p * rY p * (1 + rX p) * rHa p * hz

private lemma clear_σA_uS :
    rX p * rY p * rZ p * σA p (uS p) =
      rX p * rY p * rZ p ^ 2 +
        (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p) * rZ p * rHa p := by
  have hx := rX_mul_rXi p; have hy := rY_mul_rYi p
  simp only [uS, map_mul, map_add, map_ofNat, σA_rX, σA_rXi, σA_rY, σA_rYi, σA_rZi, σA_rH]
  linear_combination rY p * rZ p * rHa p * hx + rX p * rZ p * rHa p * hy

private lemma clear_σB_uP :
    rX p * rY p * rZ p * σB p (uP p) = (rX p + 1) * (1 + rY p) * (rZ p + 1) * rY p * rHa p := by
  have hx := rX_mul_rXi p; have hz := rZ_mul_rZi p
  simp only [uP, map_mul, map_add, map_one, σB_rX, σB_rY, σB_rZ, σB_rH]
  linear_combination
    rY p * (1 + rY p) * (1 + rZi p) * rZ p * rHa p * hx +
    (rX p + 1) * rY p * (1 + rY p) * rHa p * hz

private lemma clear_σB_uQ :
    rX p * rY p * rZ p * σB p (uQ p) =
      rZ p * ((rX p + 1) * (rX p * rY p + 1) + rX p * (rY p + 1) * (1 + rZ p)) * rHa p := by
  have hx := rX_mul_rXi p; have hy := rY_mul_rYi p
  simp only [uQ, map_mul, map_add, map_one, σB_rX, σB_rXi, σB_rYi, σB_rZi, σB_rH]
  linear_combination
    rZ p * (rX p + rYi p) * rY p * rHa p * hx +
    rZ p * (rX p + 1) * rHa p * hy +
    rX p * rZ p * (1 + rZ p) * rHa p * hy

private lemma clear_σB_uR :
    rX p * rY p * rZ p * σB p (uR p) =
      ((rY p + 1) * (1 + rX p * rY p) * rZ p + (rX p + 1) * (rZ p + 1) * rY p) * rHa p := by
  have hx := rX_mul_rXi p; have hy := rY_mul_rYi p; have hz := rZ_mul_rZi p
  simp only [uR, map_mul, map_add, map_one, σB_rX, σB_rY, σB_rYi, σB_rZ, σB_rH]
  linear_combination
    (1 + rYi p) * rY p * rZ p * rHa p * hx +
    (1 + rX p * rY p) * rZ p * rHa p * hy +
    rY p * (1 + rZi p) * rZ p * rHa p * hx +
    rY p * (rX p + 1) * rHa p * hz

private lemma clear_σB_uS :
    rX p * rY p * rZ p * σB p (uS p) =
      rX p * rY p * rZ p ^ 2 +
        (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p) * rZ p * rHa p := by
  have hx := rX_mul_rXi p; have hy := rY_mul_rYi p
  simp only [uS, map_mul, map_add, map_ofNat, σB_rX, σB_rXi, σB_rY, σB_rYi, σB_rZi, σB_rH]
  linear_combination rY p * rZ p * rHa p * hx + rX p * rZ p * rHa p * hy

private lemma clear_σC_uP :
    rX p * rY p * rZ p * σC p (uP p) = (rX p + 1) * (rY p + 1) * (1 + rZ p) * rZ p * rH p := by
  have hx := rX_mul_rXi p; have hy := rY_mul_rYi p
  simp only [uP, map_mul, map_add, map_one, σC_rX, σC_rY, σC_rZ, σC_rH]
  linear_combination
    (1 + rYi p) * rY p * (1 + rZ p) * rZ p * rH p * hx +
    (rX p + 1) * (1 + rZ p) * rZ p * rH p * hy

private lemma clear_σC_uQ :
    rX p * rY p * rZ p * σC p (uQ p) =
      rY p * ((rX p + 1) * (rX p + rY p) * rZ p + rX p * (1 + rY p) * (rZ p + 1)) * rH p := by
  have hx := rX_mul_rXi p; have hz := rZ_mul_rZi p
  simp only [uQ, map_mul, map_add, map_one, σC_rX, σC_rXi, σC_rYi, σC_rZi, σC_rH]
  linear_combination
    rY p * (rX p + rY p) * rZ p * rH p * hx +
    rX p * rY p * (1 + rY p) * rH p * hz

private lemma clear_σC_uR :
    rX p * rY p * rZ p * σC p (uR p) =
      rZ p * ((1 + rY p) * (rY p + rX p) + (rX p + 1) * (1 + rZ p) * rY p) * rH p := by
  have hx := rX_mul_rXi p; have hy := rY_mul_rYi p
  simp only [uR, map_mul, map_add, map_one, σC_rX, σC_rY, σC_rYi, σC_rZ, σC_rH]
  linear_combination
    (1 + rY p) * rY p * rZ p * rH p * hx +
    (1 + rY p) * rX p * rZ p * rH p * hy +
    rY p * (1 + rZ p) * rZ p * rH p * hx

private lemma clear_σC_uS :
    rX p * rY p * rZ p * σC p (uS p) =
      rX p * rY p +
        (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p) * rZ p * rH p := by
  have hx := rX_mul_rXi p; have hy := rY_mul_rYi p; have hz := rZ_mul_rZi p
  simp only [uS, map_mul, map_add, map_ofNat, σC_rX, σC_rXi, σC_rY, σC_rYi, σC_rZi, σC_rH]
  linear_combination rX p * rY p * hz + rY p * rZ p * rH p * hx + rX p * rZ p * rH p * hy

private lemma clear_σA_vP :
    rX p ^ 2 * rY p * rZ p * σA p (vP p) =
      rX p * rY p * rZ p * ((1 + rX p) * (1 + rY p) * (1 + rZ p) * rH p) := by
  have hx := rX_mul_rXi p
  have h1 : σA p (vP p) = rXi p * uP p := by
    simp only [vP, uP, map_mul, map_add, map_one, σA_rX, σA_rXi, σA_rY, σA_rYi, σA_rZ, σA_rZi,
      σA_rH, σA_rHa]
  rw [h1, uP]
  linear_combination rX p * rY p * rZ p * ((1 + rX p) * (1 + rY p) * (1 + rZ p) * rH p) * hx

private lemma clear_σA_vQ :
    rX p ^ 2 * rY p * rZ p * σA p (vQ p) =
      - rY p * rZ p * ((1 + rX p) * (1 + rX p * rY p) + rX p * (1 + rY p) * (1 + rZ p)) * rHa p := by
  have hx := rX_mul_rXi p
  have hq := clear_σA_uQ p
  simp only [vQ, map_mul, map_neg, σA_rXi]
  linear_combination - rX p * rY p * rZ p * σA p (uQ p) * hx - hq

private lemma clear_σA_vR :
    rX p * rY p * rZ p * σA p (vR p) =
      - rX p * rY p * ((1 + rY p) * (rX p * rY p + 1) * rZ p + (1 + rX p) * (rZ p + 1) * rY p) * rHa p := by
  have hr := clear_σA_uR p
  simp only [vR, map_mul, map_neg, σA_rYi]
  linear_combination - rY p * hr

private lemma clear_σA_vS :
    rX p * rY p * rZ p * σA p (vS p) =
      rZ p * (rX p * rY p +
        (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p) * rZ p * rH p) := by
  have hs := clear_uS p
  have h1 : σA p (vS p) = rZ p * uS p := by
    simp only [vS, uS, map_mul, map_add, map_ofNat, σA_rX, σA_rXi, σA_rY, σA_rYi, σA_rZ, σA_rZi,
      σA_rH, σA_rHa]
  rw [h1]
  linear_combination rZ p * hs

private lemma clear_σB_vP :
    rX p * rY p * rZ p * σB p (vP p) =
      rX p * (rX p + 1) * (rY p + 1) * (1 + rZ p) * rZ p * rH p := by
  have hx := rX_mul_rXi p; have hy := rY_mul_rYi p
  simp only [vP, uP, map_mul, map_add, map_one, σA_rX, σA_rY, σA_rZ, σA_rH,
    σB_rX, σB_rXi, σB_rYi, σB_rZi, σB_rHa]
  linear_combination
    rX p * (1 + rYi p) * rY p * (1 + rZ p) * rZ p * rH p * hx +
    rX p * (rX p + 1) * (1 + rZ p) * rZ p * rH p * hy

private lemma clear_σB_vQ :
    rX p * rY p * rZ p * σB p (vQ p) =
      - rX p * rZ p * ((rX p + 1) * (rX p * rY p + 1) + rX p * (rY p + 1) * (1 + rZ p)) * rHa p := by
  have hq := clear_σB_uQ p
  simp only [vQ, map_mul, map_neg, σB_rXi]
  linear_combination - rX p * hq

private lemma clear_σB_vR :
    rX p * rY p ^ 2 * rZ p * σB p (vR p) =
      - ((rY p + 1) * (1 + rX p * rY p) * rZ p + (rX p + 1) * (rZ p + 1) * rY p) * rHa p := by
  have hy := rY_mul_rYi p
  have hr := clear_σB_uR p
  simp only [vR, map_mul, map_neg, σB_rYi]
  linear_combination - rX p * rY p * rZ p * σB p (uR p) * hy - hr

private lemma clear_σB_vS :
    rX p * rY p * rZ p * σB p (vS p) =
      rZ p * (rX p * rY p +
        (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p) * rZ p * rH p) := by
  have hx := rX_mul_rXi p; have hy := rY_mul_rYi p; have hz := rZ_mul_rZi p
  simp only [vS, uS, map_mul, map_add, map_ofNat, σA_rX, σA_rXi, σA_rY, σA_rYi, σA_rZi, σA_rH,
    σB_rX, σB_rXi, σB_rY, σB_rYi, σB_rZ, σB_rZi, σB_rHa]
  linear_combination
    rX p * rY p * rZ p * hz + rY p * rZ p ^ 2 * rH p * hx + rX p * rZ p ^ 2 * rH p * hy

private lemma clear_σC_vP :
    rX p * rY p * rZ p * σC p (vP p) =
      rX p * (rX p + 1) * (1 + rY p) * (rZ p + 1) * rY p * rHa p := by
  have hx := rX_mul_rXi p; have hz := rZ_mul_rZi p
  simp only [vP, uP, map_mul, map_add, map_one, σA_rX, σA_rY, σA_rZ, σA_rH,
    σC_rX, σC_rXi, σC_rYi, σC_rZi, σC_rHa]
  linear_combination
    rX p * rY p * (1 + rY p) * (1 + rZi p) * rZ p * rHa p * hx +
    rX p * (rX p + 1) * rY p * (1 + rY p) * rHa p * hz

private lemma clear_σC_vQ :
    rX p * rY p * rZ p * σC p (vQ p) =
      - rX p * rY p * ((rX p + 1) * (rX p + rY p) * rZ p + rX p * (1 + rY p) * (rZ p + 1)) * rH p := by
  have hq := clear_σC_uQ p
  simp only [vQ, map_mul, map_neg, σC_rXi]
  linear_combination - rX p * hq

private lemma clear_σC_vR :
    rX p * rY p * rZ p * σC p (vR p) =
      - rY p * rZ p * ((1 + rY p) * (rY p + rX p) + (rX p + 1) * (1 + rZ p) * rY p) * rH p := by
  have hr := clear_σC_uR p
  simp only [vR, map_mul, map_neg, σC_rYi]
  linear_combination - rY p * hr

private lemma clear_σC_vS :
    rX p * rY p * rZ p * σC p (vS p) =
      rX p * rY p * rZ p +
        (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p) * rHa p := by
  have hx := rX_mul_rXi p; have hy := rY_mul_rYi p; have hz := rZ_mul_rZi p
  simp only [vS, uS, map_mul, map_add, map_ofNat, σA_rX, σA_rXi, σA_rY, σA_rYi, σA_rZi, σA_rH,
    σC_rX, σC_rXi, σC_rY, σC_rYi, σC_rZ, σC_rZi, σC_rHa]
  linear_combination
    rX p * rY p * rZ p * hz +
    rX p * rY p * (4 + rXi p + rX p + rY p + rYi p) * rHa p * hz +
    rY p * rHa p * hx + rX p * rHa p * hy

private lemma unitU_mul_unitV : unitU p * unitV p = 1 := by
  rw [unitU, unitV, quad_mul, ← quad_one p]
  have hx := rX_mul_rXi p; have hy := rY_mul_rYi p; have hz := rZ_mul_rZi p
  have hfh := frobenius_H_Ha_poly p
  have huP := clear_uP p; have huQ := clear_uQ p; have huR := clear_uR p; have huS := clear_uS p
  have hvP := clear_vP p; have hvQ := clear_vQ p; have hvR := clear_vR p; have hvS := clear_vS p
  have hAvP := clear_σA_vP p; have hAvQ := clear_σA_vQ p
  have hAvR := clear_σA_vR p; have hAvS := clear_σA_vS p
  have hBvP := clear_σB_vP p; have hBvQ := clear_σB_vQ p
  have hBvR := clear_σB_vR p; have hBvS := clear_σB_vS p
  have hCvP := clear_σC_vP p; have hCvQ := clear_σC_vQ p
  have hCvR := clear_σC_vR p; have hCvS := clear_σC_vS p
  congr 1
  · apply cancel_xyz p
    linear_combination
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) * (rX p * rY p * rZ p * uP p) * hvP +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) * ((1 + rX p) * (rY p + 1) * (rZ p + 1) * rHa p) * huP +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) * (rX p * rY p * rZ p * uQ p) * hAvQ +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) *
        (- rY p * rZ p * ((1 + rX p) * (1 + rX p * rY p) + rX p * (1 + rY p) * (1 + rZ p)) * rHa p) * huQ +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) * (rX p * rY p * rZ p * uR p) * hBvR +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) *
        (- ((rY p + 1) * (1 + rX p * rY p) * rZ p + (rX p + 1) * (rZ p + 1) * rY p) * rHa p) * huR +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 3) * (rX p * rY p * rZ p * uS p) * hCvS +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 3) *
        (rX p * rY p * rZ p + (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p) * rHa p) * huS +
      (rX p ^ 3 * rY p ^ 3 * rZ p ^ 3 * (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p)) * hfh
  · apply cancel_xyz p
    linear_combination
      (rX p * rY p ^ 2 * rZ p ^ 2) * (rX p * rY p * rZ p * uP p) * hvQ +
      (rX p * rY p ^ 2 * rZ p ^ 2) *
        (- ((1 + rX p) * (rY p + rX p) * rZ p + rX p * (rY p + 1) * (rZ p + 1)) * rH p) * huP +
      (rX p * rY p ^ 2 * rZ p ^ 2) * (rX p * rY p * rZ p * uQ p) * hAvP +
      (rX p * rY p ^ 2 * rZ p ^ 2) *
        (rX p * rY p * rZ p * ((1 + rX p) * (1 + rY p) * (1 + rZ p) * rH p)) * huQ +
      (rX p ^ 3 * rY p ^ 4 * rZ p ^ 4 * uR p * σB p (vS p) * rZi p) * hx +
      (rX p ^ 3 * rY p ^ 4 * rZ p ^ 3 * uR p * σB p (vS p)) * hz +
      (rX p * rY p ^ 2 * rZ p) * (rX p * rY p * rZ p * uR p) * hBvS +
      (rX p * rY p ^ 2 * rZ p) *
        (rZ p * (rX p * rY p + (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p) * rZ p * rH p)) * huR +
      (rX p ^ 4 * rY p ^ 3 * rZ p ^ 4 * uS p * σC p (vR p)) * hy +
      (rX p ^ 2 * rY p * rZ p ^ 2) * (rX p * rY p * rZ p * uS p) * hCvR +
      (rX p ^ 2 * rY p * rZ p ^ 2) *
        (- rY p * rZ p * ((1 + rY p) * (rY p + rX p) + (rX p + 1) * (1 + rZ p) * rY p) * rH p) * huS
  · apply cancel_xyz p
    linear_combination
      (rX p ^ 2 * rY p * rZ p ^ 2) * (rX p * rY p * rZ p * uP p) * hvR +
      (rX p ^ 2 * rY p * rZ p ^ 2) *
        (- rX p * rZ p * ((rY p + 1) * (rX p + rY p) + (1 + rX p) * (1 + rZ p) * rY p) * rH p) * huP +
      (rX p ^ 3 * rY p ^ 2 * rZ p ^ 2) * (rX p * rY p * rZ p * uQ p) * hAvS +
      (rX p ^ 3 * rY p ^ 2 * rZ p ^ 2) *
        (rZ p * (rX p * rY p + (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p) * rZ p * rH p)) * huQ +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) * (rX p * rY p * rZ p * uR p) * hBvP +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) *
        (rX p * (rX p + 1) * (rY p + 1) * (1 + rZ p) * rZ p * rH p) * huR +
      (rX p ^ 4 * rY p ^ 3 * rZ p ^ 5 * uS p * σC p (vQ p)) * hy +
      (rX p ^ 2 * rY p * rZ p ^ 3) * (rX p * rY p * rZ p * uS p) * hCvQ +
      (rX p ^ 2 * rY p * rZ p ^ 3) *
        (- rX p * rY p * ((rX p + 1) * (rX p + rY p) * rZ p + rX p * (1 + rY p) * (rZ p + 1)) * rH p) * huS
  · apply cancel_xyz p
    linear_combination
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) * (rX p * rY p * rZ p * uP p) * hvS +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) *
        (rX p * rY p * rZ p + (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p) * rHa p) * huP +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) * (rX p * rY p * rZ p * uQ p) * hAvR +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) *
        (- rX p * rY p * ((1 + rY p) * (rX p * rY p + 1) * rZ p + (1 + rX p) * (rZ p + 1) * rY p) * rHa p) * huQ +
      (rX p ^ 3 * rY p ^ 5 * rZ p ^ 4 * uR p * σB p (vQ p) * rZi p) * hx +
      (rX p ^ 3 * rY p ^ 5 * rZ p ^ 3 * uR p * σB p (vQ p)) * hz +
      (rX p * rY p ^ 3 * rZ p) * (rX p * rY p * rZ p * uR p) * hBvQ +
      (rX p * rY p ^ 3 * rZ p) *
        (- rX p * rZ p * ((rX p + 1) * (rX p * rY p + 1) + rX p * (rY p + 1) * (1 + rZ p)) * rHa p) * huR +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) * (rX p * rY p * rZ p * uS p) * hCvP +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) *
        (rX p * (rX p + 1) * (1 + rY p) * (rZ p + 1) * rY p * rHa p) * huS +
      (rX p ^ 4 * rY p ^ 4 * rZ p ^ 2 * (1 + rX p) * (1 + rY p) * (rZ p + 1)) * hfh

private lemma unitV_mul_unitU : unitV p * unitU p = 1 := by
  rw [unitV, unitU, quad_mul, ← quad_one p]
  have hx := rX_mul_rXi p; have hy := rY_mul_rYi p; have hz := rZ_mul_rZi p
  have hfh := frobenius_H_Ha_poly p
  have huP := clear_uP p; have huQ := clear_uQ p; have huR := clear_uR p; have huS := clear_uS p
  have hvP := clear_vP p; have hvQ := clear_vQ p; have hvR := clear_vR p; have hvS := clear_vS p
  have hAuP := clear_σA_uP p; have hAuQ := clear_σA_uQ p
  have hAuR := clear_σA_uR p; have hAuS := clear_σA_uS p
  have hBuP := clear_σB_uP p; have hBuQ := clear_σB_uQ p
  have hBuR := clear_σB_uR p; have hBuS := clear_σB_uS p
  have hCuP := clear_σC_uP p; have hCuQ := clear_σC_uQ p
  have hCuR := clear_σC_uR p; have hCuS := clear_σC_uS p
  congr 1
  · apply cancel_xyz p
    linear_combination
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) * (rX p * rY p * rZ p * vP p) * huP +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) *
        (rX p * rY p * rZ p * ((1 + rX p) * (1 + rY p) * (1 + rZ p) * rH p)) * hvP +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) * (rX p ^ 2 * rY p * rZ p * vQ p) * hAuQ +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) *
        (rY p * rZ p * ((1 + rX p) * (1 + rX p * rY p) + rX p * (1 + rY p) * (1 + rZ p)) * rHa p) * hvQ +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) * (rX p * rY p ^ 2 * rZ p * vR p) * hBuR +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) *
        (((rY p + 1) * (1 + rX p * rY p) * rZ p + (rX p + 1) * (rZ p + 1) * rY p) * rHa p) * hvR +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 3) * (rX p * rY p * rZ p * vS p) * hCuS +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 3) *
        (rX p * rY p + (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p) * rZ p * rH p) * hvS +
      (rX p ^ 3 * rY p ^ 3 * rZ p ^ 3 * (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p)) * hfh
  · apply cancel_xyz p
    linear_combination
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) * (rX p * rY p * rZ p * vP p) * huQ +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) *
        (((1 + rX p) * (rY p + rX p) * rZ p + rX p * (rY p + 1) * (rZ p + 1)) * rH p) * hvP +
      (rX p * rY p ^ 2 * rZ p ^ 2) * (rX p ^ 2 * rY p * rZ p * vQ p) * hAuP +
      (rX p * rY p ^ 2 * rZ p ^ 2) *
        (rX p * (1 + rX p) * (rY p + 1) * (rZ p + 1) * rHa p) * hvQ +
      (rX p ^ 3 * rY p ^ 4 * rZ p ^ 4 * vR p * σB p (uS p) * rZi p) * hx +
      (rX p ^ 3 * rY p ^ 4 * rZ p ^ 3 * vR p * σB p (uS p)) * hz +
      (rX p * rY p * rZ p) * (rX p * rY p ^ 2 * rZ p * vR p) * hBuS +
      (rX p * rY p * rZ p) *
        (rX p * rY p * rZ p ^ 2 + (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p) * rZ p * rHa p) * hvR +
      (rX p ^ 4 * rY p ^ 3 * rZ p ^ 4 * vS p * σC p (uR p)) * hy +
      (rX p ^ 2 * rY p * rZ p ^ 2) * (rX p * rY p * rZ p * vS p) * hCuR +
      (rX p ^ 2 * rY p * rZ p ^ 2) *
        (rZ p * ((1 + rY p) * (rY p + rX p) + (rX p + 1) * (1 + rZ p) * rY p) * rH p) * hvS
  · apply cancel_xyz p
    linear_combination
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) * (rX p * rY p * rZ p * vP p) * huR +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) *
        (rX p * rZ p * ((rY p + 1) * (rX p + rY p) + (1 + rX p) * (1 + rZ p) * rY p) * rH p) * hvP +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) * (rX p ^ 2 * rY p * rZ p * vQ p) * hAuS +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) *
        (rX p * rY p * rZ p ^ 2 + (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p) * rZ p * rHa p) * hvQ +
      (rX p ^ 2 * rY p * rZ p ^ 2) * (rX p * rY p ^ 2 * rZ p * vR p) * hBuP +
      (rX p ^ 2 * rY p * rZ p ^ 2) *
        ((rX p + 1) * (1 + rY p) * (rZ p + 1) * rY p * rHa p) * hvR +
      (rX p ^ 4 * rY p ^ 3 * rZ p ^ 5 * vS p * σC p (uQ p)) * hy +
      (rX p ^ 2 * rY p * rZ p ^ 3) * (rX p * rY p * rZ p * vS p) * hCuQ +
      (rX p ^ 2 * rY p * rZ p ^ 3) *
        (rY p * ((rX p + 1) * (rX p + rY p) * rZ p + rX p * (1 + rY p) * (rZ p + 1)) * rH p) * hvS
  · apply cancel_xyz p
    linear_combination
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) * (rX p * rY p * rZ p * vP p) * huS +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) *
        (rX p * rY p + (4 * rX p * rY p + rX p ^ 2 * rY p + rY p + rX p * rY p ^ 2 + rX p) * rZ p * rH p) * hvP +
      (rX p * rY p ^ 2 * rZ p ^ 2) * (rX p ^ 2 * rY p * rZ p * vQ p) * hAuR +
      (rX p * rY p ^ 2 * rZ p ^ 2) *
        (rX p * ((1 + rY p) * (rX p * rY p + 1) * rZ p + (1 + rX p) * (rZ p + 1) * rY p) * rHa p) * hvQ +
      (rX p ^ 3 * rY p ^ 5 * rZ p ^ 4 * vR p * σB p (uQ p) * rZi p) * hx +
      (rX p ^ 3 * rY p ^ 5 * rZ p ^ 3 * vR p * σB p (uQ p)) * hz +
      (rX p * rY p ^ 2 * rZ p) * (rX p * rY p ^ 2 * rZ p * vR p) * hBuQ +
      (rX p * rY p ^ 2 * rZ p) *
        (rZ p * ((rX p + 1) * (rX p * rY p + 1) + rX p * (rY p + 1) * (1 + rZ p)) * rHa p) * hvR +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) * (rX p * rY p * rZ p * vS p) * hCuP +
      (rX p ^ 2 * rY p ^ 2 * rZ p ^ 2) *
        ((rX p + 1) * (rY p + 1) * (1 + rZ p) * rZ p * rH p) * hvS +
      (rX p ^ 3 * rY p ^ 3 * rZ p ^ 2 * (rX p + 1) * (rY p + 1) * (rZ p + 1)) * hfh

/- ### Non-triviality via 4×4 integer matrix representation -/

private def mA_mat : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 1; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]

private def mAi_mat : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, -1; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]

private def mB_mat : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-1, 0, 0, 0; 0, 1, 0, 1; 0, 0, -1, 1; 0, 0, 0, 1]

private def mBi_mat : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-1, 0, 0, 0; 0, 1, 0, -1; 0, 0, -1, 1; 0, 0, 0, 1]

private def mA : (Matrix (Fin 4) (Fin 4) ℤ)ˣ :=
  ⟨mA_mat, mAi_mat, by decide, by decide⟩

private def mB : (Matrix (Fin 4) (Fin 4) ℤ)ˣ :=
  ⟨mB_mat, mBi_mat, by decide, by decide⟩

private def φ : P →* (Matrix (Fin 4) (Fin 4) ℤ)ˣ :=
  PresentedGroup.toGroup (f := fun i : Fin 2 => if i = 0 then mA else mB) (by
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      apply Units.ext
      decide
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      apply Units.ext
      decide)

private lemma φ_gA : φ gA = mA := by
  simp [φ, gA, PresentedGroup.toGroup.of]

private lemma φ_gB : φ gB = mB := by
  simp [φ, gB, PresentedGroup.toGroup.of]

private def transMat (i j k : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 2 * i; 0, 1, 0, 2 * j; 0, 0, 1, -2 * k; 0, 0, 0, 1]

private lemma transMat_mul (i₁ j₁ k₁ i₂ j₂ k₂ : ℤ) :
    transMat i₁ j₁ k₁ * transMat i₂ j₂ k₂ = transMat (i₁ + i₂) (j₁ + j₂) (k₁ + k₂) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [transMat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private lemma transMat_zero : transMat 0 0 0 = 1 := by decide

private def transUnit (i j k : ℤ) : (Matrix (Fin 4) (Fin 4) ℤ)ˣ :=
  ⟨transMat i j k, transMat (-i) (-j) (-k),
    by rw [transMat_mul]; simp [transMat_zero],
    by rw [transMat_mul]; simp [transMat_zero]⟩

private def transHom : N →* (Matrix (Fin 4) (Fin 4) ℤ)ˣ where
  toFun n := let v := Multiplicative.toAdd n; transUnit v.1 v.2.1 v.2.2
  map_one' := Units.ext transMat_zero
  map_mul' n₁ n₂ := by
    rcases n₁ with ⟨i₁, j₁, k₁⟩; rcases n₂ with ⟨i₂, j₂, k₂⟩
    exact Units.ext (transMat_mul i₁ j₁ k₁ i₂ j₂ k₂).symm

private lemma φ_gX : φ gX = transUnit 1 0 0 := by
  rw [gX, map_mul, φ_gA]
  apply Units.ext
  decide

private lemma φ_gY : φ gY = transUnit 0 1 0 := by
  rw [gY, map_mul, φ_gB]
  apply Units.ext
  decide

private lemma φ_gZ : φ gZ = transUnit 0 0 1 := by
  rw [gZ, gAB, map_mul, map_mul, φ_gA, φ_gB]
  apply Units.ext
  decide

private lemma φ_ι (n : N) : φ (ι n) = transHom n := by
  rcases n with ⟨i, j, k⟩
  have hsplit : mkN i j k = mkN 1 0 0 ^ i * mkN 0 1 0 ^ j * mkN 0 0 1 ^ k := by
    change Multiplicative.ofAdd (i, j, k) =
      Multiplicative.ofAdd (i • (1, 0, 0) + j • (0, 1, 0) + k • (0, 0, 1))
    simp
  have h1 : φ (ι (mkN 1 0 0)) = transHom (mkN 1 0 0) := by
    change φ (gX ^ (1 : ℤ) * gY ^ (0 : ℤ) * gZ ^ (0 : ℤ)) = transUnit 1 0 0
    simp [φ_gX]
  have h2 : φ (ι (mkN 0 1 0)) = transHom (mkN 0 1 0) := by
    change φ (gX ^ (0 : ℤ) * gY ^ (1 : ℤ) * gZ ^ (0 : ℤ)) = transUnit 0 1 0
    simp [φ_gY]
  have h3 : φ (ι (mkN 0 0 1)) = transHom (mkN 0 0 1) := by
    change φ (gX ^ (0 : ℤ) * gY ^ (0 : ℤ) * gZ ^ (1 : ℤ)) = transUnit 0 0 1
    simp [φ_gZ]
  change φ (ι (mkN i j k)) = transHom (mkN i j k)
  rw [hsplit]
  simp only [map_mul, map_zpow, h1, h2, h3]

private lemma φ_ι_injective : Function.Injective (fun n : N => φ (ι n)) := by
  intro n₁ n₂ h
  dsimp only at h
  rw [φ_ι, φ_ι] at h
  rcases n₁ with ⟨i₁, j₁, k₁⟩; rcases n₂ with ⟨i₂, j₂, k₂⟩
  have hm : transMat i₁ j₁ k₁ = transMat i₂ j₂ k₂ := congr_arg Units.val h
  have h0 : (transMat i₁ j₁ k₁) 0 3 = (transMat i₂ j₂ k₂) 0 3 := by rw [hm]
  have h1 : (transMat i₁ j₁ k₁) 1 3 = (transMat i₂ j₂ k₂) 1 3 := by rw [hm]
  have h2 : (transMat i₁ j₁ k₁) 2 3 = (transMat i₂ j₂ k₂) 2 3 := by rw [hm]
  change 2 * i₁ = 2 * i₂ at h0
  change 2 * j₁ = 2 * j₂ at h1
  change -2 * k₁ = -2 * k₂ at h2
  have hi : i₁ = i₂ := by omega
  have hj : j₁ = j₂ := by omega
  have hk : k₁ = k₂ := by omega
  subst hi; subst hj; subst hk
  rfl

private lemma diag_φ_ι (n : N) :
    ((φ (ι n) : Matrix (Fin 4) (Fin 4) ℤ) 0 0, (φ (ι n) : Matrix (Fin 4) (Fin 4) ℤ) 1 1) = (1, 1) := by
  rw [φ_ι]
  rcases n with ⟨i, j, k⟩
  change ((transMat i j k) 0 0, (transMat i j k) 1 1) = (1, 1)
  simp [transMat]

private lemma diag_φ_ι_gA (n : N) :
    ((φ (ι n * gA) : Matrix (Fin 4) (Fin 4) ℤ) 0 0,
      (φ (ι n * gA) : Matrix (Fin 4) (Fin 4) ℤ) 1 1) = (1, -1) := by
  rw [map_mul, φ_ι, φ_gA]
  rcases n with ⟨i, j, k⟩
  change ((transMat i j k * mA_mat) 0 0, (transMat i j k * mA_mat) 1 1) = (1, -1)
  simp [transMat, mA_mat, Matrix.mul_apply, Fin.sum_univ_four]

private lemma diag_φ_ι_gB (n : N) :
    ((φ (ι n * gB) : Matrix (Fin 4) (Fin 4) ℤ) 0 0,
      (φ (ι n * gB) : Matrix (Fin 4) (Fin 4) ℤ) 1 1) = (-1, 1) := by
  rw [map_mul, φ_ι, φ_gB]
  rcases n with ⟨i, j, k⟩
  change ((transMat i j k * mB_mat) 0 0, (transMat i j k * mB_mat) 1 1) = (-1, 1)
  simp [transMat, mB_mat, Matrix.mul_apply, Fin.sum_univ_four]

private lemma diag_φ_ι_gAB (n : N) :
    ((φ (ι n * gAB) : Matrix (Fin 4) (Fin 4) ℤ) 0 0,
      (φ (ι n * gAB) : Matrix (Fin 4) (Fin 4) ℤ) 1 1) = (-1, -1) := by
  rw [map_mul, gAB, map_mul, φ_ι, φ_gA, φ_gB]
  rcases n with ⟨i, j, k⟩
  change ((transMat i j k * (mA_mat * mB_mat)) 0 0,
    (transMat i j k * (mA_mat * mB_mat)) 1 1) = (-1, -1)
  simp [transMat, mA_mat, mB_mat, Matrix.mul_apply, Fin.sum_univ_four]

private lemma mkN_inj {a₁ b₁ c₁ a₂ b₂ c₂ : ℤ} :
    mkN a₁ b₁ c₁ = mkN a₂ b₂ c₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ := by
  simp [mkN]

private lemma one_sub_rZ_pow_support (m : ℕ) :
    (∀ i j k : ℤ, (i ≠ 0 ∨ j ≠ 0 ∨ k < 0) → ((1 - rZ p) ^ m).coeff (mkN i j k) = 0) ∧
    ((1 - rZ p) ^ m).coeff (mkN 0 0 0) = 1 := by
  induction m with
  | zero =>
    constructor
    · intro i j k hne
      rw [pow_zero, MonoidAlgebra.one_def, ← mkN_one, MonoidAlgebra.coeff_single,
        Finsupp.single_apply, if_neg]
      rw [mkN_inj]
      omega
    · rw [pow_zero, MonoidAlgebra.one_def, ← mkN_one, MonoidAlgebra.coeff_single,
        Finsupp.single_apply, if_pos rfl]
  | succ m ih =>
    have hmul_z : ∀ (f : R p) (i j k : ℤ), (f * rZ p).coeff (mkN i j k) = f.coeff (mkN i j (k - 1)) := by
      intro f i j k
      refine MonoidAlgebra.induction_linear f ?_ ?_ ?_
      · simp
      · intro f₁ f₂ h₁ h₂
        simp only [add_mul, MonoidAlgebra.coeff_add, Finsupp.add_apply, h₁, h₂]
      · intro n c
        rcases n with ⟨a, b, d⟩
        change (MonoidAlgebra.single (mkN a b d) c * rZ p).coeff (mkN i j k) =
          (MonoidAlgebra.single (mkN a b d) c).coeff (mkN i j (k - 1))
        simp only [rZ, MonoidAlgebra.single_mul_single, mul_one, mkN_mul,
          MonoidAlgebra.coeff_single, Finsupp.single_apply, add_zero]
        have hiff : mkN a b (d + 1) = mkN i j k ↔ mkN a b d = mkN i j (k - 1) := by
          simp only [mkN_inj]; omega
        simp only [hiff]
    have hstep : ∀ i j k : ℤ,
        ((1 - rZ p) ^ (m + 1)).coeff (mkN i j k) =
          ((1 - rZ p) ^ m).coeff (mkN i j k) - ((1 - rZ p) ^ m).coeff (mkN i j (k - 1)) := by
      intro i j k
      rw [pow_succ, mul_sub, mul_one, MonoidAlgebra.coeff_sub, Finsupp.sub_apply, hmul_z]
    constructor
    · intro i j k hne
      rw [hstep, ih.1 i j k hne, ih.1 i j (k - 1) (by omega), sub_zero]
    · rw [hstep, ih.2, ih.1 0 0 (0 - 1) (by omega), sub_zero]

private lemma uS_eval_shift (a b d i j k : ℤ) (f : R p) :
    (MonoidAlgebra.single (mkN a b d) (1 : ZMod p) * f).coeff (mkN i j k) =
      f.coeff (mkN (i - a) (j - b) (k - d)) := by
  refine MonoidAlgebra.induction_linear f ?_ ?_ ?_
  · simp
  · intro f₁ f₂ h₁ h₂
    simp only [mul_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, h₁, h₂]
  · intro n c
    rcases n with ⟨u, v, w⟩
    change (MonoidAlgebra.single (mkN a b d) 1 * MonoidAlgebra.single (mkN u v w) c).coeff (mkN i j k) =
      (MonoidAlgebra.single (mkN u v w) c).coeff (mkN (i - a) (j - b) (k - d))
    simp only [MonoidAlgebra.single_mul_single, one_mul, mkN_mul,
      MonoidAlgebra.coeff_single, Finsupp.single_apply]
    have hiff : mkN (a + u) (b + v) (d + w) = mkN i j k ↔
        mkN u v w = mkN (i - a) (j - b) (k - d) := by
      simp only [mkN_inj]; omega
    simp only [hiff]

private lemma uS_coeff_X : (uS p).coeff (mkN 1 0 0) = 1 := by
  have hH := one_sub_rZ_pow_support p (p - 2)
  change (rZi p + (4 + rX p + rXi p + rY p + rYi p) * rH p).coeff (mkN 1 0 0) = 1
  have hzi : (rZi p).coeff (mkN 1 0 0) = 0 := by
    simp only [rZi, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [if_neg]
    intro h
    have h' := congr_arg Multiplicative.toAdd h
    simp [mkN] at h'
  have hexp : (4 + rX p + rXi p + rY p + rYi p) * rH p =
      (4 : ZMod p) • rH p + rX p * rH p + rXi p * rH p + rY p * rH p + rYi p * rH p := by
    have h4 : (4 : R p) * rH p = (4 : ZMod p) • rH p := by
      rw [Algebra.smul_def, map_ofNat]
    linear_combination h4
  rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, hzi, zero_add, hexp]
  simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_smul_apply,
    smul_eq_mul, rX, rXi, rY, rYi, uS_eval_shift]
  norm_num
  rw [rH, hH.1 1 0 0 (by omega), hH.2, hH.1 2 0 0 (by omega),
    hH.1 1 (-1) 0 (by omega), hH.1 1 1 0 (by omega)]
  ring

private lemma uS_coeff_Y : (uS p).coeff (mkN 0 1 0) = 1 := by
  have hH := one_sub_rZ_pow_support p (p - 2)
  change (rZi p + (4 + rX p + rXi p + rY p + rYi p) * rH p).coeff (mkN 0 1 0) = 1
  have hzi : (rZi p).coeff (mkN 0 1 0) = 0 := by
    simp only [rZi, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [if_neg]
    intro h
    have h' := congr_arg Multiplicative.toAdd h
    simp [mkN] at h'
  have hexp : (4 + rX p + rXi p + rY p + rYi p) * rH p =
      (4 : ZMod p) • rH p + rX p * rH p + rXi p * rH p + rY p * rH p + rYi p * rH p := by
    have h4 : (4 : R p) * rH p = (4 : ZMod p) • rH p := by
      rw [Algebra.smul_def, map_ofNat]
    linear_combination h4
  rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, hzi, zero_add, hexp]
  simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_smul_apply,
    smul_eq_mul, rX, rXi, rY, rYi, uS_eval_shift]
  norm_num
  rw [rH, hH.1 0 1 0 (by omega), hH.1 (-1) 1 0 (by omega), hH.1 1 1 0 (by omega),
    hH.2, hH.1 0 2 0 (by omega)]
  ring

private lemma mapDomain_φ_vanish_of_diag_ne (f : R p) (g : P)
    (M : (Matrix (Fin 4) (Fin 4) ℤ)ˣ)
    (hne : ∀ n : N, φ (ι n * g) ≠ M) :
    (MonoidAlgebra.mapDomainRingHom (ZMod p) φ (embed p f * MonoidAlgebra.single g 1)).coeff M = 0 := by
  refine MonoidAlgebra.induction_linear f ?_ ?_ ?_
  · simp
  · intro f₁ f₂ h₁ h₂
    simp only [map_add, add_mul, MonoidAlgebra.coeff_add, Finsupp.add_apply, h₁, h₂, add_zero]
  · intro n c
    rw [embed_single, MonoidAlgebra.single_mul_single, mul_one]
    simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
      MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (hne n)]

private lemma mapDomain_φ_embed_mul_eAB (f : R p) (n₀ : N) :
    (MonoidAlgebra.mapDomainRingHom (ZMod p) φ (embed p f * eAB p)).coeff (φ (ι n₀ * gAB)) =
      f.coeff n₀ := by
  have hinj : Function.Injective (fun n : N => φ (ι n * gAB)) := by
    intro n₁ n₂ h
    simp only [map_mul] at h
    exact φ_ι_injective (mul_right_cancel h)
  refine MonoidAlgebra.induction_linear f ?_ ?_ ?_
  · simp
  · intro f₁ f₂ h₁ h₂
    simp only [map_add, add_mul, MonoidAlgebra.coeff_add, Finsupp.add_apply, h₁, h₂]
  · intro n c
    rw [embed_single, eAB, MonoidAlgebra.single_mul_single, mul_one]
    simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
      MonoidAlgebra.coeff_single, Finsupp.single_apply, hinj.eq_iff]

private lemma unitU_not_trivial : ¬ IsTrivialUnit (unitU p) := by
  rintro ⟨k, g, hg⟩
  let Ψ := MonoidAlgebra.mapDomainRingHom (ZMod p) φ
  have hΨ_eval : ∀ n₀ : N, (Ψ (unitU p)).coeff (φ (ι n₀ * gAB)) = (uS p).coeff n₀ := by
    intro n₀
    have hM := diag_φ_ι_gAB n₀
    have hP0 : (Ψ (embed p (uP p))).coeff (φ (ι n₀ * gAB)) = 0 := by
      have h := mapDomain_φ_vanish_of_diag_ne p (uP p) 1 (φ (ι n₀ * gAB)) fun n heq => by
        rw [mul_one] at heq
        have h1 := diag_φ_ι n
        rw [heq, hM] at h1
        norm_num at h1
      rw [← MonoidAlgebra.one_def, mul_one] at h
      exact h
    have hQ0 : (Ψ (embed p (uQ p) * eA p)).coeff (φ (ι n₀ * gAB)) = 0 := by
      exact mapDomain_φ_vanish_of_diag_ne p (uQ p) gA (φ (ι n₀ * gAB)) fun n heq => by
        have h1 := diag_φ_ι_gA n
        rw [heq, hM] at h1
        norm_num at h1
    have hR0 : (Ψ (embed p (uR p) * eB p)).coeff (φ (ι n₀ * gAB)) = 0 := by
      exact mapDomain_φ_vanish_of_diag_ne p (uR p) gB (φ (ι n₀ * gAB)) fun n heq => by
        have h1 := diag_φ_ι_gB n
        rw [heq, hM] at h1
        norm_num at h1
    have hS := mapDomain_φ_embed_mul_eAB p (uS p) n₀
    simp only [unitU, quad, Ψ, map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply]
    rw [hP0, hQ0, hR0, hS]
    ring
  have h1 : (Ψ (unitU p)).coeff (φ (ι (mkN 1 0 0) * gAB)) = 1 := by
    rw [hΨ_eval, uS_coeff_X]
  have h2 : (Ψ (unitU p)).coeff (φ (ι (mkN 0 1 0) * gAB)) = 1 := by
    rw [hΨ_eval, uS_coeff_Y]
  have htriv : Ψ (unitU p) = MonoidAlgebra.single (φ g) (k : ZMod p) := by
    rw [hg]
    simp [Ψ]
  rw [htriv, MonoidAlgebra.coeff_single, Finsupp.single_apply] at h1 h2
  have heq1 : φ g = φ (ι (mkN 1 0 0) * gAB) := by
    by_contra hne
    rw [if_neg hne] at h1
    exact zero_ne_one h1
  have heq2 : φ g = φ (ι (mkN 0 1 0) * gAB) := by
    by_contra hne
    rw [if_neg hne] at h2
    exact zero_ne_one h2
  have hsame : φ (ι (mkN 1 0 0) * gAB) = φ (ι (mkN 0 1 0) * gAB) := heq1.symm.trans heq2
  simp only [map_mul] at hsame
  have hn_eq : mkN 1 0 0 = mkN 0 1 0 := φ_ι_injective (mul_right_cancel hsame)
  have hadd := congr_arg Multiplicative.toAdd hn_eq
  simp [mkN] at hadd

end RingAlgebra

end

end KaplanskyUnitCharP

open Kaplansky KaplanskyUnitCharP

theorem OMA.solution : type_of% @Kaplansky.UnitConjecture.counterexamples.i := by
  intro p hp
  refine ⟨⟨unitU p, unitV p, unitU_mul_unitV p, unitV_mul_unitU p⟩, unitU_not_trivial p⟩
