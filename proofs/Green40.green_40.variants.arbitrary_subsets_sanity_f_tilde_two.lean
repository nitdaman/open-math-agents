import FormalConjectures.GreensOpenProblems.«40»
import Mathlib

-- Problem: Ben Green's Open Problem 40 — arbitrary subsets sanity f tilde two
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/40.lean:118 (declaration Green40.green_40.variants.arbitrary_subsets_sanity_f_tilde_two)
-- Credit: @mucoucah (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Covering codes of radius two with density tending to one (Struik).

Sketch of the construction formalised below. Let F be the field with 2^(2k+1) elements, so that
cubing is a bijection of F and z^2 + z + 1 has no root in F. A word consists of two blocks X, Y
indexed by F, two small auxiliary blocks indexed by Fin k → ZMod 2 and Fin (k+1) → ZMod 2, and a
tail of 4k+3 bits. The syndrome of the first four blocks is the Preparata style triple
  (s1 X + s1 Y, s3 X + (s1 X)^3 + s3 Y + pair (t1, t2), parity of X),
where s1, s3 are the sums of the labels and of their cubes, and the code is the graph of this map
(the tail stores the syndrome), so it has 2^m words in length m + 4k + 3, m = 4 * 4^k + 3 * 2^k.

Two flips always reach any prescribed syndrome: one flip in X and one in Y when the parity is
wrong (the cubic equation that appears is a shifted cube), two flips inside X or inside Y when the
parity is right and the first component is wrong (the images of z^2 + z and of z^2 + z + 1 cover
F), and two flips in the auxiliary blocks otherwise. Hence the covering radius is two and the
density is at most (1 + n + n choose 2) / 2^(4k+3) with n = m + 4k + 3, which tends to one.
The matching lower bound is the sphere covering bound.
-/

open Green40
open scoped ENNReal Pointwise

namespace OMA.G40

-- Size of the radius two ball (same argument as in the accepted upper_bound_f_two.R1.H2 proof).
theorem card_bound (n : ℕ) : Nat.card (hammingBall n 2) ≤ 1 + n + n.choose 2 := by
  classical
  let U := (Finset.univ : Finset (Fin n))
  let S := (U.powersetCard 0 ∪ U.powersetCard 1) ∪ U.powersetCard 2
  let supp (x : hammingBall n 2) := U.filter (fun i => x.val i ≠ 0)
  have hs (x : hammingBall n 2) : supp x ∈ S := by
    have h : (supp x).card ≤ 2 := x.property
    have hc : (supp x).card = 0 ∨ (supp x).card = 1 ∨ (supp x).card = 2 := by omega
    simpa [S, U, Finset.mem_powersetCard, or_assoc] using hc
  let F (x : hammingBall n 2) : ↥S := ⟨supp x, hs x⟩
  have hinj : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    funext i
    have he : supp x = supp y := congrArg Subtype.val h
    have hm : i ∈ supp x ↔ i ∈ supp y := he ▸ Iff.rfl
    have hb : x.val i ≠ 0 ↔ y.val i ≠ 0 := by simpa [supp, U] using hm
    exact (by decide : ∀ a b : ZMod 2, (a ≠ 0 ↔ b ≠ 0) → a = b) _ _ hb
  have hcount := Nat.card_le_card_of_injective F hinj
  calc
    Nat.card (hammingBall n 2) ≤ S.card := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcount
    _ ≤ ((U.powersetCard 0).card + (U.powersetCard 1).card) + (U.powersetCard 2).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ = _ := by simp [U, Finset.card_powersetCard]

theorem ball_eq (n : ℕ) : Nat.card (hammingBall n 2) = (hammingBallFinset n 2).card := by
  have h : hammingBall n 2 = ↑(hammingBallFinset n 2) := by
    ext x
    simp [hammingBall, hammingBallFinset]
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset]

-- Sphere covering bound.
theorem lower (n : ℕ) (V : Finset (𝔽₂ n)) (hV : IsCoveringFinset n 2 V) :
    (1 : ℝ≥0∞) ≤ (V.card : ℝ≥0∞) * (Nat.card (hammingBall n 2) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞) := by
  have h1 : (V + hammingBallFinset n 2).card ≤ V.card * (hammingBallFinset n 2).card :=
    Finset.card_add_le
  unfold IsCoveringFinset at hV
  rw [hV, Finset.card_univ, ← ball_eq] at h1
  have h2 : Fintype.card (𝔽₂ n) = 2 ^ n := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [h2] at h1
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by simp)), one_mul]
  exact_mod_cast h1

theorem dens (A D t : ℕ) (ht : 0 < t) (h : A * t ≤ D * (t + 1)) :
    (A : ℝ≥0∞) / (D : ℝ≥0∞) ≤ 1 + (t : ℝ≥0∞)⁻¹ := by
  have ht0 : (t : ℝ≥0∞) ≠ 0 := by exact_mod_cast ht.ne'
  have ht' : (t : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top t
  have h1 : (A : ℝ≥0∞) * t ≤ D * (t + 1) := by exact_mod_cast h
  apply ENNReal.div_le_of_le_mul
  calc (A : ℝ≥0∞) = A * t * (t : ℝ≥0∞)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel ht0 ht', mul_one]
    _ ≤ D * (t + 1) * (t : ℝ≥0∞)⁻¹ := by gcongr
    _ = (1 + (t : ℝ≥0∞)⁻¹) * D := by
        rw [mul_assoc, add_mul, ENNReal.mul_inv_cancel ht0 ht', one_mul, mul_comm]

-- Linear statistics of a binary word.
def stat {M H : Type*} [Fintype M] [AddCommMonoid H] [Module (ZMod 2) H] (l : M → H)
    (w : M → ZMod 2) : H :=
  ∑ i, w i • l i

theorem stat_add {M H : Type*} [Fintype M] [AddCommMonoid H] [Module (ZMod 2) H] (l : M → H)
    (w w' : M → ZMod 2) : stat l (w + w') = stat l w + stat l w' := by
  simp only [stat, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem stat_single {M H : Type*} [Fintype M] [DecidableEq M] [AddCommMonoid H]
    [Module (ZMod 2) H] (l : M → H) (i : M) :
    stat l (Pi.single i (1 : ZMod 2) : M → ZMod 2) = l i := by
  unfold stat
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, one_smul]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem stat_flip2 {M H : Type*} [Fintype M] [DecidableEq M] [AddCommMonoid H]
    [Module (ZMod 2) H] (l : M → H) (x : M → ZMod 2) (i j : M) :
    stat l (x + ((Pi.single i (1 : ZMod 2) : M → ZMod 2) + (Pi.single j (1 : ZMod 2) : M → ZMod 2)))
      = stat l x + l i + l j := by
  rw [stat_add, stat_add, stat_single, stat_single, add_assoc]

theorem norm_two {M : Type*} [Fintype M] [DecidableEq M] (i j : M) :
    hammingNorm ((Pi.single i (1 : ZMod 2) : M → ZMod 2) + (Pi.single j (1 : ZMod 2) : M → ZMod 2)) ≤ 2 := by
  unfold hammingNorm
  refine (Finset.card_le_card ?_).trans (Finset.card_le_two (a := i) (b := j))
  intro l hl
  rw [Finset.mem_filter] at hl
  rw [Finset.mem_insert, Finset.mem_singleton]
  by_contra hne
  push Not at hne
  apply hl.2
  rw [Pi.add_apply, Pi.single_eq_of_ne hne.1, Pi.single_eq_of_ne hne.2, add_zero]

-- Labels of the coordinates: two blocks indexed by the field, two auxiliary blocks.
def lA1 (F K1 K2 : Type*) [Field F] [AddCommGroup K1] [AddCommGroup K2] : F ⊕ F ⊕ K1 ⊕ K2 → F :=
  Sum.elim id (fun _ => 0)

def lA3 (F K1 K2 : Type*) [Field F] [AddCommGroup K1] [AddCommGroup K2] : F ⊕ F ⊕ K1 ⊕ K2 → F :=
  Sum.elim (fun u => u ^ 3) (fun _ => 0)

def lB1 (F K1 K2 : Type*) [Field F] [AddCommGroup K1] [AddCommGroup K2] : F ⊕ F ⊕ K1 ⊕ K2 → F :=
  Sum.elim (fun _ => 0) (Sum.elim id (fun _ => 0))

def lB3 (F K1 K2 : Type*) [Field F] [AddCommGroup K1] [AddCommGroup K2] : F ⊕ F ⊕ K1 ⊕ K2 → F :=
  Sum.elim (fun _ => 0) (Sum.elim (fun v => v ^ 3) (fun _ => 0))

def lT1 (F K1 K2 : Type*) [Field F] [AddCommGroup K1] [AddCommGroup K2] : F ⊕ F ⊕ K1 ⊕ K2 → K1 :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim id (fun _ => 0)))

def lT2 (F K1 K2 : Type*) [Field F] [AddCommGroup K1] [AddCommGroup K2] : F ⊕ F ⊕ K1 ⊕ K2 → K2 :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) id))

def lP (F K1 K2 : Type*) [Field F] [AddCommGroup K1] [AddCommGroup K2] :
    F ⊕ F ⊕ K1 ⊕ K2 → ZMod 2 :=
  Sum.elim (fun _ => 1) (fun _ => 0)

-- The syndrome map.
def Phi (F K1 K2 : Type*) [Field F] [Fintype F] [Module (ZMod 2) F]
    [AddCommGroup K1] [AddCommGroup K2] [Fintype K1] [Fintype K2]
    [Module (ZMod 2) K1] [Module (ZMod 2) K2]
    (pair : K1 × K2 → F) (w : F ⊕ F ⊕ K1 ⊕ K2 → ZMod 2) : F × F × ZMod 2 :=
  (stat (lA1 F K1 K2) w + stat (lB1 F K1 K2) w,
   stat (lA3 F K1 K2) w + (stat (lA1 F K1 K2) w) ^ 3 + stat (lB3 F K1 K2) w
     + pair (stat (lT1 F K1 K2) w, stat (lT2 F K1 K2) w),
   stat (lP F K1 K2) w)

-- Algebraic heart: two flips always reach any prescribed syndrome.
theorem core (F K1 K2 : Type*) [Field F] [AddCommGroup K1] [AddCommGroup K2]
    (h2 : (2 : F) = 0) (hcube : ∀ y : F, ∃ r : F, r ^ 3 = y)
    (hdich : ∀ γ : F, ∃ z : F, z ^ 2 + z = γ ∨ z ^ 2 + z + 1 = γ)
    (pair : K1 × K2 → F) (hpair : Function.Surjective pair)
    (A1 A3 B1 B3 : F) (T1 : K1) (T2 : K2) (P : ZMod 2) (a bt : F) (π : ZMod 2) :
    ∃ i j : F ⊕ F ⊕ K1 ⊕ K2,
      A1 + lA1 F K1 K2 i + lA1 F K1 K2 j + (B1 + lB1 F K1 K2 i + lB1 F K1 K2 j) = a ∧
      A3 + lA3 F K1 K2 i + lA3 F K1 K2 j + (A1 + lA1 F K1 K2 i + lA1 F K1 K2 j) ^ 3 +
          (B3 + lB3 F K1 K2 i + lB3 F K1 K2 j) +
          pair (T1 + lT1 F K1 K2 i + lT1 F K1 K2 j, T2 + lT2 F K1 K2 i + lT2 F K1 K2 j) = bt ∧
      P + lP F K1 K2 i + lP F K1 K2 j = π := by
  by_cases hp : P = π
  · by_cases hA : A1 + B1 = a
    · obtain ⟨⟨j1, j2⟩, hj⟩ := hpair (bt - (A3 + A1 ^ 3 + B3))
      have e1 : T1 + (j1 - T1) = j1 := by abel
      have e2 : T2 + (j2 - T2) = j2 := by abel
      refine ⟨Sum.inr (Sum.inr (Sum.inl (j1 - T1))), Sum.inr (Sum.inr (Sum.inr (j2 - T2))),
        ?_, ?_, ?_⟩
      · simp only [lA1, lB1, Sum.elim_inr, add_zero]
        exact hA
      · simp only [lA1, lA3, lB3, lT1, lT2, Sum.elim_inl, Sum.elim_inr, add_zero, id_eq]
        rw [e1, e2, hj]
        ring
      · simp only [lP, Sum.elim_inr, add_zero]
        exact hp
    · have hα : a - A1 - B1 ≠ 0 := fun h => hA (by linear_combination -h)
      have hα3 : (a - A1 - B1) ^ 3 ≠ 0 := pow_ne_zero 3 hα
      obtain ⟨z, hz⟩ := hdich ((bt - A3 - B3 - pair (T1, T2) - A1 ^ 3) / (a - A1 - B1) ^ 3)
      rcases hz with hz | hz
      · have hβ : (a - A1 - B1) ^ 3 * (z ^ 2 + z) = bt - A3 - B3 - pair (T1, T2) - A1 ^ 3 := by
          rw [hz]
          field_simp
        refine ⟨Sum.inl ((a - A1 - B1) * z - A1),
          Sum.inl ((a - A1 - B1) - (a - A1 - B1) * z + A1), ?_, ?_, ?_⟩
        · simp only [lA1, lB1, Sum.elim_inl, add_zero, id_eq]
          ring
        · simp only [lA1, lA3, lB3, lT1, lT2, Sum.elim_inl, add_zero, id_eq]
          linear_combination hβ + ((a - A1 - B1) ^ 3 - 2 * (a - A1 - B1) ^ 3 * z
            + (a - A1 - B1) ^ 3 * z ^ 2
            + 3 * A1 * (a - A1 - B1) * ((a - A1 - B1) - (a - A1 - B1) * z + A1)) * h2
        · simp only [lP, Sum.elim_inl]
          rw [← hp]
          exact (by decide : ∀ P : ZMod 2, P + 1 + 1 = P) P
      · have hβ : (a - A1 - B1) ^ 3 * (z ^ 2 + z + 1) = bt - A3 - B3 - pair (T1, T2) - A1 ^ 3 := by
          rw [hz]
          field_simp
        refine ⟨Sum.inr (Sum.inl ((a - A1 - B1) * z)),
          Sum.inr (Sum.inl ((a - A1 - B1) - (a - A1 - B1) * z)), ?_, ?_, ?_⟩
        · simp only [lA1, lB1, Sum.elim_inl, Sum.elim_inr, add_zero, id_eq]
          ring
        · simp only [lA1, lA3, lB3, lT1, lT2, Sum.elim_inl, Sum.elim_inr, add_zero]
          linear_combination hβ + ((a - A1 - B1) ^ 3 * (z ^ 2 - 2 * z)) * h2
        · simp only [lP, Sum.elim_inr, add_zero]
          exact hp
  · obtain ⟨r, hr⟩ := hcube ((bt - A3 - B3 - pair (T1, T2) - A1 ^ 3) + (a - B1) ^ 3
      - (a - A1 - B1) ^ 3)
    refine ⟨Sum.inl (r - (a - B1)), Sum.inr (Sum.inl ((a - A1 - B1) - (r - (a - B1)))),
      ?_, ?_, ?_⟩
    · simp only [lA1, lB1, Sum.elim_inl, Sum.elim_inr, add_zero, id_eq]
      ring
    · simp only [lA1, lA3, lB3, lT1, lT2, Sum.elim_inl, Sum.elim_inr, add_zero, id_eq]
      linear_combination hr - 3 * (r - (a - B1)) * (a - A1 - B1) * (a - B1) * h2
    · simp only [lP, Sum.elim_inl, Sum.elim_inr, add_zero]
      exact (by decide : ∀ P π : ZMod 2, P ≠ π → P + 1 = π) P π hp

theorem cover_main (F K1 K2 : Type*) [Field F] [Fintype F] [DecidableEq F] [Module (ZMod 2) F]
    [AddCommGroup K1] [AddCommGroup K2] [Fintype K1] [Fintype K2] [DecidableEq K1]
    [DecidableEq K2] [Module (ZMod 2) K1] [Module (ZMod 2) K2]
    (h2 : (2 : F) = 0) (hcube : ∀ y : F, ∃ r : F, r ^ 3 = y)
    (hdich : ∀ γ : F, ∃ z : F, z ^ 2 + z = γ ∨ z ^ 2 + z + 1 = γ)
    (pair : K1 × K2 → F) (hpair : Function.Surjective pair)
    (x : F ⊕ F ⊕ K1 ⊕ K2 → ZMod 2) (g : F × F × ZMod 2) :
    ∃ b : F ⊕ F ⊕ K1 ⊕ K2 → ZMod 2, hammingNorm b ≤ 2 ∧ Phi F K1 K2 pair (x + b) = g := by
  obtain ⟨a, bt, π⟩ := g
  obtain ⟨i, j, h1, h2', h3⟩ := core F K1 K2 h2 hcube hdich pair hpair
    (stat (lA1 F K1 K2) x) (stat (lA3 F K1 K2) x) (stat (lB1 F K1 K2) x)
    (stat (lB3 F K1 K2) x) (stat (lT1 F K1 K2) x) (stat (lT2 F K1 K2) x)
    (stat (lP F K1 K2) x) a bt π
  refine ⟨(Pi.single i (1 : ZMod 2) : F ⊕ F ⊕ K1 ⊕ K2 → ZMod 2) + (Pi.single j (1 : ZMod 2) : F ⊕ F ⊕ K1 ⊕ K2 → ZMod 2), norm_two i j, ?_⟩
  simp only [Phi, stat_flip2]
  exact Prod.ext h1 (Prod.ext h2' h3)

-- Field facts.
theorem cube_inj (F : Type*) [Field F] [Fintype F] (k : ℕ)
    (hcard : Fintype.card F = 2 ^ (2 * k + 1)) : ∀ x y : F, x ^ 3 = y ^ 3 → x = y := by
  have hr : ∃ r, Fintype.card F - 1 = 3 * r + 1 := by
    have h4 : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have h2k : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
      rw [pow_succ, pow_mul, mul_comm]
      norm_num
    rw [hcard, h2k]
    generalize 4 ^ k = w at h4
    exact ⟨(2 * w - 2) / 3, by omega⟩
  obtain ⟨r, hr⟩ := hr
  have key : ∀ z : F, z ^ 3 = 1 → z = 1 := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz
    have h1 := FiniteField.pow_card_sub_one_eq_one z hz0
    rw [hr, pow_succ, pow_mul, hz, one_pow, one_mul] at h1
    exact h1
  intro x y h
  by_cases hy : y = 0
  · subst hy
    simpa using h
  · have h3 : (x / y) ^ 3 = 1 := by rw [div_pow, h, div_self (pow_ne_zero 3 hy)]
    have h4 := key _ h3
    rwa [div_eq_one_iff_eq hy] at h4

theorem dich (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h2 : (2 : F) = 0)
    (hinj : ∀ z : F, z ^ 3 = 1 → z = 1) (γ : F) :
    ∃ z : F, z ^ 2 + z = γ ∨ z ^ 2 + z + 1 = γ := by
  have hB : ∀ z : F, z ^ 2 + z ≠ 1 := by
    intro z hz
    have h3 : z ^ 3 = 1 := by linear_combination (z + 1) * hz - z ^ 2 * h2
    have h1 := hinj z h3
    rw [h1] at hz
    have h0 : (1 : F) = 0 := by linear_combination hz
    exact one_ne_zero h0
  have hker : ∀ a b : F, a ^ 2 + a = b ^ 2 + b → a = b ∨ a = b + 1 := by
    intro a b h
    have h0 : (a - b) * (a + b + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h0 with h1 | h1
    · left
      exact sub_eq_zero.mp h1
    · right
      linear_combination h1 - (b + 1) * h2
  have hcard : Fintype.card F ≤ 2 * ((Finset.univ : Finset F).image (fun z : F => z ^ 2 + z)).card := by
    have h := Finset.card_le_mul_card_image (f := fun z : F => z ^ 2 + z) (Finset.univ : Finset F) 2
      (by
        intro y hy
        obtain ⟨z0, -, hz0⟩ := Finset.mem_image.mp hy
        refine (Finset.card_le_card ?_).trans (Finset.card_le_two (a := z0) (b := z0 + 1))
        intro z hz
        rw [Finset.mem_filter] at hz
        rw [Finset.mem_insert, Finset.mem_singleton]
        have hz' : z ^ 2 + z = y := hz.2
        have hz0' : z0 ^ 2 + z0 = y := hz0
        exact hker z z0 (hz'.trans hz0'.symm))
    rwa [Finset.card_univ] at h
  have hdisj : Disjoint ((Finset.univ : Finset F).image (fun z : F => z ^ 2 + z))
      (((Finset.univ : Finset F).image (fun z : F => z ^ 2 + z)).image (fun y : F => y + 1)) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hy
    obtain ⟨y', hy'', hyy⟩ := Finset.mem_image.mp hy'
    obtain ⟨z', -, hz'⟩ := Finset.mem_image.mp hy''
    have hz1 : z ^ 2 + z = y := hz
    have hz2 : z' ^ 2 + z' = y' := hz'
    have hz3 : y' + 1 = y := hyy
    apply hB (z + z')
    linear_combination hz1 - hz3 - hz2 + (z * z' + z' ^ 2 + z') * h2
  have hcardT : (((Finset.univ : Finset F).image (fun z : F => z ^ 2 + z)).image
      (fun y : F => y + 1)).card = ((Finset.univ : Finset F).image (fun z : F => z ^ 2 + z)).card :=
    Finset.card_image_of_injective _ (add_left_injective (1 : F))
  have hunion := Finset.card_union_of_disjoint hdisj
  have huniv : ((Finset.univ : Finset F).image (fun z : F => z ^ 2 + z)) ∪
      (((Finset.univ : Finset F).image (fun z : F => z ^ 2 + z)).image (fun y : F => y + 1))
      = Finset.univ := by
    apply Finset.eq_univ_of_card
    apply le_antisymm (Finset.card_le_univ _)
    rw [hunion, hcardT]
    omega
  have hγ : γ ∈ ((Finset.univ : Finset F).image (fun z : F => z ^ 2 + z)) ∪
      (((Finset.univ : Finset F).image (fun z : F => z ^ 2 + z)).image (fun y : F => y + 1)) := by
    rw [huniv]
    exact Finset.mem_univ γ
  rcases Finset.mem_union.mp hγ with h | h
  · obtain ⟨z, -, hz⟩ := Finset.mem_image.mp h
    exact ⟨z, Or.inl hz⟩
  · obtain ⟨y', hy', hyy⟩ := Finset.mem_image.mp h
    obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hy'
    have hz1 : z ^ 2 + z = y' := hz
    have hz3 : y' + 1 = γ := hyy
    exact ⟨z, Or.inr (by rw [hz1, hz3])⟩

-- From a syndrome map to a covering code on Fin (m + s).
theorem graph_cover {M : Type*} [Fintype M] [DecidableEq M] (m s : ℕ)
    (hm : Fintype.card M = m) (Ψ : (M → ZMod 2) → (Fin s → ZMod 2))
    (hΨ : ∀ (x : M → ZMod 2) (t : Fin s → ZMod 2),
      ∃ b : M → ZMod 2, hammingNorm b ≤ 2 ∧ Ψ (x + b) = t) :
    ∃ V : Finset (𝔽₂ (m + s)), V.card ≤ 2 ^ m ∧ IsCoveringFinset (m + s) 2 V := by
  subst hm
  let e : M ⊕ Fin s ≃ Fin (Fintype.card M + s) :=
    (Equiv.sumCongr (Fintype.equivFin M) (Equiv.refl (Fin s))).trans finSumFinEquiv
  let enc : (M → ZMod 2) → 𝔽₂ (Fintype.card M + s) :=
    fun x i => Sum.elim x (Ψ x) (e.symm i)
  refine ⟨Finset.univ.image enc, ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    exact le_of_eq (by rw [Finset.card_univ, Fintype.card_fun, ZMod.card])
  · unfold IsCoveringFinset
    rw [Finset.eq_univ_iff_forall]
    intro z
    obtain ⟨b, hb, hbΨ⟩ := hΨ (fun j => z (e (Sum.inl j))) (fun j => z (e (Sum.inr j)))
    rw [Finset.mem_add]
    refine ⟨enc ((fun j => z (e (Sum.inl j))) + b),
      Finset.mem_image_of_mem _ (Finset.mem_univ _),
      fun i => Sum.elim b (fun _ => (0 : ZMod 2)) (e.symm i), ?_, ?_⟩
    · unfold hammingBallFinset
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, le_trans ?_ hb⟩
      unfold hammingNorm
      have hsub : (Finset.univ.filter
          (fun i => Sum.elim b (fun _ => (0 : ZMod 2)) (e.symm i) ≠ 0)) ⊆
          (Finset.univ.filter (fun j => b j ≠ 0)).image (fun j => e (Sum.inl j)) := by
        intro i hi
        rw [Finset.mem_filter] at hi
        obtain ⟨y, rfl⟩ := e.surjective i
        rw [Equiv.symm_apply_apply] at hi
        rcases y with j | j
        · exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.2⟩, rfl⟩
        · exact absurd rfl hi.2
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    · funext i
      obtain ⟨y, rfl⟩ := e.surjective i
      rcases y with j | j
      · simp only [enc, Pi.add_apply, Equiv.symm_apply_apply, Sum.elim_inl]
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      · simp only [enc, Pi.add_apply, Equiv.symm_apply_apply, Sum.elim_inr, add_zero]
        exact congrFun hbΨ j

def mlen (k : ℕ) : ℕ := 2 ^ (2 * k + 1) + (2 ^ (2 * k + 1) + (2 ^ k + 2 ^ (k + 1)))

theorem exists_code (k : ℕ) :
    ∃ V : Finset (𝔽₂ (mlen k + (4 * k + 3))),
      V.card ≤ 2 ^ mlen k ∧ IsCoveringFinset (mlen k + (4 * k + 3)) 2 V := by
  classical
  have : Fintype (GaloisField 2 (2 * k + 1)) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 2 (2 * k + 1)) = 2 ^ (2 * k + 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (2 * k + 1) (by omega)
  have h2 : (2 : GaloisField 2 (2 * k + 1)) = 0 := CharTwo.two_eq_zero
  have hinj := cube_inj (GaloisField 2 (2 * k + 1)) k hF
  have hcube : ∀ y : GaloisField 2 (2 * k + 1), ∃ r : GaloisField 2 (2 * k + 1), r ^ 3 = y := by
    have hi : Function.Injective (fun x : GaloisField 2 (2 * k + 1) => x ^ 3) :=
      fun x y h => hinj x y h
    exact fun y => (Finite.injective_iff_surjective.mp hi) y
  have hdich := dich (GaloisField 2 (2 * k + 1)) h2
    (fun z hz => hinj z 1 (by rw [hz, one_pow]))
  have hpc : Fintype.card ((Fin k → ZMod 2) × (Fin (k + 1) → ZMod 2)) =
      Fintype.card (GaloisField 2 (2 * k + 1)) := by
    rw [hF, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin,
      Fintype.card_fin, ← pow_add]
    congr 1
    omega
  have hsc : Fintype.card (GaloisField 2 (2 * k + 1) × GaloisField 2 (2 * k + 1) × ZMod 2) =
      Fintype.card (Fin (4 * k + 3) → ZMod 2) := by
    rw [Fintype.card_prod, Fintype.card_prod, hF, Fintype.card_fun, ZMod.card, Fintype.card_fin,
      ← pow_succ, ← pow_add]
    congr 1
    omega
  let pair := Fintype.equivOfCardEq hpc
  let encS := Fintype.equivOfCardEq hsc
  refine graph_cover (M := GaloisField 2 (2 * k + 1) ⊕ GaloisField 2 (2 * k + 1) ⊕
    (Fin k → ZMod 2) ⊕ (Fin (k + 1) → ZMod 2)) (mlen k) (4 * k + 3) ?_
    (fun w => encS (Phi (GaloisField 2 (2 * k + 1)) (Fin k → ZMod 2) (Fin (k + 1) → ZMod 2)
      pair w)) ?_
  · unfold mlen
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum, hF, Fintype.card_fun,
      Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin]
  · intro x t
    obtain ⟨b, hb, hΦ⟩ := cover_main (GaloisField 2 (2 * k + 1)) (Fin k → ZMod 2)
      (Fin (k + 1) → ZMod 2) h2 hcube hdich pair pair.surjective x (encS.symm t)
    refine ⟨b, hb, ?_⟩
    show encS (Phi (GaloisField 2 (2 * k + 1)) (Fin k → ZMod 2) (Fin (k + 1) → ZMod 2)
      pair (x + b)) = t
    rw [hΦ]
    exact encS.apply_symm_apply t

theorem arith (t N0 : ℕ) : ∃ k : ℕ, N0 ≤ k ∧
    (1 + (mlen k + (4 * k + 3)) + (mlen k + (4 * k + 3)).choose 2) * t ≤
      2 ^ (4 * k + 3) * (t + 1) := by
  obtain ⟨k, hk1, hk2⟩ : ∃ k, N0 ≤ k ∧ 8 * t + 8 ≤ k := ⟨N0 + 8 * t + 8, by omega, by omega⟩
  refine ⟨k, hk1, ?_⟩
  have hks : k < 2 ^ k := Nat.lt_two_pow_self
  have e1 : 2 ^ (2 * k + 1) = 2 * (2 ^ k) ^ 2 := by ring
  have e2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have e3 : 2 ^ (4 * k + 3) = 8 * (2 ^ k) ^ 4 := by ring
  unfold mlen
  rw [e1, e2, e3]
  clear e1 e2 e3
  generalize 2 ^ k = s at *
  generalize hn : 2 * s ^ 2 + (2 * s ^ 2 + (s + 2 * s)) + (4 * k + 3) = n
  have hs : 8 * t + 9 ≤ s := by omega
  have hc : 2 * n.choose 2 ≤ n * n := by
    rw [Nat.choose_two_right]
    have := Nat.mul_le_mul_left n (Nat.sub_le n 1)
    omega
  have hb : 2 * (1 + n + n.choose 2) ≤ (n + 1) ^ 2 + 1 := by nlinarith [hc]
  have hn1 : n + 1 ≤ 4 * s ^ 2 + 8 * s := by
    rw [← hn]
    nlinarith [hks]
  have h1 : (n + 1) ^ 2 ≤ (4 * s ^ 2 + 8 * s) ^ 2 := Nat.pow_le_pow_left hn1 2
  have hbt : 2 * (1 + n + n.choose 2) * t ≤ ((4 * s ^ 2 + 8 * s) ^ 2 + 1) * t :=
    Nat.mul_le_mul_right t (hb.trans (Nat.add_le_add_right h1 1))
  have h2 : 16 * s ^ 3 * (8 * t + 8) ≤ 16 * s ^ 3 * s := Nat.mul_le_mul_left _ (by omega)
  have h3 : s ^ 2 * t ≤ s ^ 3 * t :=
    Nat.mul_le_mul_right t (Nat.pow_le_pow_right (by omega) (by norm_num))
  have h4 : t ≤ s ^ 3 := le_trans (by omega) (Nat.le_self_pow (by norm_num) s)
  nlinarith [hbt, h2, h3, h4]

theorem freq_bound (t : ℕ) (ht : 0 < t) :
    ∃ᶠ n in Filter.atTop, minDensityFinset n 2 ≤ 1 + (t : ℝ≥0∞)⁻¹ := by
  apply Filter.frequently_atTop.2
  intro N0
  obtain ⟨k, hk, hk2⟩ := arith t N0
  obtain ⟨V, hVc, hVcov⟩ := exists_code k
  refine ⟨mlen k + (4 * k + 3), by omega, ?_⟩
  unfold minDensityFinset
  refine le_trans (iInf₂_le V hVcov) ?_
  have hball := card_bound (mlen k + (4 * k + 3))
  have hnat : V.card * Nat.card (hammingBall (mlen k + (4 * k + 3)) 2) * t ≤
      2 ^ (mlen k + (4 * k + 3)) * (t + 1) := by
    calc V.card * Nat.card (hammingBall (mlen k + (4 * k + 3)) 2) * t
        ≤ 2 ^ mlen k * (1 + (mlen k + (4 * k + 3)) + (mlen k + (4 * k + 3)).choose 2) * t :=
          Nat.mul_le_mul_right t (Nat.mul_le_mul hVc hball)
      _ = 2 ^ mlen k * ((1 + (mlen k + (4 * k + 3)) + (mlen k + (4 * k + 3)).choose 2) * t) := by
          ring
      _ ≤ 2 ^ mlen k * (2 ^ (4 * k + 3) * (t + 1)) := Nat.mul_le_mul_left _ hk2
      _ = 2 ^ (mlen k + (4 * k + 3)) * (t + 1) := by
          rw [pow_add]
          ring
  have hfinal := dens (V.card * Nat.card (hammingBall (mlen k + (4 * k + 3)) 2))
    (2 ^ (mlen k + (4 * k + 3))) t ht hnat
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hfinal

end OMA.G40

theorem OMA.solution : type_of% @Green40.green_40.variants.arbitrary_subsets_sanity_f_tilde_two := by
  show Green40.f_tilde 2 = 1
  unfold Green40.f_tilde
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨t, ht⟩ := ENNReal.exists_inv_nat_lt (show (ε : ℝ≥0∞) ≠ 0 by exact_mod_cast hε.ne')
    have h1 := Filter.liminf_le_of_frequently_le' (OMA.G40.freq_bound (t + 1) (Nat.succ_pos t))
    refine h1.trans ?_
    gcongr
    refine le_trans ?_ ht.le
    rw [ENNReal.inv_le_inv]
    exact_mod_cast Nat.le_succ t
  · refine Filter.le_liminf_of_le (by isBoundedDefault) (Filter.Eventually.of_forall fun n => ?_)
    exact le_iInf₂ fun V hV => OMA.G40.lower n V hV
