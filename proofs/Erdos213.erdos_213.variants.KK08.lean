import FormalConjectures.ErdosProblems.«213»

-- Problem: Erdős Problem 213 — KK08
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/213.lean:53 (declaration Erdos213.erdos_213.variants.KK08)
-- Credit: @snoozingnewt (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Construction: the integral heptagon of Kreisel and Kurz (2008, arXiv:0804.1303). Each point is
-- (X / 2227, (B / 2227) * sqrt 2002) with integers X, B. All 21 squared distances are squares of
-- the integers in N; collinear triples and concyclic quadruples would make an integer determinant
-- vanish, and those determinants are checked to be nonzero by kernel computation.

open EuclideanGeometry

namespace OMA.E213

noncomputable def pt (a b : ℝ) : ℝ² := !₂[a, b * Real.sqrt 2002]

lemma pt0 (a b : ℝ) : (pt a b) 0 = a := by simp [pt]
lemma pt1 (a b : ℝ) : (pt a b) 1 = b * Real.sqrt 2002 := by simp [pt]

lemma dist_pt (a b c d : ℝ) :
    dist (pt a b) (pt c d) = Real.sqrt ((a - c) ^ 2 + 2002 * (b - d) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, pt0, pt0, pt1, pt1]
  simp only [Real.dist_eq, sq_abs]
  congr 1
  have hs : Real.sqrt 2002 ^ 2 = 2002 := Real.sq_sqrt (by norm_num)
  linear_combination (b - d) ^ 2 * hs

lemma col_eq (p q r : ℝ²) (h : Collinear ℝ ({p, q, r} : Set ℝ²)) :
    (q 0 - p 0) * (r 1 - p 1) = (q 1 - p 1) * (r 0 - p 0) := by
  rw [collinear_iff_of_mem (Set.mem_insert p _)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨s, hs⟩ := hv q (by simp)
  obtain ⟨t, ht⟩ := hv r (by simp)
  have hq0 : q 0 = s * v 0 + p 0 := by rw [hs]; simp
  have hq1 : q 1 = s * v 1 + p 1 := by rw [hs]; simp
  have hr0 : r 0 = t * v 0 + p 0 := by rw [ht]; simp
  have hr1 : r 1 = t * v 1 + p 1 := by rw [ht]; simp
  rw [hq0, hq1, hr0, hr1]
  ring

lemma sph_eq (a b : ℝ) (c : ℝ²) (r : ℝ) (h : dist (pt a b) c = r) :
    (a - c 0) ^ 2 + (b * Real.sqrt 2002 - c 1) ^ 2 = r ^ 2 := by
  rw [← h, EuclideanSpace.dist_eq, Fin.sum_univ_two, pt0, pt1,
    Real.sq_sqrt (by positivity)]
  simp only [Real.dist_eq, sq_abs]


def X : Fin 7 → ℤ := ![0, 49595290, 26127018, 32142553, 17615968, 7344908, 19079044]
def B : Fin 7 → ℤ := ![0, 0, 932064, 411864, 238464, 411864, -54168]
def N : Fin 7 → Fin 7 → ℕ := ![
    ![0, 22270, 22098, 16637, 9248, 8908, 8636],
    ![22270, 0, 21488, 11397, 15138, 20698, 13746],
    ![22098, 21488, 0, 10795, 14450, 13430, 20066],
    ![16637, 11397, 10795, 0, 7395, 11135, 11049],
    ![9248, 15138, 14450, 7395, 0, 5780, 5916],
    ![8908, 20698, 13430, 11135, 5780, 0, 10744],
    ![8636, 13746, 20066, 11049, 5916, 10744, 0]]

def D3 {R : Type*} [CommRing R] (a0 b0 a1 b1 a2 b2 : R) : R :=
  (a1 - a0) * (b2 - b0) - (b1 - b0) * (a2 - a0)

def M3 {R : Type*} [CommRing R] (ap bp aq bq ar br : R) : R :=
  ap * (bq - br) - bp * (aq - ar) + (aq * br - ar * bq)

def D4 {R : Type*} [CommRing R] (k a0 b0 a1 b1 a2 b2 a3 b3 : R) : R :=
  (a0 ^ 2 + k * b0 ^ 2) * M3 a1 b1 a2 b2 a3 b3 - (a1 ^ 2 + k * b1 ^ 2) * M3 a0 b0 a2 b2 a3 b3
    + (a2 ^ 2 + k * b2 ^ 2) * M3 a0 b0 a1 b1 a3 b3 - (a3 ^ 2 + k * b3 ^ 2) * M3 a0 b0 a1 b1 a2 b2

lemma hXinj : ∀ i j : Fin 7, X i = X j → i = j := by decide +kernel

lemma hN : ∀ i j : Fin 7,
    (X i - X j) ^ 2 + 2002 * (B i - B j) ^ 2 = (2227 * (N i j : ℤ)) ^ 2 := by decide +kernel

lemma h3 : ∀ i j k : Fin 7, i ≠ j → j ≠ k → i ≠ k →
    D3 (X i) (B i) (X j) (B j) (X k) (B k) ≠ 0 := by decide +kernel

lemma h4 : ∀ i j k l : Fin 7, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    D4 2002 (X i) (B i) (X j) (B j) (X k) (B k) (X l) (B l) ≠ 0 := by decide +kernel


lemma sqrt2002_ne : Real.sqrt 2002 ≠ 0 := by positivity

lemma col_pt (a0 b0 a1 b1 a2 b2 : ℝ)
    (h : Collinear ℝ ({pt a0 b0, pt a1 b1, pt a2 b2} : Set ℝ²)) :
    D3 a0 b0 a1 b1 a2 b2 = 0 := by
  have h1 := col_eq _ _ _ h
  rw [pt0, pt0, pt0, pt1, pt1, pt1] at h1
  have h2 : Real.sqrt 2002 * D3 a0 b0 a1 b1 a2 b2 = 0 := by
    unfold D3
    linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 sqrt2002_ne
  · exact h3

lemma sph_pt (a0 b0 a1 b1 a2 b2 a3 b3 : ℝ)
    (h : Cospherical ({pt a0 b0, pt a1 b1, pt a2 b2, pt a3 b3} : Set ℝ²)) :
    D4 2002 a0 b0 a1 b1 a2 b2 a3 b3 = 0 := by
  obtain ⟨c, r, hc⟩ := h
  have e0 := sph_eq a0 b0 c r (hc _ (by simp))
  have e1 := sph_eq a1 b1 c r (hc _ (by simp))
  have e2 := sph_eq a2 b2 c r (hc _ (by simp))
  have e3 := sph_eq a3 b3 c r (hc _ (by simp))
  have hs : Real.sqrt 2002 ^ 2 = 2002 := Real.sq_sqrt (by norm_num)
  linear_combination (norm := skip) M3 a1 b1 a2 b2 a3 b3 * e0 - M3 a0 b0 a2 b2 a3 b3 * e1
    + M3 a0 b0 a1 b1 a3 b3 * e2 - M3 a0 b0 a1 b1 a2 b2 * e3
    - (M3 a1 b1 a2 b2 a3 b3 * b0 ^ 2 - M3 a0 b0 a2 b2 a3 b3 * b1 ^ 2
      + M3 a0 b0 a1 b1 a3 b3 * b2 ^ 2 - M3 a0 b0 a1 b1 a2 b2 * b3 ^ 2) * hs
  simp only [D4, M3]
  ring

noncomputable def P (i : Fin 7) : ℝ² := pt ((X i : ℝ) / 2227) ((B i : ℝ) / 2227)

lemma P_inj : Function.Injective P := by
  intro i j h
  have h0 := congrArg (fun p : ℝ² => p 0) h
  simp only [P, pt0] at h0
  have : (X i : ℝ) = X j := by
    have := h0
    field_simp at this
    exact this
  exact hXinj i j (by exact_mod_cast this)

end OMA.E213

open OMA.E213 in
theorem OMA.solution : type_of% @Erdos213.erdos_213.variants.KK08 := by
  refine ⟨Set.range P, Set.finite_range P, ?_, ?_, ?_, ?_⟩
  · rw [Set.ncard_range_of_injective P_inj]
    simp
  · intro x hx y hy z hz hxy hyz hxz hcol
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    obtain ⟨k, rfl⟩ := hz
    have hij : i ≠ j := fun h => hxy (by rw [h])
    have hjk : j ≠ k := fun h => hyz (by rw [h])
    have hik : i ≠ k := fun h => hxz (by rw [h])
    have hr := col_pt _ _ _ _ _ _ hcol
    apply h3 i j k hij hjk hik
    have e : ((D3 (X i) (B i) (X j) (B j) (X k) (B k) : ℤ) : ℝ) =
        2227 ^ 2 * D3 ((X i : ℝ) / 2227) ((B i : ℝ) / 2227) ((X j : ℝ) / 2227)
          ((B j : ℝ) / 2227) ((X k : ℝ) / 2227) ((B k : ℝ) / 2227) := by
      simp only [D3]
      push_cast
      field_simp
    have : ((D3 (X i) (B i) (X j) (B j) (X k) (B k) : ℤ) : ℝ) = 0 := by
      rw [e, hr, mul_zero]
    exact_mod_cast this
  · rintro Q ⟨hQS, hQ4⟩ hcos
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Set.ncard_eq_four.mp hQ4
    have ha : a ∈ Set.range P := hQS (by simp)
    have hb : b ∈ Set.range P := hQS (by simp)
    have hc : c ∈ Set.range P := hQS (by simp)
    have hd : d ∈ Set.range P := hQS (by simp)
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    obtain ⟨k, rfl⟩ := hc
    obtain ⟨l, rfl⟩ := hd
    have hij : i ≠ j := fun h => hab (by rw [h])
    have hik : i ≠ k := fun h => hac (by rw [h])
    have hil : i ≠ l := fun h => had (by rw [h])
    have hjk : j ≠ k := fun h => hbc (by rw [h])
    have hjl : j ≠ l := fun h => hbd (by rw [h])
    have hkl : k ≠ l := fun h => hcd (by rw [h])
    have hr := sph_pt _ _ _ _ _ _ _ _ hcos
    apply h4 i j k l hij hik hil hjk hjl hkl
    have e : ((D4 2002 (X i) (B i) (X j) (B j) (X k) (B k) (X l) (B l) : ℤ) : ℝ) =
        2227 ^ 4 * D4 2002 ((X i : ℝ) / 2227) ((B i : ℝ) / 2227) ((X j : ℝ) / 2227)
          ((B j : ℝ) / 2227) ((X k : ℝ) / 2227) ((B k : ℝ) / 2227)
          ((X l : ℝ) / 2227) ((B l : ℝ) / 2227) := by
      simp only [D4, M3]
      push_cast
      field_simp
    have : ((D4 2002 (X i) (B i) (X j) (B j) (X k) (B k) (X l) (B l) : ℤ) : ℝ) = 0 := by
      rw [e, hr, mul_zero]
    exact_mod_cast this
  · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ -
    refine ⟨(N i j : ℤ), ?_⟩
    have h1 : (((X i - X j) ^ 2 + 2002 * (B i - B j) ^ 2 : ℤ) : ℝ) =
        ((2227 * (N i j : ℤ)) ^ 2 : ℤ) := by exact_mod_cast hN i j
    push_cast at h1
    have e : ((X i : ℝ) / 2227 - (X j : ℝ) / 2227) ^ 2 + 2002 * ((B i : ℝ) / 2227 - (B j : ℝ) / 2227) ^ 2
        = ((N i j : ℝ)) ^ 2 := by
      field_simp
      linear_combination h1
    simp only [P]
    rw [dist_pt, e, Real.sqrt_sq (by positivity)]
    push_cast
    rfl
