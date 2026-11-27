import FormalConjectures.ErdosProblems.«13»

/-!
# A dense terminal interval for Erdős Problem 13

Write the upper endpoint as (r + 1)m and call its last m integers T.
If T has h holes and (2r + 3)h + r + 2 ≤ m, the exact bound is m.
The two remaining steps treat different densities on T. Both only concern
sets for which deleting any final segment of whole blocks costs more than
one element per block. This restriction follows by strong induction on m.
-/

-- Credit: @jenil-bodhani

namespace OMA.R_Erdos13_erdos_13_variants_general_R1

open Finset

/-- Find a forbidden sum when at most half of the terminal interval T is occupied. -/
def H1 : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 ((r + 1) * m) → m + K < A.card →
    (∀ j < m, m - j < (A.filter fun a => (r + 1) * j < a).card) →
    2 * (Ioc (r * m) ((r + 1) * m) ∩ A).card ≤ m →
    ∃ a ∈ A, ∃ b : Fin r → ℕ, (∀ i, b i ∈ A ∧ a < b i) ∧ a ∣ ∑ i, b i

/-- Find a forbidden sum when more than half of T is occupied and too many
holes remain for the interval argument. -/
def H2 : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 ((r + 1) * m) → m + K < A.card →
    (∀ j < m, m - j < (A.filter fun a => (r + 1) * j < a).card) →
    m < 2 * (Ioc (r * m) ((r + 1) * m) ∩ A).card →
    m < (2 * r + 3) * (Ioc (r * m) ((r + 1) * m) \ A).card + (r + 2) →
    ∃ a ∈ A, ∃ b : Fin r → ℕ, (∀ i, b i ∈ A ∧ a < b i) ∧ a ∣ ∑ i, b i

/-- At most h missing integers leave a central interval of two-term sums.
Reflection in s/2 sends each unsuccessful first summand to a hole. -/
lemma pair_of_few_holes (B : Finset ℕ) {L U h s : ℕ}
    (holes : (Icc L U \ B).card ≤ h) (hsL : 2 * (L + h) ≤ s)
    (hsU : s + 2 * h ≤ 2 * U) :
    ∃ x ∈ B, ∃ y ∈ B, x + y = s := by
  classical
  let D := Icc L U \ B
  let J := Icc (s / 2 - h) (s / 2 + h)
  by_contra hn
  have sub : J ⊆ D ∪ D.image (fun y => s - y) := by
    intro x hx
    have hx' := mem_Icc.mp hx
    have hxI : x ∈ Icc L U := mem_Icc.mpr ⟨by omega, by omega⟩
    have hyI : s - x ∈ Icc L U := mem_Icc.mpr ⟨by omega, by omega⟩
    by_cases hb : x ∈ B
    · have hy : s - x ∉ B := fun hy => hn ⟨x, hb, s - x, hy, by omega⟩
      exact mem_union_right _ (mem_image.mpr
        ⟨s - x, mem_sdiff.mpr ⟨hyI, hy⟩, by omega⟩)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hxI, hb⟩)
  have sizeJ : J.card = 2 * h + 1 := by
    dsimp [J]
    rw [Nat.card_Icc]
    omega
  have imageBound : (D.image (fun y => s - y)).card ≤ D.card := card_image_le
  have sizeBound := (card_le_card sub).trans (card_union_le _ _)
  change D.card ≤ h at holes
  omega

/-- Consecutive translates of the interval of pair sums overlap. Extending
by either endpoint witness gives every sum in the stated central interval. -/
lemma sums_of_few_holes (B : Finset ℕ) {L U h r : ℕ}
    (sub : B ⊆ Icc L U) (holes : (Icc L U \ B).card ≤ h)
    (room : L + 4 * h ≤ U) (hr : 2 ≤ r) :
    ∀ s : ℕ, r * (L + h) ≤ s → s ≤ r * (U - h) →
      ∃ b : Fin r → ℕ, (∀ i, b i ∈ B) ∧ ∑ i, b i = s := by
  let l := L + h
  let u := U - h
  have hu : u + h = U := by dsimp [u]; omega
  have hlu : l ≤ u := by dsimp [l, u]; omega
  have base (s : ℕ) (hsl : 2 * l ≤ s) (hsu : s ≤ 2 * u) :=
    pair_of_few_holes B holes hsl (by omega : s + 2 * h ≤ 2 * U)
  obtain ⟨x, hx, y, hy, hxy⟩ := base (2 * l) le_rfl (by omega)
  obtain ⟨v, hv, w, hw, hvw⟩ := base (2 * u) (by omega) le_rfl
  have existsLo : ∃ lo ∈ B, lo ≤ l := by
    by_cases hx' : x ≤ l
    · exact ⟨x, hx, hx'⟩
    · exact ⟨y, hy, by omega⟩
  have existsHi : ∃ hi ∈ B, u ≤ hi := by
    by_cases hv' : u ≤ v
    · exact ⟨v, hv, hv'⟩
    · exact ⟨w, hw, by omega⟩
  obtain ⟨lo, hlo, hlo'⟩ := existsLo
  obtain ⟨hi, hhi, hhi'⟩ := existsHi
  have hLoL := (mem_Icc.mp (sub hlo)).1
  have hHiU := (mem_Icc.mp (sub hhi)).2
  have hover : 2 * l + hi ≤ 2 * u + lo := by dsimp [l, u]; omega
  have rep (j : ℕ) : ∀ s, (j + 2) * l ≤ s → s ≤ (j + 2) * u →
      ∃ b : Fin (j + 2) → ℕ, (∀ i, b i ∈ B) ∧ ∑ i, b i = s := by
    induction j with
    | zero =>
      intro s hsl hsu
      obtain ⟨p, hp, q, hq, hpq⟩ := base s hsl hsu
      exact ⟨![p, q], by simpa [Fin.forall_fin_two] using And.intro hp hq,
        by simpa [Fin.sum_univ_two] using hpq⟩
    | succ j ih =>
      intro s hsl hsu
      have overlap : (j + 2) * l + hi ≤ (j + 2) * u + lo := by
        simpa only [Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.add_le_add (Nat.mul_le_mul_left j hlu) hover
      have ext : ∃ c ∈ B, (j + 2) * l + c ≤ s ∧ s ≤ (j + 2) * u + c := by
        have hl' : (j + 2) * l + l ≤ s := by rwa [← Nat.succ_mul]
        have hu' : s ≤ (j + 2) * u + u := by rwa [← Nat.succ_mul]
        by_cases hl : s ≤ (j + 2) * u + lo
        · exact ⟨lo, hlo, by omega, hl⟩
        · exact ⟨hi, hhi, by omega, by omega⟩
      obtain ⟨c, hc, hcsL, hcsU⟩ := ext
      obtain ⟨f, hf, hsum⟩ := ih (s - c) (by omega) (by omega)
      refine ⟨Fin.cons c f, ?_, ?_⟩
      · exact Fin.forall_fin_succ.mpr ⟨by simpa, by simpa using hf⟩
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hsum]
        omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hr
  rw [show r = j + 2 by omega]
  exact rep j

/-- A multiple exists either by rounding down the upper endpoint or by using
the prescribed multiplier k. -/
lemma multiple_in_interval {L U k a : ℕ} (ha : 0 < a) (hLU : L ≤ U)
    (overlap : L ≤ k * (U - L)) (top : k * a ≤ U) :
    ∃ s, L ≤ s ∧ s ≤ U ∧ a ∣ s := by
  by_cases hsmall : a ≤ U - L
  · have rem := Nat.mod_lt U ha
    have div := Nat.mod_add_div U a
    exact ⟨a * (U / a), by omega, by omega, dvd_mul_right _ _⟩
  · exact ⟨k * a, overlap.trans (Nat.mul_le_mul_left _ (by omega)), top, dvd_mul_left _ _⟩

/-- With few holes in the top interval, every admissible set satisfies the
sharp upper bound. Each lower element must lie among the last h integers
below that interval, so the h holes pay for all of them. -/
lemma dense_top_block {r m : ℕ} (hr : 2 ≤ r) (A : Finset ℕ)
    (sub : A ⊆ Icc 1 ((r + 1) * m))
    (free : ∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) →
      ¬ a ∣ ∑ i, b i)
    (dense : (2 * r + 3) * (Ioc (r * m) ((r + 1) * m) \ A).card + (r + 2) ≤ m) :
    A.card ≤ m := by
  classical
  let L := r * m + 1
  let U := (r + 1) * m
  let T := Icc L U
  let B := T ∩ A
  let h := (T \ A).card
  have hT : T = Ioc (r * m) ((r + 1) * m) := by
    apply Finset.ext
    intro a
    change a ∈ Icc (r * m + 1) U ↔ a ∈ Ioc (r * m) U
    rw [mem_Icc, mem_Ioc]
    rfl
  rw [← hT] at dense
  change (2 * r + 3) * h + (r + 2) ≤ m at dense
  have h4 : 4 * h + 1 ≤ m := by
    have := Nat.mul_le_mul_right h (show 4 ≤ 2 * r + 3 by omega)
    omega
  have hU : U = r * m + m := by dsimp [U]; ring
  have room : L + 4 * h ≤ U := by dsimp [L]; omega
  have hRm : h ≤ r * m := by
    have := Nat.mul_le_mul_right m (show 1 ≤ r by omega)
    omega
  let l := L + h
  let u := U - h
  have hu : u + h = U := by dsimp [u]; omega
  have hlu : l ≤ u := by dsimp [l]; omega
  have width : (u - l) + 1 + 2 * h = m := by dsimp [l, L] at *; omega
  have gap : l ≤ (r + 1) * (u - l) := by
    have eq := congrArg (fun k : ℕ => (r + 1) * k) width
    change r * m + 1 + h ≤ _
    nlinarith only [eq, dense]
  have overlap : r * l ≤ (r + 1) * (r * u - r * l) := by
    rw [← Nat.mul_sub]
    calc r * l ≤ r * ((r + 1) * (u - l)) := Nat.mul_le_mul_left _ gap
         _ = _ := by ring
  have holes : (Icc L U \ B).card ≤ h := by
    apply card_le_card
    intro x hx
    obtain ⟨hI, hB⟩ := mem_sdiff.mp hx
    exact mem_sdiff.mpr ⟨hI, fun hA => hB (mem_inter.mpr ⟨hI, hA⟩)⟩
  have above (a) (ha : a ∈ A) : r * m - h < a := by
    by_contra! low
    have ha' : a + h ≤ r * m := by omega
    have top : (r + 1) * a ≤ r * u := by
      have ineq := Nat.mul_le_mul_left (r + 1) ha'
      have eq := congrArg (fun k : ℕ => r * k) hu
      change r * (u + h) = r * ((r + 1) * m) at eq
      nlinarith only [ineq, eq, Nat.zero_le h]
    have hpos := (mem_Icc.mp (sub ha)).1
    obtain ⟨s, hsL, hsU, hdvd⟩ := multiple_in_interval hpos
      (Nat.mul_le_mul_left r hlu) overlap top
    obtain ⟨b, hb, heq⟩ := sums_of_few_holes B (inter_subset_left (s₂ := A))
      holes room hr s hsL hsU
    apply free a ha b (fun i => (mem_inter.mp (hb i)).2) _ (heq ▸ hdvd)
    intro i
    have hbi := (mem_Icc.mp (mem_inter.mp (hb i)).1).1
    change r * m + 1 ≤ b i at hbi
    omega
  have bound : A ∪ (T \ A) ⊆ Icc (r * m - h + 1) U := by
    intro x hx
    rcases mem_union.mp hx with ha | hh
    · exact mem_Icc.mpr ⟨above x ha, (mem_Icc.mp (sub ha)).2⟩
    · have hi := mem_Icc.mp (mem_sdiff.mp hh).1
      change r * m + 1 ≤ x ∧ x ≤ U at hi
      exact mem_Icc.mpr ⟨by omega, hi.2⟩
  have hc := card_le_card bound
  rw [card_union_of_disjoint disjoint_sdiff, Nat.card_Icc] at hc
  change A.card + h ≤ U + 1 - (r * m - h + 1) at hc
  omega

/-- For one summand, the odd part indexes disjoint chains of powers of two.
There are m possible odd parts in the interval from 1 to 2m. -/
lemma one_summand {m : ℕ} (A : Finset ℕ) (sub : A ⊆ Icc 1 (2 * m))
    (free : ∀ a ∈ A, ∀ b : Fin 1 → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) →
      ¬ a ∣ ∑ i, b i) : A.card ≤ m := by
  classical
  have fact (a : ℕ) : ∃ k j : ℕ, a = 0 ∨ a = 2 ^ k * (2 * j + 1) := by
    by_cases hz : a = 0
    · exact ⟨0, 0, Or.inl hz⟩
    · obtain ⟨k, t, ⟨j, hj⟩, ht⟩ := Nat.exists_eq_two_pow_mul_odd hz
      exact ⟨k, j, Or.inr (by simpa [hj] using ht)⟩
  choose k j hkj using fact
  have eqn (a) (ha : a ∈ A) : a = 2 ^ (k a) * (2 * j a + 1) :=
    (hkj a).resolve_left (by have := (mem_Icc.mp (sub ha)).1; omega)
  have primitive (a) (ha : a ∈ A) (b) (hb : b ∈ A) (hd : a ∣ b) : a = b := by
    have hab := Nat.le_of_dvd ((mem_Icc.mp (sub hb)).1) hd
    by_contra h
    exact free a ha (fun _ => b) (fun _ => hb) (fun _ => by omega) (by simpa using hd)
  have comp (a) (ha : a ∈ A) (b) (hb : b ∈ A) (hj : j a = j b) (hk : k a ≤ k b) : a = b := by
    apply primitive a ha b hb
    conv_lhs => rw [eqn a ha]
    conv_rhs => rw [eqn b hb]
    rw [hj]
    exact mul_dvd_mul_right (pow_dvd_pow 2 hk) _
  have hc : A.card ≤ (range m).card := by
    apply card_le_card_of_injOn j
    · intro a ha
      have h2 : 0 < 2 ^ k a := by positivity
      have hb := (mem_Icc.mp (sub ha)).2
      have he := eqn a ha
      apply mem_range.mpr
      have := Nat.mul_le_mul_right (2 * j a + 1) (show 1 ≤ 2 ^ k a by omega)
      omega
    · intro a ha b hb hj
      rcases le_total (k a) (k b) with hk | hk
      · exact comp a ha b hb hj hk
      · exact (comp b hb a ha hj.symm hk).symm
  simpa using hc

theorem main : H1 → H2 → type_of% @Erdos13.erdos_13.variants.general := by
  classical
  intro sparseStep intermediateStep r
  suffices blocks : ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ), A ⊆ Icc 1 ((r + 1) * m) →
      (∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) →
        ¬ a ∣ ∑ i, b i) → A.card ≤ m + K by
    obtain ⟨K, bound⟩ := blocks
    refine ⟨(K : ℝ) + 1, ?_⟩
    intro N A sub free
    let q := N / (r + 1)
    have cover : N ≤ (r + 1) * (q + 1) := by
      have hd := Nat.mod_add_div N (r + 1)
      have hm := Nat.mod_lt N (show 0 < r + 1 by omega)
      dsimp [q]
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have size := bound (q + 1) A (sub.trans (Icc_subset_Icc_right cover)) free
    have quotient : (q : ℝ) ≤ (N : ℝ) / ((r : ℝ) + 1) := by
      apply (le_div_iff₀ (by positivity : 0 < (r : ℝ) + 1)).mpr
      exact_mod_cast Nat.div_mul_le_self N (r + 1)
    have size' : (A.card : ℝ) ≤ (q : ℝ) + 1 + (K : ℝ) := by exact_mod_cast size
    linarith
  by_cases hz : r = 0
  · subst r
    refine ⟨0, ?_⟩
    intro m A sub _
    simpa using card_le_card sub
  by_cases ho : r = 1
  · subst r
    refine ⟨0, ?_⟩
    intro m A sub free
    simpa using one_summand A (by simpa using sub) free
  have hr : 2 ≤ r := by omega
  obtain ⟨K₁, smallTail⟩ := sparseStep r hr
  obtain ⟨K₂, middleTail⟩ := intermediateStep r hr
  refine ⟨K₁ + K₂, ?_⟩
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro A sub free
    by_contra! large
    by_cases record : ∀ j < m, m - j < (A.filter fun a => (r + 1) * j < a).card
    · have noWitness : ¬ ∃ a ∈ A, ∃ b : Fin r → ℕ,
          (∀ i, b i ∈ A ∧ a < b i) ∧ a ∣ ∑ i, b i := by
        rintro ⟨a, ha, b, hb, hd⟩
        exact free a ha b (fun i => (hb i).1) (fun i => (hb i).2) hd
      by_cases sparse : 2 * (Ioc (r * m) ((r + 1) * m) ∩ A).card ≤ m
      · exact noWitness (smallTail m A sub (by omega) record sparse)
      by_cases dense : (2 * r + 3) * (Ioc (r * m) ((r + 1) * m) \ A).card + (r + 2) ≤ m
      · have := dense_top_block hr A sub free dense
        omega
      · exact noWitness (middleTail m A sub (by omega) record (by omega) (by omega))
    · push Not at record
      obtain ⟨j, hj, suffix⟩ := record
      let P := A.filter fun a => ¬ (r + 1) * j < a
      have subP : P ⊆ Icc 1 ((r + 1) * j) := by
        intro a ha
        have h := mem_filter.mp ha
        exact mem_Icc.mpr ⟨(mem_Icc.mp (sub h.1)).1, le_of_not_gt h.2⟩
      have smallerBound := ih j hj P subP (by
        intro a ha b hb hlt
        exact free a (mem_filter.mp ha).1 b (fun i => (mem_filter.mp (hb i)).1) hlt)
      have count := A.card_filter_add_card_filter_not (fun a => (r + 1) * j < a)
      change _ + P.card = A.card at count
      omega

end OMA.R_Erdos13_erdos_13_variants_general_R1
