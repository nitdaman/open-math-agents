import FormalConjectures.ErdosProblems.«211»

/-!
# A reduction of Erdős's one-sixth conjecture

Elementary pair counting handles maximum collinearities of at most three or at
least four ninths of the point set. Langer's and Melchior's inequalities together
cover maximum collinearities between one third and four ninths. The remaining
step is a weighted inequality between ordinary lines and lines with four or more points.
-/

-- Credit: @kenanwienberg

namespace OMA.R_Erdos211_erdos_211_variants_one_sixth_R1

open EuclideanGeometry Erdos211
open scoped BigOperators Classical

/-- The quadratic part of Langer's incidence bound. -/
def H1 : Prop :=
  ∀ s : Finset ℝ², 2 ≤ s.card →
    (∀ L : AffineSubspace ℝ ℝ², IsLine L →
      3 * (s.filter fun p => p ∈ L).card ≤ 2 * s.card) →
    (s.card : ℝ) ^ 2 ≤ 3 * ∑ L ∈ determinedLines s, ((s.filter fun p => p ∈ L).card : ℝ)

/-- The consequence of Melchior's inequality that the mean multiplicity is at most three. -/
def H2 : Prop :=
  ∀ s : Finset ℝ², 2 ≤ s.card →
    (∀ L : AffineSubspace ℝ ℝ², IsLine L → (s.filter fun p => p ∈ L).card < s.card) →
    (∑ L ∈ determinedLines s, ((s.filter fun p => p ∈ L).card : ℝ)) ≤
      3 * ((determinedLines s).card : ℝ)

/-- The residual pair-count inequality for configurations of maximum multiplicity
strictly between three and a third of the number of points. Each ordinary line
contributes minus four, each three-point line contributes zero, and each line of
multiplicity r at least four contributes (r - 3) * (r + 2). -/
def H3 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ (s : Finset ℝ²) (m : ℕ),
    N ≤ s.card → 4 ≤ m → 3 * m < s.card →
    (∀ L : AffineSubspace ℝ ℝ², IsLine L → (s.filter fun p => p ∈ L).card ≤ m) →
    (∑ L ∈ determinedLines s,
      (((s.filter fun p => p ∈ L).card : ℝ) - 3) *
        (((s.filter fun p => p ∈ L).card : ℝ) + 2)) ≤
      ((m : ℝ) - 1) * (s.card : ℝ) + δ * (s.card : ℝ) ^ 2

lemma ordered_pair_count_real (s : Finset ℝ²) (hs : 1 ≤ s.card) :
    (s.card : ℝ) * ((s.card : ℝ) - 1) =
      ∑ L ∈ determinedLines s,
        ((s.filter fun p => p ∈ L).card : ℝ) *
          (((s.filter fun p => p ∈ L).card : ℝ) - 1) := by
  calc
    (s.card : ℝ) * ((s.card : ℝ) - 1) = (↑(s.card * (s.card - 1)) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_sub hs, Nat.cast_one]
    _ = ∑ L ∈ determinedLines s,
        (↑((s.filter fun p => p ∈ L).card * ((s.filter fun p => p ∈ L).card - 1)) : ℝ) := by
      rw [ordered_pair_count, Nat.cast_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro L hL
      obtain ⟨a, ha, b, _, _, rfl⟩ := mem_determinedLines.mp hL
      have hpos : 1 ≤ (s.filter fun p => p ∈ line[ℝ, a, b]).card :=
        Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, left_mem_affineSpan_pair ℝ a b⟩⟩
      rw [Nat.cast_mul, Nat.cast_sub hpos, Nat.cast_one]

lemma max_line {s : Finset ℝ²} (hs : 2 ≤ s.card) :
    ∃ L ∈ determinedLines s, ∀ W : AffineSubspace ℝ ℝ², IsLine W →
      (s.filter fun p => p ∈ W).card ≤ (s.filter fun p => p ∈ L).card := by
  have hne : (determinedLines s).Nonempty := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
    exact ⟨_, mem_determinedLines.mpr ⟨a, ha, b, hb, hab, rfl⟩⟩
  obtain ⟨L, hL, hmax⟩ := Finset.exists_max_image (determinedLines s)
    (fun L => (s.filter fun p => p ∈ L).card) hne
  refine ⟨L, hL, fun W hW => ?_⟩
  by_cases hWdet : W ∈ determinedLines s
  · exact hmax W hWdet
  · have hWsmall : (s.filter fun p => p ∈ W).card ≤ 1 := by
      by_contra! hlarge
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlarge
      exact hWdet (mem_determinedLines.mpr ⟨a, (Finset.mem_filter.mp ha).1,
        b, (Finset.mem_filter.mp hb).1, hab,
        line_pair_eq hW (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab⟩)
    apply hWsmall.trans
    obtain ⟨a, ha, b, _, _, rfl⟩ := mem_determinedLines.mp hL
    exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, left_mem_affineSpan_pair ℝ a b⟩⟩

/-- Each mixed pair spans a line. Repeated uses of a line can be charged to
pairs of points off the given line. -/
lemma rich_line_bound (s : Finset ℝ²) (L : AffineSubspace ℝ ℝ²) (hL : IsLine L) :
    let m : ℝ := (s.filter fun p => p ∈ L).card
    let q : ℝ := (s.filter fun p => p ∉ L).card
    2 * m * q ≤ 2 * ((determinedLines s).card : ℝ) + q * (q - 1) := by
  dsimp only
  let A := s.filter fun p => p ∈ L
  let B := s.filter fun p => p ∉ L
  let lineOf : ℝ² × ℝ² → AffineSubspace ℝ ℝ² := fun p => line[ℝ, p.1, p.2]
  let mixed := A.product B
  have hmix : (mixed : Set (ℝ² × ℝ²)).MapsTo lineOf (determinedLines s) := by
    intro p hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hp)
    obtain ⟨ha, haL⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hbL⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_coe.mpr (mem_determinedLines.mpr
      ⟨p.1, ha, p.2, hb, fun h => hbL (h ▸ haL), rfl⟩)
  have houtside : (B.offDiag : Set (ℝ² × ℝ²)).MapsTo lineOf (determinedLines s) := by
    intro p hp
    obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp (Finset.mem_coe.mp hp)
    exact Finset.mem_coe.mpr (mem_determinedLines.mpr
      ⟨p.1, (Finset.mem_filter.mp ha).1, p.2, (Finset.mem_filter.mp hb).1, hab, rfl⟩)
  have hbound (W : AffineSubspace ℝ ℝ²) (hW : W ∈ determinedLines s) :
      (mixed.filter fun p => lineOf p = W).card ≤ (B.filter fun p => p ∈ W).card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro p hp
      obtain ⟨hcross, hspan⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨(Finset.mem_product.mp hcross).2, hspan ▸ right_mem_affineSpan_pair ℝ p.1 p.2⟩)
    · intro a ha b hb hab
      obtain ⟨hacross, haspan⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
      obtain ⟨hbcross, hbspan⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
      have haL := (Finset.mem_filter.mp (Finset.mem_product.mp hacross).1).2
      have hbL := (Finset.mem_filter.mp (Finset.mem_product.mp hbcross).1).2
      have haW : a.1 ∈ W := haspan ▸ left_mem_affineSpan_pair ℝ a.1 a.2
      have hbW : b.1 ∈ W := hbspan ▸ left_mem_affineSpan_pair ℝ b.1 b.2
      refine Prod.ext ?_ hab
      by_contra hne
      have hWL : W = L :=
        (line_pair_eq (isLine_of_mem_determinedLines hW) haW hbW hne).symm.trans
          (line_pair_eq hL haL hbL hne)
      have ha₂W : a.2 ∈ W := haspan ▸ right_mem_affineSpan_pair ℝ a.1 a.2
      exact (Finset.mem_filter.mp (Finset.mem_product.mp hacross).2).2 (hWL ▸ ha₂W)
  have hcount : 2 * (A.card * B.card) ≤
      2 * (determinedLines s).card + B.card * (B.card - 1) := by
    have hprod : mixed.card = A.card * B.card := Finset.card_product _ _
    have hpairs : B.offDiag.card = B.card * (B.card - 1) := by
      rw [Finset.offDiag_card, Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [← hprod, Finset.card_eq_sum_card_fiberwise hmix, ← hpairs,
      Finset.card_eq_sum_card_fiberwise houtside, Finset.mul_sum,
      Finset.card_eq_sum_ones (s := determinedLines s), Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun W hW => ?_
    change 2 * (mixed.filter fun p => lineOf p = W).card ≤
      2 * 1 + (B.offDiag.filter fun p => line[ℝ, p.1, p.2] = W).card
    rw [pair_fiber_eq (isLine_of_mem_determinedLines hW), Finset.offDiag_card]
    set r := (B.filter fun p => p ∈ W).card
    have hc := hbound W hW
    have hlocal : 2 * r ≤ 2 + (r * r - r) := by
      obtain hr | hr | hr : r = 0 ∨ r = 1 ∨ 2 ≤ r := by omega
      · simp [hr]
      · simp [hr]
      · calc
          2 * r ≤ 2 + 2 * (r - 1) := by omega
          _ ≤ 2 + r * (r - 1) := Nat.add_le_add_left (Nat.mul_le_mul_right (r - 1) hr) _
          _ = _ := by rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    omega
  change 2 * (A.card : ℝ) * (B.card : ℝ) ≤
    2 * ((determinedLines s).card : ℝ) + (B.card : ℝ) * ((B.card : ℝ) - 1)
  by_cases hB : 1 ≤ B.card
  · have hreal : (↑(2 * (A.card * B.card)) : ℝ) ≤
        (↑(2 * (determinedLines s).card + B.card * (B.card - 1)) : ℝ) :=
      Nat.cast_le.mpr hcount
    push_cast [Nat.cast_sub hB] at hreal
    simpa only [mul_assoc] using hreal
  · have hz : B.card = 0 := by omega
    simp [hz]

theorem main : H1 → H2 → H3 → type_of% @Erdos211.erdos_211.variants.one_sixth := by
  intro hIncidence hMelchior hDefect ε hε
  obtain ⟨N, hN⟩ := hDefect (2 * ε / 3) (by positivity)
  refine ⟨max N 2, fun n k hn hk hkn s hs hcap => ?_⟩
  subst n
  have hn₂ : 2 ≤ s.card := (le_max_right _ _).trans hn
  have hkn₁ : k ≤ s.card - 1 := by omega
  have hkn_real : (k : ℝ) ≤ (s.card : ℝ) - 1 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (show 1 ≤ s.card by omega)]
    exact Nat.cast_le.mpr hkn₁
  obtain ⟨L, hL, hmax⟩ := max_line hn₂
  let m := (s.filter fun p => p ∈ L).card
  have hLline := isLine_of_mem_determinedLines hL
  have hm_cap : m ≤ s.card - k := hcap L hLline
  have hmk : (m : ℝ) + (k : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast (show m + k ≤ s.card by omega)
  have hmul_nonneg : 0 ≤ (k : ℝ) * (s.card : ℝ) := by positivity
  have hgoal (hh : (k : ℝ) * (s.card : ℝ) ≤ 6 * ((determinedLines s).card : ℝ)) :
      (1 - ε) / 6 * (k : ℝ) * (s.card : ℝ) ≤ ((determinedLines s).card : ℝ) := by
    nlinarith only [hh, mul_nonneg hε.le hmul_nonneg]
  by_cases hsmall : m ≤ 3
  · apply hgoal
    have hcount := real_lower_bound_no_four (s := s) (fun W hW => (hmax W hW).trans hsmall)
    nlinarith only [hcount,
      mul_nonneg (sub_nonneg.mpr hkn_real) (Nat.cast_nonneg s.card : (0 : ℝ) ≤ s.card)]
  by_cases hrich : 4 * s.card ≤ 9 * m
  · apply hgoal
    let q := (s.filter fun p => p ∉ L).card
    have hpartition : m + q = s.card := Finset.card_filter_add_card_filter_not _
    have hpartition_real : (m : ℝ) + (q : ℝ) = (s.card : ℝ) := by exact_mod_cast hpartition
    have hq : (k : ℝ) ≤ (q : ℝ) := by linarith
    have hr : 4 * (s.card : ℝ) ≤ 9 * (m : ℝ) := by exact_mod_cast hrich
    have hbound := rich_line_bound s L hLline
    change 2 * (m : ℝ) * (q : ℝ) ≤
      2 * ((determinedLines s).card : ℝ) + (q : ℝ) * ((q : ℝ) - 1) at hbound
    have hq_nonneg : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hgap : 0 ≤ 6 * (m : ℝ) - 3 * (q : ℝ) - (s.card : ℝ) := by linarith
    nlinarith only [hbound, hq_nonneg, mul_nonneg hgap hq_nonneg,
      mul_nonneg (sub_nonneg.mpr hq) (Nat.cast_nonneg s.card : (0 : ℝ) ≤ s.card)]
  by_cases hmiddle : s.card ≤ 3 * m
  · apply hgoal
    have hinc := hIncidence s hn₂ (fun W hW => by have := hmax W hW; omega)
    have hmel := hMelchior s hn₂ (fun W hW => by have := hcap W hW; omega)
    have hmid : (s.card : ℝ) ≤ 3 * (m : ℝ) := by exact_mod_cast hmiddle
    have hk_bound : 0 ≤ 2 * (s.card : ℝ) - 3 * (k : ℝ) := by linarith
    nlinarith only [hinc, hmel,
      mul_nonneg hk_bound (Nat.cast_nonneg s.card : (0 : ℝ) ≤ s.card)]
  · have hdef := hN s m ((le_max_left _ _).trans hn) (by omega) (by omega) hmax
    have hpair := ordered_pair_count_real s (by omega)
    have hidentity :
        (∑ L ∈ determinedLines s, (((s.filter fun p => p ∈ L).card : ℝ) - 3) *
            (((s.filter fun p => p ∈ L).card : ℝ) + 2)) =
          (s.card : ℝ) * ((s.card : ℝ) - 1) - 6 * ((determinedLines s).card : ℝ) := by
      have hconst : (∑ _W ∈ determinedLines s, (6 : ℝ)) =
          6 * ((determinedLines s).card : ℝ) := by simp [mul_comm]
      rw [hpair, ← hconst, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro W _
      ring
    rw [hidentity] at hdef
    have hm_real : 3 * (m : ℝ) ≤ (s.card : ℝ) := by
      exact_mod_cast (show 3 * m ≤ s.card by omega)
    have hq_gap : 0 ≤ (s.card : ℝ) - (m : ℝ) - 2 * (s.card : ℝ) / 3 := by linarith
    have hsize : (0 : ℝ) ≤ s.card := Nat.cast_nonneg s.card
    rcases le_or_gt ε 1 with hε_le | hε_gt
    · have hq : (k : ℝ) ≤ (s.card : ℝ) - (m : ℝ) := by linarith
      have hqscale := mul_nonneg (sub_nonneg.mpr hε_le) (sub_nonneg.mpr hq)
      have hE := mul_nonneg (mul_nonneg hε.le hq_gap) hsize
      nlinarith only [hdef, mul_nonneg hqscale hsize, hE]
    · have hsign := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hε_gt.le) hmul_nonneg
      have hline_nonneg : (0 : ℝ) ≤ (determinedLines s).card := Nat.cast_nonneg _
      nlinarith only [hline_nonneg, hsign]

end OMA.R_Erdos211_erdos_211_variants_one_sixth_R1
