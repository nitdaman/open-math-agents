import FormalConjectures.ErdosProblems.«36»

/-!
This is the Motzkin–Ralston–Selfridge upper bound for Erdős Problem 36.

A balanced word of length 30 with at most six overlaps per shift gives the desired bound.
Expand each letter into a constant block and count overlaps separately in each residue class.
-/

-- Credit: @Genbox

open Filter Erdos36
open scoped Topology BigOperators

namespace MRS1956

private def ones : Finset ℤ := {4, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 19, 21, 22, 25}

private def zeros : Finset ℤ := {0, 1, 2, 3, 5, 6, 11, 13, 20, 23, 24, 26, 27, 28, 29}

private theorem word_partition :
    Disjoint ones zeros ∧ ones ∪ zeros = Finset.Ico 0 30 ∧
      ones.card = 15 ∧ zeros.card = 15 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem finite_overlap :
    ∀ k ∈ Finset.Icc (-29 : ℤ) 29, Overlap ones zeros k ≤ 6 := by
  decide +kernel

private theorem word_overlap (k : ℤ) : Overlap ones zeros k ≤ 6 := by
  by_cases hk : k ∈ Finset.Icc (-29 : ℤ) 29
  · exact finite_overlap k hk
  have hw : ∀ z, z ∈ ones ∨ z ∈ zeros → 0 ≤ z ∧ z < 30 := by
    intro z hz
    exact Finset.mem_Ico.mp (word_partition.2.1 ▸ Finset.mem_union.mpr hz)
  have hempty : ((ones.product zeros).filter fun p => p.1 - p.2 = k) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp hk'
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    have h₁ := hw p.1 (Or.inl hx)
    have h₂ := hw p.2 (Or.inr hy)
    apply hk
    exact Finset.mem_Icc.mpr (by omega)
  simp [Overlap, hempty]

private def blocks (b : ℤ) (A : Finset ℤ) : Finset ℤ :=
  (A.product (Finset.Ico 0 b)).image fun p => 1 + b * p.1 + p.2

private theorem block_div {b x r : ℤ} (hb : 0 < b) (hr : 0 ≤ r ∧ r < b) :
    (1 + b * x + r - 1) / b = x := by
  rw [show 1 + b * x + r - 1 = r + b * x by omega,
    Int.add_mul_ediv_left _ _ hb.ne', Int.ediv_eq_zero_of_lt hr.1 hr.2, zero_add]

private theorem block_mod {b x r : ℤ} (hr : 0 ≤ r ∧ r < b) :
    (1 + b * x + r - 1) % b = r := by
  rw [show 1 + b * x + r - 1 = r + b * x by omega,
    Int.add_mul_emod_self_left, Int.emod_eq_of_lt hr.1 hr.2]

private theorem mem_blocks {b z : ℤ} (hb : 0 < b) {A : Finset ℤ} :
    z ∈ blocks b A ↔ (z - 1) / b ∈ A := by
  constructor
  · intro hz
    obtain ⟨⟨x, r⟩, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx, hr⟩ := Finset.mem_product.mp hp
    rw [block_div hb (Finset.mem_Ico.mp hr)]
    exact hx
  · intro hz
    refine Finset.mem_image.mpr ⟨((z - 1) / b, (z - 1) % b), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨hz,
        Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hb.ne', Int.emod_lt_of_pos _ hb⟩⟩
    · change 1 + b * ((z - 1) / b) + (z - 1) % b = z
      have h := Int.emod_add_mul_ediv (z - 1) b
      omega

private theorem card_blocks {b : ℤ} (hb : 0 < b) (A : Finset ℤ) :
    (blocks b A).card = A.card * b.toNat := by
  unfold blocks
  have hInj : Set.InjOn (fun p : ℤ × ℤ => 1 + b * p.1 + p.2)
      (↑(A.product (Finset.Ico 0 b)) : Set (ℤ × ℤ)) := by
    intro p hp q hq h
    have hp' := Finset.mem_Ico.mp (Finset.mem_product.mp (Finset.mem_coe.mp hp)).2
    have hq' := Finset.mem_Ico.mp (Finset.mem_product.mp (Finset.mem_coe.mp hq)).2
    exact Prod.ext
      ((block_div hb hp').symm.trans ((congrArg (fun z : ℤ => (z - 1) / b) h).trans
        (block_div hb hq')))
      ((block_mod hp').symm.trans ((congrArg (fun z : ℤ => (z - 1) % b) h).trans
        (block_mod hq')))
  rw [Finset.card_image_of_injOn hInj, Finset.product_eq_sprod, Finset.card_product, Int.card_Ico, sub_zero]

private theorem blocks_partition {b : ℤ} (hb : 0 < b) :
    Disjoint (blocks b ones) (blocks b zeros) ∧
    blocks b ones ∪ blocks b zeros = Finset.Icc 1 (30 * b) := by
  constructor
  · rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    exact Finset.disjoint_left.mp word_partition.1
      ((mem_blocks hb).mp hz₁) ((mem_blocks hb).mp hz₂)
  · ext z
    rw [Finset.mem_union, mem_blocks hb, mem_blocks hb, ← Finset.mem_union,
      word_partition.2.1, Finset.mem_Ico, Finset.mem_Icc,
      Int.le_ediv_iff_mul_le hb, Int.ediv_lt_iff_lt_mul hb, zero_mul]
    omega

private theorem blocks_overlap {b : ℤ} (hb : 0 < b) (k : ℤ) :
    Overlap (blocks b ones) (blocks b zeros) k ≤ 6 * b.toNat := by
  let pairs := ((blocks b ones).product (blocks b zeros)).filter fun p => p.1 - p.2 = k
  let residue := fun p : ℤ × ℤ => (p.1 - 1) % b
  let quotients := fun p : ℤ × ℤ => ((p.1 - 1) / b, (p.2 - 1) / b)
  change pairs.card ≤ 6 * b.toNat
  rw [Finset.card_eq_sum_card_fiberwise (f := residue)
    (t := Finset.Ico 0 b) (fun _ _ =>
      Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hb.ne', Int.emod_lt_of_pos _ hb⟩)]
  calc
    _ ≤ ∑ _r ∈ Finset.Ico 0 b, 6 := by
      apply Finset.sum_le_sum
      intro r _
      -- The residue and shift determine a single difference between the block indices.
      let d := -((r - k) / b)
      have hCard : (pairs.filter fun p => residue p = r).card ≤ Overlap ones zeros d := by
        apply Finset.card_le_card_of_injOn quotients
        · intro p hp
          have ⟨hp', hr⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
          have ⟨hmem, hk⟩ := Finset.mem_filter.mp hp'
          have ⟨ha, hc⟩ := Finset.mem_product.mp hmem
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_product.mpr ⟨(mem_blocks hb).mp ha, (mem_blocks hb).mp hc⟩, ?_⟩
          have h := Int.emod_add_mul_ediv (p.1 - 1) b
          change (p.1 - 1) % b = r at hr
          have hRight : p.2 - 1 = (r - k) + b * ((p.1 - 1) / b) := by omega
          change (p.1 - 1) / b - (p.2 - 1) / b = d
          rw [hRight, Int.add_mul_ediv_left _ _ hb.ne']
          dsimp [d]
          omega
        · intro p hp q hq hpq
          have ⟨hp', hrp⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
          have ⟨hq', hrq⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
          have hpDiff := (Finset.mem_filter.mp hp').2
          have hqDiff := (Finset.mem_filter.mp hq').2
          have hDiv : (p.1 - 1) / b = (q.1 - 1) / b := congrArg Prod.fst hpq
          have hpEd := Int.emod_add_mul_ediv (p.1 - 1) b
          have hqEd := Int.emod_add_mul_ediv (q.1 - 1) b
          change (p.1 - 1) % b = r at hrp
          change (q.1 - 1) % b = r at hrq
          rw [hDiv] at hpEd
          exact Prod.ext (by omega) (by omega)
      exact hCard.trans (word_overlap d)
    _ = 6 * b.toNat := by simp [Int.card_Ico, Nat.mul_comm]

private theorem extended_overlap (A B C D : Finset ℤ) (k : ℤ) :
    Overlap (A ∪ C) (B ∪ D) k ≤ Overlap A B k + C.card + D.card := by
  let cut := fun X Y : Finset ℤ => (X.product Y).filter fun p => p.1 - p.2 = k
  have hsub : cut (A ∪ C) (B ∪ D) ⊆
      (cut A B ∪ cut C (B ∪ D)) ∪ cut (A ∪ C) D := by
    intro p hp
    obtain ⟨hmem, hk⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hmem
    rcases Finset.mem_union.mp ha with ha' | hc
    · rcases Finset.mem_union.mp hb with hb' | hd
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha', hb'⟩, hk⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hd⟩, hk⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc, hb⟩, hk⟩))
  have hC : (cut C (B ∪ D)).card ≤ C.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp q hq h
      have hpDiff := (Finset.mem_filter.mp hp).2
      have hqDiff := (Finset.mem_filter.mp hq).2
      exact Prod.ext h (by omega)
  have hD : (cut (A ∪ C) D).card ≤ D.card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
    · intro p hp q hq h
      have hpDiff := (Finset.mem_filter.mp hp).2
      have hqDiff := (Finset.mem_filter.mp hq).2
      exact Prod.ext (by omega) h
  change (cut (A ∪ C) (B ∪ D)).card ≤ (cut A B).card + C.card + D.card
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hC _)) hD))

private theorem finite_bound {n : ℕ} (hn : 15 ≤ n) : 5 * M n ≤ 2 * n + 140 := by
  let b := n / 15
  let s := n % 15
  let B : ℤ := b
  let S : ℤ := s
  have hb : 0 < B := by dsimp [B, b]; omega
  have hs : s < 15 := Nat.mod_lt _ (by decide)
  have hn' : n = 15 * b + s := by dsimp [b, s]; omega
  have hnZ : (n : ℤ) = 15 * B + S := by
    change (n : ℤ) = 15 * (b : ℤ) + (s : ℤ)
    exact_mod_cast hn'
  have hS : 0 ≤ S := by
    change (0 : ℤ) ≤ (s : ℤ)
    exact_mod_cast (Nat.zero_le s)
  let A := blocks B ones
  let C := blocks B zeros
  -- Append the same number of positions to each side of the partition.
  let P := Finset.Ioc (30 * B) (30 * B + S)
  let Q := Finset.Ioc (30 * B + S) (30 * B + 2 * S)
  have hcardP : P.card = s := by
    simp [P, Int.card_Ioc, show 30 * B + S - 30 * B = S by omega, S]
  have hcardQ : Q.card = s := by
    simp [Q, Int.card_Ioc, show 30 * B + 2 * S - (30 * B + S) = S by omega, S]
  have hAc : A.card = 15 * b := by
    simp [A, card_blocks hb, word_partition.2.2.1, B]
  have hCc : C.card = 15 * b := by
    simp [C, card_blocks hb, word_partition.2.2.2, B]
  have hU : A ∪ C = Finset.Icc 1 (30 * B) := (blocks_partition hb).2
  have hA {z : ℤ} (hz : z ∈ A) : 1 ≤ z ∧ z ≤ 30 * B :=
    Finset.mem_Icc.mp (hU ▸ Finset.mem_union_left _ hz)
  have hC {z : ℤ} (hz : z ∈ C) : 1 ≤ z ∧ z ≤ 30 * B :=
    Finset.mem_Icc.mp (hU ▸ Finset.mem_union_right _ hz)
  have hAP : Disjoint A P := Finset.disjoint_left.mpr fun _ hz hp => by
    have := hA hz
    have := Finset.mem_Ioc.mp hp
    omega
  have hCQ : Disjoint C Q := Finset.disjoint_left.mpr fun _ hz hq => by
    have := hC hz
    have := Finset.mem_Ioc.mp hq
    omega
  have hPart : Disjoint (A ∪ P) (C ∪ Q) := by
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    rcases Finset.mem_union.mp hz₁ with ha | hp <;>
      rcases Finset.mem_union.mp hz₂ with hc | hq
    · exact Finset.disjoint_left.mp (blocks_partition hb).1 ha hc
    · have := hA ha
      have := Finset.mem_Ioc.mp hq
      omega
    · have := hC hc
      have := Finset.mem_Ioc.mp hp
      omega
    · have := Finset.mem_Ioc.mp hp
      have := Finset.mem_Ioc.mp hq
      omega
  have hFull : (A ∪ P) ∪ (C ∪ Q) = Finset.Icc (1 : ℤ) (2 * n) := by
    ext z
    rw [show (A ∪ P) ∪ (C ∪ Q) = (A ∪ C) ∪ (P ∪ Q) by
      ac_rfl, hU, Finset.mem_union, Finset.mem_union, Finset.mem_Icc,
      Finset.mem_Ioc, Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hEqual : (A ∪ P).card = (C ∪ Q).card := by
    rw [Finset.card_union_of_disjoint hAP, Finset.card_union_of_disjoint hCQ,
      hAc, hCc, hcardP, hcardQ]
  have hMin : M n ≤ MaxOverlap (A ∪ P) (C ∪ Q) :=
    Nat.sInf_le ⟨A ∪ P, C ∪ Q, hPart, hFull, hEqual, rfl⟩
  have hMax : MaxOverlap (A ∪ P) (C ∪ Q) ≤ 6 * b + s + s := by
    apply ciSup_le
    intro k
    calc
      _ ≤ Overlap A C k + P.card + Q.card := extended_overlap A C P Q k
      _ ≤ _ := by
        rw [hcardP, hcardQ]
        exact Nat.add_le_add_right (Nat.add_le_add_right (by
          simpa [A, C, B] using blocks_overlap hb k) s) s
  have := hMin.trans hMax
  omega

end MRS1956

theorem OMA.solution : type_of% @Erdos36.minimum_overlap.variants.upper.MRS_1956 := by
  have hnonneg : ∀ n, 0 ≤ MinOverlapQuotient n := by
    intro n
    unfold MinOverlapQuotient
    positivity
  have hc : atTop.IsCoboundedUnder (· ≤ ·) MinOverlapQuotient :=
    IsCoboundedUnder.of_frequently_ge (Frequently.of_forall hnonneg)
  have hApprox : ∀ y : ℝ, 2 / 5 < y → ∀ᶠ n in atTop, MinOverlapQuotient n ≤ y := by
    intro y hy
    obtain ⟨N, hN⟩ := exists_nat_gt (28 / (y - 2 / 5))
    filter_upwards [eventually_ge_atTop (max 15 N)] with n hn
    have hn15 : 15 ≤ n := (le_max_left ..).trans hn
    have hnN : N ≤ n := (le_max_right ..).trans hn
    have hbound : 5 * (M n : ℝ) ≤ 2 * (n : ℝ) + 140 := by
      exact_mod_cast MRS1956.finite_bound hn15
    have hErr : 28 < (n : ℝ) * (y - 2 / 5) :=
      (div_lt_iff₀ (sub_pos.mpr hy)).mp (hN.trans_le (by exact_mod_cast hnN))
    have hnPos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    unfold MinOverlapQuotient
    apply (div_le_iff₀ hnPos).mpr
    linarith
  have hb : atTop.IsBoundedUnder (· ≤ ·) MinOverlapQuotient :=
    isBoundedUnder_of_eventually_le (hApprox 1 (by norm_num))
  exact (limsup_le_iff' hc hb).mpr hApprox