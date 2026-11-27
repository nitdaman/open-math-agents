import FormalConjectures.ErdosProblems.«757»

/-! A finite certificate for the strict upper bound in Erdős problem 757. -/

open scoped Pointwise
namespace SidonWitness

-- The fourteen-point block of Ma and Tang, arXiv:2602.23282, Lemma 5.1.
private def block : Finset ℤ :=
  {0, 136, 200, 243, 246, 249, 272, 286, 298, 323, 400, 528, 596, 1056}

private theorem block_card : block.card = 14 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem four_check :
    ∀ t ∈ block.powersetCard 4, 11 ≤ (t - t).card := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem nine_check : ∀ t ∈ block.powersetCard 9,
    ∃ x ∈ t, ∃ y ∈ t, x < y ∧ 2 * y - x ∈ t := by decide +kernel

private def realBlock : Set ℝ := (fun z : ℤ => (z : ℝ)) '' (block : Set ℤ)

private theorem cast_inj : Function.Injective (fun z : ℤ => (z : ℝ)) :=
  Int.cast_injective

private theorem realBlock_card : realBlock.ncard = 14 := by
  rw [realBlock, Set.ncard_image_of_injective _ cast_inj, Set.ncard_coe_finset, block_card]

private theorem lift_subset {s : Set ℝ} (hs : s ⊆ realBlock) :
    ∃ t : Finset ℤ, t ⊆ block ∧ s = (fun z : ℤ => (z : ℝ)) '' (t : Set ℤ) := by
  classical
  refine ⟨block.filter (fun z => (z : ℝ) ∈ s), Finset.filter_subset _ _, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := hs hx
    exact ⟨z, Finset.mem_filter.mpr ⟨hz, hx⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact (Finset.mem_filter.mp hz).2

private theorem four_diffs (s : Set ℝ) (hs : s ⊆ realBlock) (hc : s.ncard = 4) :
    11 ≤ (s - s).ncard := by
  obtain ⟨t, ht, rfl⟩ := lift_subset hs
  rw [Set.ncard_image_of_injective _ cast_inj, Set.ncard_coe_finset] at hc
  have hcast : (fun z : ℤ => (z : ℝ)) '' ((t - t : Finset ℤ) : Set ℤ) =
      ((fun z : ℤ => (z : ℝ)) '' (t : Set ℤ)) - ((fun z : ℤ => (z : ℝ)) '' (t : Set ℤ)) := by
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hd
      exact ⟨a, ⟨a, ha, rfl⟩, b, ⟨b, hb, rfl⟩, (Int.cast_sub a b).symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a-b, Finset.mem_sub.mpr ⟨a, ha, b, hb, rfl⟩, Int.cast_sub a b⟩
  rw [← hcast, Set.ncard_image_of_injective _ cast_inj, Set.ncard_coe_finset]
  exact four_check t (Finset.mem_powersetCard.mpr ⟨ht, hc⟩)

private theorem sidon_bound (s : Set ℝ) (hs : s ⊆ realBlock) (hSidon : IsSidon s) :
    s.ncard ≤ 8 := by
  obtain ⟨t, ht, rfl⟩ := lift_subset hs
  rw [Set.ncard_image_of_injective _ cast_inj, Set.ncard_coe_finset]
  by_contra! h
  obtain ⟨u, hu, huc⟩ := Finset.exists_subset_card_eq (show 9 ≤ t.card by omega)
  obtain ⟨x, hx, y, hy, hxy, hz⟩ := nine_check u
    (Finset.mem_powersetCard.mpr ⟨hu.trans ht, huc⟩)
  have member (z : ℤ) (hz : z ∈ u) :
      (z : ℝ) ∈ (fun w : ℤ => (w : ℝ)) '' (t : Set ℤ) := ⟨z, hu hz, rfl⟩
  have he : (x : ℝ) + ((2 * y - x : ℤ) : ℝ) = y + y := by push_cast; ring
  have hne : (x : ℝ) ≠ y := by exact_mod_cast hxy.ne
  rcases hSidon _ (member x hx) _ (member y hy) _ (member _ hz) _ (member y hy) he with hh | hh <;>
    exact hne hh.1

private theorem admissible_zero : Erdos757.IsAdmissible 0 := by
  intro A _ _
  refine ⟨∅, Set.empty_subset _, ?_, by simp⟩
  simp [IsSidon]

end SidonWitness

open SidonWitness in
theorem OMA.solution : type_of% @Erdos757.erdos_757.variants.upperBound := by
  intro A
  have hnon : {c : ℝ | Erdos757.IsAdmissible c}.Nonempty := ⟨0, @admissible_zero⟩
  apply lt_of_le_of_lt (csSup_le hnon ?_) (show (4/7 : ℝ) < 3/5 by norm_num)
  intro c hc
  change Erdos757.IsAdmissible c at hc
  obtain ⟨s, hs, hSidon, hlarge⟩ := hc (A := realBlock) (block.finite_toSet.image _) four_diffs
  have hsmall : (s.ncard : ℝ) ≤ 8 := by exact_mod_cast sidon_bound s hs hSidon
  change c * realBlock.ncard ≤ _ at hlarge
  rw [realBlock_card] at hlarge
  norm_num at hlarge
  linarith