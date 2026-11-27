import FormalConjectures.Wikipedia.DedekindNumber

-- Problem: Dedekind Numbers — M eq kisielewiczFormula
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/DedekindNumber.lean:259 (declaration DedekindNumber.M_eq_kisielewiczFormula)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace W4Ded

open Finset Classical

/-- Bits of a sum of distinct powers of two. -/
lemma testBit_sum (T : Finset ℕ) (m : ℕ) : (∑ i ∈ T, 2 ^ i).testBit m = true ↔ m ∈ T := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, toFinset_bitIndices_sum_two_pow]

/-- Binary code of a subset of `Fin n`. -/
def c {n : ℕ} (s : Finset (Fin n)) : ℕ := ∑ i ∈ s.map Fin.valEmbedding, 2 ^ i

lemma tb_c {n : ℕ} (s : Finset (Fin n)) (m : ℕ) :
    (c s).testBit m = true ↔ ∃ x ∈ s, (x : ℕ) = m := by
  rw [c, testBit_sum]; simp

lemma c_lt {n : ℕ} (s : Finset (Fin n)) : c s < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_contra h
  rw [Bool.not_eq_false, tb_c] at h
  obtain ⟨x, _, rfl⟩ := h
  have := x.isLt
  omega

lemma c_inj {n : ℕ} : Function.Injective (c (n := n)) := by
  intro s t h
  ext x
  have h1 := tb_c s x
  have h2 := tb_c t x
  rw [h] at h1
  rw [h1] at h2
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := h2.1 ⟨x, hx, rfl⟩
    rwa [Fin.ext hyx] at hy
  · intro hx
    obtain ⟨y, hy, hyx⟩ := h2.2 ⟨x, hx, rfl⟩
    rwa [Fin.ext hyx] at hy

lemma c_surj {n i : ℕ} (hi : i < 2 ^ n) : ∃ s : Finset (Fin n), c s = i := by
  refine ⟨univ.filter (fun x : Fin n => i.testBit x = true), ?_⟩
  apply Nat.eq_of_testBit_eq
  intro m
  by_cases hm : m < n
  · rw [Bool.eq_iff_iff, tb_c]
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro h; exact ⟨⟨m, hm⟩, h, rfl⟩
  · push Not at hm
    have hp : 2 ^ n ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hi hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (c_lt _) hp)]

lemma c_sub {n : ℕ} (s t : Finset (Fin n)) :
    (∀ m, (c s).testBit m = true → (c t).testBit m = true) ↔ s ⊆ t := by
  constructor
  · intro h x hx
    obtain ⟨y, hy, hyx⟩ := (tb_c t x).1 (h x ((tb_c s x).2 ⟨x, hx, rfl⟩))
    rwa [Fin.ext hyx] at hy
  · intro h m hm
    obtain ⟨x, hx, rfl⟩ := (tb_c s m).1 hm
    exact (tb_c t _).2 ⟨x, h hx, rfl⟩

lemma c_mono {n : ℕ} {s t : Finset (Fin n)} (h : s ⊆ t) : c s ≤ c t := by
  unfold c
  exact Finset.sum_le_sum_of_subset (Finset.map_subset_map.2 h)

/-- Code of a family of subsets. -/
def φ {n : ℕ} (A : Finset (Finset (Fin n))) : ℕ := ∑ i ∈ A.image c, 2 ^ i

lemma tb_φ {n : ℕ} (A : Finset (Finset (Fin n))) (m : ℕ) :
    (φ A).testBit m = true ↔ ∃ s ∈ A, c s = m := by
  rw [φ, testBit_sum, mem_image]

lemma φ_lt {n : ℕ} (A : Finset (Finset (Fin n))) : φ A < 2 ^ (2 ^ n) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_contra h
  rw [Bool.not_eq_false, tb_φ] at h
  obtain ⟨s, _, rfl⟩ := h
  have := c_lt s
  omega

def good (n k : ℕ) : Prop :=
  ∀ j ∈ Icc 1 (2 ^ n), ∀ i ∈ range j,
    ¬ (k.testBit i = true ∧ k.testBit j = true ∧ ∀ m, i.testBit m = true → j.testBit m = true)

lemma good_iff {n : ℕ} (A : Finset (Finset (Fin n))) :
    good n (φ A) ↔ DedekindNumber.IsSperner A := by
  constructor
  · intro hg s hs t ht hne hst
    have hlt : c s < c t := lt_of_le_of_ne (c_mono hst) (fun h => hne (c_inj h))
    have hct := c_lt t
    exact hg (c t) (mem_Icc.2 ⟨by omega, hct.le⟩) (c s) (mem_range.2 hlt)
      ⟨(tb_φ A _).2 ⟨s, hs, rfl⟩, (tb_φ A _).2 ⟨t, ht, rfl⟩, (c_sub s t).2 hst⟩
  · rintro hA j _ i hi ⟨h1, h2, h3⟩
    obtain ⟨s, hs, rfl⟩ := (tb_φ A _).1 h1
    obtain ⟨t, ht, rfl⟩ := (tb_φ A _).1 h2
    have hst := (c_sub s t).1 h3
    have hne : s ≠ t := by
      rintro rfl
      simp at hi
    exact hA (Finset.mem_coe.2 hs) (Finset.mem_coe.2 ht) hne hst

lemma card_eq (n : ℕ) :
    (univ.filter (fun A : Finset (Finset (Fin n)) => DedekindNumber.IsSperner A)).card =
      ((range (2 ^ (2 ^ n))).filter (good n)).card := by
  apply Finset.card_bij (fun A _ => φ A)
  · intro A hA
    exact mem_filter.2 ⟨mem_range.2 (φ_lt A), (good_iff A).2 (mem_filter.1 hA).2⟩
  · intro A _ B _ h
    apply Finset.image_injective c_inj
    ext m
    have h1 := tb_φ A m
    have h2 := tb_φ B m
    rw [h] at h1
    rw [mem_image, mem_image, ← h1, h2]
  · intro k hk
    obtain ⟨hk1, hk2⟩ := mem_filter.1 hk
    rw [mem_range] at hk1
    set A := univ.filter (fun s : Finset (Fin n) => k.testBit (c s) = true) with hAdef
    have hφ : φ A = k := by
      apply Nat.eq_of_testBit_eq
      intro m
      by_cases hm : m < 2 ^ n
      · obtain ⟨s, rfl⟩ := c_surj hm
        rw [Bool.eq_iff_iff, tb_φ]
        constructor
        · rintro ⟨s', hs', he⟩
          rw [← c_inj he]
          exact (mem_filter.1 hs').2
        · intro h
          exact ⟨s, mem_filter.2 ⟨mem_univ _, h⟩, rfl⟩
      · push Not at hm
        have hp : 2 ^ (2 ^ n) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hk1 hp),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (φ_lt A) hp)]
    refine ⟨A, mem_filter.2 ⟨mem_univ _, (good_iff A).1 (hφ ▸ hk2)⟩, hφ⟩

lemma factor (i j k : ℕ) :
    (1 - (k.testBit i).toNat * (k.testBit j).toNat * ∏ m ∈ Finset.range (i.log2 + 1),
      (1 - (i.testBit m).toNat + (i.testBit m).toNat * (j.testBit m).toNat)) =
    if (k.testBit i = true ∧ k.testBit j = true ∧
      ∀ m, i.testBit m = true → j.testBit m = true) then 0 else 1 := by
  have hP : (∏ m ∈ Finset.range (i.log2 + 1),
      (1 - (i.testBit m).toNat + (i.testBit m).toNat * (j.testBit m).toNat)) =
      if (∀ m, i.testBit m = true → j.testBit m = true) then 1 else 0 := by
    by_cases h : ∀ m, i.testBit m = true → j.testBit m = true
    · rw [if_pos h]
      apply prod_eq_one
      intro m _
      have := h m
      cases h1 : i.testBit m <;> cases h2 : j.testBit m <;> simp_all
    · rw [if_neg h]
      push Not at h
      obtain ⟨m, h1, h2⟩ := h
      have hm : m ∈ Finset.range (i.log2 + 1) := by
        rw [mem_range]
        by_contra hc
        push Not at hc
        have := Nat.testBit_lt_two_pow
          (lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by norm_num) hc))
        rw [this] at h1
        exact absurd h1 (by simp)
      apply prod_eq_zero hm
      simp [h1, h2]
  rw [hP]
  split_ifs with h1 h2 <;> cases hb1 : k.testBit i <;> cases hb2 : k.testBit j <;> simp_all

lemma key (n k : ℕ) :
    (∏ j ∈ Finset.Icc 1 (2 ^ n), ∏ i ∈ Finset.range j,
      (1 - (k.testBit i).toNat * (k.testBit j).toNat * ∏ m ∈ Finset.range (i.log2 + 1),
        (1 - (i.testBit m).toNat + (i.testBit m).toNat * (j.testBit m).toNat))) =
    if good n k then 1 else 0 := by
  by_cases h : good n k
  · rw [if_pos h]
    apply prod_eq_one
    intro j hj
    apply prod_eq_one
    intro i hi
    rw [factor, if_neg (h j hj i hi)]
  · rw [if_neg h]
    unfold good at h
    push Not at h
    obtain ⟨j, hj, i, hi, hc⟩ := h
    apply prod_eq_zero hj
    apply prod_eq_zero hi
    rw [factor, if_pos hc]

end W4Ded

theorem OMA.solution : type_of% @DedekindNumber.M_eq_kisielewiczFormula := by
  rw [DedekindNumber.M_eq_M']
  funext n
  unfold DedekindNumber.M' DedekindNumber.kisielewiczFormula
  rw [Fintype.card_subtype]
  rw [Finset.sum_congr rfl (fun k _ => W4Ded.key n k)]
  classical
  rw [Finset.sum_boole, Nat.cast_id]
  convert W4Ded.card_eq n using 2
