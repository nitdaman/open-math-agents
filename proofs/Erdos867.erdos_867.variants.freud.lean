import FormalConjectures.ErdosProblems.«867»

/-! Freud's lower bound for consecutive - sum - free sets. -/

open Filter Finset

namespace Freud

private def band (a b p : ℕ) (R : Finset ℕ) : Finset ℕ :=
  (Ico a b).filter fun x => x % p ∈ R

private def base (k : ℕ) : Finset ℕ :=
  Ico (32 * k) (36 * k) ∪ band (48 * k) (54 * k) 3 {1, 2} ∪
    band (64 * k) (72 * k) 2 {0} ∪ Ico (72 * k) (96 * k) ∪
    band (96 * k) (108 * k) 3 {1, 2} ∪ Ico (108 * k) (128 * k) ∪
    band (128 * k) (144 * k) 4 {0, 1, 3}

private theorem mem_base (k x : ℕ) :
    x ∈ base k ↔
      (32 * k ≤ x ∧ x < 36 * k) ∨
      (48 * k ≤ x ∧ x < 54 * k ∧ x % 3 ≠ 0) ∨
      (64 * k ≤ x ∧ x < 72 * k ∧ x % 2 = 0) ∨
      (72 * k ≤ x ∧ x < 96 * k) ∨
      (96 * k ≤ x ∧ x < 108 * k ∧ x % 3 ≠ 0) ∨
      (108 * k ≤ x ∧ x < 128 * k) ∨
      (128 * k ≤ x ∧ x < 144 * k ∧ x % 4 ≠ 2) := by
  simp only [base, band, mem_union, mem_filter, mem_Ico, mem_insert, mem_singleton]
  omega

private theorem band_card (a p r : ℕ) (R : Finset ℕ) :
    (band a (a + p * r) p R).card = r * p.count (fun x => x % p ∈ R) := by
  induction r with
  | zero => simp [band]
  | succ r ih =>
    have h₁ : a ≤ a + p * r := Nat.le_add_right _ _
    have h₂ : a + p * r ≤ a + p * r + p := Nat.le_add_right _ _
    rw [Nat.mul_succ, ← Nat.add_assoc, band, ← Ico_union_Ico_eq_Ico h₁ h₂, filter_union,
      card_union_of_disjoint ((Ico_disjoint_Ico_consecutive a (a + p * r) (a + p * r + p)).mono
        (filter_subset _ _) (filter_subset _ _))]
    change (band a (a + p * r) p R).card + _ = _
    rw [ih, Nat.filter_Ico_card_eq_of_periodic _ _ _ (fun x => by simp [Nat.add_mod_right]),
      Nat.succ_mul]

private theorem union_card {A B : Finset ℕ} (c : ℕ)
    (hA : ∀ x ∈ A, x < c) (hB : ∀ x ∈ B, c ≤ x) :
    (A ∪ B).card = A.card + B.card :=
  card_union_of_disjoint (Finset.disjoint_left.mpr fun x hx hy => (hA x hx).not_ge (hB x hy))

private theorem base_card (k : ℕ) : (base k).card = 76 * k := by
  have h1 : (band (48 * k) (54 * k) 3 {1, 2}).card = 4 * k := by
    rw [show 54 * k = 48 * k + 3 * (2 * k) by omega, band_card]
    have h : Nat.count (fun x => x % 3 ∈ ({1, 2} : Finset ℕ)) 3 = 2 := by decide
    rw [h]
    omega
  have h2 : (band (64 * k) (72 * k) 2 {0}).card = 4 * k := by
    rw [show 72 * k = 64 * k + 2 * (4 * k) by omega, band_card]
    have h : Nat.count (fun x => x % 2 ∈ ({0} : Finset ℕ)) 2 = 1 := by decide
    rw [h, mul_one]
  have h4 : (band (96 * k) (108 * k) 3 {1, 2}).card = 8 * k := by
    rw [show 108 * k = 96 * k + 3 * (4 * k) by omega, band_card]
    have h : Nat.count (fun x => x % 3 ∈ ({1, 2} : Finset ℕ)) 3 = 2 := by decide
    rw [h]
    omega
  have h6 : (band (128 * k) (144 * k) 4 {0, 1, 3}).card = 12 * k := by
    rw [show 144 * k = 128 * k + 4 * (4 * k) by omega, band_card]
    have h : Nat.count (fun x => x % 4 ∈ ({0, 1, 3} : Finset ℕ)) 4 = 3 := by decide
    rw [h]
    omega
  unfold base
  rw [union_card (128 * k), union_card (108 * k), union_card (96 * k), union_card (72 * k),
    union_card (64 * k), union_card (48 * k), h1, h2, h4, h6]
  · simp only [Nat.card_Ico]
    omega
  all_goals
    intro x hx
    simp only [band, mem_union, mem_filter, mem_Ico] at hx
    omega

private def leftNear (A : Finset ℕ) (b : ℕ) : Finset ℕ :=
  A.filter fun x => x < b ∧ (A.filter fun y => x ≤ y ∧ y < b).card ≤ 4

private def rightNear (A : Finset ℕ) (b : ℕ) : Finset ℕ :=
  A.filter fun x => b ≤ x ∧ (A.filter fun y => b ≤ y ∧ y ≤ x).card ≤ 4

private theorem leftNear_card (A : Finset ℕ) (b : ℕ) : (leftNear A b).card ≤ 4 := by
  by_cases h : (leftNear A b).Nonempty
  · let x := (leftNear A b).min' h
    have hx : x ∈ leftNear A b := min'_mem _ _
    refine le_trans (card_le_card ?_) (mem_filter.mp hx).2.2
    intro y hy
    exact mem_filter.mpr ⟨(mem_filter.mp hy).1, min'_le _ _ hy, (mem_filter.mp hy).2.1⟩
  · simp [not_nonempty_iff_eq_empty.mp h]

private theorem rightNear_card (A : Finset ℕ) (b : ℕ) : (rightNear A b).card ≤ 4 := by
  by_cases h : (rightNear A b).Nonempty
  · let x := (rightNear A b).max' h
    have hx : x ∈ rightNear A b := max'_mem _ _
    refine le_trans (card_le_card ?_) (mem_filter.mp hx).2.2
    intro y hy
    exact mem_filter.mpr ⟨(mem_filter.mp hy).1, (mem_filter.mp hy).2.1, le_max' _ _ hy⟩
  · simp [not_nonempty_iff_eq_empty.mp h]

private theorem near_of_crossing {A : Finset ℕ} {b m n : ℕ}
    {u v : ℕ} (hu : u ∈ Icc m n ∩ A) (hv : v ∈ Icc m n ∩ A) (hb : u < b ∧ b ≤ v)
    (hc : (Icc m n ∩ A).card ≤ 4) :
    Icc m n ∩ A ⊆ leftNear A b ∪ rightNear A b := by
  have hu' := mem_Icc.mp (mem_inter.mp hu).1
  have hv' := mem_Icc.mp (mem_inter.mp hv).1
  intro x hx
  obtain ⟨hxi, hxA⟩ := mem_inter.mp hx
  have hxi' := mem_Icc.mp hxi
  by_cases hxb : x < b
  · apply mem_union_left
    refine mem_filter.mpr ⟨hxA, hxb, le_trans (card_le_card ?_) hc⟩
    intro y hy
    obtain ⟨hyA, hyx, hyb⟩ := mem_filter.mp hy
    exact mem_inter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hyA⟩
  · apply mem_union_right
    refine mem_filter.mpr ⟨hxA, by omega, le_trans (card_le_card ?_) hc⟩
    intro y hy
    obtain ⟨hyA, hyb, hyx⟩ := mem_filter.mp hy
    exact mem_inter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hyA⟩

-- Each short window crossing a cut is contained among the four nearest points on either side.
private def exceptional (k : ℕ) : Finset ℕ :=
  let H := [48 * k, 64 * k, 72 * k].toFinset.biUnion
    (fun b => leftNear (base k) b ∪ rightNear (base k) b)
  (H.powerset.image (fun s => ∑ x ∈ s, x)).filter fun x => 80 * k ≤ x

private theorem exceptional_card (k : ℕ) : (exceptional k).card ≤ 2 ^ 24 := by
  dsimp [exceptional]
  refine (card_filter_le _ _).trans (card_image_le.trans ?_)
  rw [card_powerset]
  change 2 ^ _ ≤ 2 ^ 24
  apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
  refine card_biUnion_le.trans ?_
  calc
    _ ≤ ∑ _b ∈ [48 * k, 64 * k, 72 * k].toFinset, 8 := by
      apply sum_le_sum
      intro b _
      exact (card_union_le _ _).trans (by
        have := leftNear_card (base k) b
        have := rightNear_card (base k) b
        omega)
    _ ≤ 24 := by
      rw [sum_const, nsmul_eq_mul, Nat.cast_id]
      have h : [48 * k, 64 * k, 72 * k].toFinset.card ≤ 3 := by
        simpa using List.toFinset_card_le [48 * k, 64 * k, 72 * k]
      omega

private theorem min_bound {k m n c : ℕ}
    (h : ∀ x ∈ Icc m n ∩ base k, c ≤ x) :
    (Icc m n ∩ base k).card * c ≤ ∑ x ∈ Icc m n ∩ base k, x := by
  simpa [nsmul_eq_mul] using card_nsmul_le_sum _ _ _ h

private theorem window {k m n : ℕ} (hk : 1 ≤ k)
    (hcard : 2 ≤ (Icc m n ∩ base k).card)
    (hz : (∑ x ∈ Icc m n ∩ base k, x) ∈ base k) :
    (∑ x ∈ Icc m n ∩ base k, x) ∈ exceptional k := by
  let T := Icc m n ∩ base k
  let z := ∑ x ∈ T, x
  change 2 ≤ T.card at hcard
  change z ∈ base k at hz
  change z ∈ exceptional k
  have hT : T.Nonempty := card_pos.mp (by omega)
  let u := T.min' hT
  let v := T.max' hT
  have hu : u ∈ T := min'_mem _ _
  have hv : v ∈ T := max'_mem _ _
  have huz := mem_Icc.mp (mem_inter.mp hu).1
  have hvz := mem_Icc.mp (mem_inter.mp hv).1
  have huB := (mem_base k u).mp (mem_inter.mp hu).2
  have hvB := (mem_base k v).mp (mem_inter.mp hv).2
  have hzB := (mem_base k z).mp hz
  have hlo (x : ℕ) (hx : x ∈ T) := min'_le T x hx
  have hhi (x : ℕ) (hx : x ∈ T) := le_max' T x hx
  have hlt : u < v := by
    by_contra! h
    have hc : T.card ≤ ({u} : Finset ℕ).card := card_le_card fun x hx => by
      have := hlo x hx
      have := hhi x hx
      simp only [mem_singleton]
      omega
    simp at hc
    omega
  have hpair : u + v ≤ z := by
    let P : Finset ℕ := {u, v}
    have hP : P ⊆ T := insert_subset_iff.mpr ⟨hu, singleton_subset_iff.mpr hv⟩
    simpa [P, sum_insert, hlt.ne] using
      (sum_le_sum_of_subset (f := fun x : ℕ => x) hP)
  have hs32 : T.card * (32 * k) ≤ z := min_bound fun x hx => by
    have := (mem_base k x).mp (mem_inter.mp hx).2
    omega
  have hfour : T.card ≤ 4 := by
    by_contra! h
    have := Nat.mul_le_mul_right (32 * k) (show 5 ≤ T.card by omega)
    omega
  by_contra hbad
  have nocross (b : ℕ) (hb : b ∈ [48 * k, 64 * k, 72 * k].toFinset) :
      ¬ (u < b ∧ b ≤ v) := by
    intro hc
    apply hbad
    have hlarge : 80 * k ≤ z := by
      simp at hb
      omega
    refine mem_filter.mpr ⟨mem_image.mpr ⟨T, mem_powerset.mpr ?_, rfl⟩, hlarge⟩
    exact (near_of_crossing hu hv hc hfour).trans fun x hx => mem_biUnion.mpr ⟨b, hb, hx⟩
  by_cases hv0 : v < 48 * k
  · have hu0 : 32 * k ≤ u := by omega
    have hv0' : v < 36 * k := by omega
    have hinterval : T = Ico u (v + 1) := by
      ext x
      constructor
      · intro hx
        exact mem_Ico.mpr ⟨hlo x hx, by have := hhi x hx; omega⟩
      · intro hx
        obtain ⟨hxu, hxv⟩ := mem_Ico.mp hx
        exact mem_inter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩,
          (mem_base k x).mpr (Or.inl ⟨by omega, by omega⟩)⟩
    have hc : T.card = v + 1 - u := by rw [hinterval, Nat.card_Ico]
    have hsum : z = ∑ j ∈ range T.card, (u + j) := by
      change ∑ x ∈ T, x = _
      rw [hc, hinterval, sum_Ico_eq_sum_range]
    have hcases : T.card = 2 ∨ T.card = 3 ∨ T.card = 4 := by omega
    rcases hcases with h2 | h3 | h4
    · simp only [h2, sum_range_succ, sum_range_zero] at hsum
      omega
    · simp only [h3, sum_range_succ, sum_range_zero] at hsum
      omega
    · simp only [h4, sum_range_succ, sum_range_zero] at hsum
      omega
  have hu1 : 48 * k ≤ u := by
    have := nocross (48 * k) (by simp)
    omega
  by_cases hv1 : v < 64 * k
  · have hu1' : u % 3 ≠ 0 := by omega
    have hv1' : v % 3 ≠ 0 := by omega
    have hv54 : v < 54 * k := by omega
    have hs48 : T.card * (48 * k) ≤ z := min_bound fun x hx => (hlo x hx).trans' hu1
    have htwo : T.card = 2 := by
      by_contra! h
      have := Nat.mul_le_mul_right (48 * k) (show 3 ≤ T.card by omega)
      omega
    have hp : ({u, v} : Finset ℕ) = T := by
      apply eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨hu, singleton_subset_iff.mpr hv⟩)
      simp [htwo, hlt.ne]
    have hsum : z = u + v := by
      change ∑ x ∈ T, x = _
      rw [← hp]
      simp [hlt.ne]
    have hnext (x : ℕ) (hx : u < x ∧ x < v) : x % 3 = 0 := by
      by_contra hx'
      have hxA : x ∈ base k := (mem_base k x).mpr (Or.inr (Or.inl ⟨by omega, by omega, hx'⟩))
      have hxT : x ∈ T := mem_inter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hxA⟩
      rw [← hp] at hxT
      simp at hxT
      omega
    have hvu : v ≤ u + 2 := by
      by_contra! h
      have := hnext (u + 1) (by omega)
      have := hnext (u + 2) (by omega)
      omega
    by_cases hu2 : u % 3 = 1
    · have hvu1 : v = u + 1 := by
        by_contra h
        have := hnext (u + 1) (by omega)
        omega
      omega
    · omega
  have hu2 : 64 * k ≤ u := by
    have := nocross (64 * k) (by simp)
    omega
  by_cases hv2 : v < 72 * k
  · have hue : u % 2 = 0 := by omega
    have hve : v % 2 = 0 := by omega
    have hs64 : T.card * (64 * k) ≤ z := min_bound fun x hx => (hlo x hx).trans' hu2
    have htwo : T.card = 2 := by
      by_contra! h
      have := Nat.mul_le_mul_right (64 * k) (show 3 ≤ T.card by omega)
      omega
    have hp : ({u, v} : Finset ℕ) = T := by
      apply eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨hu, singleton_subset_iff.mpr hv⟩)
      simp [htwo, hlt.ne]
    have hsum : z = u + v := by
      change ∑ x ∈ T, x = _
      rw [← hp]
      simp [hlt.ne]
    have hvu : v = u + 2 := by
      by_contra h
      have hxA : u + 2 ∈ base k := (mem_base k (u + 2)).mpr
        (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
      have hxT : u + 2 ∈ T := mem_inter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hxA⟩
      rw [← hp] at hxT
      simp at hxT
      omega
    omega
  have hu3 : 72 * k ≤ u := by
    have := nocross (72 * k) (by simp)
    omega
  omega

-- The two points just above the middle prevent deletions from creating new short sums.
private theorem clean (k : ℕ) (hk : 1 ≤ k) :
    Erdos867.ConsecutiveSumFree (base k \ exceptional k) := by
  intro m n hcard hz
  let T := Icc m n ∩ (base k \ exceptional k)
  let U := Icc m n ∩ base k
  let z := ∑ x ∈ T, x
  change 2 ≤ T.card at hcard
  change z ∈ base k \ exceptional k at hz
  have hz' := (mem_base k z).mp (mem_sdiff.mp hz).1
  have hsub : T ⊆ U := fun x hx =>
    mem_inter.mpr ⟨(mem_inter.mp hx).1, (mem_sdiff.mp (mem_inter.mp hx).2).1⟩
  have hlo : ∃ x ∈ T, x < 72 * k := by
    by_contra! h
    have hc := card_nsmul_le_sum T (fun x : ℕ => x) (72 * k) h
    simp at hc
    have := Nat.mul_le_mul_right (72 * k) hcard
    omega
  obtain ⟨x, hx, hxlo⟩ := hlo
  have hU : U ⊆ T := by
    intro y hy
    obtain ⟨hyI, hyB⟩ := mem_inter.mp hy
    refine mem_inter.mpr ⟨hyI, mem_sdiff.mpr ⟨hyB, ?_⟩⟩
    intro hyE
    have hybig : 80 * k ≤ y := (mem_filter.mp hyE).2
    have hxI := mem_Icc.mp (mem_inter.mp hx).1
    have hyI' := mem_Icc.mp hyI
    have hanchors (a : ℕ) (ha : 72 * k ≤ a ∧ a ≤ 72 * k + 1) : a ∈ T := by
      refine mem_inter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, mem_sdiff.mpr ⟨?_, ?_⟩⟩
      · exact (mem_base k a).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
      · intro hh
        have : 80 * k ≤ a := (mem_filter.mp hh).2
        omega
    have hh : ({72 * k, 72 * k + 1} : Finset ℕ) ⊆ T := by
      intro a ha
      simp at ha
      apply hanchors
      omega
    have hsum : 72 * k + (72 * k + 1) ≤ z := by
      simpa [sum_insert] using (sum_le_sum_of_subset (f := fun a : ℕ => a) hh)
    omega
  have heq := Subset.antisymm hsub hU
  have hcard' : 2 ≤ U.card := heq ▸ hcard
  have hzB : (∑ x ∈ U, x) ∈ base k := by rw [← heq]; exact (mem_sdiff.mp hz).1
  have hbad := window hk hcard' hzB
  change (∑ x ∈ U, x) ∈ exceptional k at hbad
  rw [← heq] at hbad
  exact (mem_sdiff.mp hz).2 hbad

end Freud

theorem OMA.solution : type_of% @Erdos867.erdos_867.variants.freud := by
  intro ε hε
  obtain ⟨L, hL⟩ := exists_nat_gt ((2 ^ 24 + 76 : ℝ) / ε)
  filter_upwards [eventually_ge_atTop (max 144 L)] with N hN
  let k := N / 144
  let A := Freud.base k \ Freud.exceptional k
  have hNk : 144 * k ≤ N := by dsimp [k]; omega
  have hNk' : N < 144 * (k + 1) := by dsimp [k]; omega
  have hk : 1 ≤ k := by dsimp [k]; omega
  refine ⟨A, ?_, Freud.clean k hk, ?_⟩
  · intro x hx
    have := (Freud.mem_base k x).mp (mem_sdiff.mp hx).1
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hsize : 76 * k ≤ A.card + 2 ^ 24 := by
    have hbase := card_le_card_sdiff_add_card (s := Freud.base k) (t := Freud.exceptional k)
    rw [Freud.base_card] at hbase
    exact hbase.trans (Nat.add_le_add_left (Freud.exceptional_card k) _)
  have hsizeR : 76 * (k : ℝ) ≤ (A.card : ℝ) + 2 ^ 24 := by exact_mod_cast hsize
  have hNkR : (N : ℝ) < 144 * ((k : ℝ) + 1) := by exact_mod_cast hNk'
  have hLN : (L : ℝ) ≤ N := by exact_mod_cast (show L ≤ N by omega)
  have hεN : 2 ^ 24 + 76 < ε * N := by
    have h := (div_lt_iff₀ hε).mp (hL.trans_le hLN)
    linarith
  linarith