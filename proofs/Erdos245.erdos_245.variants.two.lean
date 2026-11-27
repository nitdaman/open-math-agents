import FormalConjectures.ErdosProblems.«245»

/-! The problem is Erdős Problem 245, https://www.erdosproblems.com/245.
The proof uses the gap translations in Schnirelmann's sumset inequality,
as presented in Tao and Vu, Additive Combinatorics, Theorem 2.1.
An error term handles the initial prefixes that contain no positive element.
https://www.math.cmu.edu/~af1p/Teaching/AdditiveCombinatorics/Additive-Combinatorics.pdf
-/

open Filter Set
open scoped Pointwise Topology

namespace OMA

private noncomputable def truncation (A : Set ℕ) (n : ℕ) : Finset ℕ :=
  @Finset.filter ℕ (· ∈ A) (Classical.decPred _) (Finset.Ioc 0 n)

private lemma mem_prefix {A : Set ℕ} {n x : ℕ} :
    x ∈ truncation A n ↔ x ∈ A ∧ 0 < x ∧ x ≤ n := by
  simp [truncation, and_left_comm, and_comm]

private noncomputable def count (A : Set ℕ) (n : ℕ) : ℕ := (truncation A n).card

private lemma count_eq (A : Set ℕ) (n : ℕ) :
    count A n = (A ∩ Set.Icc 1 n).ncard := by
  rw [count, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp only [Finset.mem_coe, mem_prefix, Set.mem_inter_iff, Set.mem_Icc]
  constructor
  · rintro ⟨hA, h0, hn⟩
    exact ⟨hA, Nat.succ_le_of_lt h0, hn⟩
  · rintro ⟨hA, h1, hn⟩
    exact ⟨hA, Nat.lt_of_succ_le h1, hn⟩

private lemma count_mono (A : Set ℕ) : Monotone (count A) := by
  intro m n hmn
  exact Finset.card_le_card fun x hx =>
    let ⟨ha, hx0, hxm⟩ := mem_prefix.mp hx
    mem_prefix.mpr ⟨ha, hx0, hxm.trans hmn⟩

private lemma count_le_add (A : Set ℕ) (m n : ℕ) :
    count A n ≤ count A m + (n - m) := by
  have hsub : truncation A n ⊆ truncation A m ∪ Finset.Ioc m n := by
    intro x hx
    obtain ⟨ha, hx0, hxn⟩ := mem_prefix.mp hx
    by_cases hxle : x ≤ m
    · exact Finset.mem_union_left _ (mem_prefix.mpr ⟨ha, hx0, hxle⟩)
    · exact Finset.mem_union_right _ (Finset.mem_Ioc.mpr ⟨lt_of_not_ge hxle, hxn⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans_eq
    (by rw [Nat.card_Ioc, count]))

private lemma count_succ_of_mem {A : Set ℕ} {n : ℕ} (hn : n + 1 ∈ A) :
    count A (n + 1) = count A n + 1 := by
  have hprefix : truncation A (n + 1) = insert (n + 1) (truncation A n) := by
    ext x
    rw [mem_prefix, Finset.mem_insert, mem_prefix]
    constructor
    · rintro ⟨ha, hx0, hx⟩
      by_cases he : x = n + 1
      · exact Or.inl he
      · exact Or.inr ⟨ha, hx0, by omega⟩
    · rintro (rfl | ⟨ha, hx0, hx⟩)
      · exact ⟨hn, by omega, le_rfl⟩
      · exact ⟨ha, hx0, by omega⟩
  unfold count
  rw [hprefix, Finset.card_insert_of_notMem]
  exact fun h => by have := (mem_prefix.mp h).2.2; omega

private lemma count_zero (A : Set ℕ) : count A 0 = 0 := by
  rw [count_eq]
  simp

private lemma sum_count_gap {B : Set ℕ} {b n : ℕ} (hb : b ∈ B) (hbn : b ≤ n) :
    count (B + B) b + count B (n - b) ≤ count (B + B) n := by
  let F := truncation (B + B) b
  let G := (truncation B (n - b)).image (fun x => b + x)
  have hG : G.card = count B (n - b) :=
    Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)
  have hdisj : Disjoint F G := by
    refine Finset.disjoint_left.mpr fun a ha hu => ?_
    have hle := (mem_prefix.mp ha).2.2
    obtain ⟨x, hx, hax⟩ := Finset.mem_image.mp hu
    have hx0 := (mem_prefix.mp hx).2.1
    omega
  have hsub : F ∪ G ⊆ truncation (B + B) n := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨hm, ha0, hb'⟩ := mem_prefix.mp ha
      exact mem_prefix.mpr ⟨hm, ha0, hb'.trans hbn⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hm, hx0, hx⟩ := mem_prefix.mp hx
      exact mem_prefix.mpr ⟨Set.add_mem_add hb hm, by omega, by omega⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hG] at h
  exact h

/-- Translate an initial segment into each gap, with an error of at most αk per gap. -/
private lemma gap_bound {B : Set ℕ} [DecidablePred (· ∈ B)] {α : ℝ} {k N : ℕ}
    (h0 : 0 ∈ B) (hα : 0 ≤ α)
    (hprefix : ∀ n ≤ N, α * (n : ℝ) ≤ (count B n : ℝ) + α * (k : ℝ)) :
    ∀ n ≤ N, (count B n : ℝ) + α * ((n : ℝ) - count B n) ≤
      (count (B + B) n : ℝ) + α * (k : ℝ) * ((count B n : ℝ) + if n ∈ B then 0 else 1) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hαk : 0 ≤ α * (k : ℝ) := by positivity
    rcases n with _ | n
    · simp [count_zero, h0]
    · by_cases hb : n + 1 ∈ B
      · have hab : n + 1 ∈ B + B := by
          simpa only [zero_add] using Set.add_mem_add h0 hb
        have hh := ih n (by omega) (by omega)
        rw [if_pos hb, count_succ_of_mem hb, count_succ_of_mem hab]
        push_cast
        split_ifs at hh <;> nlinarith only [hh, hαk]
      · let P := (Finset.Icc 0 (n + 1)).filter (· ∈ B)
        have hP : P.Nonempty := ⟨0, by simp [P, h0]⟩
        let b := P.max' hP
        have hbP : b ∈ P := Finset.max'_mem _ _
        have hbB : b ∈ B := (Finset.mem_filter.mp hbP).2
        have hbn : b ≤ n + 1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hbP).1).2
        have hblt : b < n + 1 := lt_of_le_of_ne hbn (fun he => hb (he ▸ hbB))
        have hEq : count B (n + 1) = count B b := by
          apply le_antisymm _ ((count_mono B) hbn)
          apply Finset.card_le_card
          intro x hx
          obtain ⟨hxb, hx0, hxle⟩ := mem_prefix.mp hx
          have hxP : x ∈ P :=
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le x, hxle⟩, hxb⟩
          exact mem_prefix.mpr ⟨hxb, hx0, Finset.le_max' _ _ hxP⟩
        have hsum : (count (B + B) b : ℝ) + count B (n + 1 - b) ≤
            count (B + B) (n + 1) := by exact_mod_cast sum_count_gap hbB hbn
        have hgap := hprefix (n + 1 - b) (by omega)
        rw [Nat.cast_sub hbn] at hgap
        have hh := ih b hblt (by omega)
        rw [if_pos hbB] at hh
        rw [if_neg hb, hEq]
        nlinarith only [hh, hsum, hgap]

private def shifted (A : Set ℕ) (m : ℕ) : Set ℕ := {x | m + x ∈ A}

private lemma count_pos_of_mem {A : Set ℕ} {k n : ℕ} (hk : k ∈ A)
    (hk₀ : 0 < k) (hkn : k ≤ n) : 0 < count A n :=
  Finset.card_pos.mpr ⟨k, mem_prefix.mpr ⟨hk, hk₀, hkn⟩⟩

private lemma count_shift_le (A : Set ℕ) (m n : ℕ) :
    count (shifted A m) n ≤ count A (n + m) := by
  let f := fun x : ℕ => m + x
  have hf : Function.Injective f := fun _ _ h => Nat.add_left_cancel h
  have hsub : (truncation (shifted A m) n).image f ⊆ truncation A (n + m) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxA, hx₀, hxn⟩ := mem_prefix.mp hx
    exact mem_prefix.mpr ⟨hxA, by dsimp [f]; omega, by dsimp [f]; omega⟩
  exact (Finset.card_image_of_injective _ hf).symm.le.trans (Finset.card_le_card hsub)

private lemma count_unshift_le {A : Set ℕ} {m : ℕ} (hm : ∀ a ∈ A, m ≤ a) (n : ℕ) :
    count A (n + 2 * m) ≤ count (shifted A m) n + (m + 1) := by
  let f := fun x : ℕ => m + x
  have hf : Function.Injective f := fun _ _ h => Nat.add_left_cancel h
  have hsub : truncation A (n + m) ⊆ insert m ((truncation (shifted A m) n).image f) := by
    intro x hx
    obtain ⟨hxA, _, hxn⟩ := mem_prefix.mp hx
    by_cases hxm : x = m
    · exact Finset.mem_insert.mpr (Or.inl hxm)
    · have hxge := hm x hxA
      apply Finset.mem_insert.mpr
      right
      apply Finset.mem_image.mpr
      have hval : m + (x - m) = x := by omega
      have hshift : x - m ∈ shifted A m := by
        change m + (x - m) ∈ A
        rwa [hval]
      exact ⟨x - m, mem_prefix.mpr ⟨hshift, by omega, by omega⟩, hval⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  rw [Finset.card_image_of_injective _ hf] at hcard
  change count A (n + m) ≤ count (shifted A m) n + 1 at hcard
  have h := count_le_add A (n + m) (n + 2 * m)
  omega

private lemma count_shift_sum_le (A : Set ℕ) (m n : ℕ) :
    count (shifted A m + shifted A m) n ≤ count (A + A) (n + 2 * m) := by
  let f := fun x : ℕ => 2 * m + x
  have hf : Function.Injective f := fun _ _ h => Nat.add_left_cancel h
  have hsub : (truncation (shifted A m + shifted A m) n).image f ⊆
      truncation (A + A) (n + 2 * m) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxB, hx₀, hxn⟩ := mem_prefix.mp hx
    have hfx : f x ∈ A + A := by
      obtain ⟨a, ha, b, hb, he⟩ := Set.mem_add.mp hxB
      refine Set.mem_add.mpr ⟨m + a, ha, m + b, hb, ?_⟩
      dsimp [f]
      omega
    exact mem_prefix.mpr ⟨hfx, by dsimp [f]; omega, by dsimp [f]; omega⟩
  exact (Finset.card_image_of_injective _ hf).symm.le.trans (Finset.card_le_card hsub)

private lemma shifted_infinite {A : Set ℕ} {m : ℕ} (hA : A.Infinite)
    (hm : ∀ a ∈ A, m ≤ a) : (shifted A m).Infinite := by
  intro hB
  apply hA
  apply (hB.image (fun x => m + x)).subset
  intro x hx
  have hxm := hm x hx
  have he : m + (x - m) = x := by omega
  have hmem : x - m ∈ shifted A m := by
    change m + (x - m) ∈ A
    rwa [he]
  exact ⟨x - m, hmem, he⟩

private lemma count_unbounded {A : Set ℕ} (hA : A.Infinite) (k : ℕ) :
    ∃ n : ℕ, k ≤ count A n := by
  obtain ⟨S, hS, hSfin, hScard⟩ :=
    (hA.sdiff (Set.finite_singleton 0)).exists_subset_ncard_eq k
  obtain ⟨n, hn⟩ := hSfin.bddAbove
  have hsub : S ⊆ A ∩ Set.Icc 1 n := by
    intro x hx
    obtain ⟨hxA, hxne⟩ := hS hx
    have hx₀ : x ≠ 0 := hxne
    have hxn : x ≤ n := hn hx
    exact ⟨hxA, by exact ⟨by omega, hxn⟩⟩
  refine ⟨n, ?_⟩
  rw [count_eq, ← hScard]
  exact Set.ncard_le_ncard hsub ((Set.finite_Icc 1 n).subset Set.inter_subset_right)

private lemma density_shift (A : Set ℕ) (m : ℕ)
    (h : Tendsto (fun n : ℕ => (count A n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (count (shifted A m) n : ℝ) / n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (m : ℝ) / n) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop (m : ℝ)
  have hf : Tendsto (fun n : ℕ => (count A n : ℝ) / n + (m : ℝ) / n) atTop (𝓝 0) := by
    simpa only [add_zero] using h.add ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf
  · intro n
    positivity
  · intro n
    change (count (shifted A m) n : ℝ) / n ≤ (count A n : ℝ) / n + (m : ℝ) / n
    rw [← add_div]
    have hh : count (shifted A m) n ≤ count A n + m := by
      have h₁ := count_shift_le A m n
      have h₂ := count_le_add A n (n + m)
      omega
    exact div_le_div_of_nonneg_right (by exact_mod_cast hh) (by positivity)

private lemma late_record {B : Set ℕ} {k : ℕ} (hk : k ∈ B) (hk₀ : 0 < k)
    (h : Tendsto (fun n : ℕ => (count B n : ℝ) / n) atTop (𝓝 0))
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, N ≤ n ∧ k ≤ n ∧ (count B n : ℝ) / n < δ ∧
      ∀ i : ℕ, k ≤ i → i ≤ n → (count B n : ℝ) / n ≤ (count B i : ℝ) / i := by
  let M := max N k
  let q (n : ℕ) := (count B n : ℝ) / n
  have hev : ∀ᶠ n : ℕ in atTop, q n < min δ (1 / ((M : ℝ) + 1)) :=
    (tendsto_order.mp h).2 _ (lt_min hδ (by positivity))
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  let t := max T M
  have hkt : k ≤ t := (le_max_right N k).trans (le_max_right T M)
  obtain ⟨n, hn, hmin⟩ := Finset.exists_min_image (Finset.Icc k t) q
    ⟨t, Finset.mem_Icc.mpr ⟨hkt, le_rfl⟩⟩
  obtain ⟨hkn, hnt⟩ := Finset.mem_Icc.mp hn
  have hsmall := (hmin t (Finset.mem_Icc.mpr ⟨hkt, le_rfl⟩)).trans_lt
    (hT t (le_max_left T M))
  have hMn : M ≤ n := by
    by_contra hnM
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hk₀.trans_le hkn
    have hcast : (n : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast (show n ≤ M + 1 by omega)
    have hcnt : (1 : ℝ) ≤ count B n := by
      exact_mod_cast count_pos_of_mem hk hk₀ hkn
    have hv : 1 / ((M : ℝ) + 1) ≤ q n :=
      (div_le_div_of_nonneg_left (by norm_num) hnpos hcast).trans
        (div_le_div_of_nonneg_right hcnt hnpos.le)
    exact (hsmall.trans_le (min_le_right _ _)).not_ge hv
  refine ⟨n, (le_max_left N k).trans hMn, hkn, hsmall.trans_le (min_le_left _ _),
    fun i hki hin => hmin i (Finset.mem_Icc.mpr ⟨hki, hin.trans hnt⟩)⟩

private lemma arbitrarily_large_ratio {A : Set ℕ} (hA : A.Infinite)
    (hf : Tendsto (fun n : ℕ => (count A n : ℝ) / n) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (T : ℕ) :
    ∃ n : ℕ, T ≤ n ∧ 0 < count A n ∧
      (2 - ε) * (count A n : ℝ) ≤ (count (A + A) n : ℝ) := by
  classical
  let m := Nat.find hA.nonempty
  have hm : m ∈ A := Nat.find_spec hA.nonempty
  have hm_min (a : ℕ) (ha : a ∈ A) : m ≤ a := Nat.find_min' hA.nonempty ha
  let B := shifted A m
  have hB : B.Infinite := shifted_infinite hA hm_min
  have h0 : 0 ∈ B := by
    change m + 0 ∈ A
    simpa only [add_zero] using hm
  obtain ⟨k, hk, hk₀⟩ := (hB.sdiff (Set.finite_singleton 0)).nonempty
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk₀
  have hBden : Tendsto (fun n : ℕ => (count B n : ℝ) / n) atTop (𝓝 0) :=
    density_shift A m hf
  let δ : ℝ := ε / (2 * (2 * (k : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨H, hH⟩ := exists_nat_ge (4 * ((m : ℝ) + 1) / ε)
  obtain ⟨L, hL⟩ := count_unbounded hB H
  obtain ⟨n, hn, hkn, hsmall, hrecord⟩ := late_record hk hkpos hBden (max T L) hδ
  let α : ℝ := (count B n : ℝ) / n
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hkpos.trans_le hkn
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hαn : α * (n : ℝ) = count B n := div_mul_cancel₀ _ hnpos.ne'
  have hncount : 0 < count B n := count_pos_of_mem hk hkpos hkn
  have h1 : (1 : ℝ) ≤ count B n := by exact_mod_cast hncount
  have hprefix (i : ℕ) (hin : i ≤ n) : α * (i : ℝ) ≤ count B i + α * (k : ℝ) := by
    by_cases hki : k ≤ i
    · have hipos : 0 < (i : ℝ) := by exact_mod_cast hkpos.trans_le hki
      have hi := (le_div_iff₀ hipos).mp (hrecord i hki hin)
      exact hi.trans (le_add_of_nonneg_right (by positivity))
    · have hik : (i : ℝ) ≤ k := by exact_mod_cast (show i ≤ k by omega)
      exact (mul_le_mul_of_nonneg_left hik hα).trans (le_add_of_nonneg_left (by positivity))
  have hgap := gap_bound h0 hα hprefix n (le_refl n)
  have hαk : 0 ≤ α * (k : ℝ) := by positivity
  have hBbound : (2 - α) * (count B n : ℝ) ≤
      count (B + B) n + α * (k : ℝ) * ((count B n : ℝ) + 1) := by
    split_ifs at hgap <;> nlinarith only [hgap, hαn, hαk]
  have hαkc : α * (k : ℝ) ≤ α * (k : ℝ) * (count B n : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h1 hαk
  have hBstrong : (2 - α * (2 * (k : ℝ) + 1)) * (count B n : ℝ) ≤ count (B + B) n := by
    nlinarith only [hBbound, hαkc]
  have hαsmall : α * (2 * (k : ℝ) + 1) ≤ ε / 2 := by
    have hs : α < ε / (2 * (2 * (k : ℝ) + 1)) := hsmall
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * (2 * (k : ℝ) + 1))).mp hs
    linarith only [hh]
  have hblarge : (2 - ε / 2) * (count B n : ℝ) ≤ count (B + B) n :=
    (mul_le_mul_of_nonneg_right (sub_le_sub_left hαsmall _) (by positivity)).trans hBstrong
  have hHn : (H : ℝ) ≤ count B n := by
    exact_mod_cast hL.trans ((count_mono B) ((le_max_right T L).trans hn))
  have herror : 2 * ((m : ℝ) + 1) ≤ (ε / 2) * (count B n : ℝ) := by
    have hh := (div_le_iff₀ hε).mp (hH.trans hHn)
    nlinarith only [hh]
  have hshift : (count A (n + 2 * m) : ℝ) ≤ (count B n : ℝ) + ((m : ℝ) + 1) := by
    exact_mod_cast count_unshift_le hm_min n
  have hsum : (count (B + B) n : ℝ) ≤ (count (A + A) (n + 2 * m) : ℝ) := by
    exact_mod_cast count_shift_sum_le A m n
  have hcount : 0 < count A (n + 2 * m) := by
    have hkA : m + k ∈ A := hk
    exact count_pos_of_mem hkA (by omega) (by omega)
  refine ⟨n + 2 * m, (le_max_left T L).trans (hn.trans (by omega)), hcount, ?_⟩
  calc
    _ ≤ (2 - ε) * ((count B n : ℝ) + ((m : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hshift (by linarith)
    _ ≤ (2 - ε / 2) * (count B n : ℝ) := by
      have he : 0 ≤ ε * ((m : ℝ) + 1) := by positivity
      nlinarith only [herror, he]
    _ ≤ count (B + B) n := hblarge
    _ ≤ _ := hsum

end OMA

theorem OMA.solution : type_of% @Erdos245.erdos_245.variants.two := by
  intro A hA hf
  have hf_nat : Tendsto (fun n : ℕ => (OMA.count A n : ℝ) / n) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => ((A ∩ Set.Icc 1 ⌊(n : ℝ)⌋₊).ncard : ℝ) / n)
        atTop (𝓝 0) := hf.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Nat.floor_natCast, ← OMA.count_eq] using h
  let f (x : ℝ) : EReal :=
    (((A + A) ∩ Set.Icc 1 ⌊x⌋₊).ncard : EReal) / (A ∩ Set.Icc 1 ⌊x⌋₊).ncard
  change (2 : EReal) ≤ limsup f atTop
  by_contra h
  obtain ⟨b, hb₁, hb₂⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  have hb_lt : b < 2 := EReal.coe_lt_coe_iff.mp hb₂
  let ε : ℝ := min 1 ((2 - b) / 2)
  have hε : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε₁ : ε ≤ 1 := min_le_left _ _
  have hb : b ≤ 2 - ε := by
    have he : ε ≤ (2 - b) / 2 := min_le_right _ _
    linarith
  have hfreq : ∃ᶠ x : ℝ in atTop, (b : EReal) ≤ f x := by
    rw [frequently_atTop]
    intro R
    obtain ⟨T, hRT⟩ := exists_nat_ge R
    obtain ⟨n, hTn, hn, hratio⟩ := OMA.arbitrarily_large_ratio hA hf_nat hε hε₁ T
    refine ⟨(n : ℝ), hRT.trans (by exact_mod_cast hTn), ?_⟩
    have hn' : 0 < (OMA.count A n : ℝ) := by exact_mod_cast hn
    have hle : b ≤ (OMA.count (A + A) n : ℝ) / OMA.count A n :=
      hb.trans ((le_div_iff₀ hn').mpr hratio)
    have hcast : ((↑(OMA.count (A + A) n) / ↑(OMA.count A n) : ℝ) : EReal) = f (n : ℝ) := by
      simp only [f, Nat.floor_natCast, EReal.coe_div, EReal.coe_coe_eq_natCast, OMA.count_eq]
    exact (EReal.coe_le_coe_iff.mpr hle).trans_eq hcast
  exact (not_le_of_gt hb₁) (le_limsup_of_frequently_le hfreq)