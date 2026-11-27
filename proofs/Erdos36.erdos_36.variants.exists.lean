import FormalConjectures.ErdosProblems.«36»

/-! Repeating each letter of a balanced word in long blocks shows that the
minimum overlap quotient converges to its infimum. The hexadecimal word below
has 16,384 letters of each color. The digits of a product count every directed
overlap, with no carry because the base exceeds the total number of pairs.
The kernel checks that all of these digits are at most 6,319. -/

open Filter Erdos36
open scoped Topology BigOperators

namespace OverlapLimit

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

private theorem blocks_partition {b : ℤ} (hb : 0 < b) {ones zeros : Finset ℤ}
    {L : ℤ} (hdisj : Disjoint ones zeros) (hpartition : ones ∪ zeros = Finset.Ico 0 L) :
    Disjoint (blocks b ones) (blocks b zeros) ∧
    blocks b ones ∪ blocks b zeros = Finset.Icc 1 (L * b) := by
  constructor
  · rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    exact Finset.disjoint_left.mp hdisj
      ((mem_blocks hb).mp hz₁) ((mem_blocks hb).mp hz₂)
  · ext z
    rw [Finset.mem_union, mem_blocks hb, mem_blocks hb, ← Finset.mem_union,
      hpartition, Finset.mem_Ico, Finset.mem_Icc,
      Int.le_ediv_iff_mul_le hb, Int.ediv_lt_iff_lt_mul hb, zero_mul]
    omega

private theorem blocks_overlap {b : ℤ} (hb : 0 < b) {ones zeros : Finset ℤ} {c : ℕ}
    (word_overlap : ∀ k : ℤ, Overlap ones zeros k ≤ c) (k : ℤ) :
    Overlap (blocks b ones) (blocks b zeros) k ≤ c * b.toNat := by
  let pairs := ((blocks b ones).product (blocks b zeros)).filter fun p => p.1 - p.2 = k
  let residue := fun p : ℤ × ℤ => (p.1 - 1) % b
  let quotients := fun p : ℤ × ℤ => ((p.1 - 1) / b, (p.2 - 1) / b)
  change pairs.card ≤ c * b.toNat
  rw [Finset.card_eq_sum_card_fiberwise (f := residue)
    (t := Finset.Ico 0 b) (fun _ _ =>
      Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hb.ne', Int.emod_lt_of_pos _ hb⟩)]
  calc
    _ ≤ ∑ _r ∈ Finset.Ico 0 b, c := by
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
    _ = c * b.toNat := by simp [Int.card_Ico, Nat.mul_comm]

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

private theorem finite_bound {m n c : ℕ} (hm : 0 < m) (hn : m ≤ n)
    {ones zeros : Finset ℤ} (hdisj : Disjoint ones zeros)
    (hpartition : ones ∪ zeros = Finset.Ico 0 (2 * m : ℤ)) (hsame : ones.card = zeros.card)
    (word_overlap : ∀ k : ℤ, Overlap ones zeros k ≤ c) :
    M n ≤ c * (n / m) + 2 * (n % m) := by
  let b := n / m
  let s := n % m
  let B : ℤ := b
  let S : ℤ := s
  have hb : 0 < B := by
    change 0 < (b : ℤ)
    exact_mod_cast (Nat.div_pos hn hm : 0 < b)
  have hn' : n = m * b + s := (Nat.div_add_mod n m).symm
  have hnZ : (n : ℤ) = (m : ℤ) * B + S := by
    change (n : ℤ) = (m : ℤ) * (b : ℤ) + (s : ℤ)
    exact_mod_cast hn'
  have hS : 0 ≤ S := by
    change (0 : ℤ) ≤ (s : ℤ)
    exact_mod_cast (Nat.zero_le s)
  let L := (2 * (m : ℤ)) * B
  have hL : 2 * (n : ℤ) = L + 2 * S := by rw [hnZ]; dsimp [L]; ring
  let A := blocks B ones
  let C := blocks B zeros
  -- Append the same number of positions to each side of the partition.
  let P := Finset.Ioc (L) (L + S)
  let Q := Finset.Ioc (L + S) (L + 2 * S)
  have hcardP : P.card = s := by
    simp [P, Int.card_Ioc, show L + S - L = S by omega, S]
  have hcardQ : Q.card = s := by
    simp [Q, Int.card_Ioc, show L + 2 * S - (L + S) = S by omega, S]
  have hAc : A.card = ones.card * b := by
    simp [A, card_blocks hb, B]
  have hCc : C.card = ones.card * b := by
    simp [C, card_blocks hb, B, hsame]
  have hU : A ∪ C = Finset.Icc 1 (L) := (blocks_partition hb hdisj hpartition).2
  have hA {z : ℤ} (hz : z ∈ A) : 1 ≤ z ∧ z ≤ L :=
    Finset.mem_Icc.mp (hU ▸ Finset.mem_union_left _ hz)
  have hC {z : ℤ} (hz : z ∈ C) : 1 ≤ z ∧ z ≤ L :=
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
    · exact Finset.disjoint_left.mp (blocks_partition hb hdisj hpartition).1 ha hc
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
  have hMax : MaxOverlap (A ∪ P) (C ∪ Q) ≤ c * b + s + s := by
    apply ciSup_le
    intro k
    calc
      _ ≤ Overlap A C k + P.card + Q.card := extended_overlap A C P Q k
      _ ≤ _ := by
        rw [hcardP, hcardQ]
        exact Nat.add_le_add_right (Nat.add_le_add_right (by
          simpa [A, C, B] using blocks_overlap hb word_overlap k) s) s
  exact (hMin.trans hMax).trans_eq (by change c * b + s + s = c * b + 2 * s; omega)

private theorem eventually_quotient_lt {m c : ℕ} (hm : 0 < m)
    {ones zeros : Finset ℤ} (hdisj : Disjoint ones zeros)
    (hpartition : ones ∪ zeros = Finset.Ico 0 (2 * m : ℤ)) (hsame : ones.card = zeros.card)
    (word_overlap : ∀ k : ℤ, Overlap ones zeros k ≤ c)
    {y : ℝ} (hy : (c : ℝ) / m < y) :
    ∀ᶠ n in atTop, MinOverlapQuotient n < y := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (m : ℝ) / (y - (c : ℝ) / m))
  filter_upwards [eventually_ge_atTop (max m N)] with n hn
  have hnm : m ≤ n := (le_max_left ..).trans hn
  have hnN : N ≤ n := (le_max_right ..).trans hn
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hm.trans_le hnm
  have hBound : (M n : ℝ) ≤ c * (↑(n / m) : ℝ) + 2 * (↑(n % m) : ℝ) := by
    exact_mod_cast finite_bound hm hnm hdisj hpartition hsame word_overlap
  have hRem : (↑(n % m) : ℝ) ≤ m := by exact_mod_cast (Nat.mod_lt n hm).le
  have hMul : (↑(n / m) : ℝ) * m ≤ n := by exact_mod_cast Nat.div_mul_le_self n m
  have hProd : (c : ℝ) * (↑(n / m) : ℝ) ≤ (c : ℝ) / m * n := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hmR).mpr
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hMul (Nat.cast_nonneg c : 0 ≤ (c : ℝ))
  have hErr : 2 * (m : ℝ) < (n : ℝ) * (y - (c : ℝ) / m) :=
    (div_lt_iff₀ (sub_pos.mpr hy)).mp (hN.trans_le (by exact_mod_cast hnN))
  unfold MinOverlapQuotient
  apply (div_lt_iff₀ hnR).mpr
  linarith [show (n : ℝ) * (y - (c : ℝ) / m) =
    (n : ℝ) * y - (c : ℝ) / m * n by ring]

private def shiftDown : ℤ ↪ ℤ where
  toFun x := x - 1
  inj' := by
    intro x y he
    change x - 1 = y - 1 at he
    omega

private theorem overlap_shiftDown (A B : Finset ℤ) (k : ℤ) :
    Overlap (A.map shiftDown) (B.map shiftDown) k = Overlap A B k := by
  unfold Overlap
  refine Finset.card_bij'
    (fun p _ => (p.1 + 1, p.2 + 1)) (fun p _ => (p.1 - 1, p.2 - 1)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpa, hpb⟩ := Finset.mem_product.mp hp
    obtain ⟨a, ha, hea⟩ := Finset.mem_map.mp hpa
    obtain ⟨b, hb, heb⟩ := Finset.mem_map.mp hpb
    change a - 1 = p.1 at hea
    change b - 1 = p.2 at heb
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨by
      rwa [show p.1 + 1 = a by omega], by rwa [show p.2 + 1 = b by omega]⟩, by dsimp; omega⟩
  · intro p hp
    obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨
      Finset.mem_map.mpr ⟨p.1, ha, rfl⟩, Finset.mem_map.mpr ⟨p.2, hb, rfl⟩⟩, by dsimp; omega⟩
  · intro p _
    exact Prod.ext (by simp) (by simp)
  · intro p _
    exact Prod.ext (by simp) (by simp)

private theorem bdd_overlap (A B : Finset ℤ) : BddAbove (Set.range (Overlap A B)) := by
  use (A.product B).card
  rintro x ⟨k, rfl⟩
  exact Finset.card_filter_le _ _

private theorem exists_min_partition (m : ℕ) :
    ∃ A B : Finset ℤ, Disjoint A B ∧ A ∪ B = Finset.Icc 1 (2 * m : ℤ) ∧
      A.card = B.card ∧ MaxOverlap A B = M m := by
  let T : Set ℕ := {MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
    (_disjoint : Disjoint A B) (_union : A ∪ B = Finset.Icc 1 (2 * m : ℤ))
    (_same_card : A.card = B.card)}
  have hT : T.Nonempty := by
    refine ⟨_, Finset.Icc 1 (m : ℤ), Finset.Ioc (m : ℤ) (2 * m : ℤ), ?_, ?_, ?_, rfl⟩
    · rw [Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨_, hz⟩ := Finset.mem_Icc.mp hz
      obtain ⟨hz', _⟩ := Finset.mem_Ioc.mp hz'
      omega
    · ext z
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    · rw [Int.card_Icc, Int.card_Ioc]
      congr 1
      omega
  obtain ⟨A, B, hd, hu, hc, he⟩ := (show M m ∈ T from csInf_mem hT)
  exact ⟨A, B, hd, hu, hc, he⟩

private theorem eventually_lt_of_value_lt {m : ℕ} (hm : 0 < m) {y : ℝ}
    (hy : MinOverlapQuotient m < y) : ∀ᶠ n in atTop, MinOverlapQuotient n < y := by
  obtain ⟨A, B, hdisj, hparts, hsame, hmin⟩ := exists_min_partition m
  have hpartShift : A.map shiftDown ∪ B.map shiftDown = Finset.Ico 0 (2 * m : ℤ) := by
    rw [← Finset.map_union, hparts]
    ext x
    simp only [Finset.mem_map, Finset.mem_Icc, Finset.mem_Ico]
    constructor
    · rintro ⟨z, hz, hzx⟩
      change z - 1 = x at hzx
      omega
    · intro hx
      exact ⟨x + 1, by omega, by change x + 1 - 1 = x; omega⟩
  apply eventually_quotient_lt hm ((Finset.disjoint_map shiftDown).mpr hdisj) hpartShift
    (by simpa only [Finset.card_map] using hsame) (c := M m) _ hy
  intro k
  rw [overlap_shiftDown, ← hmin]
  exact le_ciSup (bdd_overlap A B) k

noncomputable def limit : ℝ := sInf {y | ∃ n : ℕ, 0 < n ∧ MinOverlapQuotient n = y}

private theorem limit_bounded :
    BddBelow {y | ∃ n : ℕ, 0 < n ∧ MinOverlapQuotient n = y} := by
  refine ⟨0, ?_⟩
  rintro y ⟨n, _, rfl⟩
  unfold MinOverlapQuotient
  positivity

theorem tendsto_limit : atTop.Tendsto MinOverlapQuotient (𝓝 limit) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact ha.trans_le (csInf_le limit_bounded ⟨n, hn, rfl⟩)
  · intro b hb
    have hne : {y | ∃ n : ℕ, 0 < n ∧ MinOverlapQuotient n = y}.Nonempty :=
      ⟨_, 1, by decide, rfl⟩
    obtain ⟨y, ⟨m, hm, hmy⟩, hyb⟩ := (csInf_lt_iff limit_bounded hne).mp hb
    exact eventually_lt_of_value_lt hm (hmy ▸ hyb)

theorem limit_le_word_bound {m c : ℕ} (hm : 0 < m)
    {ones zeros : Finset ℤ} (hdisj : Disjoint ones zeros)
    (hpartition : ones ∪ zeros = Finset.Ico 0 (2 * m : ℤ)) (hsame : ones.card = zeros.card)
    (word_overlap : ∀ k : ℤ, Overlap ones zeros k ≤ c) :
    limit ≤ (c : ℝ) / m := by
  by_contra! hlt
  have hEventually : ∀ᶠ n in atTop, MinOverlapQuotient n < limit :=
    eventually_quotient_lt hm hdisj hpartition hsame word_overlap hlt
  obtain ⟨n, hn, hlow⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and hEventually).exists
  exact (not_lt_of_ge (csInf_le limit_bounded ⟨n, hn, rfl⟩)) hlow

theorem exists_lt_of_word_bound {m c : ℕ} (hm : 0 < m)
    {ones zeros : Finset ℤ} (hdisj : Disjoint ones zeros)
    (hpartition : ones ∪ zeros = Finset.Ico 0 (2 * m : ℤ)) (hsame : ones.card = zeros.card)
    (word_overlap : ∀ k : ℤ, Overlap ones zeros k ≤ c) (hstrict : (c : ℝ) / m < 0.385694) :
    ∃ c, atTop.Tendsto MinOverlapQuotient (𝓝 c) ∧ c < 0.385694 :=
  ⟨limit, tendsto_limit, (limit_le_word_bound hm hdisj hpartition hsame word_overlap).trans_lt hstrict⟩

end OverlapLimit

namespace OMA

open scoped BigOperators

private lemma powerSum_digit {ι : Type*} (s : Finset ι) (e : ι → ℕ) (q j : ℕ)
    (hq : 2 ≤ q) (hs : s.card < q) :
    ((∑ x ∈ s, q ^ e x) / q ^ j) % q = (s.filter fun x => e x = j).card := by
  classical
  let lo := s.filter fun x => e x < j
  let mid := s.filter fun x => e x = j
  let hi := s.filter fun x => j < e x
  have hpos : 0 < q := by omega
  have hlo : (∑ x ∈ lo, q ^ e x) < q ^ j := by
    cases j with
    | zero =>
      simp [lo]
    | succ j =>
      calc
        (∑ x ∈ lo, q ^ e x) ≤ ∑ _x ∈ lo, q ^ j :=
          Finset.sum_le_sum fun x hx =>
            pow_le_pow_right' (by omega : 1 ≤ q) (by
              have h := (Finset.mem_filter.mp hx).2
              omega)
        _ = lo.card * q ^ j := by simp
        _ ≤ s.card * q ^ j :=
          Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.filter_subset _ _))
        _ < q ^ (j + 1) := by
          rw [pow_succ, mul_comm (q ^ j) q]
          exact Nat.mul_lt_mul_of_pos_right hs (pow_pos hpos _)
  have hmid : (∑ x ∈ mid, q ^ e x) = mid.card * q ^ j :=
    Finset.sum_const_nat fun x hx => by rw [(Finset.mem_filter.mp hx).2]
  have hhi : q ^ (j + 1) ∣ ∑ x ∈ hi, q ^ e x :=
    Finset.dvd_sum fun x hx => Nat.pow_dvd_pow _ (Nat.succ_le_of_lt (Finset.mem_filter.mp hx).2)
  obtain ⟨u, hu⟩ := hhi
  let rest := s.filter fun x => ¬ e x < j
  have hrestMid : (rest.filter fun x => e x = j) = mid := by
    ext x
    simp only [rest, mid, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by omega⟩, h.2⟩⟩
  have hrestHi : (rest.filter fun x => e x ≠ j) = hi := by
    ext x
    simp only [rest, hi, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, by have := h.1.2; have := h.2; omega⟩,
      fun h => ⟨⟨h.1, by omega⟩, by omega⟩⟩
  have hsum : (∑ x ∈ s, q ^ e x) =
      (∑ x ∈ lo, q ^ e x) + (∑ x ∈ mid, q ^ e x) + (∑ x ∈ hi, q ^ e x) := by
    have hfirst := Finset.sum_filter_add_sum_filter_not s (fun x => e x < j)
      (fun x => q ^ e x)
    have hsecond := Finset.sum_filter_add_sum_filter_not rest (fun x => e x = j)
      (fun x => q ^ e x)
    rw [hrestMid, hrestHi] at hsecond
    rw [← hfirst, ← hsecond, add_assoc]
  have hupper : mid.card < q :=
    lt_of_le_of_lt (Finset.card_le_card (Finset.filter_subset _ _)) hs
  change ((∑ x ∈ s, q ^ e x) / q ^ j) % q = mid.card
  rw [hsum, hmid, hu, pow_succ, mul_assoc, add_assoc, mul_comm mid.card, ← mul_add,
    Nat.add_mul_div_left _ _ (pow_pos hpos _), Nat.div_eq_of_lt hlo, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hupper]

lemma overlap_eq_digit (A B : Finset ℤ) (L q : ℕ)
    (hA : ∀ a ∈ A, 0 ≤ a ∧ a < L) (hB : ∀ b ∈ B, 0 ≤ b ∧ b < L)
    (hq : 2 ≤ q) (hcard : A.card * B.card < q)
    (k : ℤ) (hk : 1 - (L : ℤ) ≤ k) :
    ((∑ a ∈ A, q ^ a.toNat) * (∑ b ∈ B, q ^ (L - 1 - b.toNat)) /
      q ^ ((L : ℤ) - 1 + k).toNat) % q = Erdos36.Overlap A B k := by
  classical
  let e (p : ℤ × ℤ) := p.1.toNat + (L - 1 - p.2.toNat)
  have hprod :
      (∑ a ∈ A, q ^ a.toNat) * (∑ b ∈ B, q ^ (L - 1 - b.toNat)) =
      ∑ p ∈ A.product B, q ^ e p := by
    rw [Finset.sum_mul_sum, Finset.product_eq_sprod, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp [e, pow_add]
  rw [hprod, powerSum_digit _ _ _ _ hq (by simpa using hcard)]
  unfold Erdos36.Overlap
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
  constructor
  · rintro ⟨⟨ha, hb⟩, he⟩
    refine ⟨⟨ha, hb⟩, ?_⟩
    have ha' := hA p.1 ha
    have hb' := hB p.2 hb
    dsimp [e] at he
    omega
  · rintro ⟨⟨ha, hb⟩, he⟩
    refine ⟨⟨ha, hb⟩, ?_⟩
    have ha' := hA p.1 ha
    have hb' := hB p.2 hb
    dsimp [e]
    omega

lemma overlap_eq_zero_of_outside (A B : Finset ℤ) (L : ℕ)
    (hA : ∀ a ∈ A, 0 ≤ a ∧ a < L) (hB : ∀ b ∈ B, 0 ≤ b ∧ b < L)
    (k : ℤ) (hk : k < 1 - (L : ℤ) ∨ (L : ℤ) - 1 < k) :
    Erdos36.Overlap A B k = 0 := by
  unfold Erdos36.Overlap
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  have ha' := hA p.1 ha
  have hb' := hB p.2 hb
  change p.1 - p.2 = k at he
  omega

lemma overlap_le_of_digits_le (A B : Finset ℤ) (L q U : ℕ)
    (hA : ∀ a ∈ A, 0 ≤ a ∧ a < L) (hB : ∀ b ∈ B, 0 ≤ b ∧ b < L)
    (hq : 2 ≤ q) (hcard : A.card * B.card < q)
    (hdigits : ∀ j < 2 * L,
      ((∑ a ∈ A, q ^ a.toNat) * (∑ b ∈ B, q ^ (L - 1 - b.toNat)) / q ^ j) % q ≤ U)
    (k : ℤ) : Erdos36.Overlap A B k ≤ U := by
  by_cases hk : 1 - (L : ℤ) ≤ k ∧ k ≤ (L : ℤ) - 1
  · rw [← overlap_eq_digit A B L q hA hB hq hcard k hk.1]
    exact hdigits _ (by omega)
  · rw [overlap_eq_zero_of_outside A B L hA hB k (by omega)]
    exact Nat.zero_le _

end OMA

namespace OMA

open scoped BigOperators

lemma integer_partition_of_nat_digits (PA PB : Finset ℕ) (m q F R U : ℕ)
    (hDisj : Disjoint PA PB) (hUnion : PA ∪ PB = Finset.range (2 * m))
    (hCard : PA.card = m) (hF : ∑ i ∈ PA, q ^ i = F)
    (hR : ∑ i ∈ PB, q ^ (2 * m - 1 - i) = R)
    (hq : 2 ≤ q) (hcard : m * m < q)
    (hdigits : ∀ j < 2 * (2 * m), (F * R / q ^ j) % q ≤ U) :
    ∃ ones zeros : Finset ℤ, Disjoint ones zeros ∧
      ones ∪ zeros = Finset.Ico 0 (2 * (m : ℤ)) ∧
      ones.card = zeros.card ∧ ∀ k, Erdos36.Overlap ones zeros k ≤ U := by
  let castInt : ℕ ↪ ℤ := Nat.castEmbedding
  let ones := PA.map castInt
  let zeros := PB.map castInt
  have hCardB : PB.card = m := by
    have h := Finset.card_union_of_disjoint hDisj
    rw [hUnion, Finset.card_range, hCard] at h
    omega
  have hIco : ones ∪ zeros = Finset.Ico 0 (2 * (m : ℤ)) := by
    change PA.map castInt ∪ PB.map castInt = _
    rw [← Finset.map_union, hUnion]
    ext z
    rw [Finset.mem_map, Finset.mem_Ico]
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hn' := Finset.mem_range.mp hn
      change 0 ≤ (n : ℤ) ∧ (n : ℤ) < 2 * (m : ℤ)
      omega
    · intro hz
      refine ⟨z.toNat, Finset.mem_range.mpr (by omega), ?_⟩
      change (z.toNat : ℤ) = z
      exact Int.toNat_of_nonneg hz.1
  have hbounds (z : ℤ) (hz : z ∈ ones ∪ zeros) : 0 ≤ z ∧ z < (2 * m : ℕ) := by
    rw [hIco, Finset.mem_Ico] at hz
    exact ⟨hz.1, by exact_mod_cast hz.2⟩
  have hA (a : ℤ) (ha : a ∈ ones) : 0 ≤ a ∧ a < (2 * m : ℕ) :=
    hbounds a (Finset.mem_union_left _ ha)
  have hB (b : ℤ) (hb : b ∈ zeros) : 0 ≤ b ∧ b < (2 * m : ℕ) :=
    hbounds b (Finset.mem_union_right _ hb)
  have hF' : ∑ a ∈ ones, q ^ a.toNat = F := by
    simpa only [ones, Finset.sum_map, castInt, Nat.castEmbedding_apply, Int.toNat_natCast] using hF
  have hR' : ∑ b ∈ zeros, q ^ (2 * m - 1 - b.toNat) = R := by
    simpa only [zeros, Finset.sum_map, castInt, Nat.castEmbedding_apply, Int.toNat_natCast] using hR
  have hCardA' : ones.card = m := by simpa only [ones, Finset.card_map] using hCard
  have hCardB' : zeros.card = m := by simpa only [zeros, Finset.card_map] using hCardB
  refine ⟨ones, zeros, (Finset.disjoint_map castInt).mpr hDisj, hIco,
    hCardA'.trans hCardB'.symm, ?_⟩
  apply overlap_le_of_digits_le ones zeros (2 * m) q U hA hB hq
  · simpa only [hCardA', hCardB'] using hcard
  · simpa only [hF', hR'] using hdigits

end OMA

namespace OverlapWord
open Finset

private structure Data where
  count : ℕ
  forward : ℕ
  reverseZeros : ℕ

private def pack (q : ℕ) : ℕ → ℕ → Data
  | 0, w => if w % 2 = 1 then ⟨1, 1, 0⟩ else ⟨0, 0, 1⟩
  | d + 1, w =>
    let size := 2 ^ d
    let low := pack q d (w % (2 ^ size))
    let high := pack q d (w / (2 ^ size))
    ⟨low.count + high.count, low.forward + q ^ size * high.forward,
      q ^ size * low.reverseZeros + high.reverseZeros⟩

private def shift (k : ℕ) (s : Finset ℕ) := s.image (k + ·)

private def join (k : ℕ) (s t : Finset ℕ) := s ∪ shift k t

private lemma join_sum {k : ℕ} {s t : Finset ℕ} (hs : s ⊆ range k) (f : ℕ → ℕ) :
    ∑ z ∈ join k s t, f z = (∑ z ∈ s, f z) + ∑ z ∈ t, f (k + z) := by
  have dis : Disjoint s (shift k t) := by
    refine disjoint_left.mpr ?_
    intro x hx h
    obtain ⟨z, _, rfl⟩ := mem_image.mp h
    have := mem_range.mp (hs hx)
    omega
  rw [join, sum_union dis, shift, sum_image]
  intro x _ y _ h
  exact Nat.add_left_cancel h

private lemma join_card {k : ℕ} {s t : Finset ℕ} (hs : s ⊆ range k) :
    (join k s t).card = s.card + t.card := by
  simpa using join_sum (t := t) hs (fun _ => 1)

private lemma join_partition {k : ℕ} {A B C D : Finset ℕ}
    (hAB : Disjoint A B) (hCD : Disjoint C D) (hAB' : A ∪ B = range k)
    (hCD' : C ∪ D = range k) :
    Disjoint (join k A C) (join k B D) ∧ join k A C ∪ join k B D = range (2*k) := by
  have ab (x : ℕ) : (x ∈ A ∨ x ∈ B) ↔ x < k := by rw [← mem_union, hAB', mem_range]
  have cd (x : ℕ) : (x ∈ C ∨ x ∈ D) ↔ x < k := by rw [← mem_union, hCD', mem_range]
  have test (u : Finset ℕ) (x : ℕ) : x ∈ shift k u ↔ k ≤ x ∧ x-k ∈ u := by
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      simp [hz]
    · rintro ⟨hx, hm⟩
      exact mem_image.mpr ⟨x-k, hm, by omega⟩
  constructor
  · refine disjoint_left.mpr ?_
    intro x hx hy
    simp only [join, mem_union, test] at hx hy
    rcases hx with hA | ⟨ha, hC⟩ <;> rcases hy with hB | ⟨hb, hD⟩
    · exact disjoint_left.mp hAB hA hB
    · have := (ab x).1 (.inl hA)
      omega
    · have := (ab x).1 (.inr hB)
      omega
    · exact disjoint_left.mp hCD hC hD
  · ext x
    simp only [join, mem_union, test, mem_range]
    by_cases h : x < k
    · have hn : ¬ k ≤ x := by omega
      have hx : x < 2 * k := by omega
      simpa [hn, hx] using (ab x).2 h
    · have hk : k ≤ x := by omega
      have hh := (ab x).not.mpr h
      push Not at hh
      simp only [hh.1, hh.2, false_or, hk, true_and, cd]
      omega

private theorem realize (q : ℕ) (d w : ℕ) :
    ∃ A B : Finset ℕ, Disjoint A B ∧ A ∪ B = range (2^d) ∧
      A.card = (pack q d w).count ∧
      (∑ i ∈ A, q ^ i) = (pack q d w).forward ∧
      (∑ i ∈ B, q ^ (2^d-1-i)) = (pack q d w).reverseZeros := by
  induction d generalizing w with
  | zero =>
    by_cases h : w%2=1
    · exact ⟨{0}, ∅, by simp, by decide, by simp [pack, h], by simp [pack, h], by simp [pack, h]⟩
    · exact ⟨∅, {0}, by simp, by decide, by simp [pack, h], by simp [pack, h], by simp [pack, h]⟩
  | succ d ih =>
    let k := 2 ^ d
    obtain ⟨A, B, hd, hcov, hcard, hforward, hreverse⟩ := ih (w % 2^k)
    obtain ⟨C, D, hd', hcov', hcard', hforward', hreverse'⟩ := ih (w / 2^k)
    have hA : A ⊆ range k := hcov ▸ subset_union_left
    have hB : B ⊆ range k := hcov ▸ subset_union_right
    have hD : D ⊆ range k := hcov' ▸ subset_union_right
    have hpart := join_partition hd hd' hcov hcov'
    refine ⟨join k A C, join k B D, hpart.1, ?_, ?_, ?_, ?_⟩
    · simpa [k, pow_succ, Nat.mul_comm] using hpart.2
    · exact (join_card hA).trans (congrArg₂ (·+·) hcard hcard')
    · rw [join_sum hA, hforward]
      change _ + _ = _ + q^k * _
      rw [← hforward', mul_sum]
      simp only [pow_add]
      rfl
    · rw [join_sum hB]
      have hbig : 2 ^ (d+1) = k + k := by simp [k, pow_succ, Nat.mul_two]
      rw [hbig]
      change _ = q^k * _ + _
      rw [← hreverse, ← hreverse', mul_sum]
      congr 1
      · apply sum_congr rfl
        intro i hi
        have hi' := mem_range.mp (hB hi)
        change q^(k+k-1-i) = q^k * q^(k-1-i)
        rw [← pow_add]
        congr 1
        omega
      · apply sum_congr rfl
        intro i hi
        change q^(k+k-1-(k+i)) = q^(k-1-i)
        congr 1
        omega

private def checkDigits (q bound : ℕ) : ℕ → ℕ → Bool
  | 0, x => decide (x % q ≤ bound)
  | depth+1, x =>
    let scale := q ^ (2 ^ depth)
    checkDigits q bound depth (x % scale) && checkDigits q bound depth (x / scale)

private lemma checkDigits_sound {q bound d x : ℕ} (_hq : 2 ≤ q)
    (hc : checkDigits q bound d x = true) (j : ℕ) (hj : j < 2^d) :
    x / q^j % q ≤ bound := by
  induction d generalizing x j with
  | zero =>
    have : j = 0 := by simpa using hj
    simpa [this, checkDigits] using hc
  | succ d ih =>
    have hparts := Bool.and_eq_true_iff.mp hc
    by_cases h : j < 2 ^ d
    · have hh := ih hparts.1 j h
      have hsplit : x / q^j % q = (x % q^(2^d)) / q^j % q := by
        conv_rhs => rw [show 2^d = j + (2^d - j) by omega, pow_add]
        rw [Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
        obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : 2^d - j ≠ 0)
        rw [hr, pow_succ]
        exact Nat.dvd_mul_left _ _
      exact hsplit ▸ hh
    · have hj' : j - 2^d < 2^d := by rw [pow_succ] at hj; omega
      have hh := ih hparts.2 (j-2^d) hj'
      rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_of_le (by omega : 2^d ≤ j)] at hh
      exact hh

private def word : ℕ := 0x400000000000000000000800000000000000000000000000000000000000000000020000000000000001000000000000000000000000140008000000000080000000000004000000000000000000000000000000000100000100000000000000000004000040000000000000000000002000000000000000000000000000000084000000400000000000000000200000000000000000000000000000000000000000000000000100000000600000000000000000000000200001000000000000000000000004000000000000000004000000a0000000000000000200000000020000000000000001000000000200000000000000000008000000000000000030001002040404000100110800001100020000100002060809050020000484410000000800000000200484001002084400000a0000009000020012104000001000110030000085102040400000400080421519008001040030000254001000180403301004000400a4008000c5850020032080100064800000000000820280441080200080000c0000800001108011000600002420089401000400008e60b0800000000042202000008104042000080000000080100000400000490600600008084422080000090c00c00005000810002000100440004a0a0040000200281000040020101000004080290022048010022001408000c041000120040004800000130000100062400000000000000200303a03c9b1e5ec8d11cee1236cf123debfeaee8ddeb1df6bd9c5ae3ea7c7dfb47e5dfe71ee326fa7bccf24f5b3b77ffb73e782677af3db69233af3913733a5eb4f3ef531ff7a7b3fe8ece74efd2ef7ffdf7fad1e7ceadbb647e1753f9a37ef11fcab53eaad5d14e7b9ea303f7789ddf73122ac33ba76e8ddefaec58fe69db7af8e9faf7776d6dade8f2c9a7895cde5ddb2cf9ec531797f427fabcfefdd21ed74d4aab794ff5b61d775a5537fb8f870bfe2d13d6bfefed6403ff96eef07feebefaebf0e355cbfb55f70d8c568fcf79ffc3766f37b495c7e7d4d382bad0f7997de9eadbde9ff5d6bf8bada4f7a8ffebff667677f5e9cc9cf3277a4bef5ab377647c0a5fcd3777ceed70811fe9af6fdadfe8e67d453d8081280a9b0212a548500343164400f8e40100ca8408f952bb90500085fc0e084160894000f00221790bb60de8b0ac9042685838c5cbc421e9309325245e0f9222052b19c082216ab4681a3b4a41020453550b82cd0024c5141ad007693748153852a1b72a58910dc78424702442b000a714dcd0aec295aa42cd4425aa8215140609442306b36cdb0c8c10598024e77580408c84092626d269a58ee1d423562406421864c0c8a8714a03c88cd005093061d720500803021508361890bc2a959856507500006c4808383c5b2d65bcd2a44012f5703d90032c50f8408aaaf0dca290cb0e1b104c304a884228dcd004f105708291001a7c2864490c16b2d041c06e020082c52483287b50042440e1dd13fdebde1af75716dfdbee546b9ff3669f9732fddfdff7b9f6f937c257ffa497fc4bb55f5bd6fdeffffe9bf8eabdaefd777ee34edc5f3d36eade8fbb7fd77fbe5f93efaff83f45be8ebfffaeedbed7fffac9ed777eb7572dbbe73f3b7daff7cf8df7757f696f017dff9fbb77fcfffacfa53bae977d6bb65f95bffbfaff7f0ff680a2ffddd7a6ebbde96eff57fdff2ff95e7e466abb7cfa7cef7ddeeecfbfdd78f92fbccc8c5fbd83f4efefe4dffebb21f6bf39a77bed7f0fcd5cdf9a5bdb7fd6a6e0dfd7fac8ffed5fa29ab33f97b7dff64efffcfee6616dff6f9f9f53fe1267bedffa9397fbf887aaa63fafba777ff7f3ddcdeff2e93df7e4f76ce3b8dddbc19cbff8f7dff121fd2a9f31bed7bdfff6dd9f67f1bdfa2657d7aa76f7625e53772bb8d5ef6b99baa70fb8065b85a74de7efcc9737b83ef418d83f5eddf1cbfb451e2e0b7ecfae78e260e5ef31df67de382e53d595aff5ae1df6e5139a5cddaaf7888d74ade256bf7bdf9bc94b1ecbbee9da9a28f36dfb7f20d2f6fdcef0905aeb10d5e6cb675d3f14cc334d4ad4a1cfe7f3462fae2db7cc65cbff96f7f5f5709715ff96eff9e1a7bc7f01fd7b4ffb93355d6abf19ebc8c36dfec98e66d3bdcad47ec59b78b730952bf5d75dfe50e5abe0e7ebb65c3db9f234f9bb65baf5beec6177dbfdfbfe3cb7ef5e51991704a38ca9bfe15ea1fcb500fb47d61df433def76b76b439feb57bfbcfb5bd731e5a79f70dd79bf4d9baeffb3a36f243fd8db5b8d84f0e6fff7dbd7fff5bff7ff7ceffffef7ffd7ffffffffbfedff7bffffbef6f3fffffffefe7fffbbbfeffdffffbfbfeffffdeeff9dbffdfffffffbfdefedfefbca5dfffbfffefdeffbffeeffffffff3fffbfefebffffcf7fd3ffcffbefefbeff5edb7adffbfdfff7fdfbfbfebff7fffff7ffff7ff7fffffff7fff1f9df5fffffefdff5ffffffbffed7ffbbfffffbffff7fdfffffe7feef6f7fdff7e7fdffffeffffff7f7efffbfffe7efffb3effffffffefdefffff7ffaffffdffdefedffff9ffffffeffffdb7fffffffffffbedbffffbebfffeffeffefbffffdbffffbffcfff7fe6ff5ffed3effffdffffffffdbfffffedfef9ffdffffebeebffffe2bfffe6f7effff7ffffdfff7ffffffffffffafff7fff57fffffffffeff7ffffeb7fddd7fffdf7fefffffffbff7bdbfdffffbbff75fdaf7febfef7ffffff7fffdffffefbffdf7effefbfffbfffffdffffeffeeefdffff7df7ffeff7fffffffefffbfffffbfefffffff7bffdfff77feffaffffbfffcffffdffffdfe7ffbffff6ffffff3efff7fffeffffb7ffffdfdfffffffff9fffdbffeffff6fff6bfdffffe6ef7ffff7eeddffdefffffff7ffffbfeffe7bffffffffdd7f3fffeffefffeff77ffeffffdffffeffffff7fffffdffff7ffffffeffdfffb7f9ffffffffffffffffbfe7febfffefeffff7efe7cfbfff7f5fbeffffffff7ffff9bbf6ffff7fffcdbfffbffafebf337ffffffffdfdff7fffffefffffffffe9fffffefffffffbfffffffffffffbfd7dfffeffffb7fff6ff7efdfbffdbff7dfdfff37fffff8ffbfff7ffd9bfffdfdd7fffeffefdbff7ff7fbfffff5ffffdfbaefd7ffffffffffffdfff53fefbfffbfd9feffff1fefbfffbff7f9fffffffffcffb7fdfffffcffeffdeffb3f3fffffffffdffb7ffffaf7feaffffdffdfdff7fffffbf9e79ff3ffeffbed6cef7fbfff6ffffd7ffeff7ffdafbbfaffe7fff7ffffeffffdefffffffbfefffdf96fffebefffffbffd6ffffeffdfdffbfffbfffdffef7fdeffffdfff9fffff67edf7ffff6fffa7ffbf7fffd7fffffbeeffdfdcffffdffffffbfffefffb77ff7fffefffeffefdeffeffefffff7fff73fffffcdeff7fb7ffffeffef7fbdfefdef5bfcfffdf7ed7fffbffeef7ff7cffea7fffff97f5fbfefbfb7faff7efff44c7a66c923daee93cc3c7b3f1f5f5c6398a6e8bff1e95b17d0f65c12d3aeef0326af993e38675fa7574fb6e9f3f13fd3d5a358b89da33b6da6ebd45fbd357bf65bc3d3df6bf5b1ac65b07f1e65f3f0b18f2f99fd25feb2bf7005e5ecb11befaa3ffff2ae8af593dfdce902eaf5d76fb0a9fbe0c6969fbcfac5fd3f4ce6cdab77dd4858f1df38cf67b39c16dfd2beec9a92bc91f66979bbfe778637dafb43fe5e6ca71946effde9bff9bef55d4d8b95bbe7e59f41e35b4797b391e1f0265676bf9b91b77ab5b8a0dd221cb7d2b19ebfe977fdef104d71ec5bbfe513fe9770f4fdd4df8dadd7f1867fd87b797df8dd5efef8ef001ecd2a6f90ced72f75f95e76d873a0f6391a6bafcab2e2c441cb7d8fcd1febbec5d83f67b7fe9b3da7e6f6dee35ef16a7797fbfb6b1f3fafffb336fbf2cbef0acd9bcdee3fbdbff75fb5ffe7f3fb16bde11ffbde7fbfa935ff636edd5fabff8dbf97349d4fcab5bfb6e5fd79bf5bdfefcbc676faebfd7fafa55fc7ee62d98fd5d5b3addd9bf4f3e43bbaf39ffeaae3757ffdff9c9defa7677beac7be7f7fd653b56ef96e7ff925ddca6f7ede7f6dbfe7fc67bb57ff976f76aa25f5baff5db6f0efe96bbf67d6e573e23fe37e9f3ece6ebdee7c8a7b0ff3afecf86ffd5de7deff0baf3d7b0f7befff1737edd5d9efb4afeff5a6fbda47fa6bee33f4bcaf2abfba8f7f7e9163c9c4767da5de7ebdf7edefeffff9d66eebaff6ebe6e5cae9edf5f5dccbff8d4ebc777d9a59f73fe4c513c48923002edf8c68c6246aa044bbf9424c83f8a3e488688e4bb02584f34058a0900d80834906c29c0001392080a312e0c103062c649c250884a212cb289196339841e011832b21302920069e517a9a91a88580cd1ea81440d834c9400aa4afb22054da61b0d182e64671b586e12d43c22564dd09770828d644a6003cd2c804b0480024d927223a40484490ba92cc0016ce82850092ccd00056c0083f04202113843264b2b475188cd757f9825a4286288c690ac2804c55a41ce02e56104c1084628922d48347550505aaf28c2553a4451582446b105d1f218e6704eb5c822a08cacea203e98d06589ad612090341c42a491f861a6201b585a2940c2d06649193802a82d0801c2353184f06001001819fa83dc584bec35cced977a4863e7b2b7facfff25af175dfd35dfa7afdd9b74617d357fba4cbc294d3d58f1da9fe623bdcf977bccdac647df25d74d7fe8390bb09f70aa77fe7938191ff9fb9fcd9ff7534eb4685e755bf8cd26f68b01e55fb097ccf16bb8c997557862bf57dbd3fb5cefef7bc7ee32881bf531ed8658a6cdfecf2fbefdde077d2617f9dea5d55b18f2dcdb55eeb5fb7ff5faefe75f7ec78efdffefdede53f73eebd7ff27775a7664c5e9372f93bd6597d761bf9b4f43fea7dfa8c25e2be7f552377b239dab9dd77bf762bf66d86ede45b7fb2f677cdf263ddbe5d7fe7377f360b6f23ef89c76f4163d4195bf3f98efccf01480a16ec709e585f7b33fa78e90b5dfd37ffea5af89e04b2bfe020115015008006802010100011000000082000101522801400000100c016200004004c00000020000290100001000001004000000110101000208a00401404000080000c42000000004000000301000000040200800802084100000822400000c000021050e8100500220001100961020000000102080400008020010000012008c822802a080b00044010000401200b00004641440a110004c000000600004000010801c08004405000000021800000008028001000c00000800c001800500000000040800004504000000000206202020004006104c8208400800c00800040020081002011041000000008821000a008004000040242000800409000400088040820000108000038000081080100011000000000010000000000008000400000000000000000000000000000000000000000000000020000000000000000000000000000000004000008000000000040000000000000000000000000020011008000080000000000000000000000000000000000000000080000001000000080000000800200000000000000000000000000400000000000000000000000000010000000000400000000040000000000000000000000000000000000000000000000000000040000800000000000000000000080000000000002000008000000000000000000000000000011000000000000000000000000000002000000000000000000008002040000000000000200000000000000000000000000000000000

set_option maxHeartbeats 5000000 in
private theorem wordCount : (pack (2^29) 15 word).count = 16384 := by decide +kernel

set_option maxHeartbeats 30000000 in
private theorem wordDigits : checkDigits (2^29) 6319 16
    ((pack (2^29) 15 word).forward * (pack (2^29) 15 word).reverseZeros) = true := by decide +kernel

private theorem certified_partition :
    ∃ A B : Finset ℤ, Disjoint A B ∧ A ∪ B = Finset.Ico 0 (2 * 16384 : ℤ) ∧
      A.card = B.card ∧ ∀ k : ℤ, Erdos36.Overlap A B k ≤ 6319 := by
  obtain ⟨A, B, hd, hu, ha, hf, hr⟩ := realize (2^29) 15 word
  apply OMA.integer_partition_of_nat_digits A B 16384 (2^29)
    (pack (2^29) 15 word).forward (pack (2^29) 15 word).reverseZeros 6319 hd hu
    (ha.trans wordCount) hf hr (by decide) (by decide)
  intro j hj
  exact checkDigits_sound (by decide) wordDigits j hj

end OverlapWord

theorem OMA.solution : type_of% @Erdos36.erdos_36.variants.exists := by
  obtain ⟨A, B, hd, hu, hc, ho⟩ := OverlapWord.certified_partition
  exact OverlapLimit.exists_lt_of_word_bound (m := 16384) (by decide)
    hd hu hc ho (by norm_num)