import FormalConjectures.ErdosProblems.«732»

/-
The core of this file (namespace E732P) is adapted from the formalization of Erdős Problem 732,
part ii, in https://github.com/plby/lean-proofs (src/latest/ErdosProblems/Erdos732.lean),
credited there to its formal authors (informal argument: Noga Alon). It shows exponentially many block-size
sequences of pairwise balanced designs via projective planes of prime order (cf. Alon).
The bridge to the formal-conjectures statement (namespace OMA732Bridge) is new.
-/
open scoped BigOperators LinearAlgebra.Projectivization
open Finset Fintype

namespace E732P

universe u v

/-- A finite pairwise balanced block design: every pair of distinct points is
contained in exactly one block, and every block has at least two points. -/
structure PairwiseBalancedDesign (P : Type u) [Fintype P] where
  Block : Type u
  blockFintype : Fintype Block
  block : Block → Finset P
  two_le_card : ∀ i, 2 ≤ (block i).card
  pair_unique : ∀ ⦃x y : P⦄, x ≠ y → ∃! i, x ∈ block i ∧ y ∈ block i

instance PairwiseBalancedDesign.instFintypeBlock {P : Type u} [Fintype P] (D : PairwiseBalancedDesign P) : Fintype D.Block := D.blockFintype

/-- The multiset of block cardinalities of a design. -/
noncomputable def PairwiseBalancedDesign.blockSizes {P : Type u} [Fintype P]
    (D : PairwiseBalancedDesign P) : Multiset ℕ :=
  Finset.univ.val.map fun i ↦ (D.block i).card

/-- A block-size multiset is compatible for `n` if a pairwise balanced design
on `Fin n` has exactly those block sizes. -/
def BlockCompatible (n : ℕ) (sizes : Multiset ℕ) : Prop :=
  ∃ D : PairwiseBalancedDesign (Fin n), D.blockSizes = sizes

/-- The multiset of cardinalities of an arbitrary finite indexed family. -/
noncomputable def familySizes {P : Type u} {I : Type v} [Fintype I]
    (A : I → Finset P) : Multiset ℕ :=
  Finset.univ.val.map fun i ↦ (A i).card

/-- Every pair of distinct points occurs in at most one member of `A`. -/
def IsPartialDesign {P : Type u} {I : Type v} (A : I → Finset P) : Prop :=
  ∀ ⦃x y : P⦄, x ≠ y → ∀ ⦃i j : I⦄,
    x ∈ A i → y ∈ A i → x ∈ A j → y ∈ A j → i = j

/-- A two-element subset which is not contained in any member of `A`. -/
def UncoveredPair {P : Type u} {I : Type v} [Fintype P]
    (A : I → Finset P) :=
  {s : Finset P // s.card = 2 ∧ ∀ i, ¬ (s ⊆ A i)}

noncomputable instance uncoveredPairFintype {P : Type u} {I : Type v}
    [Fintype P] [Fintype I] (A : I → Finset P) : Fintype (UncoveredPair A) := by
  classical
  change Fintype {s : Finset P // s.card = 2 ∧ ∀ i, ¬s ⊆ A i}
  exact Fintype.subtype
    ((Finset.univ : Finset (Finset P)).filter
      fun s ↦ s.card = 2 ∧ ∀ i, ¬s ⊆ A i) (by simp)

/-- Complete a partial pair design by adjoining every uncovered pair as a
two-element block. -/
noncomputable def completePartialDesign {P : Type u} {I : Type u}
    [Fintype P] [Fintype I] (A : I → Finset P) (hpartial : IsPartialDesign A)
    (hcard : ∀ i, 2 ≤ (A i).card) : PairwiseBalancedDesign P where
  Block := I ⊕ UncoveredPair A
  blockFintype := by classical infer_instance
  block
    | Sum.inl i => A i
    | Sum.inr s => s.1
  two_le_card
    | Sum.inl i => hcard i
    | Sum.inr s => by
        change 2 ≤ s.1.card
        exact s.2.1.ge
  pair_unique := by
    classical
    intro x y hxy
    by_cases hcovered : ∃ i, x ∈ A i ∧ y ∈ A i
    · obtain ⟨i, hxi, hyi⟩ := hcovered
      refine ⟨Sum.inl i, ⟨hxi, hyi⟩, ?_⟩
      intro j hj
      cases j with
      | inl j =>
          exact congrArg Sum.inl
            (hpartial hxy (i := i) (j := j) hxi hyi hj.1 hj.2).symm
      | inr s =>
          exfalso
          have hpairCard : ({x, y} : Finset P).card = 2 := by simp [hxy]
          have hsub : ({x, y} : Finset P) ⊆ s.1 := by
            intro z hz
            simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact hj.1
            · exact hj.2
          have hEq : (s.1 : Finset P) = {x, y} := by
            symm
            apply Finset.eq_of_subset_of_card_le hsub
            rw [s.2.1, hpairCard]
          apply s.2.2 i
          rw [hEq]
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hxi
          · exact hyi
    · have huncovered : ∀ i, ¬(({x, y} : Finset P) ⊆ A i) := by
        intro i hi
        apply hcovered
        exact ⟨i, hi (by simp), hi (by simp)⟩
      let p : UncoveredPair A := ⟨{x, y}, by simp [hxy], huncovered⟩
      refine ⟨Sum.inr p, by simp [p], ?_⟩
      intro j hj
      cases j with
      | inl j =>
          exfalso
          exact hcovered ⟨j, hj.1, hj.2⟩
      | inr s =>
          have hpairCard : ({x, y} : Finset P).card = 2 := by simp [hxy]
          have hsub : ({x, y} : Finset P) ⊆ s.1 := by
            intro z hz
            simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact hj.1
            · exact hj.2
          have hEq : (s.1 : Finset P) = {x, y} := by
            symm
            apply Finset.eq_of_subset_of_card_le hsub
            rw [s.2.1, hpairCard]
          apply congrArg Sum.inr
          apply Subtype.ext
          exact hEq

/-- Completion adds only blocks of cardinality two. -/
lemma blockSizes_completePartialDesign {P : Type u} {I : Type u}
    [Fintype P] [Fintype I] (A : I → Finset P) (hpartial : IsPartialDesign A)
    (hcard : ∀ i, 2 ≤ (A i).card) :
    (completePartialDesign A hpartial hcard).blockSizes =
      familySizes A + Multiset.replicate (Fintype.card (UncoveredPair A)) 2 := by
  classical
  rw [PairwiseBalancedDesign.blockSizes, familySizes]
  change
    (Finset.univ.val.map fun i : I ⊕ UncoveredPair A ↦
      ((completePartialDesign A hpartial hcard).block i).card) = _
  rw [← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.map_disjSum]
  congr 1
  change (Finset.univ.val.map fun s : UncoveredPair A ↦ s.1.card) = _
  calc
    (Finset.univ.val.map fun s : UncoveredPair A ↦ s.1.card) =
        Finset.univ.val.map (fun _ : UncoveredPair A ↦ 2) := by
      apply Multiset.map_congr
      · rfl
      intro s hs
      exact s.2.1
    _ = Multiset.replicate (Fintype.card (UncoveredPair A)) 2 := by simp

/-- Filtering a completion at size at least three recovers the original size
multiset, when every original block has size at least three. -/
lemma filter_blockSizes_completePartialDesign {P : Type u} {I : Type u}
    [Fintype P] [Fintype I] (A : I → Finset P) (hpartial : IsPartialDesign A)
    (hcard : ∀ i, 3 ≤ (A i).card) :
    (completePartialDesign A hpartial (fun i ↦ (hcard i).trans' (by omega))).blockSizes.filter
        (fun k ↦ 3 ≤ k) = familySizes A := by
  classical
  rw [blockSizes_completePartialDesign, Multiset.filter_add]
  have hleft : (familySizes A).filter (fun k ↦ 3 ≤ k) = familySizes A := by
    apply Multiset.filter_eq_self.2
    intro k hk
    rw [familySizes, Multiset.mem_map] at hk
    obtain ⟨i, -, rfl⟩ := hk
    exact hcard i
  rw [hleft]
  have hright :
      (Multiset.replicate (Fintype.card (UncoveredPair A)) 2).filter
        (fun k ↦ 3 ≤ k) = 0 := by
    apply Multiset.filter_eq_nil.2
    intro k hk
    have hk2 : k = 2 := Multiset.eq_of_mem_replicate hk
    omega
  rw [hright, add_zero]

/-! ## The unavoidable pair-count condition -/

/-- Every two-element subset belongs to exactly one block, so summing the
number of pairs inside the blocks counts every pair of points once. -/
theorem pair_count_identity {P : Type u} [Fintype P]
    (D : PairwiseBalancedDesign P) :
    ∑ i : D.Block, Nat.choose (D.block i).card 2 =
      Nat.choose (Fintype.card P) 2 := by
  classical
  let pairSets : D.Block → Finset (Finset P) :=
    fun i ↦ (D.block i).powersetCard 2
  have hdisjoint :
      ((Finset.univ : Finset D.Block) : Set D.Block).PairwiseDisjoint pairSets := by
    intro i hi j hj hij
    change Disjoint (pairSets i) (pairSets j)
    rw [Finset.disjoint_left]
    intro s hsi hsj
    have hsi' := Finset.mem_powersetCard.mp hsi
    have hsj' := Finset.mem_powersetCard.mp hsj
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hsi'.2
    obtain ⟨k, hk, hunique⟩ := D.pair_unique hxy
    have hik : i = k := hunique i ⟨hsi'.1 (by simp), hsi'.1 (by simp)⟩
    have hjk : j = k := hunique j ⟨hsj'.1 (by simp), hsj'.1 (by simp)⟩
    exact hij (hik.trans hjk.symm)
  have hunion :
      (Finset.univ.biUnion pairSets) =
        (Finset.univ : Finset P).powersetCard 2 := by
    ext s
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, pairSets,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨i, hsub, hcard⟩
      exact ⟨Finset.subset_univ s, hcard⟩
    · rintro ⟨-, hcard⟩
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
      obtain ⟨i, hi, -⟩ := D.pair_unique hxy
      exact ⟨i, by
        refine ⟨?_, by simp [hxy]⟩
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hi.1
        · exact hi.2⟩
  calc
    (∑ i : D.Block, Nat.choose (D.block i).card 2) =
        ∑ i : D.Block, (pairSets i).card := by
      simp [pairSets, Finset.card_powersetCard]
    _ = (Finset.univ.biUnion pairSets).card :=
      (Finset.card_biUnion hdisjoint).symm
    _ = ((Finset.univ : Finset P).powersetCard 2).card := by rw [hunion]
    _ = Nat.choose (Fintype.card P) 2 := by
      rw [Finset.card_powersetCard, Finset.card_univ]

/-- In the sequence language of the problem, compatibility implies Erdős's
necessary binomial-sum condition. -/
theorem BlockCompatible.pair_count {n : ℕ} {sizes : Multiset ℕ}
    (h : BlockCompatible n sizes) :
    (sizes.map fun k ↦ Nat.choose k 2).sum = Nat.choose n 2 := by
  obtain ⟨D, rfl⟩ := h
  simpa [PairwiseBalancedDesign.blockSizes] using pair_count_identity D

/-- A compatible multiset automatically has exactly the entry bounds from
the problem statement; its sorted list is therefore a sequence
`1 < X₁ ≤ ⋯ ≤ Xₘ ≤ n`. -/
theorem BlockCompatible.size_bounds {n : ℕ} {sizes : Multiset ℕ}
    (h : BlockCompatible n sizes) {k : ℕ} (hk : k ∈ sizes) :
    2 ≤ k ∧ k ≤ n := by
  obtain ⟨D, rfl⟩ := h
  rw [PairwiseBalancedDesign.blockSizes, Multiset.mem_map] at hk
  obtain ⟨i, -, rfl⟩ := hk
  exact ⟨D.two_le_card i, by
    simpa using Finset.card_le_univ (D.block i)⟩

/-! ## Explicit truncation profiles -/

/-- The multiset of projective-line truncation sizes encoded by `c`.
For every `j : Fin (q - 2)`, the value `j + 4` occurs `(c j).val`
times, and the remaining entries are `3`. -/
noncomputable def encodedPrimarySizes (q : ℕ) (c : Fin (q - 2) → Fin q) :
    Multiset ℕ :=
  Multiset.replicate
      (q ^ 2 + q + 1 - ∑ j, (c j).val) 3 +
    ∑ j, Multiset.replicate (c j).val (j.val + 4)

lemma code_sum_le (q : ℕ) (hq : 5 ≤ q) (c : Fin (q - 2) → Fin q) :
    (∑ j, (c j).val) ≤ (q - 2) * (q - 1) := by
  calc
    (∑ j, (c j).val) ≤ ∑ _j : Fin (q - 2), (q - 1) := by
      apply Finset.sum_le_sum
      intro j hj
      omega
    _ = (q - 2) * (q - 1) := by simp

lemma code_sum_le_planeCard (q : ℕ) (hq : 5 ≤ q)
    (c : Fin (q - 2) → Fin q) :
    (∑ j, (c j).val) ≤ q ^ 2 + q + 1 := by
  refine (code_sum_le q hq c).trans ?_
  have hq1 : q - 1 + 1 = q := by omega
  have hq2 : q - 2 + 2 = q := by omega
  nlinarith

@[simp]
lemma card_encodedPrimarySizes (q : ℕ) (hq : 5 ≤ q)
    (c : Fin (q - 2) → Fin q) :
    (encodedPrimarySizes q c).card = q ^ 2 + q + 1 := by
  classical
  rw [encodedPrimarySizes, Multiset.card_add, Multiset.card_replicate]
  rw [Multiset.card_sum]
  simp only [Multiset.card_replicate]
  exact Nat.sub_add_cancel (code_sum_le_planeCard q hq c)

lemma mem_encodedPrimarySizes_bounds (q : ℕ) (hq : 5 ≤ q)
    (c : Fin (q - 2) → Fin q) {a : ℕ}
    (ha : a ∈ encodedPrimarySizes q c) : 3 ≤ a ∧ a ≤ q + 1 := by
  classical
  rw [encodedPrimarySizes, Multiset.mem_add] at ha
  rcases ha with hthree | hsum
  · have ha3 : a = 3 := Multiset.eq_of_mem_replicate hthree
    subst a
    omega
  · rw [Multiset.mem_sum] at hsum
    obtain ⟨j, -, hrep⟩ := hsum
    have haj : a = j.val + 4 := Multiset.eq_of_mem_replicate hrep
    subst a
    constructor
    · omega
    · have := j.isLt
      omega

lemma count_encodedPrimarySizes (q : ℕ)
    (c : Fin (q - 2) → Fin q) (j : Fin (q - 2)) :
    (encodedPrimarySizes q c).count (j.val + 4) = (c j).val := by
  classical
  simp only [encodedPrimarySizes, Multiset.count_add, Multiset.count_replicate]
  rw [Multiset.count_sum']
  have hj3 : j.val + 4 ≠ 3 := by omega
  rw [if_neg (Ne.symm hj3)]
  simp only [zero_add]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    have hval : k.val ≠ j.val := fun h ↦ hkj (Fin.ext h)
    rw [Multiset.count_eq_zero]
    intro hmem
    have heq : j.val + 4 = k.val + 4 := Multiset.eq_of_mem_replicate hmem
    apply hval
    omega
  · simp

lemma encodedPrimarySizes_injective (q : ℕ) :
    Function.Injective (encodedPrimarySizes q) := by
  intro c d hcd
  funext j
  apply Fin.ext
  rw [← count_encodedPrimarySizes q c j,
    ← count_encodedPrimarySizes q d j, hcd]

/-! ## The finite projective plane over `ZMod q` -/

noncomputable section

/-- Points, and dually lines, of the projective plane over `ZMod q`. -/
abbrev PG (q : ℕ) [Fact q.Prime] := ℙ (ZMod q) (Fin 3 → ZMod q)

noncomputable instance pgFintype (q : ℕ) [Fact q.Prime] : Fintype (PG q) :=
  Fintype.ofFinite (PG q)

lemma card_PG (q : ℕ) [Fact q.Prime] :
    Fintype.card (PG q) = q ^ 2 + q + 1 := by
  rw [← Nat.card_eq_fintype_card]
  rw [Projectivization.card_of_finrank (n := 3) (ZMod q) (Fin 3 → ZMod q) (by simp)]
  simp only [Nat.card_eq_fintype_card, ZMod.card]
  norm_num [Finset.sum_range_succ, pow_two]
  ring

lemma projectivePlane_order_eq (q : ℕ) [Fact q.Prime] :
    Configuration.ProjectivePlane.order (PG q) (PG q) = q := by
  let d := Configuration.ProjectivePlane.order (PG q) (PG q)
  have hcard := Configuration.ProjectivePlane.card_points (PG q) (PG q)
  rw [card_PG q] at hcard
  change q ^ 2 + q + 1 = d ^ 2 + d + 1 at hcard
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · nlinarith
  · nlinarith

/-- The point finset of a projective line. -/
noncomputable def linePoints (q : ℕ) [Fact q.Prime] (l : PG q) : Finset (PG q) := by
  classical
  exact Finset.univ.filter fun p ↦ p ∈ l

@[simp]
lemma card_linePoints (q : ℕ) [Fact q.Prime] (l : PG q) :
    (linePoints q l).card = q + 1 := by
  classical
  calc
    (linePoints q l).card = Fintype.card {p : PG q // p ∈ l} := by
      rw [linePoints]
      symm
      apply Fintype.card_subtype
    _ = Configuration.pointCount (PG q) l := by
      rw [Configuration.pointCount, Nat.card_eq_fintype_card]
    _ = Configuration.ProjectivePlane.order (PG q) (PG q) + 1 :=
      Configuration.ProjectivePlane.pointCount_eq (PG q) l
    _ = q + 1 := by rw [projectivePlane_order_eq q]

/-- A code determines a completed design on any ground set large enough to
contain the projective plane.  Its block sizes at least three are exactly the
encoded primary sizes. -/
lemma exists_compatible_of_code (q n : ℕ) (hqPrime : q.Prime) (hq : 5 ≤ q)
    (hqn : q ^ 2 + q + 1 ≤ n) (c : Fin (q - 2) → Fin q) :
    ∃ sizes : Multiset ℕ, BlockCompatible n sizes ∧
      sizes.filter (fun k ↦ 3 ≤ k) = encodedPrimarySizes q c := by
  classical
  let _ : Fact q.Prime := ⟨hqPrime⟩
  let m := encodedPrimarySizes q c
  have hmcard : m.card = q ^ 2 + q + 1 := card_encodedPrimarySizes q hq c
  have hlineCard : Fintype.card (PG q) = Fintype.card m := by
    rw [card_PG q, Multiset.card_coe, hmcard]
  let e : PG q ≃ m := Fintype.equivOfCardEq hlineCard
  let desired : PG q → ℕ := fun l ↦ (e l : ℕ)
  have hdesiredMem (l : PG q) : desired l ∈ m := by
    exact Multiset.coe_mem
  have hdesiredBounds (l : PG q) : 3 ≤ desired l ∧ desired l ≤ q + 1 :=
    mem_encodedPrimarySizes_bounds q hq c (hdesiredMem l)
  have hdesiredSizes :
      (Finset.univ.val.map desired) = m := by
    have he := congrArg (Multiset.map fun z : m ↦ (z : ℕ))
      (Multiset.map_univ_val_equiv e)
    rw [Multiset.map_map, Multiset.map_univ_coe] at he
    exact he
  have hchoose (l : PG q) :
      ∃ s : Finset (PG q), s ⊆ linePoints q l ∧ s.card = desired l := by
    obtain ⟨s, hs, hscard⟩ :=
      Finset.exists_subset_card_eq (s := linePoints q l)
        (by simpa using (hdesiredBounds l).2)
    exact ⟨s, hs, hscard⟩
  let X : PG q → Finset (PG q) := fun l ↦ Classical.choose (hchoose l)
  have hXsub (l : PG q) : X l ⊆ linePoints q l :=
    (Classical.choose_spec (hchoose l)).1
  have hXcard (l : PG q) : (X l).card = desired l :=
    (Classical.choose_spec (hchoose l)).2
  let ι : PG q ↪ Fin n := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa [card_PG q] using hqn))
  let A : PG q → Finset (Fin n) := fun l ↦ (X l).map ι
  have hAcard (l : PG q) : (A l).card = desired l := by
    simp [A, hXcard]
  have hApartial : IsPartialDesign A := by
    intro x y hxy i j hxi hyi hxj hyj
    obtain ⟨px, hpxi, hpx⟩ := Finset.mem_map.mp hxi
    obtain ⟨py, hpyi, hpy⟩ := Finset.mem_map.mp hyi
    obtain ⟨px', hpxj, hpx'⟩ := Finset.mem_map.mp hxj
    obtain ⟨py', hpyj, hpy'⟩ := Finset.mem_map.mp hyj
    have hpxeq : px = px' := ι.injective (hpx.trans hpx'.symm)
    have hpyeq : py = py' := ι.injective (hpy.trans hpy'.symm)
    subst px'
    subst py'
    have hpxy : px ≠ py := by
      intro heq
      apply hxy
      rw [← hpx, ← hpy, heq]
    have hpxiLine : px ∈ i := (Finset.mem_filter.mp (hXsub i hpxi)).2
    have hpyiLine : py ∈ i := (Finset.mem_filter.mp (hXsub i hpyi)).2
    have hpxjLine : px ∈ j := (Finset.mem_filter.mp (hXsub j hpxj)).2
    have hpyjLine : py ∈ j := (Finset.mem_filter.mp (hXsub j hpyj)).2
    exact (Configuration.Nondegenerate.eq_or_eq hpxiLine hpyiLine hpxjLine hpyjLine).resolve_left
      hpxy
  have hAsizes : familySizes A = m := by
    rw [familySizes]
    calc
      (Finset.univ.val.map fun l ↦ (A l).card) =
          Finset.univ.val.map desired := by
        apply Multiset.map_congr
        · rfl
        intro l hl
        exact hAcard l
      _ = m := hdesiredSizes
  have hAthree (l : PG q) : 3 ≤ (A l).card := by
    rw [hAcard]
    exact (hdesiredBounds l).1
  let D := completePartialDesign A hApartial
    (fun l ↦ (hAthree l).trans' (by omega))
  refine ⟨D.blockSizes, ⟨D, rfl⟩, ?_⟩
  rw [show D.blockSizes.filter (fun k ↦ 3 ≤ k) = familySizes A by
    exact filter_blockSizes_completePartialDesign A hApartial
      hAthree, hAsizes]

end

/-! ## The exact finite lower bound -/

/-- Alon's construction in an exact finite form: a prime-power projective
plane of prime order `q` supplies `q ^ (q - 2)` distinct block-size
multisets, even after the point set is enlarged to `Fin n`. -/
theorem projectivePlane_family (q n : ℕ) (hqPrime : q.Prime) (hq : 5 ≤ q)
    (hqn : q ^ 2 + q + 1 ≤ n) :
    ∃ S : Finset (Multiset ℕ),
      S.card = q ^ (q - 2) ∧ ∀ sizes ∈ S, BlockCompatible n sizes := by
  classical
  let C := Fin (q - 2) → Fin q
  have hex (c : C) := exists_compatible_of_code q n hqPrime hq hqn c
  let sizes : C → Multiset ℕ := fun c ↦ Classical.choose (hex c)
  have hsizes_compatible (c : C) : BlockCompatible n (sizes c) :=
    (Classical.choose_spec (hex c)).1
  have hsizes_filter (c : C) :
      (sizes c).filter (fun k ↦ 3 ≤ k) = encodedPrimarySizes q c :=
    (Classical.choose_spec (hex c)).2
  have hsizes_injective : Function.Injective sizes := by
    intro c d hcd
    apply encodedPrimarySizes_injective q
    rw [← hsizes_filter c, ← hsizes_filter d, hcd]
  let e : C ↪ Multiset ℕ := ⟨sizes, hsizes_injective⟩
  refine ⟨Finset.univ.map e, ?_, ?_⟩
  · rw [Finset.card_map]
    simp [C]
  · intro s hs
    rw [Finset.mem_map] at hs
    obtain ⟨c, -, rfl⟩ := hs
    exact hsizes_compatible c

/-! ## Passing from prime orders to all sufficiently large `n` -/

/-- Bertrand's postulate supplies a projective-plane order in the interval
needed for the uniform lower bound.  The deliberately generous threshold
makes all subsequent floor estimates elementary. -/
lemma prime_order_for_large_n (n : ℕ) (hn : 65536 ^ 2 ≤ n) :
    ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ q ^ 2 + q + 1 ≤ n ∧
      Nat.sqrt n / 8 ≤ q - 2 := by
  let s := Nat.sqrt n
  let k := s / 4
  have hs : 65536 ≤ s := by
    rw [Nat.le_sqrt']
    simpa [s] using hn
  have hk0 : k ≠ 0 := by
    dsimp [k]
    omega
  obtain ⟨q, hqPrime, hkq, hqk⟩ :=
    Nat.exists_prime_lt_and_le_two_mul k hk0
  have hq : 5 ≤ q := by
    dsimp [k] at hkq
    omega
  have hqs : q ≤ s / 2 := by
    dsimp [k] at hqk
    omega
  have hsSq : s ^ 2 ≤ n := by
    simpa [s] using Nat.sqrt_le' n
  have hqn : q ^ 2 + q + 1 ≤ n := by
    have h2q : 2 * q ≤ s := by omega
    have hsmall : q ^ 2 + q + 1 ≤ s ^ 2 := by nlinarith
    exact hsmall.trans hsSq
  have hrq : s / 8 ≤ q - 2 := by
    dsimp [k] at hkq
    omega
  exact ⟨q, hqPrime, hq, hqn, hrq⟩

/-- The elementary analytic estimate used to turn the finite power count
into the exponential form asked for by Erdős.  All casts in the conclusion
are to `ℝ`. -/
lemma exponential_le_floor_power (n : ℕ) (hn : 65536 ^ 2 ≤ n) :
    Real.exp ((1 / 128 : ℝ) * Real.sqrt n * Real.log n) ≤
      ((Nat.sqrt n / 8) ^ (Nat.sqrt n / 8) : ℕ) := by
  let s := Nat.sqrt n
  let r := s / 8
  have hs : 65536 ≤ s := by
    rw [Nat.le_sqrt']
    simpa [s] using hn
  have hr : 8192 ≤ r := by
    dsimp [r]
    omega
  have hs_div : s + 1 ≤ 8 * r + 8 := by
    dsimp [r]
    omega
  have hsr : s + 1 ≤ r ^ 2 := by
    nlinarith
  have hn_succ : n < (s + 1) ^ 2 := by
    simpa [s, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' n
  have hn_r4 : n ≤ r ^ 4 := by
    calc
      n ≤ (s + 1) ^ 2 := Nat.le_of_lt hn_succ
      _ ≤ (r ^ 2) ^ 2 := by gcongr
      _ = r ^ 4 := by ring
  have hs_linear : s + 1 ≤ 32 * r := by omega
  have hsqrt : Real.sqrt n ≤ 32 * (r : ℝ) := by
    have hlt : Real.sqrt n < (s : ℝ) + 1 := by
      simpa [s] using (Real.real_sqrt_lt_nat_sqrt_succ (a := n))
    have hcast : (s : ℝ) + 1 ≤ 32 * (r : ℝ) := by exact_mod_cast hs_linear
    exact hlt.le.trans hcast
  have hnposNat : 0 < n := by nlinarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  have hrposNat : 0 < r := by omega
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hrposNat
  have hn_r4_real : (n : ℝ) ≤ (r : ℝ) ^ 4 := by exact_mod_cast hn_r4
  have hlog : Real.log n ≤ 4 * Real.log r := by
    calc
      Real.log n ≤ Real.log ((r : ℝ) ^ 4) := Real.log_le_log hnpos hn_r4_real
      _ = 4 * Real.log r := by rw [Real.log_pow]; norm_num
  have hproduct : Real.sqrt n * Real.log n ≤
      (32 * (r : ℝ)) * (4 * Real.log r) := by
    exact mul_le_mul hsqrt hlog (Real.log_natCast_nonneg n) (by positivity)
  have hargument :
      (1 / 128 : ℝ) * Real.sqrt n * Real.log n ≤ (r : ℝ) * Real.log r := by
    calc
      (1 / 128 : ℝ) * Real.sqrt n * Real.log n =
          (1 / 128 : ℝ) * (Real.sqrt n * Real.log n) := by ring
      _ ≤ (1 / 128 : ℝ) * ((32 * (r : ℝ)) * (4 * Real.log r)) := by
        exact mul_le_mul_of_nonneg_left hproduct (by norm_num)
      _ = (r : ℝ) * Real.log r := by ring
  calc
    Real.exp ((1 / 128 : ℝ) * Real.sqrt n * Real.log n) ≤
        Real.exp ((r : ℝ) * Real.log r) := Real.exp_le_exp.mpr hargument
    _ = ((r : ℝ) ^ r) := by
      rw [Real.exp_nat_mul, Real.exp_log hrpos]
    _ = ((r ^ r : ℕ) : ℝ) := by norm_num
    _ = ((Nat.sqrt n / 8) ^ (Nat.sqrt n / 8) : ℕ) := by rfl

/-- The affirmative enumerative resolution of Erdős Problem 732.  For all
sufficiently large `n`, exponentially many distinct block-size sequences are
realized by pairwise balanced designs on `Fin n`. -/
theorem erdos_732 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ S : Finset (Multiset ℕ),
        (∀ sizes ∈ S, BlockCompatible n sizes) ∧
        Real.exp (c * Real.sqrt n * Real.log n) ≤ S.card := by
  refine ⟨1 / 128, by norm_num, 65536 ^ 2, ?_⟩
  intro n hn
  obtain ⟨q, hqPrime, hq, hqn, hrq⟩ := prime_order_for_large_n n hn
  obtain ⟨S, hScard, hScompatible⟩ :=
    projectivePlane_family q n hqPrime hq hqn
  refine ⟨S, hScompatible, ?_⟩
  let r := Nat.sqrt n / 8
  have hrq' : r ≤ q := hrq.trans (Nat.sub_le q 2)
  have hpow : r ^ r ≤ q ^ (q - 2) := by
    calc
      r ^ r ≤ q ^ r := by gcongr
      _ ≤ q ^ (q - 2) := by
        exact pow_le_pow_right' (by omega) hrq
  have hpowCard : r ^ r ≤ S.card := by simpa [hScard] using hpow
  calc
    Real.exp ((1 / 128 : ℝ) * Real.sqrt n * Real.log n) ≤
        ((r ^ r : ℕ) : ℝ) := by
      simpa [r] using exponential_le_floor_power n hn
    _ ≤ S.card := by exact_mod_cast hpowCard

end E732P

namespace OMA732Bridge

open Finset

theorem block_injective {n : ℕ} (D : E732P.PairwiseBalancedDesign (Fin n)) :
    Function.Injective D.block := by
  intro i j hij
  have h2 := D.two_le_card i
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < (D.block i).card)
  obtain ⟨k, _, hk⟩ := D.pair_unique hxy
  have hi := hk i ⟨hx, hy⟩
  have hj := hk j ⟨hij ▸ hx, hij ▸ hy⟩
  rw [hi, hj]

theorem compatible_mem {n : ℕ} {sizes : Multiset ℕ} (h : E732P.BlockCompatible n sizes) :
    sizes.sort (· ≤ ·) ∈ Hypergraph.blockSizeProfiles n := by
  classical
  obtain ⟨D, hD⟩ := h
  let H : Finset (Finset (Fin n)) := Finset.univ.map ⟨D.block, block_injective D⟩
  unfold Hypergraph.blockSizeProfiles
  rw [Finset.mem_image]
  refine ⟨H, ?_, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      intro e _
      exact Finset.mem_powerset.mpr (Finset.subset_univ _)
    · intro e he
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp he
      exact D.two_le_card i
    · intro S hS
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hS
      obtain ⟨i, ⟨hxi, hyi⟩, hi⟩ := D.pair_unique hxy
      refine ⟨D.block i, ⟨Finset.mem_map_of_mem _ (Finset.mem_univ i), ?_⟩, ?_⟩
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hxi
        · rw [Finset.mem_singleton.mp hz]; exact hyi
      · rintro e ⟨he, hsub⟩
        obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp he
        have := hi j ⟨hsub (by simp), hsub (by simp)⟩
        simp [this]
  · unfold Finset.blockSizeProfile
    congr 1
    rw [← hD]
    simp only [H, Finset.map_val, Multiset.map_map]
    rfl

theorem bridge : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
    Real.exp (c * Real.sqrt n * Real.log n) ≤ (Hypergraph.blockSizeProfiles n).card := by
  obtain ⟨c, hc, N, hN⟩ := E732P.erdos_732
  refine ⟨c, hc, Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
  obtain ⟨S, hS, hle⟩ := hN n hn
  refine hle.trans ?_
  have hinj : Function.Injective (fun s : Multiset ℕ => s.sort (· ≤ ·)) := by
    intro s t hst
    have := congrArg (fun l : List ℕ => (l : Multiset ℕ)) hst
    simpa using this
  have hsub : S.image (fun s : Multiset ℕ => s.sort (· ≤ ·)) ⊆ Hypergraph.blockSizeProfiles n := by
    intro l hl
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hl
    exact compatible_mem (hS s hs)
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at this
  exact_mod_cast this

end OMA732Bridge

theorem OMA.solution : type_of% @Erdos732.erdos_732.parts.ii := OMA732Bridge.bridge
