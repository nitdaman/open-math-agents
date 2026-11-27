import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1

/-! A weight-fifteen codeword induces the compatible-star configuration of Denniston. -/

open Matrix Finset

namespace OrderSix

variable {n : ℕ}

def incidenceMatrix (incidence : Fin n → Fin n → Bool) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => if incidence i j = true then 1 else 0

lemma incidence_gram (incidence : Fin n → Fin n → Bool) (size : ℕ)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = size)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true) :
    incidenceMatrix incidence * (incidenceMatrix incidence)ᵀ =
      Matrix.of (fun i j => if i = j then (size : ℤ) else 1) := by
  ext i j
  rw [Matrix.mul_apply]
  change ∑ k, (if incidence i k = true then (1 : ℤ) else 0) *
    (if incidence j k = true then 1 else 0) = (if i = j then (size : ℤ) else 1)
  calc
    _ = ∑ k, if incidence i k = true ∧ incidence j k = true then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hi : incidence i k = true <;> by_cases hj : incidence j k = true <;> simp [hi, hj]
    _ = ((Finset.univ.filter fun k => incidence i k = true ∧ incidence j k = true).card : ℤ) := by
      rw [← Finset.sum_filter]
      simp
    _ = _ := by
      by_cases hij : i = j
      · subst j
        simp [rowSize]
      · obtain ⟨point, onBoth, unique⟩ := rowPairs i j hij
        have filter_eq : (Finset.univ.filter fun k => incidence i k = true ∧ incidence j k = true) =
            {point} := by
          ext candidate
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          exact ⟨unique candidate, fun equal => equal ▸ onBoth⟩
        simp [filter_eq, hij]

end OrderSix

open Matrix Finset

namespace OrderTen

def integerExtendedIncidence (incidence : Fin 111 → Fin 111 → Bool) :
    Matrix (Fin 111) (Fin 112) ℤ :=
  Matrix.of fun i => Fin.cons 1 (fun j => OrderSix.incidenceMatrix incidence i j)

def extendedIncidence (incidence : Fin 111 → Fin 111 → Bool) :
    Matrix (Fin 111) (Fin 112) (ZMod 2) :=
  (integerExtendedIncidence incidence).map (Int.castRingHom (ZMod 2))

lemma extendedIncidence_gram_zero (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true) :
    extendedIncidence incidence * (extendedIncidence incidence)ᵀ = 0 := by
  let A := OrderSix.incidenceMatrix incidence
  have gram : A * Aᵀ = Matrix.of (fun i j => if i = j then (11 : ℤ) else 1) :=
    OrderSix.incidence_gram incidence 11 rowSize rowPairs
  ext i j
  have entry : ∑ k, A i k * A j k = (if i = j then (11 : ℤ) else 1) := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply] using
      congrFun (congrFun gram i) j
  have reduced := congrArg (Int.castRingHom (ZMod 2)) entry
  rw [map_sum] at reduced
  simp only [map_mul] at reduced
  change (∑ k, (A i k : ZMod 2) * (A j k : ZMod 2)) =
    ((if i = j then (11 : ℤ) else 1 : ℤ) : ZMod 2) at reduced
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [Matrix.transpose_apply, extendedIncidence, Matrix.map_apply, integerExtendedIncidence,
    Matrix.of_apply, Fin.cons_zero,
    Fin.cons_succ, Matrix.zero_apply]
  change ((1 : ℤ) : ZMod 2) * ((1 : ℤ) : ZMod 2) +
    (∑ k, (A i k : ZMod 2) * (A j k : ZMod 2)) = 0
  rw [reduced]
  by_cases eq : i = j
  · simp only [eq, if_true]
    decide
  · simp only [if_neg eq]
    decide

-- The columns of the transpose generate the binary code of the extended incidence matrix.
lemma extended_row_code_isotropic (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true)
    (x y : Fin 111 → ZMod 2) :
    ((extendedIncidence incidence)ᵀ *ᵥ x) ⬝ᵥ ((extendedIncidence incidence)ᵀ *ᵥ y) = 0 := by
  let B := extendedIncidence incidence
  have gram : B * Bᵀ = 0 := extendedIncidence_gram_zero incidence rowSize rowPairs
  change (Bᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ y) = 0
  have pairing : (Bᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ y) = x ⬝ᵥ ((B * Bᵀ) *ᵥ y) := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec x, mulVec_transpose]
  rw [pairing, gram, Matrix.zero_mulVec, dotProduct_zero]

lemma binary_values : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

lemma hammingNorm_sum_indicator {I : Type} [Fintype I] (u : I → ZMod 2) :
    hammingNorm u = ∑ i, if u i ≠ 0 then (1 : ℕ) else 0 := by
  rw [← Finset.sum_filter]
  simp [hammingNorm]

lemma extended_row_weight (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = 11) (i : Fin 111) :
    hammingNorm (extendedIncidence incidence i) = 12 := by
  rw [hammingNorm_sum_indicator, Fin.sum_univ_succ]
  simp only [extendedIncidence, Matrix.map_apply, integerExtendedIncidence, Matrix.of_apply,
    Fin.cons_zero, Fin.cons_succ]
  change (if ((1 : ℤ) : ZMod 2) ≠ 0 then (1 : ℕ) else 0) +
    (∑ j, if (OrderSix.incidenceMatrix incidence i j : ZMod 2) ≠ 0 then (1 : ℕ) else 0) = 12
  have tail : (∑ j, if (OrderSix.incidenceMatrix incidence i j : ZMod 2) ≠ 0 then (1 : ℕ) else 0) =
      (Finset.univ.filter fun j => incidence i j = true).card := by
    have indicator (j : Fin 111) :
        (if (OrderSix.incidenceMatrix incidence i j : ZMod 2) ≠ 0 then (1 : ℕ) else 0) =
          (if incidence i j = true then 1 else 0) := by
      by_cases bit : incidence i j = true <;> simp [OrderSix.incidenceMatrix, bit]
    simp_rw [indicator]
    rw [← Finset.sum_filter]
    simp
  rw [tail, rowSize]
  decide

lemma overlap_even {I : Type} [Fintype I] (x y : I → ZMod 2) (orthogonal : x ⬝ᵥ y = 0) :
    2 ∣ (Finset.univ.filter fun j => x j ≠ 0 ∧ y j ≠ 0).card := by
  have dot_eq : x ⬝ᵥ y = ((Finset.univ.filter fun j => x j ≠ 0 ∧ y j ≠ 0).card : ZMod 2) := by
    calc
      _ = ∑ i, if x i ≠ 0 ∧ y i ≠ 0 then (1 : ZMod 2) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rcases binary_values (x i) with hx | hx <;> rcases binary_values (y i) with hy | hy <;>
          simp [hx, hy]
      _ = _ := by rw [← Finset.sum_filter]; simp
  rw [dot_eq] at orthogonal
  exact (ZMod.natCast_eq_zero_iff _ 2).mp orthogonal

lemma weight_add_of_orthogonal {I : Type} [Fintype I] (x y : I → ZMod 2)
    (orthogonal : x ⬝ᵥ y = 0) (hx : 4 ∣ hammingNorm x) (hy : 4 ∣ hammingNorm y) :
    4 ∣ hammingNorm (x + y) := by
  have indicator (i : I) :
      (if (x + y) i ≠ 0 then (1 : ℕ) else 0) + 2 * (if x i ≠ 0 ∧ y i ≠ 0 then 1 else 0) =
        (if x i ≠ 0 then 1 else 0) + (if y i ≠ 0 then 1 else 0) := by
    rcases binary_values (x i) with h | h <;> rcases binary_values (y i) with k | k <;>
      simp [Pi.add_apply, h, k, show (1 : ZMod 2) + 1 = 0 by decide]
  have count := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => indicator i)
  have overlapSum : (∑ j, if x j ≠ 0 ∧ y j ≠ 0 then (1 : ℕ) else 0) =
      (Finset.univ.filter fun j => x j ≠ 0 ∧ y j ≠ 0).card := by
    rw [← Finset.sum_filter]
    simp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at count
  rw [← hammingNorm_sum_indicator (x + y), ← hammingNorm_sum_indicator x,
    ← hammingNorm_sum_indicator y, overlapSum] at count
  have overlap := overlap_even x y orthogonal
  omega

-- Every word of the extended binary incidence code has weight divisible by four.
lemma extended_code_doubly_even (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true)
    (a : Fin 111 → ZMod 2) : 4 ∣ hammingNorm ((extendedIncidence incidence)ᵀ *ᵥ a) := by
  let B := extendedIncidence incidence
  have membership : Bᵀ *ᵥ a ∈ Submodule.span (ZMod 2) (Set.range Bᵀ.col) := by
    rw [← Matrix.range_mulVecLin]
    exact ⟨a, rfl⟩
  refine Submodule.span_induction (p := fun x _ => 4 ∣ hammingNorm x) ?_ ?_ ?_ ?_ membership
  · rintro _ ⟨i, rfl⟩
    change 4 ∣ hammingNorm (extendedIncidence incidence i)
    rw [extended_row_weight incidence rowSize]
    decide
  · simp
  · intro x y hx hy hweightX hweightY
    rw [← Matrix.range_mulVecLin] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact weight_add_of_orthogonal _ _
      (extended_row_code_isotropic incidence rowSize rowPairs a b) hweightX hweightY
  · intro c x _ h
    rcases binary_values c with rfl | rfl <;> simp [h]

def pointSupport (w : Fin 112 → ZMod 2) : Finset (Fin 111) :=
  Finset.univ.filter fun p => w p.succ ≠ 0

def pointsOnLine (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111)) (l : Fin 111) :
    Finset (Fin 111) :=
  S.filter fun p => incidence l p = true

lemma extended_weight_eq (w : Fin 112 → ZMod 2) :
    hammingNorm w = (if w 0 ≠ 0 then 1 else 0) + (pointSupport w).card := by
  rw [hammingNorm_sum_indicator, Fin.sum_univ_succ]
  exact congrArg (fun n : ℕ => (if w 0 ≠ 0 then 1 else 0) + n)
    (hammingNorm_sum_indicator (fun p : Fin 111 => w p.succ)).symm

lemma row_dot_word (incidence : Fin 111 → Fin 111 → Bool) (l : Fin 111) (w : Fin 112 → ZMod 2) :
    extendedIncidence incidence l ⬝ᵥ w = w 0 + ((pointsOnLine incidence (pointSupport w) l).card : ZMod 2) := by
  rw [dotProduct, Fin.sum_univ_succ]
  have head : extendedIncidence incidence l 0 = 1 := by
    simp [extendedIncidence, integerExtendedIncidence]
  rw [head, one_mul]
  have sum_eq : (∑ j : Fin 111, extendedIncidence incidence l j.succ * w j.succ) =
      ((pointsOnLine incidence (pointSupport w) l).card : ZMod 2) := by
    calc
      _ = ∑ j : Fin 111, if w j.succ ≠ 0 ∧ incidence l j = true then (1 : ZMod 2) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        change (OrderSix.incidenceMatrix incidence l j : ZMod 2) * w j.succ = _
        by_cases bit : incidence l j = true <;>
          rcases binary_values (w j.succ) with hz | hz <;>
          simp [OrderSix.incidenceMatrix, bit, hz]
      _ = _ := by
        rw [← Finset.sum_filter]
        simp [pointsOnLine, pointSupport, Finset.filter_filter, and_comm]
  exact congrArg (w 0 + ·) sum_eq

lemma sum_pointsOnLine (incidence : Fin 111 → Fin 111 → Bool)
    (columnSize : ∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11)
    (S : Finset (Fin 111)) :
    (∑ l, (pointsOnLine incidence S l).card) = S.card * 11 := by
  calc
    _ = ∑ l : Fin 111, ∑ p ∈ S, if incidence l p = true then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.sum_filter]
      simp [pointsOnLine]
    _ = ∑ p ∈ S, (Finset.univ.filter fun l => incidence l p = true).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_filter]
      simp
    _ = _ := by simp [columnSize]

-- Distinct lines through a point must meet a set that avoids that point in distinct points.
lemma pencil_bound (incidence : Fin 111 → Fin 111 → Bool)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (p : Fin 111) (L S : Finset (Fin 111)) (outside : p ∉ S)
    (through : ∀ l ∈ L, incidence l p = true)
    (meets : ∀ l ∈ L, ∃ q ∈ S, incidence l q = true) : L.card ≤ S.card := by
  classical
  have choiceSet (l : ↥L) := meets l l.property
  choose q in_S on_l using choiceSet
  let f : ↥L → ↥S := fun l => ⟨q l, in_S l⟩
  have injective : Function.Injective f := by
    intro l m same
    have same_point : q l = q m := congrArg Subtype.val same
    have distinct : p ≠ q l := fun h => outside (h.symm ▸ in_S l)
    obtain ⟨line, _, unique⟩ := columnPairs p (q l) distinct
    apply Subtype.ext
    exact (unique l ⟨through l l.property, on_l l⟩).trans
      (unique m ⟨through m m.property, by rw [same_point]; exact on_l m⟩).symm
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f injective

lemma even_intersections_large_support (incidence : Fin 111 → Fin 111 → Bool)
    (columnSize : ∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (hS : S.Nonempty)
    (evenLines : ∀ l, 2 ∣ (pointsOnLine incidence S l).card) : 12 ≤ S.card := by
  classical
  obtain ⟨p, hp⟩ := hS
  let L := Finset.univ.filter fun l => incidence l p = true
  have contains_p (l : Fin 111) (hl : l ∈ L) : incidence l p = true := (Finset.mem_filter.mp hl).2
  have second_point (l : Fin 111) (hl : l ∈ L) : ∃ q ∈ S.erase p, incidence l q = true := by
    let T := pointsOnLine incidence S l
    have p_mem : p ∈ T := Finset.mem_filter.mpr ⟨hp, contains_p l hl⟩
    have positive : 0 < T.card := Finset.card_pos.mpr ⟨p, p_mem⟩
    have even_card : 2 ∣ T.card := evenLines l
    have another : 0 < (T.erase p).card := by
      rw [Finset.card_erase_of_mem p_mem]
      omega
    obtain ⟨q, hq⟩ := Finset.card_pos.mp another
    obtain ⟨ne, in_T⟩ := Finset.mem_erase.mp hq
    obtain ⟨in_S, on_l⟩ := Finset.mem_filter.mp in_T
    exact ⟨q, Finset.mem_erase.mpr ⟨ne, in_S⟩, on_l⟩
  have bound := pencil_bound incidence columnPairs p L (S.erase p) (by simp) contains_p second_point
  rw [Finset.card_erase_of_mem hp] at bound
  change (Finset.univ.filter fun l => incidence l p = true).card ≤ S.card - 1 at bound
  rw [columnSize] at bound
  omega

-- A nonzero word in the extended incidence code has weight at least twelve.
lemma extended_code_minimum_weight (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true)
    (columnSize : ∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (a : Fin 111 → ZMod 2) (nonzero : (extendedIncidence incidence)ᵀ *ᵥ a ≠ 0) :
    12 ≤ hammingNorm ((extendedIncidence incidence)ᵀ *ᵥ a) := by
  let w := (extendedIncidence incidence)ᵀ *ᵥ a
  let S := pointSupport w
  have lineParity (l : Fin 111) : w 0 + ((pointsOnLine incidence S l).card : ZMod 2) = 0 := by
    have ortho := extended_row_code_isotropic incidence rowSize rowPairs (Pi.single l 1) a
    rw [Matrix.mulVec_single_one] at ortho
    change extendedIncidence incidence l ⬝ᵥ w = 0 at ortho
    rwa [row_dot_word] at ortho
  change 12 ≤ hammingNorm w
  have weight : hammingNorm w = (if w 0 ≠ 0 then 1 else 0) + S.card := extended_weight_eq w
  rcases binary_values (w 0) with hzero | hone
  · have supportNonempty : S.Nonempty := by
      by_contra empty
      have emptyS := Finset.not_nonempty_iff_eq_empty.mp empty
      simp [hzero, emptyS] at weight
      exact nonzero weight
    have evenLines (l : Fin 111) : 2 ∣ (pointsOnLine incidence S l).card := by
      apply (ZMod.natCast_eq_zero_iff _ 2).mp
      simpa only [hzero, zero_add] using lineParity l
    have large := even_intersections_large_support incidence columnSize columnPairs S supportNonempty evenLines
    simpa [weight, hzero] using large
  · have each (l : Fin 111) : 1 ≤ (pointsOnLine incidence S l).card := by
      by_contra small
      have emptyCount : (pointsOnLine incidence S l).card = 0 := by omega
      have parity := lineParity l
      simp [hone, emptyCount] at parity
    have bound : (∑ _l : Fin 111, (1 : ℕ)) ≤ ∑ l, (pointsOnLine incidence S l).card :=
      Finset.sum_le_sum fun l _ => each l
    rw [sum_pointsOnLine incidence columnSize] at bound
    simp at bound
    rw [weight, hone, if_pos one_ne_zero]
    omega

end OrderTen

open Matrix Finset

namespace OrderTenWeights

def tailWeight (w : Fin 112 → ZMod 2) : ℕ := (OrderTen.pointSupport w).card

lemma tail_parity_of_doublyEven (w : Fin 112 → ZMod 2) (even : 4 ∣ hammingNorm w) :
    (w 0 = 0 ↔ tailWeight w % 2 = 0) ∧ (tailWeight w % 4 = 0 ∨ tailWeight w % 4 = 3) := by
  have weight := OrderTen.extended_weight_eq w
  change _ = _ + tailWeight w at weight
  rcases OrderTen.binary_values (w 0) with h | h
  · simp only [h, ne_eq, not_true_eq_false, if_false, zero_add] at weight
    rw [weight] at even
    simp only [h, true_iff]
    omega
  · have oneNeZero : (1 : ZMod 2) ≠ 0 := by decide
    rw [h, if_pos oneNeZero] at weight
    rw [weight] at even
    simp only [h, oneNeZero, false_iff]
    omega

lemma extendedIncidence_entry (incidence : Fin 111 → Fin 111 → Bool) (l p : Fin 111) :
    OrderTen.extendedIncidence incidence l p.succ = if incidence l p = true then 1 else 0 := by
  change (OrderSix.incidenceMatrix incidence l p : ZMod 2) = _
  by_cases bit : incidence l p = true <;> simp [OrderSix.incidenceMatrix, bit]

lemma extendedIncidence_head (incidence : Fin 111 → Fin 111 → Bool) (l : Fin 111) :
    OrderTen.extendedIncidence incidence l 0 = 1 := by
  simp [OrderTen.extendedIncidence, OrderTen.integerExtendedIncidence]

lemma row_support (incidence : Fin 111 → Fin 111 → Bool) (l : Fin 111) :
    OrderTen.pointSupport (OrderTen.extendedIncidence incidence l) =
      Finset.univ.filter fun p => incidence l p = true := by
  ext p
  simp only [OrderTen.pointSupport, Finset.mem_filter, Finset.mem_univ, true_and, extendedIncidence_entry]
  split_ifs <;> simp_all

lemma extended_word_explicit (incidence : Fin 111 → Fin 111 → Bool) (a : Fin 111 → ZMod 2) :
    (OrderTen.extendedIncidence incidence)ᵀ *ᵥ a =
      Fin.cons (∑ l, a l) (fun p => ∑ l, a l * (if incidence l p = true then 1 else 0)) := by
  funext i
  refine Fin.cases ?_ (fun p => ?_) i
  · simp [Matrix.mulVec, dotProduct, extendedIncidence_head]
  · simp [Matrix.mulVec, dotProduct, extendedIncidence_entry, mul_comm]

end OrderTenWeights

open Matrix Finset

namespace OrderTenCaseShapes

-- Every ordered pair of distinct points is counted on its unique common line.
lemma sum_ordered_pairs (incidence : Fin 111 → Fin 111 → Bool)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) :
    (∑ l, (OrderTen.pointsOnLine incidence S l).offDiag.card) = S.offDiag.card := by
  classical
  have on_line (l : Fin 111) : (OrderTen.pointsOnLine incidence S l).offDiag =
      S.offDiag.filter (fun pq => incidence l pq.1 = true ∧ incidence l pq.2 = true) := by
    ext pq
    simp only [Finset.mem_offDiag, OrderTen.pointsOnLine, Finset.mem_filter]
    tauto
  calc
    _ = ∑ l : Fin 111, ∑ pq ∈ S.offDiag,
        if incidence l pq.1 = true ∧ incidence l pq.2 = true then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [on_line, ← Finset.sum_filter]
      simp
    _ = ∑ pq ∈ S.offDiag, (1 : ℕ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro pq member
      obtain ⟨l, on_both, unique⟩ := columnPairs pq.1 pq.2 (Finset.mem_offDiag.mp member).2.2
      have lines : (Finset.univ.filter (fun k => incidence k pq.1 = true ∧ incidence k pq.2 = true)) =
          {l} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨unique k, fun eq => eq.symm ▸ on_both⟩
      rw [← Finset.sum_filter, lines]
      simp
    _ = _ := by simp

lemma support_add_count {n : ℕ} (u v : Fin n → ZMod 2) :
    hammingNorm (u + v) + 2 * (Finset.univ.filter fun i => u i ≠ 0 ∧ v i ≠ 0).card =
      hammingNorm u + hammingNorm v := by
  have coordinate (i : Fin n) :
      (if (u + v) i ≠ 0 then (1 : ℕ) else 0) + 2 * (if u i ≠ 0 ∧ v i ≠ 0 then 1 else 0) =
      (if u i ≠ 0 then 1 else 0) + (if v i ≠ 0 then 1 else 0) := by
    rcases OrderTen.binary_values (u i) with ub | ub <;> rcases OrderTen.binary_values (v i) with vb | vb <;>
      simp [Pi.add_apply, ub, vb, show (1 : ZMod 2) + 1 = 0 by decide]
  have count := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => coordinate i)
  have overlap : (∑ i : Fin n, if u i ≠ 0 ∧ v i ≠ 0 then (1 : ℕ) else 0) =
      (Finset.univ.filter fun i => u i ≠ 0 ∧ v i ≠ 0).card := by
    rw [← Finset.sum_filter]
    simp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at count
  rwa [← OrderTen.hammingNorm_sum_indicator (u + v), ← OrderTen.hammingNorm_sum_indicator u,
    ← OrderTen.hammingNorm_sum_indicator v, overlap] at count

lemma tail_weight_add_row (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (w : Fin 112 → ZMod 2) (l : Fin 111) :
    OrderTenWeights.tailWeight (w + OrderTen.extendedIncidence incidence l) +
      2 * (OrderTen.pointsOnLine incidence (OrderTen.pointSupport w) l).card =
      OrderTenWeights.tailWeight w + 11 := by
  let u := fun p : Fin 111 => w p.succ
  let v := fun p : Fin 111 => OrderTen.extendedIncidence incidence l p.succ
  have row_weight : hammingNorm v = 11 := by
    change (OrderTen.pointSupport (OrderTen.extendedIncidence incidence l)).card = 11
    rw [OrderTenWeights.row_support, rowSize]
  have overlap : (Finset.univ.filter fun p : Fin 111 => u p ≠ 0 ∧ v p ≠ 0) =
      OrderTen.pointsOnLine incidence (OrderTen.pointSupport w) l := by
    ext p
    simp only [u, v, OrderTen.pointsOnLine, OrderTen.pointSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, OrderTenWeights.extendedIncidence_entry]
    split_ifs <;> simp_all
  have counts := support_add_count u v
  rw [overlap, row_weight] at counts
  exact counts

def linesWithIntersection (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111)) (k : ℕ) :
    Finset (Fin 111) := Finset.univ.filter fun l => (OrderTen.pointsOnLine incidence S l).card = k

def atPoint (incidence : Fin 111 → Fin 111 → Bool) (p : Fin 111) : Finset (Fin 111) :=
  Finset.univ.filter fun l => incidence l p = true

lemma sum_pencil_avoiding_center (incidence : Fin 111 → Fin 111 → Bool)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (p : Fin 111) (not_center : p ∉ S) :
    (∑ l ∈ atPoint incidence p, (OrderTen.pointsOnLine incidence S l).card) = S.card := by
  classical
  calc
    _ = ∑ l ∈ atPoint incidence p, ∑ q ∈ S, if incidence l q = true then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.sum_filter]
      simp [OrderTen.pointsOnLine]
    _ = ∑ q ∈ S, (1 : ℕ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      have distinct : p ≠ q := fun equal => not_center (equal.symm ▸ hq)
      obtain ⟨l, on_both, unique⟩ := columnPairs p q distinct
      have one_line : (atPoint incidence p).filter (fun k => incidence k q = true) = {l} := by
        ext k
        simp only [atPoint, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨unique k, fun eq => eq.symm ▸ on_both⟩
      rw [← Finset.sum_filter, one_line]
      simp
    _ = _ := by simp

end OrderTenCaseShapes

open Matrix Finset

namespace OrderTenCaseShapes

lemma even_set_line_bound (incidence : Fin 111 → Fin 111 → Bool)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111))
    (even_lines : ∀ l, 2 ∣ (OrderTen.pointsOnLine incidence S l).card) (l : Fin 111) :
    (OrderTen.pointsOnLine incidence S l).card ≤ S.card - 10 := by
  classical
  by_cases empty : (OrderTen.pointsOnLine incidence S l).card = 0
  · simp [empty]
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero empty)
  obtain ⟨in_S, on_l⟩ := Finset.mem_filter.mp hp
  let L := atPoint incidence p
  have l_mem : l ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ _, on_l⟩
  have L_size : L.card = 11 := columnSize p
  let k := fun m => (OrderTen.pointsOnLine incidence (S.erase p) m).card
  have total : (∑ m ∈ L, k m) = S.card - 1 := by
    dsimp only [L, k]
    rw [sum_pencil_avoiding_center incidence columnPairs _ p (by simp),
      Finset.card_erase_of_mem in_S]
  have on_pencil (m : Fin 111) (hm : m ∈ L) :
      (OrderTen.pointsOnLine incidence S m).card = k m + 1 := by
    have p_mem : p ∈ OrderTen.pointsOnLine incidence S m :=
      Finset.mem_filter.mpr ⟨in_S, (Finset.mem_filter.mp hm).2⟩
    have erase_commutes : OrderTen.pointsOnLine incidence (S.erase p) m =
        (OrderTen.pointsOnLine incidence S m).erase p := by
      ext q
      simp [OrderTen.pointsOnLine, and_assoc]
    dsimp only [k]
    rw [erase_commutes, Finset.card_erase_of_mem p_mem]
    have := Finset.card_pos.mpr ⟨p, p_mem⟩
    omega
  have one_le (m : Fin 111) (hm : m ∈ L) : 1 ≤ k m := by
    have even := even_lines m
    rw [on_pencil m hm] at even
    omega
  have other_lines := Finset.sum_le_sum (s := L.erase l)
    (f := fun _ => (1 : ℕ)) (g := k) (fun m hm => one_le m (Finset.mem_of_mem_erase hm))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem l_mem,
    L_size] at other_lines
  have separated := Finset.sum_erase_add L k l_mem
  rw [total] at separated
  have lower := one_le l l_mem
  rw [on_pencil l l_mem]
  omega

lemma twelve_even_set_is_hyperoval (incidence : Fin 111 → Fin 111 → Bool)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 12)
    (even_lines : ∀ l, 2 ∣ (OrderTen.pointsOnLine incidence S l).card) (l : Fin 111) :
    (OrderTen.pointsOnLine incidence S l).card = 0 ∨
      (OrderTen.pointsOnLine incidence S l).card = 2 := by
  have bound := even_set_line_bound incidence columnSize columnPairs S even_lines l
  have even := even_lines l
  omega

lemma row_word_line_parity (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true)
    (a : Fin 111 → ZMod 2) (l : Fin 111) :
    let w := (OrderTen.extendedIncidence incidence)ᵀ *ᵥ a
    (OrderTen.pointsOnLine incidence (OrderTen.pointSupport w) l).card % 2 = (w 0).val := by
  intro w
  have ortho := OrderTen.extended_row_code_isotropic incidence rowSize rowPairs (Pi.single l 1) a
  rw [Matrix.mulVec_single_one] at ortho
  change OrderTen.extendedIncidence incidence l ⬝ᵥ w = 0 at ortho
  rw [OrderTen.row_dot_word] at ortho
  have eq := eq_neg_of_add_eq_zero_left ortho
  have sign : ∀ b : ZMod 2, -b = b := by decide
  have val := congrArg ZMod.val eq.symm
  rw [sign ((OrderTen.pointsOnLine incidence (OrderTen.pointSupport w) l).card : ZMod 2)] at val
  simpa only [ZMod.val_natCast] using val

theorem weight_twelve_line_sizes (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (a : Fin 111 → ZMod 2)
    (weight12 : OrderTenWeights.tailWeight ((OrderTen.extendedIncidence incidence)ᵀ *ᵥ a) = 12)
    (l : Fin 111) :
    let w := (OrderTen.extendedIncidence incidence)ᵀ *ᵥ a
    let k := (OrderTen.pointsOnLine incidence (OrderTen.pointSupport w) l).card
    k = 0 ∨ k = 2 := by
  intro w k
  have head : w 0 = 0 := by
    have parity := (OrderTenWeights.tail_parity_of_doublyEven w
      (OrderTen.extended_code_doubly_even incidence rowSize rowPairs a)).1
    exact parity.mpr (by change OrderTenWeights.tailWeight w = 12 at weight12; omega)
  apply twelve_even_set_is_hyperoval incidence columnSize columnPairs _ weight12 _ l
  intro m
  have parity := row_word_line_parity incidence rowSize rowPairs a m
  change (OrderTen.pointsOnLine incidence (OrderTen.pointSupport w) m).card % 2 = (w 0).val at parity
  rw [head, ZMod.val_zero] at parity
  exact Nat.dvd_of_mod_eq_zero parity

theorem weight_fifteen_line_sizes (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (a : Fin 111 → ZMod 2)
    (weight15 : OrderTenWeights.tailWeight ((OrderTen.extendedIncidence incidence)ᵀ *ᵥ a) = 15)
    (l : Fin 111) :
    let w := (OrderTen.extendedIncidence incidence)ᵀ *ᵥ a
    let k := (OrderTen.pointsOnLine incidence (OrderTen.pointSupport w) l).card
    k = 1 ∨ k = 3 ∨ k = 5 := by
  intro w k
  change OrderTenWeights.tailWeight w = 15 at weight15
  have head : w 0 = 1 := by
    apply (OrderTen.binary_values (w 0)).resolve_left
    intro zero
    have parity := (OrderTenWeights.tail_parity_of_doublyEven w
      (OrderTen.extended_code_doubly_even incidence rowSize rowPairs a)).1.mp zero
    omega
  have odd := row_word_line_parity incidence rowSize rowPairs a l
  change k % 2 = (w 0).val at odd
  rw [head, ZMod.val_one] at odd
  let E := OrderTen.extendedIncidence incidence
  let c := a + Pi.single l 1
  let v := Eᵀ *ᵥ c
  have add_row : v = w + E l := by
    change Eᵀ *ᵥ (a + Pi.single l 1) = _
    rw [Matrix.mulVec_add, Matrix.mulVec_single_one]
    rfl
  have v_head : v 0 = 0 := by
    rw [add_row, Pi.add_apply, head]
    change 1 + OrderTen.extendedIncidence incidence l 0 = 0
    rw [OrderTenWeights.extendedIncidence_head]
    decide
  have balance := tail_weight_add_row incidence rowSize w l
  change OrderTenWeights.tailWeight (w + E l) + 2 * k = OrderTenWeights.tailWeight w + 11 at balance
  rw [← add_row, weight15] at balance
  have line_bound : k ≤ 11 := by
    change (OrderTen.pointsOnLine incidence (OrderTen.pointSupport w) l).card ≤ 11
    rw [← rowSize l]
    exact Finset.card_le_card (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hp).2⟩)
  have nonzero : v ≠ 0 := by
    intro zero
    rw [zero] at balance
    have weight_zero : OrderTenWeights.tailWeight (0 : Fin 112 → ZMod 2) = 0 := by
      simp [OrderTenWeights.tailWeight, OrderTen.pointSupport]
    omega
  have minimum := OrderTen.extended_code_minimum_weight incidence rowSize rowPairs columnSize
    columnPairs c nonzero
  change 12 ≤ hammingNorm v at minimum
  rw [OrderTen.extended_weight_eq, v_head] at minimum
  change 12 ≤ (if (0 : ZMod 2) ≠ 0 then 1 else 0) + OrderTenWeights.tailWeight v at minimum
  simp at minimum
  by_contra! outside_cases
  have k7 : k = 7 := by omega
  have v_weight : OrderTenWeights.tailWeight v = 12 := by omega
  have at_line := weight_twelve_line_sizes incidence rowSize rowPairs columnSize columnPairs c v_weight l
  change (OrderTen.pointsOnLine incidence (OrderTen.pointSupport v) l).card = 0 ∨
    (OrderTen.pointsOnLine incidence (OrderTen.pointSupport v) l).card = 2 at at_line
  let T := Finset.univ.filter fun p => incidence l p = true
  have complement : OrderTen.pointsOnLine incidence (OrderTen.pointSupport v) l =
      T \ OrderTen.pointsOnLine incidence (OrderTen.pointSupport w) l := by
    ext p
    by_cases incident : incidence l p = true
    · rcases OrderTen.binary_values (w p.succ) with h | h <;>
        simp [add_row, E, OrderTen.pointsOnLine, OrderTen.pointSupport,
          OrderTenWeights.extendedIncidence_entry, T, incident, h,
          show (1 : ZMod 2) + 1 = 0 by decide]
    · simp [OrderTen.pointsOnLine, T, incident]
  have subset : OrderTen.pointsOnLine incidence (OrderTen.pointSupport w) l ⊆ T :=
    fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
  rw [complement, Finset.card_sdiff_of_subset subset] at at_line
  have T_card : T.card = 11 := rowSize l
  rw [T_card] at at_line
  change 11 - k = 0 ∨ 11 - k = 2 at at_line
  omega

lemma fifteen_point_line_counts (incidence : Fin 111 → Fin 111 → Bool)
    (columnSize : ∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) :
    (linesWithIntersection incidence S 1).card = 90 ∧
      (linesWithIntersection incidence S 3).card = 15 ∧
      (linesWithIntersection incidence S 5).card = 6 := by
  let k := fun l => (OrderTen.pointsOnLine incidence S l).card
  let n := fun j => (linesWithIntersection incidence S j).card
  have points : (∑ l, k l) = 165 := by
    change (∑ l, (OrderTen.pointsOnLine incidence S l).card) = _
    rw [OrderTen.sum_pointsOnLine incidence columnSize, size]
  have pairs : (∑ l, (k l*k l - k l)) = 210 := by
    calc
      _ = ∑ l, (OrderTen.pointsOnLine incidence S l).offDiag.card := by simp only [k, Finset.offDiag_card]
      _ = S.offDiag.card := sum_ordered_pairs incidence columnPairs S
      _ = _ := by rw [Finset.offDiag_card, size]
  have countIndicator (j : ℕ) : (∑ l : Fin 111, if k l = j then (1 : ℕ) else 0) = n j := by
    rw [← Finset.sum_filter]
    simp [n, linesWithIntersection, k]
  have sumCoeff (m j : ℕ) : (∑ l : Fin 111, m * (if k l = j then (1 : ℕ) else 0)) = m * n j := by
    rw [← Finset.mul_sum, countIndicator]
  have five_count (l : Fin 111) : (k l*k l - k l) + 3 = 3*k l + 8*(if k l = 5 then 1 else 0) := by
    rcases lineCases l with h | h | h <;> simp [k, h]
  have five := Finset.sum_congr (s₁ := Finset.univ) rfl (fun l _ => five_count l)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Fintype.card_fin, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, countIndicator, points, pairs] at five
  have three_count (l : Fin 111) : k l = 1 + 2*(if k l = 3 then 1 else 0) + 4*(if k l = 5 then 1 else 0) := by
    rcases lineCases l with h | h | h <;> simp [k, h]
  have three := Finset.sum_congr (s₁ := Finset.univ) rfl (fun l _ => three_count l)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Fintype.card_fin, Finset.card_univ,
    nsmul_eq_mul, mul_one, sumCoeff, points] at three
  have one_count (l : Fin 111) : (1 : ℕ) =
      (if k l = 1 then 1 else 0) + (if k l = 3 then 1 else 0) + (if k l = 5 then 1 else 0) := by
    rcases lineCases l with h | h | h <;> simp [k, h]
  have one := Finset.sum_congr (s₁ := Finset.univ) rfl (fun l _ => one_count l)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Fintype.card_fin, Finset.card_univ,
    nsmul_eq_mul, mul_one, countIndicator] at one
  change n 1 = 90 ∧ n 3 = 15 ∧ n 5 = 6
  omega

lemma sum_restricted_incidence (incidence : Fin 111 → Fin 111 → Bool)
    (L S : Finset (Fin 111)) :
    (∑ p ∈ S, (OrderTen.pointsOnLine (Function.swap incidence) L p).card) =
      ∑ l ∈ L, (OrderTen.pointsOnLine incidence S l).card := by
  calc
    _ = ∑ p ∈ S, ∑ l ∈ L, if incidence l p = true then (1 : ℕ) else 0 :=
      Finset.sum_congr rfl (fun p _ => (Finset.sum_boole (fun l => incidence l p = true) L).symm)
    _ = ∑ l ∈ L, ∑ p ∈ S, if incidence l p = true then (1 : ℕ) else 0 := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun l _ => Finset.sum_boole (fun p => incidence l p = true) S)

-- Each support point is the intersection of two of the six five-secants.
lemma fifteen_point_heavy_incidence (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) (p : Fin 111) (hp : p ∈ S) :
    (OrderTen.pointsOnLine (Function.swap incidence)
      (linesWithIntersection incidence S 5) p).card = 2 := by
  let L := linesWithIntersection incidence S 5
  let d := fun q => (OrderTen.pointsOnLine (Function.swap incidence) L q).card
  have six : L.card = 6 := (fifteen_point_line_counts incidence columnSize columnPairs S size lineCases).2.2
  have line_sum : (∑ q ∈ S, d q) = 30 := by
    dsimp only [d]
    rw [sum_restricted_incidence]
    have each (l : Fin 111) (hl : l ∈ L) :
        (OrderTen.pointsOnLine incidence S l).card = 5 :=
      (Finset.mem_filter.mp hl).2
    rw [Finset.sum_congr rfl each]
    simp [six]
  have pair_sum : (∑ q ∈ S,
      (OrderTen.pointsOnLine (Function.swap incidence) L q).offDiag.card) ≤ 30 := by
    calc
      _ ≤ ∑ q : Fin 111, (OrderTen.pointsOnLine (Function.swap incidence) L q).offDiag.card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = L.offDiag.card := sum_ordered_pairs (Function.swap incidence) rowPairs L
      _ = _ := by rw [Finset.offDiag_card, six]
  have square_sum : (∑ q ∈ S, d q * d q) ≤ 60 := by
    have identity (q : Fin 111) :
        (OrderTen.pointsOnLine (Function.swap incidence) L q).offDiag.card + d q = d q * d q := by
      rw [Finset.offDiag_card]
      change d q * d q - d q + d q = d q * d q
      exact Nat.sub_add_cancel (by nlinarith [sq_nonneg (d q - 1)])
    have total := Finset.sum_congr (s₁ := S) rfl (fun q _ => identity q)
    rw [Finset.sum_add_distrib, line_sum] at total
    omega
  have Cauchy (q : Fin 111) : 4 * d q ≤ d q * d q + 4 := by
    have inequality : (4 : ℤ) * (d q : ℤ) ≤ (d q : ℤ) * (d q : ℤ) + 4 := by
      nlinarith [sq_nonneg ((d q : ℤ) - 2)]
    exact_mod_cast inequality
  change d p = 2
  by_contra neq
  have strict : 4 * d p < d p * d p + 4 := by
    have nz : (d p : ℤ) - 2 ≠ 0 := by exact sub_ne_zero.mpr (by exact_mod_cast neq)
    have inequality : (4 : ℤ) * (d p : ℤ) < (d p : ℤ) * (d p : ℤ) + 4 := by
      nlinarith [sq_pos_of_ne_zero nz]
    exact_mod_cast inequality
  have sum_strict := Finset.sum_lt_sum (s := S) (fun q _ => Cauchy q) ⟨p, hp, strict⟩
  simp only [← Finset.mul_sum, line_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, size] at sum_strict
  omega

lemma outside_fifteen_point_heavy_incidence (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) (p : Fin 111) (hp : p ∉ S) :
    (OrderTen.pointsOnLine (Function.swap incidence)
      (linesWithIntersection incidence S 5) p).card ≤ 1 := by
  let L := linesWithIntersection incidence S 5
  let pairs := fun q => (OrderTen.pointsOnLine (Function.swap incidence) L q).offDiag.card
  have six : L.card = 6 := (fifteen_point_line_counts incidence columnSize columnPairs S size lineCases).2.2
  have all : (∑ q, pairs q) = 30 := by
    rw [show (∑ q, pairs q) = L.offDiag.card from sum_ordered_pairs (Function.swap incidence) rowPairs L,
      Finset.offDiag_card, six]
  have in_support (q : Fin 111) (hq : q ∈ S) : pairs q = 2 := by
    have degrees := fifteen_point_heavy_incidence incidence rowPairs columnSize columnPairs S size lineCases q hq
    dsimp only [pairs, L]
    rw [Finset.offDiag_card, degrees]
  have sum_support : (∑ q ∈ S, pairs q) = 30 := by
    rw [Finset.sum_congr rfl in_support]
    simp [size]
  have bound := Finset.sum_le_sum_of_subset (Finset.subset_univ (insert p S)) (f := pairs)
  rw [Finset.sum_insert hp, sum_support, all] at bound
  have vanished : pairs p = 0 := by omega
  change (OrderTen.pointsOnLine (Function.swap incidence) L p).offDiag.card = 0 at vanished
  rw [Finset.offDiag_card] at vanished
  let d := (OrderTen.pointsOnLine (Function.swap incidence) L p).card
  change d * d - d = 0 at vanished
  change d ≤ 1
  by_contra! large
  have grew : d * 2 ≤ d * d := Nat.mul_le_mul_left d large
  omega

def outsideHeavyPoints (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111)) :
    Finset (Fin 111) :=
  (Finset.univ \ S).filter fun p =>
    (OrderTen.pointsOnLine (Function.swap incidence) (linesWithIntersection incidence S 5) p).card = 1

-- A light line has four outside heavy points, a medium line has none,
-- and a heavy line has six.
theorem fifteen_point_block_sizes (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) (l : Fin 111) :
    let k := (OrderTen.pointsOnLine incidence S l).card
    let b := (OrderTen.pointsOnLine incidence (outsideHeavyPoints incidence S) l).card
    (k = 1 ∧ b = 4) ∨ (k = 3 ∧ b = 0) ∨ (k = 5 ∧ b = 6) := by
  classical
  intro k b
  let L := linesWithIntersection incidence S 5
  let d := fun q => (OrderTen.pointsOnLine (Function.swap incidence) L q).card
  let B := outsideHeavyPoints incidence S
  let M := Finset.univ.filter fun p => incidence l p = true
  have inside (q : Fin 111) (hq : q ∈ S) : d q = 2 :=
    fifteen_point_heavy_incidence incidence rowPairs columnSize columnPairs S size lineCases q hq
  have outside (q : Fin 111) (hq : q ∉ S) : d q ≤ 1 :=
    outside_fifteen_point_heavy_incidence incidence rowPairs columnSize columnPairs S size lineCases q hq
  have B_mem (q : Fin 111) : q ∈ B ↔ q ∉ S ∧ d q = 1 := by
    simp [B, outsideHeavyPoints, d, L]
  have point (q : Fin 111) :
      d q = (if q ∈ S then 2 else 0) + (if q ∈ B then 1 else 0) := by
    by_cases hq : q ∈ S
    · have notB : q ∉ B := fun h => (B_mem q).mp h |>.1 <| hq
      simp [inside q hq, hq, notB]
    · have le := outside q hq
      rw [if_neg hq, zero_add]
      by_cases h : q ∈ B
      · rw [if_pos h]
        exact ((B_mem q).mp h).2
      · rw [if_neg h]
        have not_one : d q ≠ 1 := fun eq => h ((B_mem q).mpr ⟨hq, eq⟩)
        omega
  have moment : (∑ q ∈ M, d q) = 2 * k + b := by
    rw [Finset.sum_congr rfl (fun q _ => point q), Finset.sum_add_distrib]
    have two (q : Fin 111) : (if q ∈ S then 2 else 0 : ℕ) = 2 * (if q ∈ S then 1 else 0) := by
      split_ifs <;> simp
    simp only [two, ← Finset.mul_sum, Finset.sum_boole]
    have filter (T : Finset (Fin 111)) : M.filter (· ∈ T) = OrderTen.pointsOnLine incidence T l := by
      ext q
      simp [M, OrderTen.pointsOnLine, and_comm]
    rw [filter, filter]
    rfl
  have six : L.card = 6 := (fifteen_point_line_counts incidence columnSize columnPairs S size lineCases).2.2
  have meet (m : Fin 111) (different : m ≠ l) : (OrderTen.pointsOnLine incidence M m).card = 1 := by
    obtain ⟨p, hp, unique⟩ := rowPairs m l different
    have singleton : OrderTen.pointsOnLine incidence M m = {p} := by
      ext q
      simp only [OrderTen.pointsOnLine, M, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, and_comm (a := incidence l q = true)]
      exact ⟨unique q, fun eq => eq.symm ▸ hp⟩
    rw [singleton]
    simp
  have swapped : (∑ q ∈ M, d q) = ∑ m ∈ L, (OrderTen.pointsOnLine incidence M m).card :=
    sum_restricted_incidence incidence L M
  have heavy_iff : l ∈ L ↔ k = 5 := by simp [L, linesWithIntersection, k]
  have nonheavy (h : k ≠ 5) : 2 * k + b = 6 := by
    rw [← moment, swapped]
    rw [Finset.sum_congr rfl (fun m hm => meet m (fun eq => h (heavy_iff.mp (eq ▸ hm))))]
    simp [six]
  rcases lineCases l with light | medium | heavy
  · left
    change k = 1 at light
    have eq := nonheavy (by omega)
    exact ⟨light, by omega⟩
  · right; left
    change k = 3 at medium
    have eq := nonheavy (by omega)
    exact ⟨medium, by omega⟩
  · right; right
    change k = 5 at heavy
    refine ⟨heavy, ?_⟩
    have in_L := heavy_iff.mpr heavy
    have rest : (∑ m ∈ L.erase l, (OrderTen.pointsOnLine incidence M m).card) = 5 := by
      rw [Finset.sum_congr rfl (fun m hm => meet m (Finset.mem_erase.mp hm).1)]
      simp [Finset.card_erase_of_mem in_L, six]
    have same : OrderTen.pointsOnLine incidence M l = M := by
      ext q
      simp [OrderTen.pointsOnLine, M]
    rw [← Finset.sum_erase_add _ _ in_L, rest, same] at swapped
    have M_size : M.card = 11 := rowSize l
    omega

theorem fifteen_point_support_labels (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) :
    let L := linesWithIntersection incidence S 5
    ∃ relabel : S ≃ ↥(L.powersetCard 2), ∀ (p : S) (l : Fin 111),
      l ∈ (relabel p).val ↔ l ∈ L ∧ incidence l p.val = true := by
  classical
  intro L
  let d := fun q => OrderTen.pointsOnLine (Function.swap incidence) L q
  have in_targets (p : S) : d p.val ∈ L.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    exact fifteen_point_heavy_incidence incidence rowPairs columnSize columnPairs S size
      lineCases p.val p.property
  let f : S → ↥(L.powersetCard 2) := fun p => ⟨d p.val, in_targets p⟩
  have injective : Function.Injective f := by
    intro p q hf
    have eq : d p.val = d q.val := congrArg Subtype.val hf
    have card := (Finset.mem_powersetCard.mp (in_targets p)).2
    obtain ⟨l, m, different, pair⟩ := Finset.card_eq_two.mp card
    have on_l : l ∈ d p.val := by rw [pair]; simp
    have on_m : m ∈ d p.val := by rw [pair]; simp
    have q_l : l ∈ d q.val := eq ▸ on_l
    have q_m : m ∈ d q.val := eq ▸ on_m
    obtain ⟨r, _, unique⟩ := rowPairs l m different
    apply Subtype.ext
    exact (unique p.val ⟨(Finset.mem_filter.mp on_l).2, (Finset.mem_filter.mp on_m).2⟩).trans
      (unique q.val ⟨(Finset.mem_filter.mp q_l).2, (Finset.mem_filter.mp q_m).2⟩).symm
  have six : L.card = 6 := (fifteen_point_line_counts incidence columnSize columnPairs S size lineCases).2.2
  have cards : Fintype.card S = Fintype.card ↥(L.powersetCard 2) := by
    rw [Fintype.card_coe, Fintype.card_coe, Finset.card_powersetCard, six, size]
    decide
  have bijective := (Fintype.bijective_iff_injective_and_card f).mpr ⟨injective, cards⟩
  refine ⟨Equiv.ofBijective f bijective, ?_⟩
  intro p l
  exact Finset.mem_filter

end OrderTenCaseShapes

open Matrix Finset

namespace OrderTenCaseShapes

def supportDegree (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111))
    (k : ℕ) (p : Fin 111) : Finset (Fin 111) :=
  OrderTen.pointsOnLine (Function.swap incidence) (linesWithIntersection incidence S k) p

lemma mem_supportDegree {incidence : Fin 111 → Fin 111 → Bool} {S : Finset (Fin 111)}
    {k : ℕ} {p l : Fin 111} :
    l ∈ supportDegree incidence S k p ↔
      (OrderTen.pointsOnLine incidence S l).card = k ∧ incidence l p = true := by
  unfold supportDegree
  rw [OrderTen.pointsOnLine, Finset.mem_filter]
  unfold linesWithIntersection
  rw [Finset.mem_filter]
  simp

lemma sum_pencil_containing_center (incidence : Fin 111 → Fin 111 → Bool)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (p : Fin 111) (inside : p ∈ S) :
    (∑ l ∈ atPoint incidence p, (OrderTen.pointsOnLine incidence S l).card) = S.card + 10 := by
  have without := sum_pencil_avoiding_center incidence columnPairs (S.erase p) p (by simp)
  rw [Finset.card_erase_of_mem inside] at without
  have split (l : Fin 111) (hl : l ∈ atPoint incidence p) :
      (OrderTen.pointsOnLine incidence S l).card =
        (OrderTen.pointsOnLine incidence (S.erase p) l).card + 1 := by
    have member : p ∈ OrderTen.pointsOnLine incidence S l :=
      Finset.mem_filter.mpr ⟨inside, (Finset.mem_filter.mp hl).2⟩
    have same : OrderTen.pointsOnLine incidence (S.erase p) l =
        (OrderTen.pointsOnLine incidence S l).erase p := by
      ext q
      simp [OrderTen.pointsOnLine, and_assoc]
    rw [same, Finset.card_erase_of_mem member]
    have := Finset.card_pos.mpr ⟨p, member⟩
    omega
  calc
    _ = ∑ l ∈ atPoint incidence p, ((OrderTen.pointsOnLine incidence (S.erase p) l).card + 1) :=
      Finset.sum_congr rfl split
    _ = _ := by
      rw [Finset.sum_add_distrib, without]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, columnSize]
      have := Finset.card_pos.mpr ⟨p, inside⟩
      omega

lemma fifteen_point_degrees (incidence : Fin 111 → Fin 111 → Bool)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) (p : Fin 111) :
    let c := fun k => (supportDegree incidence S k p).card
    (if p ∈ S then c 3 + 2 * c 5 = 7 else c 3 + 2 * c 5 = 2) ∧
      c 1 + c 3 + c 5 = 11 := by
  classical
  intro c
  let L := atPoint incidence p
  let k := fun l => (OrderTen.pointsOnLine incidence S l).card
  have card_L : L.card = 11 := columnSize p
  have indicator (j : ℕ) : (∑ l ∈ L, if k l = j then (1 : ℕ) else 0) = c j := by
    have filtered : L.filter (fun l => k l = j) = supportDegree incidence S j p := by
      ext l
      rw [Finset.mem_filter, mem_supportDegree]
      change (l ∈ Finset.univ.filter (fun m => incidence m p = true) ∧ k l = j) ↔
        (k l = j ∧ incidence l p = true)
      simp [and_comm]
    rw [Finset.sum_boole, filtered]
    rfl
  have part (l : Fin 111) : (1 : ℕ) =
      (if k l = 1 then 1 else 0) + (if k l = 3 then 1 else 0) + (if k l = 5 then 1 else 0) := by
    rcases lineCases l with h | h | h <;> simp [k, h]
  have moments (l : Fin 111) : k l = 1 + 2 * (if k l = 3 then 1 else 0) +
      4 * (if k l = 5 then 1 else 0) := by
    rcases lineCases l with h | h | h <;> simp [k, h]
  have partition := Finset.sum_congr (s₁ := L) rfl (fun l _ => part l)
  have weighted := Finset.sum_congr (s₁ := L) rfl (fun l _ => moments l)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, card_L,
    ← Finset.mul_sum, indicator] at partition weighted
  change (∑ l ∈ L, k l) = 11 + 2 * c 3 + 4 * c 5 at weighted
  refine ⟨?_, partition.symm⟩
  by_cases hp : p ∈ S
  · rw [if_pos hp]
    have eq := sum_pencil_containing_center incidence columnSize columnPairs S p hp
    change (∑ l ∈ L, k l) = S.card + 10 at eq
    omega
  · rw [if_neg hp]
    have eq := sum_pencil_avoiding_center incidence columnPairs S p hp
    change (∑ l ∈ L, k l) = S.card at eq
    omega

def exteriorPoints (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111)) :
    Finset (Fin 111) :=
  Finset.univ.filter fun p => (supportDegree incidence S 5 p).card = 0

lemma exterior_has_two_medium_lines (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) (p : Fin 111) (hp : p ∈ exteriorPoints incidence S) :
    p ∉ S ∧ (supportDegree incidence S 3 p).card = 2 := by
  have zero : (supportDegree incidence S 5 p).card = 0 := (Finset.mem_filter.mp hp).2
  have out : p ∉ S := by
    intro in_S
    have two : (supportDegree incidence S 5 p).card = 2 :=
      fifteen_point_heavy_incidence incidence rowPairs columnSize columnPairs S size lineCases p in_S
    omega
  have degrees := (fifteen_point_degrees incidence columnSize columnPairs S size lineCases p).1
  rw [if_neg out] at degrees
  dsimp only at degrees
  rw [zero] at degrees
  exact ⟨out, by omega⟩

lemma medium_has_no_outside_heavy (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (m p : Fin 111) (medium : (OrderTen.pointsOnLine incidence S m).card = 3)
    (on_m : incidence m p = true) (hp : p ∉ S) :
    p ∈ exteriorPoints incidence S := by
  have le : (supportDegree incidence S 5 p).card ≤ 1 :=
    outside_fifteen_point_heavy_incidence incidence rowPairs columnSize columnPairs S size lineCases p hp
  have zero : (supportDegree incidence S 5 p).card = 0 := by
    by_contra h
    have one : (supportDegree incidence S 5 p).card = 1 := by omega
    have member : p ∈ outsideHeavyPoints incidence S :=
      Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hp⟩, one⟩
    have pos := Finset.card_pos.mpr
      (show (OrderTen.pointsOnLine incidence (outsideHeavyPoints incidence S) m).Nonempty from
        ⟨p, Finset.mem_filter.mpr ⟨member, on_m⟩⟩)
    have block := fifteen_point_block_sizes incidence rowSize rowPairs columnSize columnPairs S size lineCases m
    change ((OrderTen.pointsOnLine incidence S m).card = 1 ∧ _) ∨
      ((OrderTen.pointsOnLine incidence S m).card = 3 ∧ _) ∨
      ((OrderTen.pointsOnLine incidence S m).card = 5 ∧ _) at block
    rcases block with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, zero⟩

lemma medium_matches_heavy_lines (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (m l : Fin 111) (m_size : (OrderTen.pointsOnLine incidence S m).card = 3)
    (l_size : (OrderTen.pointsOnLine incidence S l).card = 5) :
    ∃! p, p ∈ S ∧ incidence m p = true ∧ incidence l p = true := by
  have different : m ≠ l := by intro eq; rw [eq, l_size] at m_size; omega
  obtain ⟨p, meets, unique⟩ := rowPairs m l different
  have in_S : p ∈ S := by
    by_contra hp
    have out := medium_has_no_outside_heavy incidence rowSize rowPairs columnSize columnPairs
      S size lineCases m p m_size meets.1 hp
    have zero : (supportDegree incidence S 5 p).card = 0 := (Finset.mem_filter.mp out).2
    have pos := Finset.card_pos.mpr ⟨l, mem_supportDegree.mpr ⟨l_size, meets.2⟩⟩
    omega
  exact ⟨p, ⟨in_S, meets⟩, fun q h => unique q h.2⟩

lemma light_pencil_card (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) (p : Fin 111) (hp : p ∈ S) :
    (supportDegree incidence S 1 p).card = 6 := by
  have heavy : (supportDegree incidence S 5 p).card = 2 :=
    fifteen_point_heavy_incidence incidence rowPairs columnSize columnPairs S size lineCases p hp
  have counts := fifteen_point_degrees incidence columnSize columnPairs S size lineCases p
  dsimp only at counts
  rw [if_pos hp] at counts
  omega

lemma light_support_singleton (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111))
    {l p : Fin 111} (hp : p ∈ S) (light : l ∈ supportDegree incidence S 1 p) :
    OrderTen.pointsOnLine incidence S l = {p} := by
  obtain ⟨card, on_line⟩ := mem_supportDegree.mp light
  obtain ⟨q, eq⟩ := Finset.card_eq_one.mp card
  have mem : p ∈ OrderTen.pointsOnLine incidence S l := Finset.mem_filter.mpr ⟨hp, on_line⟩
  rw [eq, Finset.mem_singleton] at mem
  rwa [mem]

lemma light_meets_medium_away_from_secant (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (p l m : Fin 111) (hp : p ∈ S) (light : l ∈ supportDegree incidence S 1 p)
    (medium : (OrderTen.pointsOnLine incidence S m).card = 3)
    (avoids_secant : incidence m p = false) :
    ∃! q, q ∈ exteriorPoints incidence S ∧ incidence l q = true ∧ incidence m q = true := by
  have l_card := (mem_supportDegree.mp light).1
  have different : l ≠ m := by intro eq; rw [eq, medium] at l_card; omega
  obtain ⟨q, both, unique⟩ := rowPairs l m different
  have outside : q ∉ S := by
    intro in_S
    have member : q ∈ OrderTen.pointsOnLine incidence S l := Finset.mem_filter.mpr ⟨in_S, both.1⟩
    rw [light_support_singleton incidence S hp light, Finset.mem_singleton] at member
    rw [member, avoids_secant] at both
    exact Bool.noConfusion both.2
  exact ⟨q, ⟨medium_has_no_outside_heavy incidence rowSize rowPairs columnSize columnPairs
    S size lineCases m q medium both.2 outside, both⟩, fun r h => unique r h.2⟩

lemma light_star_avoids_secant_medium (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (p l q m : Fin 111) (hp : p ∈ S) (light : l ∈ supportDegree incidence S 1 p)
    (hq : q ∈ exteriorPoints incidence S) (on_l : incidence l q = true)
    (on_m : m ∈ supportDegree incidence S 3 q) :
    incidence m p = false := by
  have q_out := (exterior_has_two_medium_lines incidence rowPairs columnSize columnPairs
    S size lineCases q hq).1
  obtain ⟨l_card, at_p⟩ := mem_supportDegree.mp light
  obtain ⟨m_card, at_q⟩ := mem_supportDegree.mp on_m
  have different : l ≠ m := by intro eq; rw [eq, m_card] at l_card; omega
  obtain ⟨r, _, unique⟩ := rowPairs l m different
  by_contra! both
  have eq := (unique q ⟨on_l, at_q⟩).trans (unique p ⟨at_p, by simpa using both⟩).symm
  exact q_out (eq.symm ▸ hp)

lemma every_eligible_exterior_point_is_in_one_star (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (p q : Fin 111) (hp : p ∈ S) (hq : q ∈ exteriorPoints incidence S)
    (eligible : ∀ m ∈ supportDegree incidence S 3 q, incidence m p = false) :
    ∃! l, l ∈ supportDegree incidence S 1 p ∧ incidence l q = true := by
  have outside := (exterior_has_two_medium_lines incidence rowPairs columnSize columnPairs
    S size lineCases q hq).1
  have different : p ≠ q := fun eq => outside (eq ▸ hp)
  obtain ⟨l, meets, unique⟩ := columnPairs p q different
  have light : (OrderTen.pointsOnLine incidence S l).card = 1 := by
    rcases lineCases l with h | h | h
    · exact h
    · have eq := eligible l (mem_supportDegree.mpr ⟨h, meets.2⟩)
      rw [eq] at meets
      exact Bool.noConfusion meets.1
    · have pos := Finset.card_pos.mpr
        (show (supportDegree incidence S 5 q).Nonempty from ⟨l, mem_supportDegree.mpr ⟨h, meets.2⟩⟩)
      have zero : (supportDegree incidence S 5 q).card = 0 := (Finset.mem_filter.mp hq).2
      omega
  exact ⟨l, ⟨mem_supportDegree.mpr ⟨light, meets.1⟩, meets.2⟩,
    fun m hm => unique m ⟨(mem_supportDegree.mp hm.1).2, hm.2⟩⟩

def mediumLabel (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111)) (m : Fin 111) :
    Finset (Finset (Fin 111)) :=
  (OrderTen.pointsOnLine incidence S m).image (supportDegree incidence S 5)

def isPerfectMatching (L : Finset (Fin 111)) (M : Finset (Finset (Fin 111))) : Prop :=
  M.card = 3 ∧ (∀ e ∈ M, e ⊆ L ∧ e.card = 2) ∧
    ∀ l ∈ L, ∃! e, e ∈ M ∧ l ∈ e

lemma support_labels_injective (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) :
    Set.InjOn (supportDegree incidence S 5) (S : Set (Fin 111)) := by
  obtain ⟨equiv, agreement⟩ :=
    fifteen_point_support_labels incidence rowPairs columnSize columnPairs S size lineCases
  have same (p : S) : (equiv p).val = supportDegree incidence S 5 p.val := by
    ext l
    rw [agreement p l]
    unfold supportDegree OrderTen.pointsOnLine
    rw [Finset.mem_filter]
  intro p hp q hq eq
  let u : S := ⟨p, hp⟩
  let v : S := ⟨q, hq⟩
  have labels : equiv u = equiv v := by
    apply Subtype.ext
    rw [same, same]
    exact eq
  exact congrArg Subtype.val (equiv.injective labels)

lemma medium_label_is_matching (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (m : Fin 111) (m_size : (OrderTen.pointsOnLine incidence S m).card = 3) :
    isPerfectMatching (linesWithIntersection incidence S 5) (mediumLabel incidence S m) := by
  let labels := supportDegree incidence S 5
  let points := OrderTen.pointsOnLine incidence S m
  have inj := support_labels_injective incidence rowPairs columnSize columnPairs S size lineCases
  have card : (points.image labels).card = 3 := by
    rw [Finset.card_image_of_injOn]
    · exact m_size
    · intro p hp q hq
      exact inj (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1
  refine ⟨card, ?_, ?_⟩
  · intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    exact ⟨Finset.filter_subset _ _, fifteen_point_heavy_incidence incidence rowPairs
      columnSize columnPairs S size lineCases p (Finset.mem_filter.mp hp).1⟩
  · intro l hl
    have heavy : (OrderTen.pointsOnLine incidence S l).card = 5 := (Finset.mem_filter.mp hl).2
    obtain ⟨p, ⟨in_S, on_m, on_l⟩, unique⟩ := medium_matches_heavy_lines incidence rowSize rowPairs
      columnSize columnPairs S size lineCases m l m_size heavy
    refine ⟨labels p, ⟨Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨in_S, on_m⟩, rfl⟩,
      mem_supportDegree.mpr ⟨heavy, on_l⟩⟩, ?_⟩
    intro e ⟨he, le⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨in_S, on_m⟩ := Finset.mem_filter.mp hq
    exact congrArg labels (unique q ⟨in_S, on_m, (mem_supportDegree.mp le).2⟩)

lemma support_point_of_pair (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (e : Finset (Fin 111)) (contained : e ⊆ linesWithIntersection incidence S 5)
    (card : e.card = 2) :
    ∃ p ∈ S, supportDegree incidence S 5 p = e := by
  obtain ⟨equiv, agreement⟩ :=
    fifteen_point_support_labels incidence rowPairs columnSize columnPairs S size lineCases
  let edges : ↥((linesWithIntersection incidence S 5).powersetCard 2) :=
    ⟨e, Finset.mem_powersetCard.mpr ⟨contained, card⟩⟩
  let p := equiv.symm edges
  refine ⟨p.val, p.property, ?_⟩
  have labels : (equiv p).val = e := congrArg Subtype.val (equiv.apply_symm_apply edges)
  rw [← labels]
  ext l
  exact Finset.mem_filter.trans (agreement p l).symm

lemma perfect_matchings_share_two_pairs (L : Finset (Fin 111))
    (M N : Finset (Finset (Fin 111))) (hM : isPerfectMatching L M)
    (hN : isPerfectMatching L N) (a b : Finset (Fin 111)) (ne : a ≠ b)
    (aM : a ∈ M) (bM : b ∈ M) (aN : a ∈ N) (bN : b ∈ N) :
    M = N := by
  classical
  have remaining (K : Finset (Finset (Fin 111))) (hK : isPerfectMatching L K)
      (ha : a ∈ K) (hb : b ∈ K) : ((K.erase a).erase b).card = 1 := by
    have in_K : b ∈ K.erase a := Finset.mem_erase.mpr ⟨ne.symm, hb⟩
    rw [Finset.card_erase_of_mem in_K, Finset.card_erase_of_mem ha, hK.1]
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (remaining M hM aM bM)
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (remaining N hN aN bN)
  have xm := Finset.mem_erase.mp (show x ∈ (M.erase a).erase b by simp [hx])
  have yn := Finset.mem_erase.mp (show y ∈ (N.erase a).erase b by simp [hy])
  have in_M := (Finset.mem_erase.mp xm.2).2
  have in_N := (Finset.mem_erase.mp yn.2).2
  have x_ne_a := (Finset.mem_erase.mp xm.2).1
  have xy : x = y := by
    apply Finset.eq_of_subset_of_card_le
    · intro l in_x
      have in_L := (hM.2.1 x in_M).1 in_x
      obtain ⟨c, hc, unique⟩ := hM.2.2 l in_L
      have not_a : l ∉ a := fun in_a => x_ne_a ((unique x ⟨in_M, in_x⟩).trans
        (unique a ⟨aM, in_a⟩).symm)
      have not_b : l ∉ b := fun in_b => xm.1 ((unique x ⟨in_M, in_x⟩).trans
        (unique b ⟨bM, in_b⟩).symm)
      obtain ⟨d, ⟨hd, at_l⟩, _⟩ := hN.2.2 l in_L
      have other : d ∈ (N.erase a).erase b := Finset.mem_erase.mpr
        ⟨fun eq => not_b (eq ▸ at_l), Finset.mem_erase.mpr ⟨fun eq => not_a (eq ▸ at_l), hd⟩⟩
      rw [hy, Finset.mem_singleton] at other
      exact other ▸ at_l
    · rw [(hM.2.1 x in_M).2, (hN.2.1 y in_N).2]
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    by_cases ea : e = a
    · exact ea.symm ▸ aN
    by_cases eb : e = b
    · exact eb.symm ▸ bN
    have rest : e ∈ (M.erase a).erase b :=
      Finset.mem_erase.mpr ⟨eb, Finset.mem_erase.mpr ⟨ea, he⟩⟩
    rw [hx, Finset.mem_singleton, xy] at rest
    exact rest.symm ▸ in_N
  · rw [hM.1, hN.1]

lemma matching_is_medium_label (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (M : Finset (Finset (Fin 111))) (matching : isPerfectMatching (linesWithIntersection incidence S 5) M) :
    ∃ m, (OrderTen.pointsOnLine incidence S m).card = 3 ∧ mediumLabel incidence S m = M := by
  classical
  obtain ⟨a, aM, b, bM, different⟩ := Finset.one_lt_card.mp (by rw [matching.1]; decide)
  have point (e : Finset (Fin 111)) (he : e ∈ M) : ∃ p ∈ S, supportDegree incidence S 5 p = e :=
    support_point_of_pair incidence rowPairs columnSize columnPairs S size lineCases e
      (matching.2.1 e he).1 (matching.2.1 e he).2
  obtain ⟨p, in_S, p_eq⟩ := point a aM
  obtain ⟨q, q_in_S, q_eq⟩ := point b bM
  have pq : p ≠ q := by intro eq; apply different; rw [← p_eq, ← q_eq, eq]
  obtain ⟨m, on_both, _⟩ := columnPairs p q pq
  have p_mem : p ∈ OrderTen.pointsOnLine incidence S m := Finset.mem_filter.mpr ⟨in_S, on_both.1⟩
  have q_mem : q ∈ OrderTen.pointsOnLine incidence S m := Finset.mem_filter.mpr ⟨q_in_S, on_both.2⟩
  have card : (OrderTen.pointsOnLine incidence S m).card = 3 := by
    rcases lineCases m with h | h | h
    · exact (pq (Finset.card_le_one.mp (by omega) p p_mem q q_mem)).elim
    · exact h
    · have ml : m ∈ linesWithIntersection incidence S 5 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      obtain ⟨e, _, unique⟩ := matching.2.2 m ml
      have at_a : m ∈ a := p_eq ▸ mem_supportDegree.mpr ⟨h, on_both.1⟩
      have at_b : m ∈ b := q_eq ▸ mem_supportDegree.mpr ⟨h, on_both.2⟩
      exact (different ((unique a ⟨aM, at_a⟩).trans (unique b ⟨bM, at_b⟩).symm)).elim
  have m_matching := medium_label_is_matching incidence rowSize rowPairs columnSize columnPairs
    S size lineCases m card
  exact ⟨m, card, perfect_matchings_share_two_pairs _ _ _ m_matching matching a b different
    (Finset.mem_image.mpr ⟨p, p_mem, p_eq⟩)
    (Finset.mem_image.mpr ⟨q, q_mem, q_eq⟩) aM bM⟩

lemma medium_label_membership (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111))
    (inj : Set.InjOn (supportDegree incidence S 5) (S : Set (Fin 111)))
    (m p : Fin 111) (hp : p ∈ S) :
    supportDegree incidence S 5 p ∈ mediumLabel incidence S m ↔ incidence m p = true := by
  constructor
  · intro mem
    obtain ⟨q, hq, same⟩ := Finset.mem_image.mp mem
    obtain ⟨qS, on_m⟩ := Finset.mem_filter.mp hq
    rwa [inj qS hp same] at on_m
  · intro on_m
    exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, on_m⟩, rfl⟩

lemma medium_labels_injective (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (S : Finset (Fin 111))
    (inj : Set.InjOn (supportDegree incidence S 5) (S : Set (Fin 111))) :
    Set.InjOn (mediumLabel incidence S) (linesWithIntersection incidence S 3 : Set (Fin 111)) := by
  intro l hl m _ equal
  by_contra neq
  obtain ⟨p, hp, q, hq, different⟩ := Finset.one_lt_card.mp
    (show 1 < (OrderTen.pointsOnLine incidence S l).card by
      have size : (OrderTen.pointsOnLine incidence S l).card = 3 := (Finset.mem_filter.mp hl).2
      rw [size]; decide)
  obtain ⟨r, _, unique⟩ := rowPairs l m neq
  have both (s : Fin 111) (hs : s ∈ OrderTen.pointsOnLine incidence S l) :
      incidence l s = true ∧ incidence m s = true := by
    obtain ⟨in_S, on_l⟩ := Finset.mem_filter.mp hs
    have label := (medium_label_membership incidence S inj l s in_S).2 on_l
    rw [equal] at label
    exact ⟨on_l, (medium_label_membership incidence S inj m s in_S).1 label⟩
  exact different ((unique p (both p hp)).trans (unique q (both q hq)).symm)

def exteriorLabel (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111)) (q : Fin 111) :
    Finset (Finset (Finset (Fin 111))) :=
  (supportDegree incidence S 3 q).image (mediumLabel incidence S)

def isExteriorLabel (L : Finset (Fin 111)) (C : Finset (Finset (Finset (Fin 111)))) : Prop :=
  C.card = 2 ∧ (∀ M ∈ C, isPerfectMatching L M) ∧
    ∀ M ∈ C, ∀ N ∈ C, M ≠ N → Disjoint M N

lemma exterior_has_valid_label (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) (q : Fin 111) (hq : q ∈ exteriorPoints incidence S) :
    isExteriorLabel (linesWithIntersection incidence S 5) (exteriorLabel incidence S q) := by
  have injectLabels := support_labels_injective incidence rowPairs columnSize columnPairs S size lineCases
  have inj := medium_labels_injective incidence rowPairs S injectLabels
  obtain ⟨out, degree⟩ := exterior_has_two_medium_lines incidence rowPairs columnSize columnPairs
    S size lineCases q hq
  refine ⟨?_, ?_, ?_⟩
  · unfold exteriorLabel
    rw [Finset.card_image_of_injOn, degree]
    intro m hm n hn
    exact inj (Finset.mem_filter.mp hm).1 (Finset.mem_filter.mp hn).1
  · intro M hM
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hM
    exact medium_label_is_matching incidence rowSize rowPairs columnSize columnPairs S size lineCases
      m (mem_supportDegree.mp hm).1
  · intro M hM N hN different
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hM
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hN
    have mn : m ≠ n := fun eq => different (congrArg _ eq)
    obtain ⟨r, _, unique⟩ := rowPairs m n mn
    apply Finset.disjoint_left.mpr
    intro e em en
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp em
    obtain ⟨pS, at_m⟩ := Finset.mem_filter.mp hp
    have at_n := (medium_label_membership incidence S injectLabels n p pS).1 en
    have eq := (unique p ⟨at_m, at_n⟩).trans
      (unique q ⟨(mem_supportDegree.mp hm).2, (mem_supportDegree.mp hn).2⟩).symm
    exact out (eq ▸ pS)

lemma valid_exterior_label_occurs (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (C : Finset (Finset (Finset (Fin 111)))) (valid : isExteriorLabel (linesWithIntersection incidence S 5) C) :
    ∃ q ∈ exteriorPoints incidence S, exteriorLabel incidence S q = C := by
  obtain ⟨M, N, different, label⟩ := Finset.card_eq_two.mp valid.1
  obtain ⟨m, m_medium, lm⟩ := matching_is_medium_label incidence rowSize rowPairs columnSize columnPairs
    S size lineCases M (valid.2.1 M (by simp [label]))
  obtain ⟨n, n_medium, ln⟩ := matching_is_medium_label incidence rowSize rowPairs columnSize columnPairs
    S size lineCases N (valid.2.1 N (by simp [label]))
  have mn : m ≠ n := by intro e; apply different; rw [← lm, ← ln, e]
  obtain ⟨q, both, _⟩ := rowPairs m n mn
  have outside : q ∉ S := by
    intro in_S
    have disj := valid.2.2 M (by simp [label]) N (by simp [label]) different
    have lm_mem : supportDegree incidence S 5 q ∈ M :=
      lm ▸ Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨in_S, both.1⟩, rfl⟩
    have ln_mem : supportDegree incidence S 5 q ∈ N :=
      ln ▸ Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨in_S, both.2⟩, rfl⟩
    exact Finset.disjoint_left.mp disj lm_mem ln_mem
  have is_out := medium_has_no_outside_heavy incidence rowSize rowPairs columnSize columnPairs
    S size lineCases m q m_medium both.1 outside
  refine ⟨q, is_out, ?_⟩
  have q_valid := exterior_has_valid_label incidence rowSize rowPairs columnSize columnPairs
    S size lineCases q is_out
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro E hE
    rw [label, Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl
    · exact Finset.mem_image.mpr ⟨m, mem_supportDegree.mpr ⟨m_medium, both.1⟩, lm⟩
    · exact Finset.mem_image.mpr ⟨n, mem_supportDegree.mpr ⟨n_medium, both.2⟩, ln⟩
  · rw [valid.1, q_valid.1]

lemma exterior_labels_injective (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) :
    Set.InjOn (exteriorLabel incidence S) (exteriorPoints incidence S : Set (Fin 111)) := by
  have inj := medium_labels_injective incidence rowPairs S
    (support_labels_injective incidence rowPairs columnSize columnPairs S size lineCases)
  intro p hp q _ labels
  have p_degree := (exterior_has_two_medium_lines incidence rowPairs columnSize columnPairs
    S size lineCases p hp).2
  obtain ⟨m, hm, n, hn, different⟩ := Finset.one_lt_card.mp
    (show 1 < (supportDegree incidence S 3 p).card by rw [p_degree]; decide)
  obtain ⟨r, _, unique⟩ := rowPairs m n different
  have on_q (m : Fin 111) (hm : m ∈ supportDegree incidence S 3 p) : incidence m q = true := by
    have member : mediumLabel incidence S m ∈ exteriorLabel incidence S p :=
      Finset.mem_image.mpr ⟨m, hm, rfl⟩
    rw [labels] at member
    obtain ⟨l, hl, eq⟩ := Finset.mem_image.mp member
    have same := inj (Finset.mem_filter.mp hl).1 (Finset.mem_filter.mp hm).1 eq
    exact same ▸ (mem_supportDegree.mp hl).2
  exact (unique p ⟨(mem_supportDegree.mp hm).2, (mem_supportDegree.mp hn).2⟩).trans
    (unique q ⟨on_q m hm, on_q n hn⟩).symm

-- Each star pairs the medium lines that avoid its support point. The six stars
-- at a support point partition the eligible exterior labels.
def HasStarCover : Prop :=
  ∃ L : Finset (Fin 111), L.card = 6 ∧
    ∃ stars : ↥(L.powersetCard 2) → Fin 6 → Finset (Finset (Finset (Finset (Fin 111)))),
      (∀ e i C, C ∈ stars e i → isExteriorLabel L C ∧ ∀ M ∈ C, e.val ∉ M) ∧
      (∀ e i M, isPerfectMatching L M → e.val ∉ M → ∃! C, C ∈ stars e i ∧ M ∈ C) ∧
      (∀ e C, isExteriorLabel L C → (∀ M ∈ C, e.val ∉ M) → ∃! i, C ∈ stars e i) ∧
      ∀ e f, e ≠ f → ∀ i j, (stars e i ∩ stars f j).card ≤ 1

theorem fifteen_point_configuration_has_star_cover (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) :
    HasStarCover := by
  classical
  let L := linesWithIntersection incidence S 5
  let E := ↥(L.powersetCard 2)
  have six : L.card = 6 := (fifteen_point_line_counts incidence columnSize columnPairs S size lineCases).2.2
  have vertices (e : E) : ∃ p ∈ S, supportDegree incidence S 5 p = e.val := by
    obtain ⟨inside, card⟩ := Finset.mem_powersetCard.mp e.property
    exact support_point_of_pair incidence rowPairs columnSize columnPairs S size lineCases e.val inside card
  choose point point_mem point_label using vertices
  let light (e : E) : Fin 6 ≃ ↥(supportDegree incidence S 1 (point e)) :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, Fintype.card_coe,
        light_pencil_card incidence rowPairs columnSize columnPairs S size lineCases (point e) (point_mem e)])
  let star := fun (e : E) (i : Fin 6) =>
    (OrderTen.pointsOnLine incidence (exteriorPoints incidence S) (light e i).val).image
      (exteriorLabel incidence S)
  have in_star (e : E) (i : Fin 6) (C : Finset (Finset (Finset (Fin 111)))) :
      C ∈ star e i ↔ ∃ q ∈ exteriorPoints incidence S,
        incidence (light e i).val q = true ∧ exteriorLabel incidence S q = C := by
    simp only [star, Finset.mem_image, OrderTen.pointsOnLine, Finset.mem_filter]
    tauto
  have point_inj := support_labels_injective incidence rowPairs columnSize columnPairs S size lineCases
  have med_inj := medium_labels_injective incidence rowPairs S point_inj
  have ext_inj := exterior_labels_injective incidence rowPairs columnSize columnPairs S size lineCases
  have med_at (e : E) (m : Fin 111) :
      e.val ∈ mediumLabel incidence S m ↔ incidence m (point e) = true := by
    rw [← point_label e]
    exact medium_label_membership incidence S point_inj m (point e) (point_mem e)
  have med_label_iff (q m : Fin 111) (hm : (OrderTen.pointsOnLine incidence S m).card = 3) :
      mediumLabel incidence S m ∈ exteriorLabel incidence S q ↔ incidence m q = true := by
    constructor
    · intro h
      obtain ⟨r, r_mem, labels⟩ := Finset.mem_image.mp h
      have eq := med_inj (Finset.mem_filter.mp r_mem).1
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩) labels
      exact eq ▸ (mem_supportDegree.mp r_mem).2
    · intro on_m
      exact Finset.mem_image.mpr ⟨m, mem_supportDegree.mpr ⟨hm, on_m⟩, rfl⟩
  refine ⟨L, six, star, ?_, ?_, ?_, ?_⟩
  · intro e i C hC
    obtain ⟨q, in_C, on_light, label⟩ := (in_star e i C).mp hC
    rw [← label]
    refine ⟨exterior_has_valid_label incidence rowSize rowPairs columnSize columnPairs S size lineCases q in_C, ?_⟩
    intro M hM
    obtain ⟨m, m_mem, rfl⟩ := Finset.mem_image.mp hM
    have avoids := light_star_avoids_secant_medium incidence rowPairs columnSize columnPairs S size
      lineCases (point e) (light e i).val q m (point_mem e) (light e i).property in_C on_light m_mem
    simp [med_at, avoids]
  · intro e i M hM avoids
    obtain ⟨m, hm, rfl⟩ := matching_is_medium_label incidence rowSize rowPairs columnSize columnPairs
      S size lineCases M hM
    have not_on_m : incidence m (point e) = false := by
      rw [med_at] at avoids
      cases bit : incidence m (point e) <;> simp_all
    obtain ⟨q, ⟨q_mem, q_light, q_medium⟩, unique⟩ :=
      light_meets_medium_away_from_secant incidence rowSize rowPairs columnSize columnPairs S size
        lineCases (point e) (light e i).val m (point_mem e) (light e i).property hm not_on_m
    refine ⟨exteriorLabel incidence S q, ⟨(in_star e i _).mpr ⟨q, q_mem, q_light, rfl⟩,
      (med_label_iff q m hm).mpr q_medium⟩, ?_⟩
    intro C' ⟨star_mem, m_mem⟩
    obtain ⟨q', q'_out, q'_light, rfl⟩ := (in_star e i C').mp star_mem
    exact congrArg (exteriorLabel incidence S) (unique q' ⟨q'_out, q'_light,
      (med_label_iff q' m hm).mp m_mem⟩)
  · intro e C valid no_e
    obtain ⟨q, q_mem, rfl⟩ := valid_exterior_label_occurs incidence rowSize rowPairs columnSize
      columnPairs S size lineCases C valid
    have eligible (m : Fin 111) (hm : m ∈ supportDegree incidence S 3 q) :
        incidence m (point e) = false := by
      have h := no_e (mediumLabel incidence S m) (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
      rw [med_at] at h
      cases bit : incidence m (point e) <;> simp_all
    obtain ⟨l, ⟨l_mem, at_l⟩, unique⟩ := every_eligible_exterior_point_is_in_one_star incidence
      rowPairs columnSize columnPairs S size lineCases (point e) q (point_mem e) q_mem eligible
    let l' : ↥(supportDegree incidence S 1 (point e)) := ⟨l, l_mem⟩
    let i := (light e).symm l'
    have i_line : (light e i).val = l := congrArg Subtype.val ((light e).apply_symm_apply l')
    refine ⟨i, (in_star e i _).mpr ⟨q, q_mem, i_line.symm ▸ at_l, rfl⟩, ?_⟩
    intro j hj
    obtain ⟨q', q'_mem, q'_on, eq⟩ := (in_star e j _).mp hj
    have same := ext_inj q'_mem q_mem eq
    have result := unique (light e j).val ⟨(light e j).property, same ▸ q'_on⟩
    apply (light e).injective
    exact Subtype.ext (result.trans i_line.symm)
  · intro e f different i j
    let l := (light e i).val
    let m := (light f j).val
    have line_ne : l ≠ m := by
      intro equal
      have l_s := light_support_singleton incidence S (point_mem e) (light e i).property
      have m_s := light_support_singleton incidence S (point_mem f) (light f j).property
      change OrderTen.pointsOnLine incidence S l = {point e} at l_s
      change OrderTen.pointsOnLine incidence S m = {point f} at m_s
      rw [equal, m_s] at l_s
      have eq : point e = point f := (Finset.singleton_inj.mp l_s).symm
      apply different
      exact Subtype.ext ((point_label e).symm.trans (eq ▸ point_label f))
    obtain ⟨z, _, unique⟩ := rowPairs l m line_ne
    apply Finset.card_le_one.mpr
    intro C hC D hD
    have common (A : Finset (Finset (Finset (Fin 111)))) (hA : A ∈ star e i ∩ star f j) :
        A = exteriorLabel incidence S z := by
      obtain ⟨A_l, A_m⟩ := Finset.mem_inter.mp hA
      obtain ⟨q, q_mem, q_l, q_eq⟩ := (in_star e i A).mp A_l
      obtain ⟨r, r_mem, r_m, r_eq⟩ := (in_star f j A).mp A_m
      have qr := ext_inj q_mem r_mem (q_eq.trans r_eq.symm)
      have qz := unique q ⟨q_l, qr.symm ▸ r_m⟩
      exact q_eq.symm.trans (congrArg (exteriorLabel incidence S) qz)
    exact (common C hC).trans (common D hD).symm

end OrderTenCaseShapes

-- The line counts force the six heavy lines to determine the labels for the
-- medium and exterior lines. Each light line then gives one star.
theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1.H1 := by
  intro incidence rowSize columnSize rowPairs columnPairs
  dsimp only
  rintro ⟨a, ha⟩
  let w := (OrderTen.extendedIncidence incidence)ᵀ *ᵥ a
  have fifteen : OrderTenWeights.tailWeight w = 15 := by
    change OrderTenWeights.tailWeight ((OrderTen.extendedIncidence incidence)ᵀ *ᵥ a) = 15
    simpa only [OrderTenWeights.tailWeight, OrderTen.pointSupport, hammingNorm,
      OrderTenWeights.extended_word_explicit, Fin.cons_succ] using ha
  exact OrderTenCaseShapes.fifteen_point_configuration_has_star_cover incidence rowSize rowPairs
    columnSize columnPairs _ fifteen
    (OrderTenCaseShapes.weight_fifteen_line_sizes incidence rowSize rowPairs columnSize columnPairs a fifteen)
