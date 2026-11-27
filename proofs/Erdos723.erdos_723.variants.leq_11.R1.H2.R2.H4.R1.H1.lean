import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1

/-! Support sizes in the primitive weight-nineteen case. -/
-- Credit: @avivorly

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

lemma incidence_row_sum (incidence : Fin n → Fin n → Bool) (size : ℕ)
    (rowSize : ∀ i, (Finset.univ.filter fun j => incidence i j = true).card = size) (i : Fin n) :
    ∑ j, incidenceMatrix incidence i j = (size : ℤ) := by
  change ∑ j, (if incidence i j = true then (1 : ℤ) else 0) = _
  rw [← Finset.sum_filter]
  simp [rowSize]

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


lemma nineteen_point_line_counts (incidence : Fin 111 → Fin 111 → Bool)
    (columnSize : ∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 19)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) :
    (linesWithIntersection incidence S 1).card = 68 ∧
      (linesWithIntersection incidence S 3).card = 37 ∧
      (linesWithIntersection incidence S 5).card = 6 := by
  let k := fun l => (OrderTen.pointsOnLine incidence S l).card
  let n := fun j => (linesWithIntersection incidence S j).card
  have points : (∑ l, k l) = 209 := by
    change (∑ l, (OrderTen.pointsOnLine incidence S l).card) = _
    rw [OrderTen.sum_pointsOnLine incidence columnSize, size]
  have pairs : (∑ l, (k l*k l - k l)) = 342 := by
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
  change n 1 = 68 ∧ n 3 = 37 ∧ n 5 = 6
  omega


theorem primitive_nineteen_line_sizes (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ i j, i ≠ j → ∃! k, incidence i k = true ∧ incidence j k = true)
    (a : Fin 111 → ZMod 2)
    (weight19 : OrderTenWeights.tailWeight ((OrderTen.extendedIncidence incidence)ᵀ *ᵥ a) = 19)
    (primitive : ∀ b c : Fin 111 → ZMod 2,
      OrderTenWeights.tailWeight ((OrderTen.extendedIncidence incidence)ᵀ *ᵥ b) < 19 →
      OrderTenWeights.tailWeight ((OrderTen.extendedIncidence incidence)ᵀ *ᵥ c) < 19 →
      (OrderTen.extendedIncidence incidence)ᵀ *ᵥ a ≠
        (OrderTen.extendedIncidence incidence)ᵀ *ᵥ b + (OrderTen.extendedIncidence incidence)ᵀ *ᵥ c)
    (l : Fin 111) :
    let S := OrderTen.pointSupport ((OrderTen.extendedIncidence incidence)ᵀ *ᵥ a)
    let k := (OrderTen.pointsOnLine incidence S l).card
    k = 1 ∨ k = 3 ∨ k = 5 := by
  intro S k
  let E := OrderTen.extendedIncidence incidence
  let w := Eᵀ *ᵥ a
  have head : w 0 = 1 := by
    apply (OrderTen.binary_values (w 0)).resolve_left
    intro zero
    have parity := (OrderTenWeights.tail_parity_of_doublyEven w
      (OrderTen.extended_code_doubly_even incidence rowSize rowPairs a)).1.mp zero
    change OrderTenWeights.tailWeight w = 19 at weight19
    omega
  have odd := row_word_line_parity incidence rowSize rowPairs a l
  change k % 2 = (w 0).val at odd
  rw [head, ZMod.val_one] at odd
  by_contra! beyond
  have large : 6 ≤ k := by omega
  let c := (Pi.single l 1 : Fin 111 → ZMod 2)
  let b := a + c
  have row : Eᵀ *ᵥ c = E l := by
    unfold c
    rw [Matrix.mulVec_single_one]
    rfl
  have added : Eᵀ *ᵥ b = w + E l := by
    unfold b
    rw [Matrix.mulVec_add, row]
  have balance := tail_weight_add_row incidence rowSize w l
  change OrderTenWeights.tailWeight (w + E l) + 2*k = OrderTenWeights.tailWeight w + 11 at balance
  have light_b : OrderTenWeights.tailWeight (Eᵀ *ᵥ b) < 19 := by
    rw [added]
    change OrderTenWeights.tailWeight w = 19 at weight19
    omega
  have light_c : OrderTenWeights.tailWeight (Eᵀ *ᵥ c) < 19 := by
    rw [row]
    change (OrderTen.pointSupport (OrderTen.extendedIncidence incidence l)).card < 19
    rw [OrderTenWeights.row_support, rowSize]
    decide
  apply primitive b c light_b light_c
  change w = Eᵀ *ᵥ b + Eᵀ *ᵥ c
  rw [added, row, add_assoc]
  have cancel : E l + E l = 0 := by
    funext p
    change E l p + E l p = 0
    rcases OrderTen.binary_values (E l p) with zero | one
    · simp [zero]
    · rw [one]
      decide
  rw [cancel, add_zero]

lemma nineteen_support_degrees (incidence : Fin 111 → Fin 111 → Bool)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 19)
    (shape : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) (p : Fin 111) :
    (supportDegree incidence S 3 p).card + 2 * (supportDegree incidence S 5 p).card =
      if p ∈ S then 9 else 4 := by
  let k := fun l => (OrderTen.pointsOnLine incidence S l).card
  let L := atPoint incidence p
  have count (j : Nat) : (∑ l ∈ L, if k l = j then (1 : ℕ) else 0) = (supportDegree incidence S j p).card := by
    have split : (L.filter fun l => k l = j) = supportDegree incidence S j p := by
      ext l
      simp only [Finset.mem_filter, L, atPoint, Finset.mem_univ, true_and, mem_supportDegree, k, and_comm]
    rw [← Finset.sum_filter, split]
    simp
  have add (l : Fin 111) : k l = 1 + 2 * (if k l = 3 then 1 else 0) + 4 * (if k l = 5 then 1 else 0) := by
    have types : k l = 1 ∨ k l = 3 ∨ k l = 5 := shape l
    rcases types with h | h | h <;> simp [h]
  have sum := Finset.sum_congr (s₁ := L) rfl (fun l _ => add l)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, count] at sum
  rw [show L.card = 11 from columnSize p] at sum
  by_cases inside : p ∈ S
  · have total : (∑ l ∈ L, k l) = 29 := by
      exact (sum_pencil_containing_center incidence columnSize columnPairs S p inside).trans (by rw [size])
    rw [total] at sum
    simp only [if_pos inside]
    omega
  · have total : (∑ l ∈ L, k l) = 19 :=
      (sum_pencil_avoiding_center incidence columnPairs S p inside).trans size
    rw [total] at sum
    simp only [if_neg inside]
    omega

end OrderTenCaseShapes


theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1.H1 := by
  intro incidence rowSize columnSize rowPairs columnPairs
  dsimp only
  intro a weight primitive
  let E := OrderTen.extendedIncidence incidence
  let w := Eᵀ *ᵥ a
  let S := OrderTen.pointSupport w
  have coordinates (b : Fin 111 → ZMod 2) (p : Fin 111) : (Eᵀ *ᵥ b) p.succ =
      ∑ l, b l * (if incidence l p = true then 1 else 0) := by
    change ((OrderTen.extendedIncidence incidence)ᵀ *ᵥ b) p.succ = _
    rw [OrderTenWeights.extended_word_explicit, Fin.cons_succ]
  have tail (b : Fin 111 → ZMod 2) : OrderTenWeights.tailWeight (Eᵀ *ᵥ b) =
      hammingNorm (fun p : Fin 111 => ∑ l, b l * (if incidence l p = true then 1 else 0)) := by
    change hammingNorm (fun p : Fin 111 => (Eᵀ *ᵥ b) p.succ) = _
    rw [funext (coordinates b)]
  have size : S.card = 19 := by
    change OrderTenWeights.tailWeight w = 19
    rw [show w = Eᵀ *ᵥ a from rfl, tail]
    exact weight
  have no_pair (b c : Fin 111 → ZMod 2) (lb : OrderTenWeights.tailWeight (Eᵀ *ᵥ b) < 19)
      (lc : OrderTenWeights.tailWeight (Eᵀ *ᵥ c) < 19) :
      Eᵀ *ᵥ a ≠ Eᵀ *ᵥ b + Eᵀ *ᵥ c := by
    rw [tail] at lb lc
    change (OrderTen.extendedIncidence incidence)ᵀ *ᵥ a ≠
      (OrderTen.extendedIncidence incidence)ᵀ *ᵥ b + (OrderTen.extendedIncidence incidence)ᵀ *ᵥ c
    rw [OrderTenWeights.extended_word_explicit incidence a, OrderTenWeights.extended_word_explicit incidence b,
      OrderTenWeights.extended_word_explicit incidence c]
    exact primitive b c lb lc
  have shape := OrderTenCaseShapes.primitive_nineteen_line_sizes incidence rowSize rowPairs a size no_pair
  have counts := OrderTenCaseShapes.nineteen_point_line_counts incidence columnSize columnPairs S size shape
  refine ⟨S, size, shape, counts, ?_⟩
  intro p
  have degree := OrderTenCaseShapes.nineteen_support_degrees incidence columnSize columnPairs S size shape p
  have countsAt (j : Nat) : OrderTenCaseShapes.supportDegree incidence S j p =
      Finset.univ.filter (fun l => (S.filter fun q => incidence l q = true).card = j ∧ incidence l p = true) := by
    ext l
    simp [OrderTenCaseShapes.mem_supportDegree, OrderTen.pointsOnLine]
  rw [countsAt, countsAt] at degree
  exact degree
