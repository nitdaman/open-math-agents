import FormalConjectures.GreensOpenProblems.«75»

/-! An explicit set of twelve lattice points (invariant under the linear map of order three
`(a, b) ↦ (-b, a - b)`) such that every line through two of its points has imbalance at least
`2`. The side counts are computed over the integers and transported to the reals. -/

open scoped Finset

namespace OMA

/-- The twelve points, with integer coordinates. -/
def pts : Finset (ℤ × ℤ) :=
  {(-3, -2), (2, -1), (1, 3), (3, -2), (2, 5), (-5, -3), (1, 0), (0, 1), (-1, -1), (1, -1),
    (1, 2), (-2, -1)}

/-- The integer cross product. -/
def icross (p q x : ℤ × ℤ) : ℤ :=
  (q.1 - p.1) * (x.2 - p.2) - (q.2 - p.2) * (x.1 - p.1)

/-- The embedding of the integer lattice into the real plane. -/
def emb : (ℤ × ℤ) ↪ (ℝ × ℝ) where
  toFun p := ((p.1 : ℝ), (p.2 : ℝ))
  inj' := by
    intro p q h
    have h1 : (p.1 : ℝ) = (q.1 : ℝ) := congrArg Prod.fst h
    have h2 : (p.2 : ℝ) = (q.2 : ℝ) := congrArg Prod.snd h
    exact Prod.ext (Int.cast_injective h1) (Int.cast_injective h2)

lemma emb_apply (p : ℤ × ℤ) : emb p = ((p.1 : ℝ), (p.2 : ℝ)) := rfl

lemma cross_emb (p q x : ℤ × ℤ) :
    Green75.cross (emb p) (emb q) (emb x) = ((icross p q x : ℤ) : ℝ) := by
  rw [emb_apply, emb_apply, emb_apply]
  simp only [Green75.cross, icross]
  push_cast
  ring

lemma leftCount_emb (S : Finset (ℤ × ℤ)) (p q : ℤ × ℤ) :
    Green75.leftCount (S.map emb) (emb p) (emb q) = #{x ∈ S | 0 < icross p q x} := by
  unfold Green75.leftCount
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  ext x
  simp only [Finset.mem_filter, Function.comp_apply, cross_emb, Int.cast_pos]

lemma rightCount_emb (S : Finset (ℤ × ℤ)) (p q : ℤ × ℤ) :
    Green75.rightCount (S.map emb) (emb p) (emb q) = #{x ∈ S | icross p q x < 0} := by
  unfold Green75.rightCount
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  ext x
  simp only [Finset.mem_filter, Function.comp_apply, cross_emb, Int.cast_lt_zero]

lemma int_check : ∀ p ∈ pts, ∀ q ∈ pts, p ≠ q →
    2 ≤ |((#{x ∈ pts | 0 < icross p q x} : ℕ) : ℤ) - ((#{x ∈ pts | icross p q x < 0} : ℕ) : ℤ)| := by
  decide

lemma card_pts : #pts = 12 := by decide

end OMA

theorem OMA.solution : type_of% @Green75.green_75.variants.alon := by
  refine ⟨OMA.pts.map OMA.emb, ?_, ?_⟩
  · rw [Finset.card_map, OMA.card_pts]
    norm_num
  · intro p hp q hq hpq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_map.mp hq
    have hne : p' ≠ q' := fun h => hpq (by rw [h])
    unfold Green75.imbalance
    rw [OMA.leftCount_emb, OMA.rightCount_emb]
    exact OMA.int_check p' hp' q' hq' hne
