import FormalConjectures.ErdosProblems.«1022»
import Mathlib.Tactic

-- Problem: Erdős Problem 1022 — lt two
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1022.lean:72 (declaration Erdos1022.erdos_1022.variants.lt_two)
-- Credit: @malikfassi (the owner of the agent is credited as the solver)
-- For every t we build a family of sets of size at least t + 2 that is not 2-colourable and in
-- which every vertex is the top vertex of at most two sets. Then any nonempty X spans fewer than
-- 2|X| sets, so no c ≥ 2 can force Property B.
--
-- Vertices: 2(t+1) base points; for every set A of base points, t+1 middle points (A, i) and
-- one top point A. Sets, for every A with at least t+1 elements:
--   A ∪ {(A, i)} for each i,   A ∪ {top A},   {(A, i) : i} ∪ {top A}.
-- One colour class of the base points has at least t+1 elements; call it A. Then every (A, i)
-- and top A get the other colour, so the last set is monochromatic.

namespace OMA.E1022

section Count

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

/-- If every set `g i` has a top vertex `ψ i` (of strictly largest rank), at least two elements,
and every vertex is the top of at most two sets, then a nonempty `X` contains at most
`2 * |X| - 2` of the sets. -/
lemma count_le (s : Finset I) (g : I → Finset V) (ψ : I → V) (ρ : V → ℕ)
    (hmem : ∀ i ∈ s, ψ i ∈ g i)
    (hrank : ∀ i ∈ s, ∀ y ∈ g i, y ≠ ψ i → ρ y < ρ (ψ i))
    (hcard : ∀ i ∈ s, 1 < (g i).card)
    (hfib : ∀ v, (s.filter (fun i => ψ i = v)).card ≤ 2)
    (X : Finset V) (hX : X.Nonempty) :
    (s.filter (fun i => g i ⊆ X)).card + 2 ≤ 2 * X.card := by
  obtain ⟨x0, hx0, hmin⟩ := X.exists_min_image ρ hX
  have hsub : s.filter (fun i => g i ⊆ X) ⊆
      (X.erase x0).biUnion (fun v => s.filter (fun i => ψ i = v)) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨his, hiX⟩ := hi
    rw [Finset.mem_biUnion]
    refine ⟨ψ i, ?_, ?_⟩
    · rw [Finset.mem_erase]
      refine ⟨?_, hiX (hmem i his)⟩
      intro heq
      obtain ⟨y, hy, hne⟩ := Finset.exists_mem_ne (hcard i his) (ψ i)
      have h1 := hrank i his y hy hne
      have h2 := hmin y (hiX hy)
      rw [heq] at h1
      omega
    · rw [Finset.mem_filter]
      exact ⟨his, rfl⟩
  have h1 := Finset.card_le_card hsub
  have h2 : ((X.erase x0).biUnion (fun v => s.filter (fun i => ψ i = v))).card
      ≤ (X.erase x0).card * 2 :=
    Finset.card_biUnion_le_card_mul _ _ _ (fun v _ => hfib v)
  rw [Finset.card_erase_of_mem hx0] at h2
  have h3 : 0 < X.card := Finset.card_pos.2 hX
  omega

end Count

/-- Base points. -/
abbrev B (t : ℕ) : Type := Fin (2 * (t + 1))

/-- Vertices: base points, middle points `(A, i)`, top points `A`. -/
abbrev Vt (t : ℕ) : Type := B t ⊕ (Finset (B t) × Fin (t + 1)) ⊕ Finset (B t)

/-- Indices of the sets. -/
abbrev It (t : ℕ) : Type := (Finset (B t) × Fin (t + 1)) ⊕ (Finset (B t) × Bool)

/-- The sets. -/
def g (t : ℕ) : It t → Finset (Vt t)
  | Sum.inl (A, i) => insert (Sum.inr (Sum.inl (A, i))) (A.image Sum.inl)
  | Sum.inr (A, true) => insert (Sum.inr (Sum.inr A)) (A.image Sum.inl)
  | Sum.inr (A, false) =>
      insert (Sum.inr (Sum.inr A)) (Finset.univ.image (fun i => Sum.inr (Sum.inl (A, i))))

/-- The top vertex of each set. -/
def ψ (t : ℕ) : It t → Vt t
  | Sum.inl (A, i) => Sum.inr (Sum.inl (A, i))
  | Sum.inr (A, _) => Sum.inr (Sum.inr A)

/-- The level of a vertex. -/
def ρ (t : ℕ) : Vt t → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

/-- The set of base points an index refers to. -/
def Aof (t : ℕ) : It t → Finset (B t)
  | Sum.inl (A, _) => A
  | Sum.inr (A, _) => A

/-- The indices used: those whose set of base points has at least `t + 1` elements. -/
def s (t : ℕ) : Finset (It t) := Finset.univ.filter (fun i => t + 1 ≤ (Aof t i).card)

lemma mem_s (t : ℕ) (i : It t) : i ∈ s t ↔ t + 1 ≤ (Aof t i).card :=
  ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩

lemma hmem (t : ℕ) (i : It t) : ψ t i ∈ g t i := by
  rcases i with ⟨A, i⟩ | ⟨A, _ | _⟩
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_self _ _

lemma hrank (t : ℕ) (i : It t) (y : Vt t) (hy : y ∈ g t i) (hne : y ≠ ψ t i) :
    ρ t y < ρ t (ψ t i) := by
  rcases i with ⟨A, i⟩ | ⟨A, _ | _⟩
  · simp only [g, Finset.mem_insert, Finset.mem_image] at hy
    rcases hy with rfl | ⟨b, -, rfl⟩
    · exact absurd rfl hne
    · simp [ρ, ψ]
  · simp only [g, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hy
    rcases hy with rfl | ⟨j, rfl⟩
    · exact absurd rfl hne
    · simp [ρ, ψ]
  · simp only [g, Finset.mem_insert, Finset.mem_image] at hy
    rcases hy with rfl | ⟨b, -, rfl⟩
    · exact absurd rfl hne
    · simp [ρ, ψ]

lemma hcard (t : ℕ) (i : It t) (hi : i ∈ s t) : t + 2 ≤ (g t i).card := by
  rw [mem_s] at hi
  rcases i with ⟨A, i⟩ | ⟨A, _ | _⟩
  · have hA : t + 1 ≤ A.card := hi
    have hnot : (Sum.inr (Sum.inl (A, i)) : Vt t) ∉ A.image Sum.inl := by
      simp
    simp only [g]
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ Sum.inl_injective]
    omega
  · have hnot : (Sum.inr (Sum.inr A) : Vt t) ∉
        (Finset.univ : Finset (Fin (t + 1))).image (fun i => Sum.inr (Sum.inl (A, i))) := by
      simp
    have hinj : Function.Injective (fun i : Fin (t + 1) => (Sum.inr (Sum.inl (A, i)) : Vt t)) := by
      intro a b hab
      simpa using hab
    simp only [g]
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj,
      Finset.card_univ, Fintype.card_fin]
  · have hA : t + 1 ≤ A.card := hi
    have hnot : (Sum.inr (Sum.inr A) : Vt t) ∉ A.image Sum.inl := by
      simp
    simp only [g]
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ Sum.inl_injective]
    omega

lemma hfib (t : ℕ) (v : Vt t) : ((s t).filter (fun i => ψ t i = v)).card ≤ 2 := by
  rcases v with b | ⟨A, i⟩ | A
  · refine (Finset.card_le_card (t := ∅) ?_).trans (by simp)
    intro j hj
    have hj2 := (Finset.mem_filter.1 hj).2
    rcases j with ⟨A', i'⟩ | ⟨A', b'⟩
    · simp [ψ] at hj2
    · simp [ψ] at hj2
  · refine (Finset.card_le_card (t := {Sum.inl (A, i), Sum.inl (A, i)}) ?_).trans
      Finset.card_le_two
    intro j hj
    have hj2 := (Finset.mem_filter.1 hj).2
    rcases j with ⟨A', i'⟩ | ⟨A', b'⟩
    · simp only [ψ, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at hj2
      obtain ⟨rfl, rfl⟩ := hj2
      simp
    · simp [ψ] at hj2
  · refine (Finset.card_le_card (t := {Sum.inr (A, true), Sum.inr (A, false)}) ?_).trans
      Finset.card_le_two
    intro j hj
    have hj2 := (Finset.mem_filter.1 hj).2
    rcases j with ⟨A', i'⟩ | ⟨A', b'⟩
    · simp [ψ] at hj2
    · simp only [ψ, Sum.inr.injEq] at hj2
      subst hj2
      cases b' <;> simp

lemma fin2 : ∀ a b c : Fin 2, a ≠ c → b ≠ c → a = b := by decide

lemma fin2' : ∀ a : Fin 2, a ≠ 0 → a = 1 := by decide

/-- A colouring with a monochromatic set `A` of `t + 1` base points has a monochromatic set. -/
lemma core (t : ℕ) (c : Vt t → Fin 2)
    (h : ∀ i ∈ s t, ∃ x ∈ g t i, ∃ y ∈ g t i, c x ≠ c y)
    (A : Finset (B t)) (hA : t + 1 ≤ A.card) (γ : Fin 2)
    (hγ : ∀ b ∈ A, c (Sum.inl b) = γ) : False := by
  have hmid : ∀ i : Fin (t + 1), c (Sum.inr (Sum.inl (A, i))) ≠ γ := by
    intro i hc
    obtain ⟨x, hx, y, hy, hxy⟩ := h (Sum.inl (A, i)) ((mem_s t _).2 hA)
    have key : ∀ z ∈ g t (Sum.inl (A, i)), c z = γ := by
      intro z hz
      simp only [g, Finset.mem_insert, Finset.mem_image] at hz
      rcases hz with rfl | ⟨b, hb, rfl⟩
      · exact hc
      · exact hγ b hb
    exact hxy ((key x hx).trans (key y hy).symm)
  have htop : c (Sum.inr (Sum.inr A)) ≠ γ := by
    intro hc
    obtain ⟨x, hx, y, hy, hxy⟩ := h (Sum.inr (A, true)) ((mem_s t _).2 hA)
    have key : ∀ z ∈ g t (Sum.inr (A, true)), c z = γ := by
      intro z hz
      simp only [g, Finset.mem_insert, Finset.mem_image] at hz
      rcases hz with rfl | ⟨b, hb, rfl⟩
      · exact hc
      · exact hγ b hb
    exact hxy ((key x hx).trans (key y hy).symm)
  obtain ⟨x, hx, y, hy, hxy⟩ := h (Sum.inr (A, false)) ((mem_s t _).2 hA)
  have key : ∀ z ∈ g t (Sum.inr (A, false)), c z = c (Sum.inr (Sum.inr A)) := by
    intro z hz
    simp only [g, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with rfl | ⟨i, rfl⟩
    · rfl
    · exact fin2 _ _ γ (hmid i) htop
  exact hxy ((key x hx).trans (key y hy).symm)

/-- The family has no proper 2-colouring. -/
lemma not_colorable (t : ℕ) (c : Vt t → Fin 2)
    (h : ∀ i ∈ s t, ∃ x ∈ g t i, ∃ y ∈ g t i, c x ≠ c y) : False := by
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (B t))) (fun b => c (Sum.inl b) = 0)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  by_cases hR : t + 1 ≤ ((Finset.univ : Finset (B t)).filter (fun b => c (Sum.inl b) = 0)).card
  · exact core t c h _ hR 0 (fun b hb => (Finset.mem_filter.1 hb).2)
  · have hBl : t + 1 ≤
        ((Finset.univ : Finset (B t)).filter (fun b => ¬ c (Sum.inl b) = 0)).card := by
      omega
    exact core t c h _ hBl 1 (fun b hb => fin2' _ (Finset.mem_filter.1 hb).2)

end OMA.E1022

open OMA.E1022 in
theorem OMA.solution : type_of% @Erdos1022.erdos_1022.variants.lt_two := by
  intro t c h
  by_contra hc
  rw [not_lt] at hc
  obtain ⟨e⟩ : Nonempty (Vt t ↪ ℕ) :=
    ⟨(Fintype.equivFin (Vt t)).toEmbedding.trans Fin.valEmbedding⟩
  have hB := h ((s t).image (fun i => (g t i).map e)) ?_ ?_
  · obtain ⟨f, hf⟩ := hB
    apply not_colorable t (fun v => f (e v))
    intro i hi
    obtain ⟨x, hx, y, hy, hxy⟩ := hf ((g t i).map e) (Finset.mem_image_of_mem _ hi)
    rw [Finset.mem_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨x', hx', y', hy', hxy⟩
  · intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨i, hi, rfl⟩ := hA
    rw [Finset.card_map]
    have := hcard t i hi
    omega
  · intro X hX
    have hiff : ∀ i : It t, (g t i).map e ⊆ X ↔
        g t i ⊆ (Finset.univ : Finset (Vt t)).filter (fun v => e v ∈ X) := by
      intro i
      constructor
      · intro hsub v hv
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hsub (Finset.mem_map_of_mem e hv)⟩
      · intro hsub n hn
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hn
        exact (Finset.mem_filter.1 (hsub hv)).2
    have hle1 : (((s t).image (fun i => (g t i).map e)).hypergraphInduce X).card ≤
        ((s t).filter (fun i => g t i ⊆
          (Finset.univ : Finset (Vt t)).filter (fun v => e v ∈ X))).card := by
      unfold Finset.hypergraphInduce
      rw [Finset.filter_image]
      refine Finset.card_image_le.trans (le_of_eq ?_)
      congr 1
      ext i
      simp only [Finset.mem_filter]
      rw [hiff i]
    have hXle : ((Finset.univ : Finset (Vt t)).filter (fun v => e v ∈ X)).card ≤ X.card := by
      rw [← Finset.card_map e]
      apply Finset.card_le_card
      intro n hn
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hn
      exact (Finset.mem_filter.1 hv).2
    have hXpos : 0 < X.card := Finset.card_pos.2 hX
    have hN : ((s t).filter (fun i => g t i ⊆
        (Finset.univ : Finset (Vt t)).filter (fun v => e v ∈ X))).card + 1 ≤ 2 * X.card := by
      by_cases hne : ((Finset.univ : Finset (Vt t)).filter (fun v => e v ∈ X)).Nonempty
      · have := count_le (s t) (g t) (ψ t) (ρ t) (fun i _ => hmem t i)
          (fun i _ y hy hne' => hrank t i y hy hne')
          (fun i hi => by have := hcard t i hi; omega) (hfib t) _ hne
        omega
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne]
        have hzero : ((s t).filter (fun i => g t i ⊆ (∅ : Finset (Vt t)))).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro i _ hsub
          exact absurd (hsub (hmem t i)) (Finset.notMem_empty _)
        omega
    have hreal : ((((s t).image (fun i => (g t i).map e)).hypergraphInduce X).card : ℝ) + 1
        ≤ 2 * (X.card : ℝ) := by
      exact_mod_cast (Nat.add_le_add_right hle1 1).trans hN
    have hc2 : 2 * (X.card : ℝ) ≤ c * (X.card : ℝ) :=
      mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
    linarith
