import FormalConjectures.ErdosProblems.«934»

-- Problem: Erdős Problem 934 — kmp h three four
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/934.lean:150 (declaration Erdos934.erdos_934.variants.kmp_h_three_four)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open SimpleGraph Finset

namespace OMA934

lemma three_le_iff {V : Type*} (G : SimpleGraph V) (a b : V) :
    ((3 : ℕ) : ℕ∞) ≤ G.edist a b ↔ a ≠ b ∧ ¬ G.Adj a b ∧ G.commonNeighbors a b = ∅ := by
  rw [← two_lt_edist_iff]
  constructor
  · intro h
    exact lt_of_lt_of_le (by norm_num) h
  · intro h
    have := Order.add_one_le_of_lt h
    have h3 : ((3 : ℕ) : ℕ∞) = 2 + 1 := by norm_num
    rw [h3]; exact this

/-- Every graph of maximum degree at most `4` with at least `1000` edges has two far edges. -/
theorem mem_big (n : ℕ) (G : SimpleGraph (Fin n))
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ 4) (hE : 1000 ≤ G.edgeSet.ncard) :
    Erdos934.HasFarEdges G 3 := by
  classical
  have hdeg' : ∀ v, (G.neighborFinset v).card ≤ 4 := by
    intro v
    rw [← Set.ncard_coe_finset, coe_neighborFinset]
    exact hdeg v
  have hEc : 1000 ≤ G.edgeFinset.card := by
    rwa [← Set.ncard_coe_finset, coe_edgeFinset]
  have hne : G.edgeFinset.Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨e, he⟩ := hne
  induction e using Sym2.ind with
  | _ u v =>
  have huv : G.Adj u v := by simpa using he
  set S : Finset (Fin n) := {u, v} with hS
  set S1 : Finset (Fin n) := S ∪ S.biUnion (fun a => G.neighborFinset a) with hS1
  set B : Finset (Fin n) := S1 ∪ S1.biUnion (fun a => G.neighborFinset a) with hB
  have hbu : ∀ s : Finset (Fin n), (s.biUnion (fun a => G.neighborFinset a)).card ≤ s.card * 4 := by
    intro s
    calc (s.biUnion (fun a => G.neighborFinset a)).card ≤ ∑ a ∈ s, (G.neighborFinset a).card :=
          card_biUnion_le
      _ ≤ ∑ _a ∈ s, 4 := sum_le_sum (fun a _ => hdeg' a)
      _ = s.card * 4 := by simp
  have hScard : S.card ≤ 2 := card_le_two
  have hS1card : S1.card ≤ 10 := by
    calc S1.card ≤ S.card + (S.biUnion (fun a => G.neighborFinset a)).card := card_union_le _ _
      _ ≤ S.card + S.card * 4 := by have := hbu S; omega
      _ ≤ 10 := by omega
  have hBcard : B.card ≤ 50 := by
    calc B.card ≤ S1.card + (S1.biUnion (fun a => G.neighborFinset a)).card := card_union_le _ _
      _ ≤ S1.card + S1.card * 4 := by have := hbu S1; omega
      _ ≤ 50 := by omega
  set T := B.biUnion (fun a => G.incidenceFinset a) with hT
  have hTcard : T.card ≤ 200 := by
    calc T.card ≤ ∑ a ∈ B, (G.incidenceFinset a).card := card_biUnion_le
      _ ≤ ∑ _a ∈ B, 4 := sum_le_sum (fun a _ => by
          rw [card_incidenceFinset_eq_degree, ← card_neighborFinset_eq_degree]
          exact hdeg' a)
      _ = B.card * 4 := by simp
      _ ≤ 200 := by omega
  have hdiff : (G.edgeFinset \ T).Nonempty := by
    rw [← Finset.card_pos]
    have := le_card_sdiff T G.edgeFinset
    omega
  obtain ⟨f, hf⟩ := hdiff
  rw [Finset.mem_sdiff] at hf
  obtain ⟨hf1, hf2⟩ := hf
  induction f using Sym2.ind with
  | _ w x =>
  have hwx : G.Adj w x := by simpa using hf1
  have hnotB : ∀ y, y ∈ s(w, x) → y ∉ B := by
    intro y hy hyB
    apply hf2
    rw [hT, Finset.mem_biUnion]
    refine ⟨y, hyB, ?_⟩
    rw [mem_incidenceFinset]
    exact ⟨hf1 |> (mem_edgeFinset.mp), hy⟩
  refine ⟨u, v, w, x, huv, hwx, ?_⟩
  intro a ha b hb
  have haS : a ∈ S := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> simp [hS]
  have hbB : b ∉ B := by
    apply hnotB
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl <;> simp
  have haS1 : a ∈ S1 := by rw [hS1]; exact mem_union_left _ haS
  rw [three_le_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    exact hbB (mem_union_left _ haS1)
  · intro hab
    apply hbB
    apply mem_union_left
    rw [hS1]
    apply mem_union_right
    rw [mem_biUnion]
    exact ⟨a, haS, by simpa using hab⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    intro c hc
    rw [mem_commonNeighbors] at hc
    apply hbB
    apply mem_union_right
    rw [mem_biUnion]
    refine ⟨c, ?_, by simpa using hc.2.symm⟩
    rw [hS1]
    apply mem_union_right
    rw [mem_biUnion]
    exact ⟨a, haS, by simpa using hc.1⟩

/-- Bit masks of the `3`-subsets of `{0, …, 6}`. -/
def masks : List ℕ :=
  [7, 11, 19, 35, 67, 13, 21, 37, 69, 25, 41, 73, 49, 81, 97, 14, 22, 38, 70, 26, 42, 74, 50,
    82, 98, 28, 44, 76, 52, 84, 100, 56, 88, 104, 112]

def M (i : Fin 35) : ℕ := masks.getD i 0

/-- The odd graph `KG(7,3)`: `3`-subsets of a `7`-set, adjacent when disjoint. -/
def KG : SimpleGraph (Fin 35) where
  Adj i j := i ≠ j ∧ M i &&& M j = 0
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [Nat.land_comm]; exact h.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

instance : DecidableRel KG.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ M i &&& M j = 0))

lemma KG_card_filter : ∀ v : Fin 35, (univ.filter (KG.Adj v)).card = 4 := by
  decide

lemma KG_degree (v : Fin 35) : KG.degree v = 4 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  exact KG_card_filter v

lemma KG_deg (v : Fin 35) : (KG.neighborSet v).ncard ≤ 4 := by
  rw [← coe_neighborFinset, Set.ncard_coe_finset, card_neighborFinset_eq_degree, KG_degree]

lemma KG_edges : 70 ≤ KG.edgeSet.ncard := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  have := KG.sum_degrees_eq_twice_card_edges
  simp only [KG_degree, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

/-- A computable test certifying that `a` and `b` are at distance at most two. -/
def close (a b : Fin 35) : Bool :=
  let x := M a &&& M b
  x == 0 || (x &&& (x - 1)) != 0

lemma close_spec : ∀ a b : Fin 35, close a b = true →
    a = b ∨ KG.Adj a b ∨ ∃ c, KG.Adj a c ∧ KG.Adj c b := by
  decide +kernel

def nb (u : Fin 35) : List (Fin 35) := (List.finRange 35).filter (fun v => decide (KG.Adj u v))

def keyB : Bool :=
  (List.finRange 35).all fun u => (nb u).all fun v => (List.finRange 35).all fun w =>
    (nb w).all fun x => close u w || close u x || close v w || close v x

lemma keyB_true : keyB = true := by decide +kernel

lemma key (u v w x : Fin 35) (huv : KG.Adj u v) (hwx : KG.Adj w x) :
    close u w || close u x || close v w || close v x := by
  have := keyB_true
  simp only [keyB, List.all_eq_true, List.mem_finRange, true_implies, nb, List.mem_filter,
    decide_eq_true_eq, and_imp] at this
  exact this u v huv w x hwx

lemma not_far_of_close {a b : Fin 35} (h : close a b = true) :
    ¬ ((3 : ℕ) : ℕ∞) ≤ KG.edist a b := by
  rw [three_le_iff]
  rintro ⟨h1, h2, h3⟩
  rcases close_spec a b h with h | h | ⟨c, hc1, hc2⟩
  · exact h1 h
  · exact h2 h
  · have : c ∈ KG.commonNeighbors a b := by
      rw [mem_commonNeighbors]; exact ⟨hc1, hc2.symm⟩
    rw [h3] at this
    exact this

lemma KG_not_far : ¬ Erdos934.HasFarEdges KG 3 := by
  rintro ⟨u, v, w, x, huv, hwx, h⟩
  have hk := key u v w x huv hwx
  simp only [Bool.or_eq_true] at hk
  rcases hk with ((hk | hk) | hk) | hk
  · exact not_far_of_close hk (h u (by simp) w (by simp))
  · exact not_far_of_close hk (h u (by simp) x (by simp))
  · exact not_far_of_close hk (h v (by simp) w (by simp))
  · exact not_far_of_close hk (h v (by simp) x (by simp))

end OMA934

theorem OMA.solution : type_of% @Erdos934.erdos_934.variants.kmp_h_three_four := by
  unfold Erdos934.h
  apply le_csInf
  · exact ⟨1000, fun n G hdeg hE => OMA934.mem_big n G hdeg hE⟩
  · intro m hm
    by_contra hlt
    rw [not_le] at hlt
    exact OMA934.KG_not_far (hm 35 OMA934.KG OMA934.KG_deg (by
      have := OMA934.KG_edges
      omega))
