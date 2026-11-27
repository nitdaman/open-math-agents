import FormalConjectures.ErdosProblems.«1182»

/-! # Sparse graphs and the five-cycle obstruction to triangle goodness -/
-- Credit: @steveDOTdigital
namespace OMA.R_Erdos1182_erdos_1182_parts_iii_R1
open Erdos1182 Filter
-- A linear number of random edges hits all pairs of disjoint k-subsets
-- with positive probability. Adding a spanning tree ensures connectivity.
def H1 : Prop := ∃ C : ℕ, ∀ k : ℕ, 0 < k →
    ∃ G : SimpleGraph (Fin (20*k)), G.Connected ∧ G.edgeSet.ncard ≤ C*(20*k) ∧
    (∀ A B : Finset (Fin (20*k)), A.card = k → B.card = k → Disjoint A B →
      ∃ a ∈ A, ∃ b ∈ B, G.Adj a b)
-- A balanced blow-up of the five-cycle has five independent parts of size 8k.
-- Any 20k embedded vertices meet three parts in at least k vertices each.
def H2 : Prop := ∀ k : ℕ, 0 < k → ∀ G : SimpleGraph (Fin (20*k)),
    (∀ A B : Finset (Fin (20*k)), A.card = k → B.card = k → Disjoint A B →
      ∃ a ∈ A, ∃ b ∈ B, G.Adj a b) → ¬ IsTriangleGood G

theorem main : H1 → H2 → type_of% @Erdos1182.erdos_1182.parts.iii := by
  intro sparse obstruction divergence
  obtain ⟨C,hC⟩ := sparse
  obtain ⟨N,hN⟩ := eventually_atTop.1 ((tendsto_atTop.1 divergence) ((C : ℝ)+1))
  let k := N+1
  have hk : 0 < k := Nat.succ_pos _
  let n := 20*k
  have hn : 0 < n := by dsimp [n]; omega
  obtain ⟨G,connected,small,edges⟩ := hC k hk
  have hbad := obstruction k hk G edges
  have upper : F n ≤ C*n := by
    unfold F
    apply csSup_le'
    rintro q ⟨_,hq⟩
    by_contra! h
    exact hbad (hq G connected (small.trans h.le))
  have hlarge := hN n (by dsimp [n,k]; omega)
  change (C : ℝ)+1 ≤ (F n : ℝ)/n at hlarge
  have pos : (0 : ℝ) < n := by exact_mod_cast hn
  have up : (F n : ℝ) ≤ C*(n : ℝ) := by exact_mod_cast upper
  rw [le_div_iff₀ pos] at hlarge
  linarith
-- Count the edge lists which miss at least one k-by-k rectangle.
private theorem hittingList (k : ℕ) (hk : 0 < k) :
    ∃ L : Fin (800*(20*k)) → Fin (20*k) × Fin (20*k),
      ∀ A B : Finset (Fin (20*k)), A.card = k → B.card = k →
        ∃ t, (L t).1 ∈ A ∧ (L t).2 ∈ B := by
  classical
  let n := 20*k
  let m := 800*n
  let V := Fin n
  let P := ((Finset.univ : Finset V).powersetCard k)
  let boxes := P ×ˢ P
  let miss (p : Finset V × Finset V) : Finset (Fin m → V × V) :=
    Fintype.piFinset fun _ => (p.1 ×ˢ p.2)ᶜ
  have count (p) (hp : p ∈ boxes) : (miss p).card = (399*k^2)^m := by
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    have a := (Finset.mem_powersetCard.mp ha).2
    have b := (Finset.mem_powersetCard.mp hb).2
    have c : ((p.1 ×ˢ p.2)ᶜ : Finset (V × V)).card = 399*k^2 := by
      rw [Finset.card_compl, Finset.card_product, a, b]
      have size : Fintype.card (V × V) = 400*(k*k) := by simp [V,n]; ring
      rw [size, pow_two]
      omega
    simp [miss, c]
  have pc : P.card ≤ 2^n := by
    calc
      _ ≤ (Finset.univ : Finset V).powerset.card :=
        Finset.card_le_card (fun _ h => Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp h).1)
      _ = _ := by simp [V]
  have bc : boxes.card ≤ 4^n := by
    calc
      boxes.card = P.card * P.card := Finset.card_product ..
      _ ≤ 2^n * 2^n := Nat.mul_le_mul pc pc
      _ = _ := by rw [← mul_pow]; rfl
  have bound : (boxes.biUnion miss).card ≤ 4^n * (399*k^2)^m := by
    calc
      _ ≤ ∑ p ∈ boxes, (miss p).card := Finset.card_biUnion_le
      _ = boxes.card * (399*k^2)^m := Finset.sum_const_nat (fun p hp => count p hp)
      _ ≤ _ := Nat.mul_le_mul_right _ bc
  have gap : 4^n * (399*k^2)^m < (400*k^2)^m := by
    have base : 4*399^800 < (400:ℕ)^800 := by
      rw [show 800 = 200 * 4 by decide, pow_mul, pow_mul]
      norm_num1
    have power := Nat.pow_lt_pow_left base (show n ≠ 0 by dsimp [n]; omega)
    rw [mul_pow, ← pow_mul, ← pow_mul] at power
    dsimp [m]
    rw [mul_pow (399:ℕ), mul_pow (400:ℕ), ← Nat.mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right power (by positivity)
  have all : (Finset.univ : Finset (Fin m → V × V)).card = (400*k^2)^m := by
    simp [V,n]
    ring
  obtain ⟨L,hL,hout⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (bound.trans_lt (gap.trans_eq all.symm))
  refine ⟨L, fun A B a b => ?_⟩
  by_contra! h
  apply hout
  refine Finset.mem_biUnion.mpr ⟨(A,B), Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,a⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,b⟩
  · apply Fintype.mem_piFinset.mpr
    intro t
    exact Finset.mem_compl.mpr fun hp => (h t (Finset.mem_product.mp hp).1) (Finset.mem_product.mp hp).2

theorem sparseGraphs : H1 := by
  classical
  refine ⟨801, fun k hk => ?_⟩
  let root : Fin (20*k) := ⟨0,by omega⟩
  obtain ⟨L,hit⟩ := hittingList k hk
  let listed := Finset.univ.image fun t => s((L t).1,(L t).2)
  let spokes := Finset.univ.image fun v => s(root,v)
  let E := listed ∪ spokes
  let G := SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin (20*k))))
  refine ⟨G, SimpleGraph.Connected.of_isUniversal (v := root) ?_, ?_, ?_⟩
  · intro w h
    exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ w)),h⟩
  · have bound : G.edgeSet.ncard ≤ E.card := by
      change (SimpleGraph.fromEdgeSet _).edgeSet.ncard ≤ _
      rw [SimpleGraph.edgeSet_fromEdgeSet, ← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard Set.sdiff_subset
    have a : listed.card ≤ 800*(20*k) := by
      exact (Finset.card_image_le).trans_eq (by simp)
    have b : spokes.card ≤ 20*k := by
      exact (Finset.card_image_le).trans_eq (by simp)
    have union := Finset.card_union_le listed spokes
    dsimp [E] at bound
    omega
  · intro A B a b dis
    obtain ⟨t,ha,hb⟩ := hit A B a b
    refine ⟨_,ha,_,hb,(SimpleGraph.fromEdgeSet_adj _).mpr ⟨?_,?_⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))
    · intro eq
      exact Finset.disjoint_left.mp dis ha (eq ▸ hb)

-- The red graph is the pullback of the cycle on five vertices.
private def near (i j : Fin 5) : Prop := i + 1 = j ∨ j + 1 = i

private theorem distinctParts : ∀ i : Fin 5, ¬ near i i := by
  unfold near
  decide

private theorem noTriangle : ∀ i j l : Fin 5, near i j → near j l → ¬ near i l := by
  unfold near
  decide

private theorem adjacentLarge {k : ℕ} (c : Fin 5 → ℕ)
    (total : ∑ i, c i = 20*k) (cap : ∀ i, c i ≤ 8*k) :
    ∃ i j, near i j ∧ k ≤ c i ∧ k ≤ c j := by
  by_contra! h
  have h01 := h 0 1 (by unfold near; decide : near 0 1)
  have h12 := h 1 2 (by unfold near; decide : near 1 2)
  have h23 := h 2 3 (by unfold near; decide : near 2 3)
  have h34 := h 3 4 (by unfold near; decide : near 3 4)
  have h40 := h 4 0 (by unfold near; decide : near 4 0)
  have c0 := cap 0
  have c1 := cap 1
  have c2 := cap 2
  have c3 := cap 3
  have c4 := cap 4
  simp [Fin.sum_univ_succ] at total
  omega

theorem obstruction : H2 := by
  classical
  intro k hk G hit good
  let N := 2*(20*k)-1
  let sizes : Set ℕ := {m | ∀ D : SimpleGraph (Fin m),
    (⊤ : SimpleGraph (Fin 3)).IsContained D ∨ G.IsContained Dᶜ}
  change sInf sizes = N at good
  have ne : sizes.Nonempty := by
    by_contra! hempty
    rw [hempty] at good
    simp [N] at good
    omega
  have minimal := csInf_mem ne
  rw [good] at minimal
  obtain ⟨e⟩ : Nonempty (Fin N ↪ Fin 5 × Fin (8*k)) :=
    Function.Embedding.nonempty_of_card_le (by simp [N]; omega)
  let D : SimpleGraph (Fin N) := {
    Adj := fun a b => near (e a).1 (e b).1
    symm := ⟨fun _ _ h => Or.symm h⟩
    loopless := ⟨fun _ => distinctParts _⟩ }
  rcases minimal D with ht | hf
  · let T := ht.some
    exact noTriangle _ _ _
      (T.toHom.map_rel' (show (⊤ : SimpleGraph (Fin 3)).Adj 0 1 by decide))
      (T.toHom.map_rel' (show (⊤ : SimpleGraph (Fin 3)).Adj 1 2 by decide))
      (T.toHom.map_rel' (show (⊤ : SimpleGraph (Fin 3)).Adj 0 2 by decide))
  · let f := hf.some
    let part (x : Fin (20*k)) := (e (f x)).1
    let S (i : Fin 5) := Finset.univ.filter fun x => part x = i
    have cap (i : Fin 5) : (S i).card ≤ 8*k := by
      have bound := Finset.card_le_card_of_injOn
        (s := S i) (t := (Finset.univ : Finset (Fin (8*k))))
        (fun x => (e (f x)).2) (fun _ _ => Finset.mem_univ _) (by
          intro x hx y hy heq
          apply f.injective
          apply e.injective
          exact Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) heq)
      simpa using bound
    have total : ∑ i, (S i).card = 20*k := by
      simpa [S] using Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ part
    obtain ⟨i,j,hij,hi,hj⟩ := adjacentLarge (fun i => (S i).card) total cap
    obtain ⟨A,hA,cardA⟩ := Finset.exists_subset_card_eq hi
    obtain ⟨B,hB,cardB⟩ := Finset.exists_subset_card_eq hj
    have dis : Disjoint A B := by
      refine Finset.disjoint_left.mpr fun x ax bx => ?_
      have eqij := (Finset.mem_filter.mp (hA ax)).2.symm.trans (Finset.mem_filter.mp (hB bx)).2
      exact distinctParts i (eqij ▸ hij)
    obtain ⟨a,ha,b,hb,edge⟩ := hit A B cardA cardB dis
    have blue := f.toHom.map_rel' edge
    have red : D.Adj (f a) (f b) := by
      change near (part a) (part b)
      rwa [(Finset.mem_filter.mp (hA ha)).2,(Finset.mem_filter.mp (hB hb)).2]
    exact blue.2 red
end OMA.R_Erdos1182_erdos_1182_parts_iii_R1

open OMA.R_Erdos1182_erdos_1182_parts_iii_R1 in
theorem OMA.solution : type_of% @Erdos1182.erdos_1182.parts.iii := main sparseGraphs obstruction
