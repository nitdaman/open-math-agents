import FormalConjectures.ErdosProblems.«617»

/-! # Four colors on seventeen vertices
The minority-color argument follows Lemma 2 of Erdős and Gyárfás,
*Split and balanced colorings of complete graphs* (1999).
-/
namespace OMA.R_Erdos617_erdos_617_variants_r_eq_4_R1
open Finset SimpleGraph
open scoped Classical

private def graph {V : Type} (c : Sym2 V → Fin 4) (k : Fin 4) : SimpleGraph V where
  Adj u v := u ≠ v ∧ c s(u,v) = k
  symm := ⟨fun _ _ ⟨h,e⟩ => ⟨h.symm,Sym2.eq_swap ▸ e⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private lemma class_edges {V : Type} [Fintype V] (c : Sym2 V → Fin 4) (k : Fin 4) :
    (graph c k).edgeFinset = (⊤ : SimpleGraph V).edgeFinset.filter (fun e => c e = k) := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
    rw [mem_filter, mem_edgeFinset, mem_edgeFinset]
    exact Iff.rfl

private lemma edge_total {V : Type} [Fintype V] (c : Sym2 V → Fin 4) :
    ∑ k, (graph c k).edgeFinset.card = (Fintype.card V).choose 2 := by
  simp_rw [class_edges]
  rw [sum_card_fiberwise_eq_card_filter]
  simpa using (card_edgeFinset_top_eq_card_choose_two (V := V))

private def Witness {V : Type} (c : Sym2 V → Fin 4) : Prop :=
  ∃ (S : Finset V) (k : Fin 4), S.card = 5 ∧
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b → c s(a,b) ≠ k

/-- In a coloring without a witness, each color occupies one to seven of
the ten edges on every set of five vertices. -/
private lemma five_edges {V : Type} [DecidableEq V] (c : Sym2 V → Fin 4) (h : ¬ Witness c)
    (S : Finset V) (five : S.card = 5) (k : Fin 4) :
    1 ≤ ((graph c k).induce (S : Set V)).edgeFinset.card ∧
      ((graph c k).induce (S : Set V)).edgeFinset.card ≤ 7 := by
  classical
  let d : Sym2 S → Fin 4 := c ∘ Sym2.map Subtype.val
  have eq (i : Fin 4) : (graph c i).induce (S : Set V) = graph d i := by
    ext a b
    change ((a : V) ≠ b ∧ _) ↔ (a ≠ b ∧ _)
    constructor
    · rintro ⟨ne,col⟩
      exact ⟨fun e => ne (congrArg Subtype.val e),col⟩
    · rintro ⟨ne,col⟩
      exact ⟨fun e => ne (Subtype.ext e),col⟩
  have pos (i : Fin 4) : 0 < (graph d i).edgeFinset.card := by
    by_contra! empty
    apply h
    refine ⟨S,i,five,?_⟩
    intro a ha b hb ne ab
    have adj : (graph d i).Adj ⟨a,ha⟩ ⟨b,hb⟩ :=
      ⟨fun e => ne (congrArg Subtype.val e), ab⟩
    have mem : s(⟨a,ha⟩,⟨b,hb⟩) ∈ (graph d i).edgeFinset := mem_edgeFinset.mpr adj
    have := card_pos.mpr ⟨_,mem⟩
    omega
  have total := edge_total d
  rw [Fintype.card_coe,five] at total
  simp only [Fin.sum_univ_four] at total
  norm_num [Nat.choose] at total
  have ce := congrArg (fun H : SimpleGraph S => Nat.card H.edgeSet) (eq k)
  change Nat.card _ = Nat.card _ at ce
  simp only [Nat.card_eq_fintype_card, card_edgeSet] at ce
  rw [ce]
  refine ⟨pos k,?_⟩
  have p0 := pos 0
  have p1 := pos 1
  have p2 := pos 2
  have p3 := pos 3
  rcases (by decide : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) k with rfl|rfl|rfl|rfl <;> omega

/-- The common nonneighbors of two distinct vertices, excluding the vertices
themselves. -/
private noncomputable def outsidePair {V : Type} [Fintype V] (G : SimpleGraph V) (x y : V) : Finset V :=
  univ.filter fun z => z ≠ x ∧ z ≠ y ∧ ¬G.Adj x z ∧ ¬G.Adj y z

private lemma mem_outsidePair {V : Type} [Fintype V] {G : SimpleGraph V} {x y z : V} :
    z ∈ outsidePair G x y ↔ z ≠ x ∧ z ≠ y ∧ ¬G.Adj x z ∧ ¬G.Adj y z := by
  simp [outsidePair]

private lemma no_empty_triple {V : Type} [Fintype V] [DecidableEq V]
    {c : Sym2 V → Fin 4} (bad : ¬ Witness c) (k : Fin 4) {x y : V}
    (xy : x ≠ y) (exy : ¬(graph c k).Adj x y) :
    ∀ a ∈ outsidePair (graph c k) x y, ∀ b ∈ outsidePair (graph c k) x y,
      ∀ d ∈ outsidePair (graph c k) x y, a ≠ b → a ≠ d → b ≠ d →
        (graph c k).Adj a b ∨ (graph c k).Adj a d ∨ (graph c k).Adj b d := by
  intro a ha b hb d hd ab ad bd
  obtain ⟨ax,ay,exa,eya⟩ := mem_outsidePair.mp ha
  obtain ⟨bx,by',exb,eyb⟩ := mem_outsidePair.mp hb
  obtain ⟨dx,dy,exd,eyd⟩ := mem_outsidePair.mp hd
  by_contra! edges
  obtain ⟨eab,ead,ebd⟩ := edges
  apply bad
  refine ⟨{x,y,a,b,d},k,by simp [xy,ax.symm,ay.symm,bx.symm,by'.symm,dx.symm,dy.symm,ab,ad,bd],?_⟩
  have diff {s t : V} (ne : s ≠ t) (e : ¬(graph c k).Adj s t) : c s(s,t) ≠ k :=
    fun same => e ⟨ne,same⟩
  have := diff xy exy
  have hxA := diff ax.symm exa
  have hxB := diff bx.symm exb
  have hxD := diff dx.symm exd
  have hyA := diff ay.symm eya
  have hyB := diff by'.symm eyb
  have hyD := diff dy.symm eyd
  have hab := diff ab eab
  have had := diff ad ead
  have hbd := diff bd ebd
  clear ha hb hd exy exa eya exb eyb exd eyd eab ead ebd
  intro u hu v hv ne
  simp only [mem_insert,mem_singleton] at hu hv
  rcases hu with rfl|rfl|rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl|rfl|rfl <;>
    simp_all [Sym2.eq_swap]

/-- Local Ramsey step. Nine vertices without an independent triple contain
five vertices spanning at least eight edges. -/
def H1 : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (X : Finset V), 9 ≤ X.card →
    (∀ a ∈ X, ∀ b ∈ X, ∀ d ∈ X, a ≠ b → a ≠ d → b ≠ d →
      G.Adj a b ∨ G.Adj a d ∨ G.Adj b d) →
    ∃ S ⊆ X, S.card = 5 ∧ 8 ≤ (G.induce (S : Set V)).edgeFinset.card

/-- The remaining extremal counting step on seventeen vertices. If every
five-set spans between one and seven edges and each independent pair has at most
eight common nonneighbors, the graph needs at least thirty-five edges. -/
def H2 : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    Fintype.card V = 17 →
    (∀ S : Finset V, S.card = 5 → 1 ≤ (G.induce (S : Set V)).edgeFinset.card ∧
      (G.induce (S : Set V)).edgeFinset.card ≤ 7) →
    (∀ x y, x ≠ y → ¬G.Adj x y →
      (univ.filter (fun z => z ≠ x ∧ z ≠ y ∧ ¬G.Adj x z ∧ ¬G.Adj y z)).card ≤ 8) →
    35 ≤ G.edgeFinset.card

theorem main : H1 → H2 → type_of% @Erdos617.erdos_617.variants.r_eq_4 := by
  intro localBound globalBound _ _ V _ _ size c
  classical
  change Witness c
  by_contra bad
  have order : Fintype.card V = 17 := by simpa using size
  have total := edge_total c
  rw [order] at total
  simp only [Fin.sum_univ_four] at total
  norm_num [Nat.choose] at total
  obtain ⟨k,minor⟩ : ∃ k : Fin 4, (graph c k).edgeFinset.card ≤ 34 := by
    by_contra! all
    have h0 := all 0
    have h1 := all 1
    have h2 := all 2
    have h3 := all 3
    omega
  have five (S : Finset V) (hs : S.card = 5) := five_edges c bad S hs k
  apply Nat.not_succ_le_self 34
  apply le_trans (globalBound (graph c k) order five ?_) minor
  intro x y xy nonedge
  by_contra! nine
  let Z := univ.filter (fun z => z ≠ x ∧ z ≠ y ∧ ¬(graph c k).Adj x z ∧ ¬(graph c k).Adj y z)
  change 8 < Z.card at nine
  have zeq : Z = outsidePair (graph c k) x y := by ext z; simp [Z, outsidePair]
  rw [zeq] at nine
  have bound : 9 ≤ (outsidePair (graph c k) x y).card := by omega
  obtain ⟨S,_,hs,dense⟩ := localBound (graph c k) _ bound (no_empty_triple bad k xy nonedge)
  have upper := (five S hs).2
  omega

end OMA.R_Erdos617_erdos_617_variants_r_eq_4_R1
