import FormalConjectures.ErdosProblems.«617»

/-! # Three colors on ten vertices
The neighborhood argument follows Erdős and Gyárfás, Lemma 1 (1999).
A disjoint-triangle count handles the cubic case directly.
-/
namespace OMA.TenVertices
open Finset
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

private def Witness (c : Sym2 V → Fin 3) : Prop :=
  ∃ (S : Finset V) (k : Fin 3), S.card = 4 ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ k

private def graph (c : Sym2 V → Fin 3) (k : Fin 3) : SimpleGraph V where
  Adj x y := x ≠ y ∧ c s(x,y) = k
  symm := ⟨fun _ _ ⟨h,e⟩ => ⟨h.symm,Sym2.eq_swap ▸ e⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private def Triangle (G : SimpleGraph V) (T : Finset V) : Prop :=
  T.card = 3 ∧ ∀ a ∈ T, ∀ b ∈ T, a ≠ b → G.Adj a b

private def ND (G : SimpleGraph V) : Prop :=
  ∀ a b x y, G.Adj a b → G.Adj a x → G.Adj b x → G.Adj a y → G.Adj b y → x = y

omit [Fintype V] in
private lemma diamond {c : Sym2 V → Fin 3} (h : ¬ Witness c) (k : Fin 3) : ND (graph c k) := by
  intro a b x y ab ax bx ay byy
  by_contra xy
  obtain ⟨j,jk,jxy⟩ := (by decide : ∀ k t : Fin 3, ∃ j, k ≠ j ∧ t ≠ j) k (c s(x,y))
  apply h
  refine ⟨{a,b,x,y},j,?_,?_⟩
  · simp [ab.1,ax.1,bx.1,ay.1,byy.1,xy]
  · have h₁ := ab.2
    have h₂ := ax.2
    have h₃ := bx.2
    have h₄ := ay.2
    have h₅ := byy.2
    intro u hu v hv ne
    simp only [mem_insert,mem_singleton] at hu hv
    rcases hu with rfl|rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl|rfl <;>
      simp_all [Sym2.eq_swap]

omit [Fintype V] in
private lemma notIndependent {c : Sym2 V → Fin 3} (h : ¬ Witness c) (k : Fin 3)
    {a b d e : V} (ab : a ≠ b) (ad : a ≠ d) (ae : a ≠ e)
    (bd : b ≠ d) (be : b ≠ e) (de : d ≠ e)
    (h₁ : ¬ (graph c k).Adj a b) (h₂ : ¬ (graph c k).Adj a d)
    (h₃ : ¬ (graph c k).Adj a e) (h₄ : ¬ (graph c k).Adj b d)
    (h₅ : ¬ (graph c k).Adj b e) (h₆ : ¬ (graph c k).Adj d e) : False := by
  apply h
  refine ⟨{a,b,d,e},k,by simp [ab,ad,ae,bd,be,de],?_⟩
  change ¬ (_ ∧ _) at h₁ h₂ h₃ h₄ h₅ h₆
  intro u hu v hv ne
  simp only [mem_insert,mem_singleton] at hu hv
  rcases hu with rfl|rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl|rfl <;>
    simp_all [Sym2.eq_swap]

private noncomputable def outside (G : SimpleGraph V) (v : V) : Finset V :=
  univ.filter fun x => x ≠ v ∧ ¬ G.Adj v x

private lemma triOrEdge {c : Sym2 V → Fin 3} (h : ¬ Witness c) (k : Fin 3)
    (v : V) {a b d : V} (ha : a ∈ outside (graph c k) v)
    (hb : b ∈ outside (graph c k) v) (hd : d ∈ outside (graph c k) v)
    (ab : a ≠ b) (ad : a ≠ d) (bd : b ≠ d) :
    (graph c k).Adj a b ∨ (graph c k).Adj a d ∨ (graph c k).Adj b d := by
  obtain ⟨av,va⟩ := (mem_filter.mp ha).2
  obtain ⟨bv,vb⟩ := (mem_filter.mp hb).2
  obtain ⟨dv,vd⟩ := (mem_filter.mp hd).2
  by_contra! empty
  exact notIndependent h k av.symm bv.symm dv.symm ab ad bd va vb vd empty.1 empty.2.1 empty.2.2

-- A graph on six vertices with no independent triple contains a triangle.
omit [Fintype V] in
private lemma ramseySix (G : SimpleGraph V) (X : Finset V) (six : 6 ≤ X.card)
    (edges : ∀ a ∈ X, ∀ b ∈ X, ∀ d ∈ X, a ≠ b → a ≠ d → b ≠ d →
      G.Adj a b ∨ G.Adj a d ∨ G.Adj b d) :
    ∃ T ⊆ X, Triangle G T := by
  classical
  have mk (a b d : V) (ha : a ∈ X) (hb : b ∈ X) (hd : d ∈ X)
      (ab : G.Adj a b) (ad : G.Adj a d) (bd : G.Adj b d) : ∃ T ⊆ X, Triangle G T := by
    refine ⟨{a,b,d},(by
      intro z hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl|rfl|rfl <;> assumption),by simp [ab.ne,ad.ne,bd.ne],?_⟩
    intro i hi j hj ne
    simp only [mem_insert,mem_singleton] at hi hj
    rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl <;>
      first | assumption | exact False.elim (ne rfl) | apply SimpleGraph.Adj.symm; assumption
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0 < X.card)
  let A := (X.erase x).filter (G.Adj x)
  let B := (X.erase x).filter (fun a => ¬ G.Adj x a)
  have sum : A.card + B.card = X.card - 1 := by
    simpa [A,B,card_erase_of_mem hx] using card_filter_add_card_filter_not (s := X.erase x) (p := G.Adj x)
  by_cases big : 2 < A.card
  · obtain ⟨a,b,d,ha,hb,hd,ab,ad,bd⟩ := two_lt_card_iff.mp big
    have extA (y) (hy : y ∈ A) : y ∈ X ∧ G.Adj x y :=
      ⟨(mem_erase.mp (mem_filter.mp hy).1).2,(mem_filter.mp hy).2⟩
    rcases edges a (extA a ha).1 b (extA b hb).1 d (extA d hd).1 ab ad bd with e|e|e
    · exact mk x a b hx (extA a ha).1 (extA b hb).1 (extA a ha).2 (extA b hb).2 e
    · exact mk x a d hx (extA a ha).1 (extA d hd).1 (extA a ha).2 (extA d hd).2 e
    · exact mk x b d hx (extA b hb).1 (extA d hd).1 (extA b hb).2 (extA d hd).2 e
  · obtain ⟨a,b,d,ha,hb,hd,ab,ad,bd⟩ := two_lt_card_iff.mp (by omega : 2 < B.card)
    have info (y) (hy : y ∈ B) : y ≠ x ∧ y ∈ X ∧ ¬ G.Adj x y :=
      ⟨(mem_erase.mp (mem_filter.mp hy).1).1,(mem_erase.mp (mem_filter.mp hy).1).2,(mem_filter.mp hy).2⟩
    have link (y z) (hy : y ∈ B) (hz : z ∈ B) (ne : y ≠ z) : G.Adj y z :=
      ((edges x hx y (info y hy).2.1 z (info z hz).2.1 (info y hy).1.symm (info z hz).1.symm ne
        ).resolve_left (info y hy).2.2).resolve_left (info z hz).2.2
    exact mk a b d (info a ha).2.1 (info b hb).2.1 (info d hd).2.1
      (link a b ha hb ab) (link a d ha hd ad) (link b d hb hd bd)
-- An external point cannot meet two vertices of a triangle, since the two
-- triangles would share their common edge.
omit [Fintype V] in
private lemma oneTouch {G : SimpleGraph V} (nd : ND G) {T : Finset V}
    (tri : Triangle G T) {v : V} (outsideT : v ∉ T) :
    (T.filter (G.Adj v)).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro a ha b hb
  obtain ⟨aT,va⟩ := mem_filter.mp ha
  obtain ⟨bT,vb⟩ := mem_filter.mp hb
  by_contra ne
  have rem : ((T.erase a).erase b).card = 1 := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm ne,bT⟩),card_erase_of_mem aT,tri.1]
  obtain ⟨z,hz⟩ := card_pos.mp (by omega : 0 < ((T.erase a).erase b).card)
  obtain ⟨zb,zrest⟩ := mem_erase.mp hz
  obtain ⟨za,zT⟩ := mem_erase.mp zrest
  have eq := nd a b v z (tri.2 a aT b bT ne) va.symm vb.symm
    (tri.2 a aT z zT za.symm) (tri.2 b bT z zT zb.symm)
  exact outsideT (eq ▸ zT)

omit [Fintype V] [DecidableEq V] in
private lemma fourClique {G : SimpleGraph V} (nd : ND G) (U : Finset V)
    (cl : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → G.Adj a b) : U.card ≤ 3 := by
  by_contra! h
  obtain ⟨a,b,x,y,ha,hb,hx,hy,ab,ax,ay,bx,byy,xy⟩ := three_lt_card_iff.mp h
  exact xy (nd a b x y (cl a ha b hb ab) (cl a ha x hx ax) (cl b hb x hx bx)
    (cl a ha y hy ay) (cl b hb y hy byy))

-- Removing a triangle from the nonneighbors leaves a clique. Two nonadjacent
-- remaining points would have a common nonneighbor in the triangle.
private lemma splitOutside {c : Sym2 V → Fin 3} (h : ¬ Witness c) (k : Fin 3) (v : V)
    (big : 6 ≤ (outside (graph c k) v).card) :
    ∃ A B : Finset V, Triangle (graph c k) A ∧ Triangle (graph c k) B ∧
      A ⊆ outside (graph c k) v ∧ B ⊆ outside (graph c k) v ∧ A ≠ B ∧
      (outside (graph c k) v).card = 6 := by
  classical
  let G := graph c k
  let X := outside G v
  have edges (a) (ha : a ∈ X) (b) (hb : b ∈ X) (d) (hd : d ∈ X) :=
    triOrEdge h k v ha hb hd
  obtain ⟨A,sub,tri⟩ := ramseySix G X big edges
  let B := X \ A
  have bc (x) (hx : x ∈ B) (y) (hy : y ∈ B) (ne : x ≠ y) : G.Adj x y := by
    obtain ⟨xx,xa⟩ := mem_sdiff.mp hx
    obtain ⟨yx,ya⟩ := mem_sdiff.mp hy
    let covered := (A.filter (G.Adj x)) ∪ (A.filter (G.Adj y))
    have ux := oneTouch (diamond h k) tri xa
    have uy := oneTouch (diamond h k) tri ya
    change (A.filter (G.Adj x)).card ≤ 1 at ux
    change (A.filter (G.Adj y)).card ≤ 1 at uy
    have le := card_union_le (A.filter (G.Adj x)) (A.filter (G.Adj y))
    have small : covered.card < A.card := by dsimp [covered]; rw [tri.1]; omega
    obtain ⟨z,za,zout⟩ := exists_mem_notMem_of_card_lt_card small
    have zx : ¬ G.Adj x z := fun hz => zout (mem_union_left _ (mem_filter.mpr ⟨za,hz⟩))
    have zy : ¬ G.Adj y z := fun hz => zout (mem_union_right _ (mem_filter.mpr ⟨za,hz⟩))
    rcases edges x xx y yx z (sub za) ne (fun e => xa (e ▸ za)) (fun e => ya (e ▸ za)) with xy|xz|yz
    · exact xy
    · exact (zx xz).elim
    · exact (zy yz).elim
  have bound := fourClique (diamond h k) B bc
  have cb : B.card = X.card - A.card := card_sdiff_of_subset sub
  have szA := tri.1
  change 6 ≤ X.card at big
  have szB : B.card = 3 := by omega
  refine ⟨A,B,tri,⟨szB,bc⟩,sub,sdiff_subset,?_,(by change X.card = 6; omega)⟩
  obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0 < A.card)
  intro e
  have hb : a ∈ B := e ▸ ha
  exact (mem_sdiff.mp hb).2 ha

private noncomputable def nbr (G : SimpleGraph V) (v : V) : Finset V := univ.filter (G.Adj v)

private lemma cubic {c : Sym2 V → Fin 3} (h : ¬ Witness c) (size : Fintype.card V = 10) (v : V) :
    ∀ k, (nbr (graph c k) v).card = 3 ∧ (outside (graph c k) v).card = 6 := by
  classical
  let S := (univ : Finset V).erase v
  have nine : S.card = 9 := by simp [S,size]
  let N (k : Fin 3) := nbr (graph c k) v
  have eqN (k : Fin 3) : N k = S.filter (fun w => c s(v,w) = k) := by
    ext w
    simp only [N,nbr,S,mem_filter,mem_univ,mem_erase,true_and,and_true]
    change (v ≠ w ∧ _) ↔ (w ≠ v ∧ _)
    rw [ne_comm]
  have totals (k : Fin 3) : (N k).card + (outside (graph c k) v).card = 9 := by
    have eqO : outside (graph c k) v = S.filter (fun w => ¬ c s(v,w) = k) := by
      ext w
      simp only [outside,S,mem_filter,mem_univ,mem_erase,true_and,and_true]
      change (w ≠ v ∧ ¬ (v ≠ w ∧ _)) ↔ (w ≠ v ∧ _)
      by_cases e : v = w <;> simp [Ne.symm, *]
    rw [eqN,eqO,card_filter_add_card_filter_not,nine]
  have lower (k) : 3 ≤ (N k).card := by
    by_contra! sm
    have t := totals k
    obtain ⟨_,_,_,_,_,_,_,six⟩ := splitOutside h k v (by omega)
    omega
  have sum : ∑ k, (N k).card = 9 := by
    simp_rw [eqN]
    simpa [nine] using sum_card_fiberwise_eq_card_filter S univ (fun w => c s(v,w))
  simp [Fin.sum_univ_succ] at sum
  have l0 := lower 0
  have l1 := lower 1
  have l2 := lower 2
  intro k
  have t := totals k
  change (N k).card = 3 ∧ _
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl|rfl|rfl <;> omega
-- In a cubic graph, distinct triangles cannot share a single vertex either.
private lemma separated {G : SimpleGraph V} (nd : ND G) (deg : ∀ v, (nbr G v).card = 3)
    {T U : Finset V} (t : Triangle G T) (u : Triangle G U) (ne : T ≠ U) : Disjoint T U := by
  classical
  apply disjoint_left.mpr
  intro x xt xu
  have ns : ¬ U ⊆ T := fun hu => ne ((eq_iff_card_le_of_subset hu).mp (by rw [t.1,u.1])).symm
  obtain ⟨y,yu,yt⟩ := not_subset.mp ns
  have inter : T ∩ U ⊆ T.filter (G.Adj y) := by
    intro z hz
    obtain ⟨zt,zu⟩ := mem_inter.mp hz
    exact mem_filter.mpr ⟨zt,u.2 y yu z zu (fun e => yt (e ▸ zt))⟩
  have small := (card_le_card inter).trans (oneTouch nd t yt)
  have union : T ∪ U ⊆ insert x (nbr G x) := by
    intro z hz
    by_cases eq : x = z
    · simp [eq]
    · apply mem_insert_of_mem
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      rcases mem_union.mp hz with zt | zu
      · exact t.2 x xt z zt eq
      · exact u.2 x xu z zu eq
  have cap := (card_le_card union).trans (card_insert_le x (nbr G x))
  rw [deg] at cap
  have count := card_union_add_card_inter T U
  rw [t.1,u.1] at count
  omega

private theorem existsWitness (c : Sym2 V → Fin 3) (size : Fintype.card V = 10) : Witness c := by
  classical
  by_contra h
  let G := graph c 0
  let Ts := (univ : Finset (Finset V)).filter (Triangle G)
  have memT (T : Finset V) : T ∈ Ts ↔ Triangle G T := by simp [Ts]
  have deg (v) : (nbr G v).card = 3 := (cubic h size v 0).1
  have pairwise : (Ts : Set (Finset V)).PairwiseDisjoint id := by
    intro A ha B hb ne
    exact separated (diamond h 0) deg ((memT A).mp ha) ((memT B).mp hb) ne
  have lim : Ts.card*3 ≤ 10 := calc
    _ = ∑ T ∈ Ts, T.card := (sum_const_nat (fun T hT => ((memT T).mp hT).1)).symm
    _ = (Ts.biUnion id).card := (card_biUnion pairwise).symm
    _ ≤ Fintype.card V := card_le_univ _
    _ = _ := size
  let can (v : V) := Ts.filter (fun T => T ⊆ outside G v)
  have lower (v : V) : 2 ≤ (can v).card := by
    obtain ⟨A,B,ta,tb,asub,bsub,ne,_⟩ :=
      splitOutside h 0 v ((cubic h size v 0).2.ge)
    exact one_lt_card.mpr ⟨A,mem_filter.mpr ⟨(memT A).mpr ta,asub⟩,
      B,mem_filter.mpr ⟨(memT B).mpr tb,bsub⟩,ne⟩
  let avoid (T : Finset V) := (univ : Finset V).filter (fun v => T ⊆ outside G v)
  have upper (T) (ht : T ∈ Ts) : (avoid T).card ≤ 6 := by
    have t := (memT _).mp ht
    obtain ⟨a,ha⟩ := card_pos.mp (by rw [t.1]; decide : 0 < T.card)
    have lt : (T.erase a).card < (nbr G a).card := by rw [card_erase_of_mem ha,t.1,deg]; decide
    obtain ⟨w,hw,wn⟩ := exists_mem_notMem_of_card_lt_card lt
    have edge : G.Adj a w := (mem_filter.mp hw).2
    have wt : w ∉ T := fun wT => wn (mem_erase.mpr ⟨edge.ne.symm,wT⟩)
    have sub : avoid T ⊆ univ \ insert w T := by
      intro v hv
      have inside : T ⊆ outside G v := (mem_filter.mp hv).2
      apply mem_sdiff.mpr
      refine ⟨mem_univ _,?_⟩
      intro bad
      rcases mem_insert.mp bad with rfl | vt
      · exact (mem_filter.mp (inside ha)).2.2 edge.symm
      · exact (mem_filter.mp (inside vt)).2.1 rfl
    have bound := card_le_card sub
    simpa [card_sdiff_of_subset (subset_univ _),size,card_insert_of_notMem wt,t.1] using bound
  have double : ∑ v, (can v).card = ∑ T ∈ Ts, (avoid T).card := by
    calc
      _ = ∑ v : V, ∑ T ∈ Ts, (if T ⊆ outside G v then 1 else 0 : ℕ) := by simp [can]
      _ = ∑ T ∈ Ts, ∑ v : V, (if T ⊆ outside G v then 1 else 0 : ℕ) := sum_comm
      _ = _ := by simp [avoid]
  have low : 20 ≤ ∑ v, (can v).card := calc
    20 = ∑ _v : V, 2 := by simp [size]
    _ ≤ _ := sum_le_sum fun v _ => lower v
  have high : ∑ T ∈ Ts, (avoid T).card ≤ Ts.card*6 := calc
    _ ≤ ∑ _T ∈ Ts, 6 := sum_le_sum upper
    _ = _ := by simp
  omega
end OMA.TenVertices

theorem OMA.solution : type_of% @Erdos617.erdos_617.variants.r_eq_3 := by
  intro _ _ V _ _ size coloring
  exact OMA.TenVertices.existsWitness coloring (by simpa using size)
