import OMAReductions.R_Erdos1088_f_isLeast_R1

/-! # Extracting a subset with distinct distances -/
-- Credit: @steveDOTdigital

open Finset Erdos1088
open scoped EuclideanGeometry
namespace OMA.E1088Thin

-- At most one candidate is excluded for each (old vertex, old edge) pair.
private theorem avoid {I J E : Type*} [Fintype I] [Fintype J] [Fintype E]
    (f : I → J → ℝ) (g : E → ℝ) (hinj : ∀ i, Function.Injective (f i))
    (hcard : Fintype.card (I × E) < Fintype.card J) :
    ∃ j, ∀ i e, f i j ≠ g e := by
  classical
  by_contra! h
  choose a b hab using h
  let code (j : J) : I × E := (a j,b j)
  have hc : Function.Injective code := by
    intro j l he
    have ha : a j = a l := congrArg Prod.fst he
    have hb : b j = b l := congrArg Prod.snd he
    apply hinj (a j)
    rw [hab j, ha, hb, hab l]
  exact (not_le_of_gt hcard) (Fintype.card_le_of_injective code hc)

private theorem insert_lengths {d : ℕ} (A : Finset (ℝ^d)) (x : ℝ^d) (hx : x ∉ A) :
    distanceSet (insert x A) = distanceSet A ∪ A.image (dist x) := by
  classical
  ext r
  simp only [distanceSet, Finset.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨⟨p,q⟩,hpq,rfl⟩
    obtain ⟨hp,hq,hne⟩ := Finset.mem_offDiag.mp hpq
    change p ∈ insert x A at hp
    change q ∈ insert x A at hq
    change p ≠ q at hne
    rcases Finset.mem_insert.mp hp with ep | inp <;> rcases Finset.mem_insert.mp hq with eq | inq
    · exact (hne (ep.trans eq.symm)).elim
    · exact Or.inr ⟨q,inq,by change dist x q = dist p q; rw [ep]⟩
    · exact Or.inr ⟨p,inp,by change dist x p = dist p q; rw [eq, dist_comm]⟩
    · exact Or.inl ⟨(p,q), Finset.mem_offDiag.mpr ⟨inp,inq,hne⟩,rfl⟩
  · rintro (⟨⟨p,q⟩,hpq,rfl⟩ | ⟨q,hq,rfl⟩)
    · obtain ⟨hp,hq,hne⟩ := Finset.mem_offDiag.mp hpq
      exact ⟨(p,q),Finset.mem_offDiag.mpr ⟨mem_insert_of_mem hp,mem_insert_of_mem hq,hne⟩,rfl⟩
    · exact ⟨(x,q),Finset.mem_offDiag.mpr ⟨mem_insert_self _ _,mem_insert_of_mem hq,
          fun he => hx (by change x = q at he; rw [he]; exact hq)⟩,rfl⟩

theorem thin : OMA.R_Erdos1088_f_isLeast_R1.H2 := by
  classical
  intro n
  induction n with
  | zero =>
    refine ⟨0,le_rfl,?_⟩
    intro d p h
    exact ⟨∅,empty_subset _,by simp,by simp [PairwiseDistancesDistinct,distinctDistances,distanceSet]⟩
  | succ n ih =>
    obtain ⟨k,hnk,hk⟩ := ih
    let u := k*k*k+1
    refine ⟨k+u,by dsimp [u]; omega,?_⟩
    intro d p chain
    let a (i : Fin k) : Fin (k+u) := ⟨i,by omega⟩
    let b (j : Fin u) : Fin (k+u) := ⟨k+j,by omega⟩
    have ha : StrictMono a := fun _ _ hij => hij
    have hb : StrictMono b := fun i j hij => by change k+i.val < k+j.val; omega
    have hab (i : Fin k) (j : Fin u) : a i < b j := by change i.val < k+j.val; omega
    let pp : Fin k ↪ (ℝ^d) := (⟨a,ha.injective⟩ : Fin k ↪ _).trans p
    obtain ⟨A,hA,hAc,hAd⟩ := hk d pp (fun i j l hij hjl => chain _ _ _ (ha hij) (ha hjl))
    obtain ⟨j,hj⟩ := avoid
      (fun i j => dist (p (a i)) (p (b j)))
      (fun e : Fin k × Fin k => dist (pp e.1) (pp e.2))
      (fun i => (show StrictMono (fun j => dist (p (a i)) (p (b j))) from
        fun s t hst => (chain _ _ _ (hab i s) (hb hst)).1).injective)
      (by simp [u, Nat.mul_assoc])
    let x := p (b j)
    have hx : x ∉ A := by
      intro hmem
      obtain ⟨i,_,he⟩ := mem_map.mp (hA hmem)
      exact (hab i j).ne (p.injective he)
    have label (v : ℝ^d) (hv : v ∈ A) : ∃ i : Fin k, pp i = v := by
      obtain ⟨i,_,he⟩ := mem_map.mp (hA hv)
      exact ⟨i,he⟩
    have fresh : Disjoint (distanceSet A) (A.image (dist x)) := by
      apply Finset.disjoint_left.mpr
      intro r hr hs
      obtain ⟨⟨v,w⟩,hvw,rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hs
      obtain ⟨i,rfl⟩ := label _ hy
      obtain ⟨s,rfl⟩ := label _ (Finset.mem_offDiag.mp hvw).1
      obtain ⟨t,rfl⟩ := label _ (Finset.mem_offDiag.mp hvw).2.1
      exact hj i (s,t) ((dist_comm _ _).trans he)
    have unique : Set.InjOn (dist x) A := by
      intro y hy z hz he
      obtain ⟨s,rfl⟩ := label _ hy
      obtain ⟨t,rfl⟩ := label _ hz
      have flip {i l : Fin k} (hil : i < l) : dist x (pp l) < dist x (pp i) := by
        rw [dist_comm x, dist_comm x]
        exact (chain _ _ _ (ha hil) (hab l j)).2
      rcases lt_trichotomy s t with h | h | h
      · exact ((flip h).ne he.symm).elim
      · rw [h]
      · exact ((flip h).ne he).elim
    refine ⟨insert x A,?_,by simp [hx,hAc],?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_map.mpr ⟨b j,mem_univ _,rfl⟩
      · obtain ⟨i,rfl⟩ := label _ hy
        exact Finset.mem_map.mpr ⟨a i,mem_univ _,rfl⟩
    · change (distanceSet (insert x A)).card = (insert x A).card.choose 2
      rw [insert_lengths A x hx, Finset.card_union_of_disjoint fresh,
        Finset.card_image_of_injOn unique,Finset.card_insert_of_notMem hx]
      change distinctDistances A + A.card = _
      rw [show distinctDistances A = A.card.choose 2 from hAd, Nat.choose_succ_succ]
      simp [add_comm]

end OMA.E1088Thin

theorem OMA.solution : OMA.R_Erdos1088_f_isLeast_R1.H2 := OMA.E1088Thin.thin
