import FormalConjectures.ErdosProblems.«210»

/-! # The sharp ordinary-line guarantee at seven points -/
-- Credit: @steveDOTdigital
namespace OMA.SevenOrdinary
open EuclideanGeometry Erdos210
open scoped Classical

-- The vertices, centroid and three side midpoints of a triangle.
private def x : Fin 7 → ℤ := ![0,6,0,2,3,0,3]
private def y : Fin 7 → ℤ := ![0,0,6,2,0,3,3]
private noncomputable def point (i : Fin 7) : ℝ² := !₂[(x i : ℝ)/6,(y i : ℝ)/6]
private def coeff : Fin 10 → ℤ := ![-12,-6,-3,2,3,4,9,12,18,-2]

private lemma injectivePoint : Function.Injective point := by
  intro i j eq
  have hx : x i = x j := by
    have h := congrArg (fun p : ℝ² => p 0) eq
    change (x i : ℝ)/6 = (x j : ℝ)/6 at h
    exact_mod_cast (show (x i : ℝ) = (x j : ℝ) by linarith)
  have hy : y i = y j := by
    have h := congrArg (fun p : ℝ² => p 1) eq
    change (y i : ℝ)/6 = (y j : ℝ)/6 at h
    exact_mod_cast (show (y i : ℝ) = (y j : ℝ) by linarith)
  exact (by decide : ∀ i j : Fin 7, x i = x j → y i = y j → i = j) i j hx hy

private lemma third (i j : Fin 7) (hne : i ≠ j) (h : i < 4 ∨ j < 4) :
    ∃ k, k ≠ i ∧ k ≠ j ∧ point k ∈ line[ℝ, point i, point j] := by
  have table : ∀ i j : Fin 7, i ≠ j → (i < 4 ∨ j < 4) →
      ∃ k : Fin 7, k ≠ i ∧ k ≠ j ∧ ∃ t : Fin 10,
        6*x i + coeff t * (x j - x i) = 6*x k ∧ 6*y i + coeff t * (y j - y i) = 6*y k := by decide
  obtain ⟨k,hki,hkj,t,hx,hy⟩ := table i j hne h
  refine ⟨k,hki,hkj,mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨(coeff t : ℝ)/6,?_⟩⟩
  ext a
  fin_cases a
  · change (coeff t : ℝ)/6 * ((x j : ℝ)/6 - (x i : ℝ)/6) + (x i : ℝ)/6 = (x k : ℝ)/6
    have h : 6*(x i : ℝ) + (coeff t : ℝ)*((x j : ℝ)-(x i : ℝ)) = 6*(x k : ℝ) := by exact_mod_cast hx
    linarith
  · change (coeff t : ℝ)/6 * ((y j : ℝ)/6 - (y i : ℝ)/6) + (y i : ℝ)/6 = (y k : ℝ)/6
    have h : 6*(y i : ℝ) + (coeff t : ℝ)*((y j : ℝ)-(y i : ℝ)) = 6*(y k : ℝ) := by exact_mod_cast hy
    linarith

private theorem example_upper : f 7 ≤ 3 := by
  classical
  let S := Finset.univ.image point
  let L (i j : Fin 7) := line[ℝ,point i,point j]
  have mem (i : Fin 7) : point i ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have size : S.card = 7 := by simp [S, Finset.card_image_of_injective _ injectivePoint]
  have nc : ¬ Collinear ℝ (S : Set ℝ²) := by
    intro hc
    apply triangle_not_collinear
    refine hc.subset ?_
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · simpa [point,x,y] using mem 0
    · simpa [point,x,y] using mem 1
    · simpa [point,x,y] using mem 2
  have cover : ordinaryLines S ⊆ {L 4 5,L 4 6,L 5 6} := by
    intro l hl
    obtain ⟨⟨a,ha,b,hb,hab,rfl⟩,card⟩ := mem_ordinaryLines.mp hl
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    have ne : i ≠ j := fun e => hab (congrArg _ e)
    by_cases small : i < 4 ∨ j < 4
    · obtain ⟨k,hi,hj,hline⟩ := third i j ne small
      let T : Finset ℝ² := {point i,point j,point k}
      have bound : T ⊆ S.filter (fun p => p ∈ L i j) := by
        intro p hp
        simp only [T,Finset.mem_insert,Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl
        · exact Finset.mem_filter.mpr ⟨mem _, left_mem_affineSpan_pair ..⟩
        · exact Finset.mem_filter.mpr ⟨mem _, right_mem_affineSpan_pair ..⟩
        · exact Finset.mem_filter.mpr ⟨mem _,hline⟩
      have three : T.card = 3 := by
        simp [T,hab,injectivePoint.ne hi.symm,injectivePoint.ne hj.symm]
      have := Finset.card_le_card bound
      change T.card ≤ (S.filter fun p => p ∈ line[ℝ,point i,point j]).card at this
      omega
    · have I : i = 4 ∨ i = 5 ∨ i = 6 := by omega
      have J : j = 4 ∨ j = 5 ∨ j = 6 := by omega
      rcases I with rfl | rfl | rfl <;> rcases J with rfl | rfl | rfl <;>
        simp_all [L,AffineSubspace.affineSpan_pair_comm]
  exact (f_le size nc).trans ((Finset.card_le_card cover).trans Finset.card_le_three)

private noncomputable abbrev lineOf (p : ℝ² × ℝ²) := line[ℝ,p.1,p.2]
private noncomputable def cuts (s : Finset ℝ²) := s.offDiag.image lineOf
private noncomputable def onLine (s : Finset ℝ²) (L : AffineSubspace ℝ ℝ²) := s.filter (fun p => p ∈ L)

-- Five collinear points leave two outside. From one outside point, at most
-- one of its five lines through the collinear points also meets the other.
private lemma fiveOnLine {s : Finset ℝ²} (hs : s.card = 7)
    {u v : ℝ²} (hfive : (onLine s (line[ℝ,u,v])).card = 5) :
    3 ≤ (ordinaryLines s).card := by
  classical
  let L := line[ℝ,u,v]
  let A := onLine s L
  have sub : A ⊆ s := Finset.filter_subset ..
  have five : A.card = 5 := hfive
  have two : (s \ A).card = 2 := by rw [Finset.card_sdiff_of_subset sub,hs,five]
  obtain ⟨p,q,hpq,hrest⟩ := Finset.card_eq_two.mp two
  have pO : p ∈ s \ A := by rw [hrest]; simp
  have qO : q ∈ s \ A := by rw [hrest]; simp
  obtain ⟨ps,pA⟩ := Finset.mem_sdiff.mp pO
  have pL : p ∉ L := fun h => pA (Finset.mem_filter.mpr ⟨ps,h⟩)
  let cross (a : ℝ²) := line[ℝ,p,a]
  have onlyOn (a z : ℝ²) (ha : a ∈ A) (hz : z ∈ A) (hz' : z ∈ cross a) : z = a := by
    by_contra ne
    have h₁ := affineSpan_pair_eq_of_mem_of_mem_of_ne
      (Finset.mem_filter.mp hz).2 (Finset.mem_filter.mp ha).2 ne
    have h₂ := affineSpan_pair_eq_of_mem_of_mem_of_ne hz' (right_mem_affineSpan_pair ℝ p a) ne
    apply pL
    change p ∈ line[ℝ,u,v]
    rw [← (h₂.symm.trans h₁)]
    exact left_mem_affineSpan_pair ℝ p a
  have inj : (A : Set ℝ²).InjOn cross := by
    intro a ha b hb eq
    exact onlyOn b a hb ha (eq ▸ right_mem_affineSpan_pair ℝ p a)
  let good := (A.image cross).erase (line[ℝ,p,q])
  have four : 4 ≤ good.card := by
    have nimg : (A.image cross).card = 5 := (Finset.card_image_of_injOn inj).trans five
    by_cases h : line[ℝ,p,q] ∈ A.image cross
    · simp [good,Finset.card_erase_of_mem h,nimg]
    · simp [good,Finset.erase_eq_of_notMem h,nimg]
  have incl : good ⊆ ordinaryLines s := by
    intro l hl
    obtain ⟨notpq,hin⟩ := Finset.mem_erase.mp hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hin
    have pa : p ≠ a := fun e => pA (e ▸ ha)
    have qnot : q ∉ cross a := by
      intro h
      exact notpq (affineSpan_pair_eq_of_mem_of_mem_of_ne
        (left_mem_affineSpan_pair ℝ p a) h hpq).symm
    apply mem_ordinaryLines.mpr
    refine ⟨⟨p,ps,a,sub ha,pa,rfl⟩,?_⟩
    have eq : (s.filter fun z => z ∈ cross a) = {p,a} := by
      ext z
      constructor
      · intro hz
        obtain ⟨zs,zl⟩ := Finset.mem_filter.mp hz
        by_cases za : z ∈ A
        · simp [onlyOn a z ha za zl]
        · have zo := Finset.mem_sdiff.mpr ⟨zs,za⟩
          rw [hrest,Finset.mem_insert,Finset.mem_singleton] at zo
          rcases zo with rfl | rfl
          · simp
          · exact (qnot zl).elim
      · intro zm
        rcases Finset.mem_insert.mp zm with rfl | zm
        · exact Finset.mem_filter.mpr ⟨ps,left_mem_affineSpan_pair ..⟩
        · rw [Finset.mem_singleton.mp zm]
          exact Finset.mem_filter.mpr ⟨sub ha,right_mem_affineSpan_pair ..⟩
    rw [eq]
    simp [pa]
  exact (by omega : 3 ≤ 4).trans (four.trans (Finset.card_le_card incl))

private lemma noFive {s : Finset ℝ²} (hs : s.card = 7)
    (hc : ¬ Collinear ℝ (s : Set ℝ²))
    (no : ∀ L ∈ cuts s, (onLine s L).card ≠ 5) : 3 ≤ (ordinaryLines s).card := by
  classical
  let w (L : AffineSubspace ℝ ℝ²) := (onLine s L).card
  have fiber (L) (hL : L ∈ cuts s) :
      (s.offDiag.filter (fun p => lineOf p = L)) = (onLine s L).offDiag := by
    obtain ⟨⟨a,b⟩,_,rfl⟩ := Finset.mem_image.mp hL
    ext ⟨y,z⟩
    simp only [Finset.mem_filter,Finset.mem_offDiag,onLine,lineOf]
    constructor
    · rintro ⟨⟨hy,hz,ne⟩,eq⟩
      exact ⟨⟨hy,eq ▸ left_mem_affineSpan_pair ℝ _ _⟩,
        ⟨hz,eq ▸ right_mem_affineSpan_pair ℝ _ _⟩,ne⟩
    · rintro ⟨⟨hy,hyl⟩,⟨hz,hzl⟩,ne⟩
      exact ⟨⟨hy,hz,ne⟩,affineSpan_pair_eq_of_mem_of_mem_of_ne hyl hzl ne⟩
  have total : 42 = ∑ L ∈ cuts s, w L * (w L - 1) := by
    have count := Finset.card_eq_sum_card_image lineOf s.offDiag
    change s.offDiag.card = ∑ L ∈ cuts s, _ at count
    calc
      42 = s.offDiag.card := by simp [Finset.offDiag_card,hs]
      _ = _ := count
      _ = _ := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [fiber l hl, Finset.offDiag_card]
        simp [w,Nat.mul_sub_left_distrib]
  have ordinary : (cuts s).filter (fun L => w L = 2) = ordinaryLines s := by
    ext L
    simp only [Finset.mem_filter,mem_ordinaryLines,cuts,Finset.mem_image,Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨⟨a,b⟩,⟨ha,hb,ne⟩,eq⟩,two⟩
      exact ⟨⟨a,ha,b,hb,ne,eq⟩,two⟩
    · rintro ⟨⟨a,ha,b,hb,ne,eq⟩,two⟩
      exact ⟨⟨(a,b),⟨ha,hb,ne⟩,eq⟩,two⟩
  have part := Finset.sum_filter_add_sum_filter_not (s := cuts s)
    (p := fun L => w L = 2) (f := fun L => w L * (w L - 1))
  have evenPart : ∑ L ∈ (cuts s).filter (fun L => w L = 2), w L * (w L - 1) =
      (ordinaryLines s).card * 2 := by
    rw [← ordinary]
    apply Finset.sum_const_nat
    intro l hl
    rw [(Finset.mem_filter.mp hl).2]
  have div : 3 ∣ ∑ L ∈ (cuts s).filter (fun L => ¬ w L = 2), w L * (w L - 1) := by
    apply Finset.dvd_sum
    intro l hl
    obtain ⟨hd,h₂⟩ := Finset.mem_filter.mp hl
    have h₅ : w l ≠ 5 := no l hd
    have hi : w l ≤ 7 := (Finset.card_filter_le ..).trans_eq hs
    generalize w l = k at *
    interval_cases k <;> first | contradiction | decide
  rw [evenPart,← total] at part
  have pos := (ordinaryLines_nonempty hc).card_pos
  omega

private lemma lower_bound : 3 ≤ f 7 := by
  apply (le_f_iff (by decide)).mpr
  intro s hs hc
  by_cases h : ∃ L ∈ cuts s, (onLine s L).card = 5
  · obtain ⟨L,hl,hf⟩ := h
    obtain ⟨⟨u,v⟩,_,rfl⟩ := Finset.mem_image.mp hl
    exact fiveOnLine hs hf
  · exact noFive hs hc (fun L hl hf => h ⟨L,hl,hf⟩)

end OMA.SevenOrdinary

open OMA.SevenOrdinary in
theorem OMA.solution : type_of% @Erdos210.erdos_210.variants.seven :=
  le_antisymm example_upper lower_bound
