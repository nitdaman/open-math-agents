import FormalConjectures.Wikipedia.PierceBirkhoff

-- Problem: Pierce–Birkhoff conjecture — pierce birkhoff conjecture dim one
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/PierceBirkhoff.lean:101 (declaration PierceBirkhoff.pierce_birkhoff_conjecture_dim_one)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial

namespace OMAPB

/-- `f` is a finite sup of finite infs of polynomials (nonempty finite index types). -/
def SI (f : ℝ → ℝ) : Prop :=
  ∃ (ι κ : Type) (_ : Fintype ι) (_ : Nonempty ι) (_ : Fintype κ) (_ : Nonempty κ)
    (g : ι → κ → ℝ[X]), ∀ x, f x = ⨆ i, ⨅ j, (g i j).eval x

lemma supinf_eq {ι κ : Type} [Finite ι] [Nonempty ι] [Finite κ] [Nonempty κ]
    (a : ι → κ → ℝ) (y : ℝ) (h1 : ∀ i, ∃ j, a i j ≤ y) (h2 : ∃ i, ∀ j, y ≤ a i j) :
    ⨆ i, ⨅ j, a i j = y := by
  apply le_antisymm
  · apply ciSup_le
    intro i
    obtain ⟨j, hj⟩ := h1 i
    exact (ciInf_le (Set.finite_range _).bddBelow j).trans hj
  · obtain ⟨i, hi⟩ := h2
    exact (le_ciInf hi).trans (le_ciSup (Set.finite_range (fun i => ⨅ j, a i j)).bddAbove i)

lemma SI_poly (p : ℝ[X]) : SI (fun x => p.eval x) := by
  refine ⟨Unit, Unit, inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ _ => p, fun x => ?_⟩
  rw [supinf_eq (fun _ _ => p.eval x) (p.eval x) (fun _ => ⟨(), le_rfl⟩) ⟨(), fun _ => le_rfl⟩]

lemma SI_add {f g : ℝ → ℝ} (hf : SI f) (hg : SI g) : SI (fun x => f x + g x) := by
  obtain ⟨ι₁, κ₁, _, _, _, _, a, ha⟩ := hf
  obtain ⟨ι₂, κ₂, _, _, _, _, b, hb⟩ := hg
  refine ⟨ι₁ × ι₂, κ₁ × κ₂, inferInstance, inferInstance, inferInstance, inferInstance,
    fun p q => a p.1 q.1 + b p.2 q.2, fun x => ?_⟩
  show f x + g x = _
  rw [ha x, hb x]
  symm
  apply supinf_eq
  · rintro ⟨i, k⟩
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := fun j => (a i j).eval x)
    obtain ⟨l, hl⟩ := exists_eq_ciInf_of_finite (f := fun l => (b k l).eval x)
    refine ⟨(j, l), ?_⟩
    simp only [eval_add]
    apply add_le_add
    · rw [hj]; exact le_ciSup (Set.finite_range (fun i => ⨅ j, (a i j).eval x)).bddAbove i
    · rw [hl]; exact le_ciSup (Set.finite_range (fun i => ⨅ j, (b i j).eval x)).bddAbove k
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => ⨅ j, (a i j).eval x)
    obtain ⟨k, hk⟩ := exists_eq_ciSup_of_finite (f := fun k => ⨅ l, (b k l).eval x)
    refine ⟨(i, k), ?_⟩
    rintro ⟨j, l⟩
    simp only [eval_add]
    rw [← hi, ← hk]
    exact add_le_add (ciInf_le (Set.finite_range _).bddBelow j)
      (ciInf_le (Set.finite_range _).bddBelow l)

lemma SI_phi (a : ℝ) (q : ℝ[X]) :
    SI (fun z => if z ≤ a then 0 else (z - a) * q.eval z) := by
  set A : ℝ[X] := q + 1 + q * q
  set B : ℝ[X] := 1 + q * q
  set u : ℝ[X] := (X - C a) * A
  set v : ℝ[X] := -((X - C a) * B)
  let g : Bool → Bool → ℝ[X] := fun i j =>
    match i, j with
    | false, false => 0
    | false, true => v
    | true, false => u
    | true, true => u + v
  refine ⟨Bool, Bool, inferInstance, inferInstance, inferInstance, inferInstance, g,
    fun z => ?_⟩
  have hA : 0 < A.eval z := by
    simp only [A, eval_add, eval_mul, eval_one]
    nlinarith [sq_nonneg (q.eval z + 1 / 2)]
  have hB : 0 < B.eval z := by
    simp only [B, eval_add, eval_mul, eval_one]
    nlinarith [sq_nonneg (q.eval z)]
  have hu : u.eval z = (z - a) * A.eval z := by simp [u]
  have hv : v.eval z = -((z - a) * B.eval z) := by simp [v]
  have hAB : A.eval z - B.eval z = q.eval z := by simp [A, B]
  show (if z ≤ a then 0 else (z - a) * eval z q) = _
  split_ifs with hz
  · have h1 : u.eval z ≤ 0 := by rw [hu]; nlinarith
    have h2 : 0 ≤ v.eval z := by rw [hv]; nlinarith
    refine (supinf_eq _ _ ?_ ?_).symm
    · intro i
      cases i
      · exact ⟨false, by simp [g]⟩
      · exact ⟨false, by simpa [g] using h1⟩
    · exact ⟨false, fun j => by cases j <;> simp [g, h2]⟩
  · push Not at hz
    have h1 : 0 ≤ u.eval z := by rw [hu]; nlinarith
    have h2 : v.eval z ≤ 0 := by rw [hv]; nlinarith
    have h3 : u.eval z + v.eval z = (z - a) * q.eval z := by
      rw [hu, hv, ← hAB]; ring
    refine (supinf_eq _ _ ?_ ?_).symm
    · intro i
      cases i
      · exact ⟨true, by simp only [g]; linarith⟩
      · exact ⟨true, by simp only [g, eval_add]; linarith⟩
    · refine ⟨true, fun j => ?_⟩
      cases j
      · simp only [g]; linarith
      · simp only [g, eval_add]; linarith

/-- On every closed interval whose interior avoids `S`, `f` is a polynomial. -/
def Hyp (S : Finset ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y, x ≤ y → (∀ s ∈ S, s ∉ Set.Ioo x y) → ∃ g : ℝ[X], ∀ z ∈ Set.Icc x y, f z = g.eval z

lemma poly_eq {g h : ℝ[X]} {x y : ℝ} (hxy : x < y)
    (H : ∀ z ∈ Set.Icc x y, g.eval z = h.eval z) : g = h :=
  Polynomial.eq_of_infinite_eval_eq g h ((Set.Icc_infinite hxy).mono fun z hz => H z hz)

lemma main (S : Finset ℝ) : ∀ f : ℝ → ℝ, Hyp S f → SI f := by
  classical
  induction S using Finset.induction_on_max with
  | empty =>
    intro f hf
    obtain ⟨g0, hg0⟩ := hf (-1) 1 (by norm_num) (by simp)
    have : f = fun z => g0.eval z := by
      funext z
      obtain ⟨g', hg'⟩ := hf (min (-1) z) (max 1 z) (by
        have := min_le_left (-1 : ℝ) z; have := le_max_left (1 : ℝ) z; linarith) (by simp)
      have hgg : g' = g0 := poly_eq (x := -1) (y := 1) (by norm_num) (fun w hw => by
        rw [← hg' w ⟨(min_le_left _ _).trans hw.1, hw.2.trans (le_max_left _ _)⟩, hg0 w hw])
      rw [hg' z ⟨min_le_right _ _, le_max_right _ _⟩, hgg]
    rw [this]; exact SI_poly g0
  | insert a S' hlt ih =>
    intro f hf
    -- right ray
    have avoidR : ∀ y, ∀ s ∈ insert a S', s ∉ Set.Ioo a y := by
      intro y s hs hmem
      rcases Finset.mem_insert.mp hs with rfl | hs'
      · exact lt_irrefl _ hmem.1
      · exact lt_asymm (hlt s hs') hmem.1
    obtain ⟨gR0, hgR0⟩ := hf a (a + 1) (by linarith) (avoidR _)
    have hgR : ∀ z, a ≤ z → f z = gR0.eval z := by
      intro z hz
      obtain ⟨g', hg'⟩ := hf a (max (a + 1) z) (by have := le_max_left (a + 1) z; linarith)
        (avoidR _)
      have hgg : g' = gR0 := poly_eq (x := a) (y := a + 1) (by linarith) (fun w hw => by
        rw [← hg' w ⟨hw.1, hw.2.trans (le_max_left _ _)⟩, hgR0 w hw])
      rw [hg' z ⟨hz, le_max_right _ _⟩, hgg]
    -- left piece
    set c := (insert (a - 1) S').max' (Finset.insert_nonempty _ _) with hcdef
    have hca : c < a := by
      rw [hcdef, Finset.max'_lt_iff]
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · linarith
      · exact hlt y hy'
    have hsc : ∀ s ∈ S', s ≤ c := fun s hs => Finset.le_max' _ _ (Finset.mem_insert_of_mem hs)
    have avoidL : ∀ x, c ≤ x → ∀ s ∈ insert a S', s ∉ Set.Ioo x a := by
      intro x hx s hs hmem
      rcases Finset.mem_insert.mp hs with rfl | hs'
      · exact lt_irrefl _ hmem.2
      · have := hsc s hs'; linarith [hmem.1]
    obtain ⟨gL, hgL⟩ := hf c a hca.le (avoidL c le_rfl)
    let f' : ℝ → ℝ := fun z => if z ≤ a then f z else gL.eval z
    have hf' : Hyp S' f' := by
      intro x y hxy hS
      by_cases hya : y ≤ a
      · obtain ⟨g, hg⟩ := hf x y hxy (by
          intro s hs hmem
          rcases Finset.mem_insert.mp hs with rfl | hs'
          · linarith [hmem.2]
          · exact hS s hs' hmem)
        refine ⟨g, fun z hz => ?_⟩
        simp only [f', if_pos (hz.2.trans hya)]
        exact hg z hz
      · push Not at hya
        have hsx : ∀ s ∈ S', s ≤ x := by
          intro s hs
          by_contra h
          push Not at h
          exact hS s hs ⟨h, (hlt s hs).trans hya⟩
        refine ⟨gL, fun z hz => ?_⟩
        simp only [f']
        split_ifs with hza
        · by_cases hxa : x < a
          · obtain ⟨g', hg'⟩ := hf x a hxa.le (by
              intro s hs hmem
              rcases Finset.mem_insert.mp hs with rfl | hs'
              · exact lt_irrefl _ hmem.2
              · have := hsx s hs'; linarith [hmem.1])
            have hgg : g' = gL := poly_eq (x := max x c) (y := a) (max_lt hxa hca)
              (fun w hw => by
                rw [← hg' w ⟨(le_max_left _ _).trans hw.1, hw.2⟩,
                  hgL w ⟨(le_max_right _ _).trans hw.1, hw.2⟩])
            rw [hg' z ⟨hz.1, hza⟩, hgg]
          · push Not at hxa
            have hz' : z = a := le_antisymm hza (hxa.trans hz.1)
            rw [hz']
            exact hgL a ⟨hca.le, le_rfl⟩
        · rfl
    have hroot : IsRoot (gR0 - gL) a := by
      simp only [IsRoot, eval_sub]
      rw [← hgR a le_rfl, ← hgL a ⟨hca.le, le_rfl⟩, sub_self]
    set q := (gR0 - gL) /ₘ (X - C a)
    have hq : (X - C a) * q = gR0 - gL := mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hfeq : f = fun z => f' z + (if z ≤ a then 0 else (z - a) * q.eval z) := by
      funext z
      simp only [f']
      split_ifs with hz
      · ring
      · push Not at hz
        have := congrArg (eval z) hq
        simp only [eval_mul, eval_sub, eval_X, eval_C] at this
        rw [this, hgR z hz.le]; ring
    rw [hfeq]
    exact SI_add (ih f' hf') (SI_phi a q)

end OMAPB

theorem OMA.solution : type_of% @PierceBirkhoff.pierce_birkhoff_conjecture_dim_one := by
  intro f hf
  classical
  obtain ⟨ι, P, g, hfin, hcl, hsa, hcov, heq⟩ := hf
  choose ι₀ ι₁ p₀ p₁ h0 h1 hP using hsa
  let bad : ℝ[X] → Set ℝ := fun p => {x | p ≠ 0 ∧ p.eval x = 0}
  have hbad : ∀ p, (bad p).Finite := by
    intro p
    by_cases hp : p = 0
    · simp [bad, hp]
    · exact (Polynomial.finite_setOfPred_isRoot hp).subset fun x hx => hx.2
  let Sset : Set ℝ := ⋃ i, ((⋃ k, bad (p₀ i k)) ∪ ⋃ k, bad (p₁ i k))
  have hS : Sset.Finite := by
    apply Set.finite_iUnion
    intro i
    have := h0 i
    have := h1 i
    exact (Set.finite_iUnion fun k => hbad _).union (Set.finite_iUnion fun k => hbad _)
  have memS : ∀ i x, (∃ k, p₀ i k ≠ 0 ∧ (p₀ i k).eval x = 0) ∨
      (∃ k, p₁ i k ≠ 0 ∧ (p₁ i k).eval x = 0) → x ∈ hS.toFinset := by
    intro i x hx
    rw [Set.Finite.mem_toFinset]
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rcases hx with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨k, hk⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨k, hk⟩)
  have hyp : OMAPB.Hyp hS.toFinset f := by
    intro x y hxy hSx
    have hm : (x + y) / 2 ∈ ⋃ i, P i := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hm
    refine ⟨g i, fun z hz => heq i z ?_⟩
    rcases eq_or_lt_of_le hxy with hxy' | hxy'
    · subst hxy'
      have : z = (x + x) / 2 := by have := hz.1; have := hz.2; linarith
      rw [this]; exact hi
    · have hsub : Set.Ioo x y ⊆ P i := by
        intro w hw
        have hmI : (x + y) / 2 ∈ Set.Ioo x y := ⟨by linarith, by linarith⟩
        rw [hP i] at hi ⊢
        rcases hi with hi | hi
        · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hi
          left
          refine Set.mem_iUnion.mpr ⟨k, ?_⟩
          by_cases hp : p₀ i k = 0
          · simp [hp]
          · exact absurd hmI (hSx _ (memS i _ (Or.inl ⟨k, hp, hk⟩)))
        · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hi
          right
          refine Set.mem_iUnion.mpr ⟨k, ?_⟩
          simp only [Set.mem_ofPred_eq] at hk ⊢
          by_contra hw0
          push Not at hw0
          have hp : p₁ i k ≠ 0 := by
            intro hp; rw [hp, eval_zero] at hk; exact lt_irrefl _ hk
          have hcont := (p₁ i k).continuous.continuousOn (s := Set.uIcc ((x + y) / 2) w)
          obtain ⟨r, hr, hr0⟩ : ∃ r ∈ Set.uIcc ((x + y) / 2) w, (p₁ i k).eval r = 0 := by
            rcases le_total ((x + y) / 2) w with hle | hle
            · rw [Set.uIcc_of_le hle] at hcont ⊢
              exact intermediate_value_Icc' hle hcont ⟨hw0, hk.le⟩
            · rw [Set.uIcc_of_ge hle] at hcont ⊢
              exact intermediate_value_Icc hle hcont ⟨hw0, hk.le⟩
          have hrI : r ∈ Set.Ioo x y := by
            rcases le_total ((x + y) / 2) w with hle | hle
            · rw [Set.uIcc_of_le hle] at hr
              exact ⟨by linarith [hr.1, hmI.1], by linarith [hr.2, hw.2]⟩
            · rw [Set.uIcc_of_ge hle] at hr
              exact ⟨by linarith [hr.1, hw.1], by linarith [hr.2, hmI.2]⟩
          exact hSx _ (memS i _ (Or.inr ⟨k, hp, hr0⟩)) hrI
      have : Set.Icc x y ⊆ P i := by
        rw [← closure_Ioo hxy'.ne]
        exact closure_minimal hsub (hcl i)
      exact this hz
  obtain ⟨ι', κ', _, _, _, _, G, hG⟩ := OMAPB.main hS.toFinset f hyp
  exact ⟨ι', κ', G, inferInstance, inferInstance, hG⟩
