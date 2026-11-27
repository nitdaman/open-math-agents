import FormalConjectures.Wikipedia.PetersenColoringConjecture

/-! The five labels are the elements of Fin 5. At a Petersen vertex the
three incident labels are exactly the complement of its two-element set.
The missing pair at each vertex of a normally colored cubic graph recovers
a Petersen coloring. Credit: @Deldor14. -/
open SimpleGraph Finset PetersenColoringConjecture

namespace OMA.Petersen
private def labelPair (x y : PetersenVertex) : Fin 5 :=
  ((List.finRange 5).find? (fun i => decide (i ∉ x.val ∧ i ∉ y.val))).getD 0

private def label : Sym2 PetersenVertex → Fin 5 :=
  Sym2.lift ⟨labelPair, fun x y => by simp only [labelPair, and_comm]⟩

private def edgeAt (x : PetersenVertex) (i : Fin 5) : Sym2 PetersenVertex :=
  let s := (insert i x.val)ᶜ
  let y : PetersenVertex := if h : s.card = 2 then ⟨s,h⟩ else x
  s(x,y)

private lemma labels : ∀ x : PetersenVertex,
    (petersenGraph.incidenceFinset x).image label = x.valᶜ := by decide +kernel

private lemma decode : ∀ x : PetersenVertex,
    ∀ e ∈ petersenGraph.incidenceFinset x, edgeAt x (label e) = e := by decide +kernel

private lemma encode : ∀ x : PetersenVertex, ∀ i ∈ x.valᶜ, label (edgeAt x i) = i := by
  decide +kernel

private lemma images : ∀ x : PetersenVertex,
    x.valᶜ.image (edgeAt x) = petersenGraph.incidenceFinset x := by decide +kernel

private lemma sizes : ∀ x y : PetersenVertex, ∀ e ∈ petersenGraph.incidenceFinset x,
    e ∈ petersenGraph.incidenceFinset y →
    (x.valᶜ ∪ y.valᶜ).card = 3 ∨ (x.valᶜ ∪ y.valᶜ).card = 5 := by decide +kernel

private lemma agree : ∀ x y : PetersenVertex, ∀ i ∈ x.valᶜ, i ∈ y.valᶜ →
    ((x.valᶜ ∪ y.valᶜ).card = 3 ∨ (x.valᶜ ∪ y.valᶜ).card = 5) →
    edgeAt x i = edgeAt y i := by decide +kernel

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private lemma incident (u : V) (e : Sym2 V) :
    e ∈ G.incidenceFinset u ↔ e ∈ G.edgeFinset ∧ u ∈ e := by
  rw [incidenceFinset_eq_filter]; exact mem_filter

private lemma both (u v : V) :
    (G.edgeFinset.filter fun f => ∃ w, w ∈ s(u,v) ∧ w ∈ f) =
      G.incidenceFinset u ∪ G.incidenceFinset v := by
  classical
  ext f
  simp only [mem_filter, Sym2.mem_iff, mem_union, incident]
  grind

private def Proper (c : Sym2 V → Fin 5) :=
  ∀ e ∈ G.edgeFinset, ∀ f ∈ G.edgeFinset, e ≠ f →
    (∃ v, v ∈ e ∧ v ∈ f) → c e ≠ c f

private lemma in_palette {c : Sym2 V → Fin 5} (hc : Proper G c) (v : V) :
    Set.InjOn c (G.incidenceFinset v : Set (Sym2 V)) := by
  intro e he f hf h
  obtain ⟨he',hev⟩ := (incident G v e).mp he
  obtain ⟨hf',hfv⟩ := (incident G v f).mp hf
  by_contra hne
  exact hc e he' f hf' hne ⟨v,hev,hfv⟩ h

end OMA.Petersen
open OMA.Petersen in
theorem OMA.solution : type_of% @PetersenColoringConjecture.petersen_coloring_conjecture.variants.normal_five_edge_coloring := by
  intro V _ _ G _ hcubic
  classical
  constructor
  · rintro ⟨φ,hφ⟩
    choose w hw using hφ
    let c := label ∘ φ
    have hlocal (v : V) : (G.incidenceFinset v).image c = (w v).valᶜ := by
      rw [show c = label ∘ φ from rfl, ← image_image, (hw v).1, labels]
    have mapped (v : V) (e : Sym2 V) (he : e ∈ G.incidenceFinset v) :
        φ e ∈ petersenGraph.incidenceFinset (w v) := (hw v).1 ▸ mem_image_of_mem φ he
    refine ⟨c, ?_, ?_⟩
    · rintro e he f hf hne ⟨v,hve,hvf⟩ hef
      have he' := (incident G v e).mpr ⟨he,hve⟩
      have hf' := (incident G v f).mpr ⟨hf,hvf⟩
      have hl : label (φ e) = label (φ f) := hef
      exact hne ((hw v).2 he' hf' ((decode _ _ (mapped v e he')).symm.trans
        ((congrArg (edgeAt (w v)) hl).trans (decode _ _ (mapped v f hf')))))
    · intro e
      induction e using Sym2.inductionOn with
      | _ u v =>
        intro he
        rw [both, image_union, hlocal, hlocal]
        exact sizes _ _ _ (mapped u _ ((incident G ..).mpr ⟨he,Sym2.mem_mk_left ..⟩))
          (mapped v _ ((incident G ..).mpr ⟨he,Sym2.mem_mk_right ..⟩))
  · rintro ⟨c, hproper, hnormal⟩
    let A (v : V) := (G.incidenceFinset v).image c
    have hcard (v : V) : (A v).card = 3 := by
      unfold A
      rw [card_image_of_injOn (in_palette G hproper v), card_incidenceFinset_eq_degree, hcubic]
    let w (v : V) : PetersenVertex := ⟨(A v)ᶜ, by simp [card_compl,hcard]⟩
    have hw (v : V) : (w v).valᶜ = A v := compl_compl _
    let φ (e : Sym2 V) := edgeAt (w e.out.1) (c e)
    have hφ (v : V) (e : Sym2 V) (he : e ∈ G.incidenceFinset v) :
        φ e = edgeAt (w v) (c e) := by
      let u := e.out.1
      have hu : u ∈ e := Sym2.out_fst_mem e
      obtain ⟨heG,hv⟩ := (incident G v e).mp he
      have hu' := (incident G u e).mpr ⟨heG,hu⟩
      change edgeAt (w u) (c e) = _
      by_cases huv : u = v
      · rw [huv]
      have heq := (Sym2.mem_and_mem_iff huv).mp ⟨hu,hv⟩
      apply agree
      · rw [hw]; exact mem_image_of_mem c hu'
      · rw [hw]; exact mem_image_of_mem c he
      · rw [hw,hw]
        have H := hnormal e heG
        rw [heq, both, image_union] at H
        exact H
    refine ⟨φ, fun v => ⟨w v, ?_, ?_⟩⟩
    · calc
        _ = (G.incidenceFinset v).image (edgeAt (w v) ∘ c) := image_congr (hφ v)
        _ = (A v).image (edgeAt (w v)) := (image_image ..).symm
        _ = _ := hw v ▸ images (w v)
    · intro e he f hf h
      apply in_palette G hproper v he hf
      rw [hφ v e he, hφ v f hf] at h
      have he' : c e ∈ (w v).valᶜ := hw v ▸ mem_image_of_mem c he
      have hf' : c f ∈ (w v).valᶜ := hw v ▸ mem_image_of_mem c hf
      exact (encode _ _ he').symm.trans ((congrArg label h).trans (encode _ _ hf'))
