import FormalConjectures.ErdosProblems.«593»

/-!
# Erdos Problem 593 — common pair not obligatory

We construct a linear 3-uniform hypergraph of uncountable chromatic cardinal whose vertices are the
non-diagonal unordered pairs on a base set `omaBase` and whose hyperedges are the triangles on three
distinct base elements. Because any two distinct edges share at most one vertex, `commonPair` cannot
appear in this hypergraph. Uncountable chromatic cardinal follows from a self-contained Cantor
diagonal / Erdos-Rado stepping argument showing that every countable coloring of pairs of `omaBase`
admits a monochromatic triangle.
-/

namespace OMAErdos593

open Cardinal Set

abbrev omaIdx : Type := (Order.succ ℵ₀).ord.ToType

abbrev omaHist : Type := Σ a : omaIdx, ({ b : omaIdx // b < a } → ℕ)

abbrev omaBase : Type := Set omaHist

abbrev omaVert : Type := { e : Sym2 omaBase // ¬ e.IsDiag }

lemma omaVert_mk_ne_diag {x y : omaBase} (hxy : x ≠ y) : ¬ (s(x, y)).IsDiag := by
  simpa [Sym2.mk_isDiag_iff] using hxy

def omaTriEdge (x y z : omaBase) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : Set omaVert :=
  { ⟨s(x, y), omaVert_mk_ne_diag hxy⟩,
    ⟨s(y, z), omaVert_mk_ne_diag hyz⟩,
    ⟨s(x, z), omaVert_mk_ne_diag hxz⟩ }

lemma omaTriEdge_encard (x y z : omaBase) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    (omaTriEdge x y z hxy hyz hxz).encard = 3 := by
  let u₁ : omaVert := ⟨s(x, y), omaVert_mk_ne_diag hxy⟩
  let u₂ : omaVert := ⟨s(y, z), omaVert_mk_ne_diag hyz⟩
  let u₃ : omaVert := ⟨s(x, z), omaVert_mk_ne_diag hxz⟩
  have h12 : u₁ ≠ u₂ := by
    intro h
    have hs : s(x, y) = s(y, z) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp hs with ⟨_, _⟩ | ⟨rfl, _⟩
    · exact hxy ‹_›
    · exact hxz rfl
  have h13 : u₁ ≠ u₃ := by
    intro h
    have hs : s(x, y) = s(x, z) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp hs with ⟨_, hyz'⟩ | ⟨hxz', _⟩
    · exact hyz hyz'
    · exact hxz hxz'
  have h23 : u₂ ≠ u₃ := by
    intro h
    have hs : s(y, z) = s(x, z) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp hs with ⟨hyx, _⟩ | ⟨hyz', _⟩
    · exact hxy hyx.symm
    · exact hyz hyz'
  change ({u₁, u₂, u₃} : Set omaVert).encard = 3
  have hn1 : u₁ ∉ ({u₂, u₃} : Set omaVert) := by
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, h12, h13]
  have hn2 : u₂ ∉ ({u₃} : Set omaVert) := by
    simp [Set.mem_singleton_iff, h23]
  rw [Set.encard_insert_of_notMem hn1, Set.encard_insert_of_notMem hn2, Set.encard_singleton]
  norm_num

lemma mem_omaTriEdge_iff (x y z : omaBase) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (p : omaVert) :
    p ∈ omaTriEdge x y z hxy hyz hxz ↔ ∀ w ∈ p.1, w ∈ ({x, y, z} : Set omaBase) := by
  constructor
  · intro hp w hw
    rcases hp with rfl | rfl | rfl
    · simp only [Sym2.mem_iff] at hw
      rcases hw with rfl | rfl <;> simp
    · simp only [Sym2.mem_iff] at hw
      rcases hw with rfl | rfl <;> simp
    · simp only [Sym2.mem_iff] at hw
      rcases hw with rfl | rfl <;> simp
  · obtain ⟨e, he⟩ := p
    induction e using Sym2.ind with
    | _ a b =>
      intro hsub
      have hab : a ≠ b := by simpa [Sym2.mk_isDiag_iff] using he
      have ha : a ∈ ({x, y, z} : Set omaBase) := hsub a (Sym2.mem_mk_left a b)
      have hb : b ∈ ({x, y, z} : Set omaBase) := hsub b (Sym2.mem_mk_right a b)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      unfold omaTriEdge
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.mk.injEq]
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact absurd rfl hab
      · left; rfl
      · right; right; rfl
      · left; exact Sym2.eq_swap
      · exact absurd rfl hab
      · right; left; rfl
      · right; right; exact Sym2.eq_swap
      · right; left; exact Sym2.eq_swap
      · exact absurd rfl hab

lemma two_edges_support (x y z : omaBase) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    {u v : omaVert} (hu : u ∈ omaTriEdge x y z hxy hyz hxz)
    (hv : v ∈ omaTriEdge x y z hxy hyz hxz) (huv : u ≠ v) (w : omaBase) :
    w ∈ ({x, y, z} : Set omaBase) ↔ w ∈ u.1 ∨ w ∈ v.1 := by
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact absurd rfl huv
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.mem_iff]; tauto
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.mem_iff]; tauto
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.mem_iff]; tauto
  · exact absurd rfl huv
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.mem_iff]; tauto
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.mem_iff]; tauto
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.mem_iff]; tauto
  · exact absurd rfl huv

def omaHypergraph : UniformHypergraph omaVert 3 where
  vertexSet := Set.univ
  edgeSet := { E : Set omaVert |
    ∃ (x y z : omaBase) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z),
      E = omaTriEdge x y z hxy hyz hxz }
  subset_vertexSet_of_mem_edgeSet' := fun _ _ => Set.subset_univ _
  vertexSet_eq_univ := rfl
  uniform := by
    rintro E ⟨x, y, z, hxy, hyz, hxz, rfl⟩
    exact omaTriEdge_encard x y z hxy hyz hxz

lemma omaHypergraph_linear {E₁ E₂ : Set omaVert}
    (hE₁ : E₁ ∈ omaHypergraph.edgeSet) (hE₂ : E₂ ∈ omaHypergraph.edgeSet)
    {u v : omaVert} (hu₁ : u ∈ E₁) (hv₁ : v ∈ E₁) (hu₂ : u ∈ E₂) (hv₂ : v ∈ E₂) (huv : u ≠ v) :
    E₁ = E₂ := by
  rcases hE₁ with ⟨x₁, y₁, z₁, hxy₁, hyz₁, hxz₁, rfl⟩
  rcases hE₂ with ⟨x₂, y₂, z₂, hxy₂, hyz₂, hxz₂, rfl⟩
  have hsup : ({x₁, y₁, z₁} : Set omaBase) = {x₂, y₂, z₂} := by
    ext w
    rw [two_edges_support x₁ y₁ z₁ hxy₁ hyz₁ hxz₁ hu₁ hv₁ huv w,
      two_edges_support x₂ y₂ z₂ hxy₂ hyz₂ hxz₂ hu₂ hv₂ huv w]
  ext p
  rw [mem_omaTriEdge_iff, mem_omaTriEdge_iff, hsup]

lemma not_commonPair_appears : ¬ Erdos593.commonPair.Appears omaHypergraph := by
  rintro ⟨φ, hφ_inj, hφ_sub⟩
  let A₁ : Finset (Fin 4) := {0, 1, 2}
  let A₂ : Finset (Fin 4) := {0, 1, 3}
  have hA₁_mem : (A₁ : Set (Fin 4)) ∈ Erdos593.commonPair.edgeSet := by
    change (A₁ : Set (Fin 4)) ∈
      (UniformHypergraph.ofFinset ({{0, 1, 2}, {0, 1, 3}} : Finset (Finset (Fin 4))) _).edgeSet
    rw [UniformHypergraph.mem_edgeSet_ofFinset]
    decide
  have hA₂_mem : (A₂ : Set (Fin 4)) ∈ Erdos593.commonPair.edgeSet := by
    change (A₂ : Set (Fin 4)) ∈
      (UniformHypergraph.ofFinset ({{0, 1, 2}, {0, 1, 3}} : Finset (Finset (Fin 4))) _).edgeSet
    rw [UniformHypergraph.mem_edgeSet_ofFinset]
    decide
  have hE₁ : φ '' (A₁ : Set (Fin 4)) ∈ omaHypergraph.edgeSet :=
    hφ_sub (Hypergraph.image_mem_edgeSet_image hA₁_mem)
  have hE₂ : φ '' (A₂ : Set (Fin 4)) ∈ omaHypergraph.edgeSet :=
    hφ_sub (Hypergraph.image_mem_edgeSet_image hA₂_mem)
  have hu₁ : φ 0 ∈ φ '' (A₁ : Set (Fin 4)) := ⟨0, by decide, rfl⟩
  have hv₁ : φ 1 ∈ φ '' (A₁ : Set (Fin 4)) := ⟨1, by decide, rfl⟩
  have hu₂ : φ 0 ∈ φ '' (A₂ : Set (Fin 4)) := ⟨0, by decide, rfl⟩
  have hv₂ : φ 1 ∈ φ '' (A₂ : Set (Fin 4)) := ⟨1, by decide, rfl⟩
  have huv : φ 0 ≠ φ 1 := fun h => absurd (hφ_inj h) (by decide)
  have heq := omaHypergraph_linear hE₁ hE₂ hu₁ hv₁ hu₂ hv₂ huv
  have hw₁ : φ 2 ∈ φ '' (A₁ : Set (Fin 4)) := ⟨2, by decide, rfl⟩
  rw [heq] at hw₁
  rcases hw₁ with ⟨i, hi, hφi⟩
  have hi2 : i = 2 := hφ_inj hφi
  subst hi2
  revert hi
  change (2 : Fin 4) ∈ A₂ → False
  decide

/- ### Monochromatic triangle for countable pair-colorings of `omaBase` -/

lemma omaIdx_not_countable : ¬ Countable omaIdx := by
  intro hcount
  have hle : #omaIdx ≤ ℵ₀ := Cardinal.mk_le_aleph0
  have hmk : #omaIdx = Order.succ ℵ₀ := by
    simp [omaIdx]
  rw [hmk] at hle
  exact not_lt_of_ge hle (Order.lt_succ ℵ₀)

lemma exists_three_same_color_on_omaIdx (sz : omaIdx → ℕ) :
    ∃ a₀ a₁ a₂ : omaIdx, a₀ < a₁ ∧ a₁ < a₂ ∧ sz a₀ = sz a₁ := by
  classical
  by_contra hno
  let g : omaIdx → ℕ × Bool := fun a => (sz a, decide (∃ b : omaIdx, b < a ∧ sz b = sz a))
  have hginj : Function.Injective g := by
    intro a₁ a₂ hg
    have hsz : sz a₁ = sz a₂ := congrArg Prod.fst hg
    have hdec : decide (∃ b : omaIdx, b < a₁ ∧ sz b = sz a₁) =
        decide (∃ b : omaIdx, b < a₂ ∧ sz b = sz a₂) := congrArg Prod.snd hg
    rcases lt_trichotomy a₁ a₂ with hlt | rfl | hgt
    · have hex₂ : ∃ b : omaIdx, b < a₂ ∧ sz b = sz a₂ := ⟨a₁, hlt, hsz⟩
      have hex₁ : ∃ b : omaIdx, b < a₁ ∧ sz b = sz a₁ :=
        of_decide_eq_true (hdec.trans (decide_eq_true hex₂))
      rcases hex₁ with ⟨a₀, ha₀, hsz₀⟩
      exact False.elim (hno ⟨a₀, a₁, a₂, ha₀, hlt, hsz₀⟩)
    · rfl
    · have hex₁ : ∃ b : omaIdx, b < a₁ ∧ sz b = sz a₁ := ⟨a₂, hgt, hsz.symm⟩
      have hex₂ : ∃ b : omaIdx, b < a₂ ∧ sz b = sz a₂ :=
        of_decide_eq_true (hdec.symm.trans (decide_eq_true hex₁))
      rcases hex₂ with ⟨a₀, ha₀, hsz₀⟩
      exact False.elim (hno ⟨a₀, a₂, a₁, ha₀, hgt, hsz₀⟩)
  exact omaIdx_not_countable (Function.Injective.countable hginj)

open Classical in
noncomputable def omaStep (col : Sym2 omaBase → ℕ) (a : omaIdx)
    (rec : ∀ b : omaIdx, b < a → ({ d : omaIdx // d < b } → ℕ) → Option omaBase)
    (s : { b : omaIdx // b < a } → ℕ) : Option omaBase :=
  let good : omaBase → Prop := fun x =>
    ∀ (b : omaIdx) (hba : b < a),
      ∃ y : omaBase,
        rec b hba (fun ⟨d, hdb⟩ => s ⟨d, hdb.trans hba⟩) = some y ∧
        x ≠ y ∧ col s(y, x) = s ⟨b, hba⟩
  if h : ∃ x : omaBase, good x then some (Classical.choose h) else none

noncomputable def omaNode (col : Sym2 omaBase → ℕ) :
    (a : omaIdx) → ({ b : omaIdx // b < a } → ℕ) → Option omaBase :=
  WellFounded.fix (wellFounded_lt (α := omaIdx)) (omaStep col)

lemma omaNode_eq (col : Sym2 omaBase → ℕ) (a : omaIdx) (s : { b : omaIdx // b < a } → ℕ) :
    omaNode col a s = omaStep col a (fun b _ => omaNode col b) s :=
  congrFun (WellFounded.fix_eq (wellFounded_lt (α := omaIdx)) (omaStep col) a) s

lemma exists_mono_triangle (col : Sym2 omaBase → ℕ) :
    ∃ x y w : omaBase, x ≠ y ∧ y ≠ w ∧ x ≠ w ∧
      col s(x, y) = col s(y, w) ∧ col s(x, y) = col s(x, w) := by
  classical
  let f : omaHist → omaBase := fun p =>
    match omaNode col p.1 p.2 with
    | some x => x
    | none => ∅
  let z : omaBase := { p : omaHist | p ∉ f p }
  have hz_not_node : ∀ (a : omaIdx) (s : { b : omaIdx // b < a } → ℕ),
      omaNode col a s ≠ some z := by
    intro a s heq
    let p : omaHist := ⟨a, s⟩
    have hfp : f p = z := by simp [f, p, heq]
    have hmem : p ∈ z ↔ p ∉ z := by
      change p ∉ f p ↔ p ∉ z
      rw [hfp]
    exact iff_not_self hmem
  let szStep : ∀ a : omaIdx, (∀ b : omaIdx, b < a → ℕ) → ℕ := fun a rec =>
    match omaNode col a (fun ⟨b, hba⟩ => rec b hba) with
    | some y => col s(y, z)
    | none => 0
  let sz : omaIdx → ℕ := WellFounded.fix (wellFounded_lt (α := omaIdx)) szStep
  have hsz_eq : ∀ a : omaIdx,
      sz a = match omaNode col a (fun ⟨b, _⟩ => sz b) with
        | some y => col s(y, z)
        | none => 0 := fun a =>
    WellFounded.fix_eq (wellFounded_lt (α := omaIdx)) szStep a
  have hnode_some : ∀ a : omaIdx, ∃ y : omaBase, omaNode col a (fun ⟨b, _⟩ => sz b) = some y := by
    intro a
    induction a using WellFounded.induction (wellFounded_lt (α := omaIdx)) with
    | h a ih =>
      have hgood_z : ∀ (b : omaIdx) (hba : b < a),
          ∃ y : omaBase,
            omaNode col b (fun ⟨d, _⟩ => sz d) = some y ∧
            z ≠ y ∧ col s(y, z) = sz b := by
        intro b hba
        obtain ⟨y, hy⟩ := ih b hba
        refine ⟨y, hy, ?_, ?_⟩
        · intro hzy
          subst hzy
          exact hz_not_node b _ hy
        · rw [hsz_eq b, hy]
      have hex : ∃ x : omaBase, ∀ (b : omaIdx) (hba : b < a),
          ∃ y : omaBase,
            omaNode col b (fun ⟨d, _⟩ => sz d) = some y ∧
            x ≠ y ∧ col s(y, x) = sz b := ⟨z, hgood_z⟩
      refine ⟨Classical.choose hex, ?_⟩
      rw [omaNode_eq]
      dsimp only [omaStep]
      rw [dif_pos hex]
  let y : omaIdx → omaBase := fun a => Classical.choose (hnode_some a)
  have hy_eq : ∀ a : omaIdx, omaNode col a (fun ⟨b, _⟩ => sz b) = some (y a) :=
    fun a => Classical.choose_spec (hnode_some a)
  have hy_rel : ∀ {b a : omaIdx}, b < a → y a ≠ y b ∧ col s(y b, y a) = sz b := by
    intro b a hba
    have hstep := hy_eq a
    rw [omaNode_eq] at hstep
    dsimp only [omaStep] at hstep
    split_ifs at hstep with hex
    · have hya : Classical.choose hex = y a := Option.some.inj hstep
      have hspec := Classical.choose_spec hex b hba
      rw [hya] at hspec
      rcases hspec with ⟨y', hy', hne, hcol⟩
      have hy'eq : y' = y b := Option.some.inj (hy'.symm.trans (hy_eq b))
      subst hy'eq
      exact ⟨hne, hcol⟩
  obtain ⟨a₀, a₁, a₂, ha01, ha12, hsz01⟩ := exists_three_same_color_on_omaIdx sz
  have ha02 : a₀ < a₂ := ha01.trans ha12
  obtain ⟨hne01, hcol01⟩ := hy_rel ha01
  obtain ⟨hne12, hcol12⟩ := hy_rel ha12
  obtain ⟨hne02, hcol02⟩ := hy_rel ha02
  refine ⟨y a₀, y a₁, y a₂, hne01.symm, hne12.symm, hne02.symm, ?_, ?_⟩
  · rw [hcol01, hcol12, hsz01]
  · rw [hcol01, hcol02]

lemma aleph0_lt_omaHypergraph_chromatic : ℵ₀ < omaHypergraph.chromaticCardinal := by
  classical
  by_contra hle
  replace hle : omaHypergraph.chromaticCardinal ≤ ℵ₀ := not_lt.mp hle
  let S : Set Cardinal.{0} :=
    { κ : Cardinal.{0} | ∃ (C : Type), #C = κ ∧ ∃ f : omaVert → C, omaHypergraph.IsProperColoring f }
  have hS_ne : S.Nonempty :=
    ⟨#omaVert, omaVert, rfl, id,
      omaHypergraph.isProperColoring_of_injective (by decide) Function.injective_id⟩
  have hmem : omaHypergraph.chromaticCardinal ∈ S := csInf_mem hS_ne
  rcases hmem with ⟨C, hC_card, f, hf⟩
  have hC_le : #C ≤ ℵ₀ := by rwa [hC_card]
  have hC_count : Countable C := Cardinal.mk_le_aleph0_iff.mp hC_le
  obtain ⟨emb, hemb_inj⟩ := @Countable.exists_injective_nat C hC_count
  let col : Sym2 omaBase → ℕ := fun e =>
    if h : ¬ e.IsDiag then emb (f ⟨e, h⟩) else 0
  obtain ⟨x, y, z, hxy, hyz, hxz, hc1, hc2⟩ := exists_mono_triangle col
  let E := omaTriEdge x y z hxy hyz hxz
  have hE : E ∈ omaHypergraph.edgeSet := ⟨x, y, z, hxy, hyz, hxz, rfl⟩
  obtain ⟨u, hu, v, hv, hfuv⟩ := hf E hE
  have hcol_eq : ∀ p ∈ E, emb (f p) = col s(x, y) := by
    intro p hp
    have hp_val : emb (f p) = col p.1 := by
      dsimp [col]
      rw [dif_pos p.2]
    rw [hp_val]
    rcases hp with rfl | rfl | rfl
    · rfl
    · exact hc1.symm
    · exact hc2.symm
  have hemb_eq : emb (f u) = emb (f v) := (hcol_eq u hu).trans (hcol_eq v hv).symm
  exact hfuv (hemb_inj hemb_eq)

end OMAErdos593

theorem OMA.solution : type_of% @Erdos593.erdos_593.variants.common_pair_not_obligatory := by
  classical
  intro hObl
  exact OMAErdos593.not_commonPair_appears
    (hObl OMAErdos593.omaVert OMAErdos593.omaHypergraph
      OMAErdos593.aleph0_lt_omaHypergraph_chromatic)
