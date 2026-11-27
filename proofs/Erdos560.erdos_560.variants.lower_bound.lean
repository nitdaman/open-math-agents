import FormalConjectures.ErdosProblems.«560»
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# The lower bound for Erdős problem 560

Count ordered pairs of sides by matching independent enumerations of the sides.
Count the colourings in which any one pair of sides is monochromatic.
-/

-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/560.lean:69
-- Credit: @amp2600

open SimpleGraph
open scoped Classical Nat

namespace Erdos560Proof

private abbrev biclique (n : ℕ) :=
  completeBipartiteGraph (Fin n) (Fin n)

private abbrev Rectangle {V : Type} (F : SimpleGraph V) (n : ℕ) :=
  {t : Finset V × Finset V // t.1.card = n ∧ t.2.card = n ∧
    ∀ a ∈ t.1, ∀ b ∈ t.2, F.Adj a b}

private theorem finset_of_enum_eq {V : Type} {n : ℕ} {s t : Finset V}
    (e : Fin n ≃ s) (f : Fin n ≃ t)
    (h : ∀ i, (e i : V) = f i) : s = t := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
    have hei : (e i : V) = x := congrArg Subtype.val hi
    rw [← hei, h]
    exact (f i).property
  · intro hx
    obtain ⟨i, hi⟩ := f.surjective ⟨x, hx⟩
    have hfi : (f i : V) = x := congrArg Subtype.val hi
    rw [← hfi, ← h]
    exact (e i).property

-- Independently enumerate the two sides and match their entries in order.
private theorem rectangle_bound {v n : ℕ} (F : SimpleGraph (Fin v)) :
    Fintype.card (Rectangle F n) * n ! ^ 2 ≤ (2 * F.edgeSet.ncard) ^ n := by
  classical
  let left (t : Rectangle F n) : Fin n ≃ t.1.1 :=
    (Finset.equivFinOfCardEq t.property.1).symm
  let right (t : Rectangle F n) : Fin n ≃ t.1.2 :=
    (Finset.equivFinOfCardEq t.property.2.1).symm
  let darts (t : Rectangle F n × Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) :
      Fin n → F.Dart := fun i =>
    ⟨((left t.1 (t.2.1 i)).val, (right t.1 (t.2.2 i)).val),
      t.1.property.2.2 _ (left t.1 (t.2.1 i)).property _ (right t.1 (t.2.2 i)).property⟩
  have hinj : Function.Injective darts := by
    rintro ⟨s, σ, τ⟩ ⟨t, σ', τ'⟩ h
    have hl (i : Fin n) : (left s (σ i)).val = (left t (σ' i)).val :=
      congrArg (fun f => (f i).fst) h
    have hr (i : Fin n) : (right s (τ i)).val = (right t (τ' i)).val :=
      congrArg (fun f => (f i).snd) h
    have hst : s = t := Subtype.ext (Prod.ext
      (finset_of_enum_eq (σ.trans (left s)) (σ'.trans (left t)) hl)
      (finset_of_enum_eq (τ.trans (right s)) (τ'.trans (right t)) hr))
    subst t
    have hσ : σ = σ' := Equiv.ext (fun i => (left s).injective (Subtype.ext (hl i)))
    have hτ : τ = τ' := Equiv.ext (fun i => (right s).injective (Subtype.ext (hr i)))
    rw [hσ, hτ]
  have he : F.edgeFinset.card = F.edgeSet.ncard := by
    simp [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
  have h := Fintype.card_le_of_injective darts hinj
  simpa [Fintype.card_prod, Fintype.card_perm, Fintype.card_fun, Fintype.card_fin,
    F.dart_card_eq_twice_card_edges, he, pow_two, Nat.mul_assoc] using h

private def hostEdge {V : Type} {F : SimpleGraph V} {a b : V} (h : F.Adj a b) : F.edgeSet :=
  ⟨s(a, b), h⟩

private def rectangleEdge {V : Type} {F : SimpleGraph V} {n : ℕ} (t : Rectangle F n)
    (p : t.1.1 × t.1.2) : F.edgeSet :=
  hostEdge (t.property.2.2 _ p.1.property _ p.2.property)

private theorem rectangleEdge_injective {V : Type} {F : SimpleGraph V} {n : ℕ}
    (t : Rectangle F n) : Function.Injective (rectangleEdge t) := by
  intro p q h
  have hpq : s(p.1.val, p.2.val) = s(q.1.val, q.2.val) := congrArg Subtype.val h
  rcases Sym2.eq_iff.mp hpq with hpq | hpq
  · exact Prod.ext (Subtype.ext hpq.1) (Subtype.ext hpq.2)
  · exact (F.irrefl (t.property.2.2 _ p.1.property _ (hpq.1 ▸ q.2.property))).elim

private theorem rectangleEdge_card {v n : ℕ} {F : SimpleGraph (Fin v)}
    (t : Rectangle F n) : Fintype.card (t.1.1 × t.1.2) = n ^ 2 := by
  simp [Fintype.card_prod, Fintype.card_coe, t.property.1, t.property.2.1, pow_two]

private theorem copy_rectangle {V : Type} {F G : SimpleGraph V} {n : ℕ} (hle : G ≤ F)
    (copy : (biclique n).Copy G) :
    ∃ t : Rectangle F n, ∀ p : t.1.1 × t.1.2, G.Adj p.1.val p.2.val := by
  classical
  let a (i : Fin n) := copy (Sum.inl i)
  let b (i : Fin n) := copy (Sum.inr i)
  have ha : Function.Injective a := fun _ _ h => Sum.inl.inj (copy.injective h)
  have hb : Function.Injective b := fun _ _ h => Sum.inr.inj (copy.injective h)
  let A := Finset.univ.image a
  let B := Finset.univ.image b
  have hA : A.card = n := by simp [A, Finset.card_image_of_injective _ ha]
  have hB : B.card = n := by simp [B, Finset.card_image_of_injective _ hb]
  have hcross : ∀ x ∈ A, ∀ y ∈ B, G.Adj x y := by
    intro x hx y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    exact copy.toHom.map_rel (by simp [biclique, completeBipartiteGraph])
  exact ⟨⟨(A, B), hA, hB, fun x hx y hy => hle (hcross x hx y hy)⟩,
    fun p => hcross _ p.1.property _ p.2.property⟩

private def redGraph {V : Type} {F : SimpleGraph V} (c : F.edgeSet → Bool) :
    SimpleGraph V where
  Adj a b := ∃ h : F.Adj a b, c (hostEdge h) = true
  symm.symm a b := by
    rintro ⟨h, hc⟩
    refine ⟨h.symm, ?_⟩
    have he : hostEdge h.symm = hostEdge h := Subtype.ext (Sym2.eq_swap)
    rwa [he]
  loopless.irrefl _ h := F.irrefl h.choose

private theorem color_has_rectangle {v n : ℕ} {F : SimpleGraph (Fin v)}
    (hR : ∀ R : SimpleGraph (Fin v), R ≤ F →
      (biclique n).IsContained R ∨ (biclique n).IsContained (F \ R))
    (c : F.edgeSet → Bool) :
    ∃ (t : Rectangle F n) (b : Bool), ∀ p, c (rectangleEdge t p) = b := by
  let R := redGraph c
  have hRF : R ≤ F := fun _ _ h => h.choose
  rcases hR R hRF with hred | hblue
  · obtain ⟨f⟩ := hred
    obtain ⟨t, ht⟩ := copy_rectangle hRF f
    refine ⟨t, true, fun p => ?_⟩
    obtain ⟨hf, hc⟩ := ht p
    exact hc
  · obtain ⟨f⟩ := hblue
    have hBF : F \ R ≤ F := fun _ _ h => h.1
    obtain ⟨t, ht⟩ := copy_rectangle hBF f
    refine ⟨t, false, fun p => ?_⟩
    cases he : c (rectangleEdge t p) with
    | false => rfl
    | true => exact ((ht p).2 ⟨t.property.2.2 _ p.1.property _ p.2.property, he⟩).elim

-- With the rectangle's edges fixed, restriction to the other edges is injective.
private theorem fixed_color_bound {E I : Type} [Fintype E] [Fintype I]
    (f : I → E) (hf : Function.Injective f) (b : Bool) :
    Nat.card {c : E → Bool // ∀ i, c (f i) = b} ≤
      2 ^ (Nat.card E - Nat.card I) := by
  classical
  simp only [Nat.card_eq_fintype_card]
  let rest : Type := {e : E // e ∉ Set.range f}
  let restrict (c : {c : E → Bool // ∀ i, c (f i) = b}) : rest → Bool :=
    fun e => c.val e.val
  have h : Function.Injective restrict := by
    intro c d he
    apply Subtype.ext
    funext e
    by_cases he' : e ∈ Set.range f
    · obtain ⟨i, rfl⟩ := he'
      exact (c.property i).trans (d.property i).symm
    · exact congrFun he ⟨e, he'⟩
  have hrest : Fintype.card rest = Fintype.card E - Fintype.card I := by
    change Fintype.card {e : E // e ∉ Set.range f} = _
    rw [Fintype.card_subtype_compl (fun e => e ∈ Set.range f)]
    congr 1
    exact Fintype.card_congr (Equiv.ofInjective f hf).symm
  simpa [Fintype.card_fun, hrest] using Fintype.card_le_of_injective restrict h

set_option maxHeartbeats 800000 in
private theorem ramsey_count {v n : ℕ} {F : SimpleGraph (Fin v)}
    (hR : ∀ R : SimpleGraph (Fin v), R ≤ F →
      (biclique n).IsContained R ∨ (biclique n).IsContained (F \ R)) :
    2 ^ (n ^ 2) * n ! ^ 2 ≤ 2 * (2 * F.edgeSet.ncard) ^ n := by
  classical
  let E := F.edgeSet
  let Index := Rectangle F n × Bool
  let Bad (i : Index) := {c : E → Bool // ∀ p, c (rectangleEdge i.1 p) = i.2}
  letI (i : Index) : Fintype (Bad i) := inferInstanceAs (Fintype
    {c : E → Bool // ∀ p, c (rectangleEdge i.1 p) = i.2})
  have hsurj : Function.Surjective (fun x : Sigma Bad => x.2.val) := by
    intro c
    obtain ⟨t, b, ht⟩ := color_has_rectangle hR c
    exact ⟨⟨(t, b), c, ht⟩, rfl⟩
  have hE : Fintype.card E = F.edgeSet.ncard :=
    (Nat.card_eq_fintype_card (α := E)).symm
  obtain ⟨t, -⟩ := color_has_rectangle hR (fun _ => false)
  have hsq : n ^ 2 ≤ F.edgeSet.ncard := calc
    n ^ 2 = Fintype.card (t.val.1 × t.val.2) := (rectangleEdge_card t).symm
    _ ≤ Fintype.card E :=
      Fintype.card_le_of_injective (rectangleEdge t) (rectangleEdge_injective t)
    _ = _ := hE
  have hcolors : 2 ^ F.edgeSet.ncard ≤
      (2 * Fintype.card (Rectangle F n)) * 2 ^ (F.edgeSet.ncard - n ^ 2) := calc
    2 ^ F.edgeSet.ncard = Fintype.card (E → Bool) := by simp [hE]
    _ ≤ Fintype.card (Sigma Bad) := Fintype.card_le_of_surjective _ hsurj
    _ = ∑ i : Index, Fintype.card (Bad i) := Fintype.card_sigma
    _ ≤ ∑ _ : Index, 2 ^ (F.edgeSet.ncard - n ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        Fintype.card (Bad i) = Nat.card (Bad i) := Nat.card_eq_fintype_card.symm
        _ ≤ 2 ^ (Nat.card E - Nat.card (i.1.val.1 × i.1.val.2)) :=
          fixed_color_bound (rectangleEdge i.1) (rectangleEdge_injective i.1) i.2
        _ = _ := congrArg₂ (fun m k : ℕ => (2 : ℕ) ^ (m - k)) rfl
          (Nat.card_eq_fintype_card.trans (rectangleEdge_card i.1))
    _ = _ := by simp [Index, Fintype.card_prod, mul_comm]
  have hfactor : 2 ^ F.edgeSet.ncard =
      2 ^ (n ^ 2) * 2 ^ (F.edgeSet.ncard - n ^ 2) := by
    rw [← pow_add, Nat.add_sub_of_le hsq]
  rw [hfactor] at hcolors
  have hsmall : 2 ^ (n ^ 2) ≤ 2 * Fintype.card (Rectangle F n) :=
    Nat.le_of_mul_le_mul_right hcolors (by positivity)
  calc
    2 ^ (n ^ 2) * n ! ^ 2 ≤ (2 * Fintype.card (Rectangle F n)) * n ! ^ 2 :=
      Nat.mul_le_mul_right _ hsmall
    _ = 2 * (Fintype.card (Rectangle F n) * n ! ^ 2) := by rw [Nat.mul_assoc]
    _ ≤ 2 * (2 * F.edgeSet.ncard) ^ n := Nat.mul_le_mul_left _ (rectangle_bound F)

private theorem clique_contains_biclique {n : ℕ} {V : Type} {G : SimpleGraph V}
    (S : Finset V) (hS : S.card = n + n)
    (hG : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b) : (biclique n).IsContained G := by
  let e : (Fin n ⊕ Fin n) ≃ S := finSumFinEquiv.trans (Finset.equivFinOfCardEq hS).symm
  have he : Function.Injective (fun a => (e a : V)) :=
    Subtype.val_injective.comp e.injective
  exact ⟨⟨⟨fun a => (e a : V), fun {a b} h =>
    hG _ (e a).property _ (e b).property (fun heq => h.ne (he heq))⟩, he⟩⟩

private theorem ramsey_host (n : ℕ) :
    {m : ℕ | ∃ v : ℕ, ∃ F : SimpleGraph (Fin v), F.edgeSet.ncard = m ∧
      ∀ R : SimpleGraph (Fin v), R ≤ F →
        (biclique n).IsContained R ∨ (biclique n).IsContained (F \ R)}.Nonempty := by
  classical
  let v := Nat.choose ((n + n) + (n + n)) (n + n)
  refine ⟨(⊤ : SimpleGraph (Fin v)).edgeSet.ncard, v, ⊤, rfl, ?_⟩
  intro R _
  let c (S : Finset (Fin v)) : Bool := decide (∃ a ∈ S, ∃ b ∈ S, R.Adj a b)
  have hpair (a b : Fin v) : c {a, b} = decide (R.Adj a b) := by
    have hp : (∃ x ∈ ({a, b} : Finset (Fin v)), ∃ y ∈ ({a, b} : Finset (Fin v)),
        R.Adj x y) ↔ R.Adj a b := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨x, rfl | rfl, y, rfl | rfl, h⟩
        · exact (R.irrefl h).elim
        · exact h
        · exact h.symm
        · exact (R.irrefl h).elim
      · exact fun h => ⟨a, Or.inl rfl, b, Or.inr rfl, h⟩
    exact decide_eq_decide.mpr hp
  have hcolor {S : Finset (Fin v)} {d : Bool}
      (hm : ∀ e ⊆ S, e.card = 2 → c e = d)
      {a b : Fin v} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
      decide (R.Adj a b) = d := by
    have hs : ({a, b} : Finset (Fin v)) ⊆ S :=
      Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩
    exact (hpair a b).symm.trans (hm _ hs (Finset.card_pair_eq_two_iff.mpr hab))
  have h := Combinatorics.Diagonal.hasRamseyProperty_choose (n + n) (n + n)
    c Finset.univ (by simp [v])
  rcases h with ⟨S, -, hS, hm⟩ | ⟨S, -, hS, hm⟩
  · right
    refine clique_contains_biclique S hS (fun a ha b hb hab => ?_)
    exact ⟨by simpa using hab, of_decide_eq_false (hcolor hm ha hb hab)⟩
  · left
    refine clique_contains_biclique S hS (fun a ha b hb hab => ?_)
    exact of_decide_eq_true (hcolor hm ha hb hab)

private theorem factorial_bound (n : ℕ) : (n : ℝ) ^ n ≤ 3 ^ n * (n ! : ℝ) := by
  have hp : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  apply (div_le_iff₀ hp).mp
  calc
    (n : ℝ) ^ n / (n ! : ℝ) ≤ Real.exp n :=
      Real.pow_div_factorial_le_exp (n : ℝ) (by positivity) n
    _ = (Real.exp 1) ^ n := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ 3 ^ n := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le n

private theorem count_implies_lower (n m : ℕ) (hn : 6 ≤ n)
    (h : 2 ^ (n ^ 2) * n ! ^ 2 ≤ 2 * (2 * m) ^ n) :
    (1 / 60 : ℝ) * (n : ℝ) ^ 2 * 2 ^ n < m := by
  by_contra! hm
  let K : ℝ := 2 ^ (n ^ 2) * (n ! : ℝ) ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  have hreal : K ≤ 2 * (2 * (m : ℝ)) ^ n := by dsimp [K]; exact_mod_cast h
  have hm' : (2 : ℝ) * m ≤ ((n : ℝ) ^ 2 * 2 ^ n) / 30 := by linarith only [hm]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ) * m) hm' n
  have hfac := pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) ^ n) (factorial_bound n) 2
  have hfrac : 2 * (3 / 10 : ℝ) ^ n < 1 := by
    have hpow' : (3 / 10 : ℝ) ^ n ≤ (3 / 10 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num at hpow'
    linarith
  have htwo : ((2 : ℝ) ^ n) ^ n = 2 ^ (n ^ 2) := by rw [← pow_mul, pow_two]
  have hn2 : ((n : ℝ) ^ 2) ^ n = ((n : ℝ) ^ n) ^ 2 := by
    simp only [← pow_mul, Nat.mul_comm]
  have hthree : ((3 : ℝ) ^ n) ^ 2 = (9 : ℝ) ^ n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have hscale : (1 / 30 : ℝ) ^ n * (9 : ℝ) ^ n = (3 / 10 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  have hc : K < K := calc
    K ≤ 2 * (2 * (m : ℝ)) ^ n := hreal
    _ ≤ 2 * (((n : ℝ) ^ 2 * 2 ^ n) / 30) ^ n :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = 2 * (((n : ℝ) ^ 2 * 2 ^ n) * (1 / 30 : ℝ)) ^ n := by
      rw [div_eq_mul_inv, one_div]
    _ = (2 * (1 / 30 : ℝ) ^ n * 2 ^ (n ^ 2)) * ((n : ℝ) ^ n) ^ 2 := by
      rw [mul_pow, mul_pow, hn2, htwo]
      ring
    _ ≤ (2 * (1 / 30 : ℝ) ^ n * 2 ^ (n ^ 2)) * ((3 : ℝ) ^ n * (n ! : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = (2 * (3 / 10 : ℝ) ^ n) * K := by
      rw [mul_pow, hthree]
      calc
        _ = 2 * ((1 / 30 : ℝ) ^ n * (9 : ℝ) ^ n) * K := by dsimp [K]; ring
        _ = _ := by rw [hscale]
    _ < K := by simpa using mul_lt_mul_of_pos_right hfrac hK
  exact (lt_irrefl _) hc

end Erdos560Proof

theorem OMA.solution : type_of% @Erdos560.erdos_560.variants.lower_bound := by
  intro n hn
  obtain ⟨v, F, hm, hR⟩ := Nat.sInf_mem (Erdos560Proof.ramsey_host n)
  have h := Erdos560Proof.ramsey_count hR
  rw [hm] at h
  exact Erdos560Proof.count_implies_lower n _ hn h
