import FormalConjectures.ErdosProblems.«750»

-- Problem: Erdős Problem 750 — epsilon
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/750.lean:160 (declaration Erdos750.erdos_750.variants.epsilon)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Shift graphs on increasing tuples, with independent sets obtained by directed cuts. -/

open Finset BigOperators NNReal

namespace Erdos750Shift

universe u

abbrev Vertex (n : ℕ) := ULift.{u} {f : Fin (n + 1) → ℕ // StrictMono f}

def front {n : ℕ} (v : Vertex (n + 1)) : Vertex n :=
  ⟨⟨Fin.init v.down.1, v.down.2.comp Fin.strictMono_castSucc⟩⟩

def back {n : ℕ} (v : Vertex (n + 1)) : Vertex n :=
  ⟨⟨Fin.tail v.down.1, v.down.2.comp Fin.strictMono_succ⟩⟩

def follows {n : ℕ} (v w : Vertex n) : Prop :=
  v.down.1 0 < w.down.1 0 ∧ ∀ i : Fin n, v.down.1 i.succ = w.down.1 i.castSucc

theorem back_eq_front {n : ℕ} {v w : Vertex (n + 1)} (h : follows v w) :
    back v = front w := by
  apply ULift.ext
  apply Subtype.ext
  funext i
  exact h.2 i

def graph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj v w := follows v w ∨ follows w v
  symm := by constructor; intro _ _ h; exact h.symm
  loopless := by constructor; intro v h; rcases h with h | h <;> exact (lt_irrefl _) h.1

private def glue {n : ℕ} {v w : Vertex n} (h : follows v w) : Vertex (n + 1) :=
  ⟨⟨Fin.cons (v.down.1 0) w.down.1, Fin.strictMono_cons.mpr
      ⟨fun j => h.1.trans_le (w.down.2.monotone (Fin.zero_le j)), w.down.2⟩⟩⟩

private theorem prefix_glue {n : ℕ} {v w : Vertex n} (h : follows v w) :
    front (glue h) = v := by
  apply ULift.ext
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [front, glue, Fin.init]
  · simpa [front, glue, Fin.init] using (h.2 j).symm

private theorem follows_glue {n : ℕ} {v w : Vertex n} (h : follows v w)
    {z : Vertex (n + 1)} (hz : front z = w) : follows (glue h) z := by
  have hp (i : Fin (n + 1)) : z.down.1 i.castSucc = w.down.1 i :=
    congrArg (fun a : Vertex n => a.down.1 i) hz
  refine ⟨?_, fun i => ?_⟩
  · have hzero : z.down.1 0 = w.down.1 0 := hp 0
    simpa [glue, hzero] using h.1
  · simpa [glue] using (hp i).symm

theorem infinite_chromatic (n : ℕ) : (graph n).chromaticNumber = ⊤ := by
  classical
  induction n with
  | zero =>
      by_contra h
      obtain ⟨k, ⟨color⟩⟩ := (graph 0).chromaticNumber_ne_top_iff_exists.mp h
      let v (a : ℕ) : Vertex 0 := ⟨⟨fun _ => a, by intro i j hij; omega⟩⟩
      have hi : Function.Injective (fun a => color (v a)) := by
        intro a b h
        rcases lt_trichotomy a b with hab | heq | hba
        · exact False.elim (color.valid (Or.inl ⟨hab, fun i => (Fin.elim0 i : False).elim⟩) h)
        · exact heq
        · exact False.elim (color.valid (Or.inr ⟨hba, fun i => (Fin.elim0 i : False).elim⟩) h)
      have : Finite ℕ := Finite.of_injective _ hi
      exact not_finite ℕ
  | succ n ih =>
      by_contra h
      obtain ⟨k, ⟨color⟩⟩ := (graph (n + 1)).chromaticNumber_ne_top_iff_exists.mp h
      let palette (v : Vertex n) : Set (Fin k) := {c | ∃ z, front z = v ∧ color z = c}
      have distinct {v w : Vertex n} (hvw : follows v w) : palette v ≠ palette w := by
        intro heq
        have hm : color (glue hvw) ∈ palette v := ⟨glue hvw, prefix_glue hvw, rfl⟩
        rw [heq] at hm
        obtain ⟨z, hz, hcolor⟩ := hm
        exact color.valid (Or.inl (follows_glue hvw hz)) hcolor.symm
      let newColor : (graph n).Coloring (Set (Fin k)) :=
        SimpleGraph.Coloring.mk palette (fun h => h.elim distinct (fun h => (distinct h).symm))
      have hc : (graph n).Colorable (Fintype.card (Set (Fin k))) :=
        ⟨(graph n).recolorOfEquiv (Fintype.equivFin _) newColor⟩
      exact ((graph n).chromaticNumber_ne_top_iff_exists.mpr ⟨_, hc⟩) ih

theorem exists_minimum {n m : ℕ} (f : Fin (n + 1) → Fin m) (p : Equiv.Perm (Fin m)) :
    ∃ i, ∀ j, p (f i) ≤ p (f j) := by
  obtain ⟨i, _, hi⟩ := exists_min_image univ (p ∘ f) univ_nonempty
  exact ⟨i, fun j => hi j (mem_univ _)⟩

noncomputable def minimum {n m : ℕ} (f : Fin (n + 1) → Fin m) (p : Equiv.Perm (Fin m)) :
    Fin (n + 1) := (exists_minimum f p).choose

theorem minimum_spec {n m : ℕ} (f : Fin (n + 1) → Fin m) (p : Equiv.Perm (Fin m))
    (j : Fin (n + 1)) : p (f (minimum f p)) ≤ p (f j) :=
  (exists_minimum f p).choose_spec j

theorem minimum_eq {n m : ℕ} {f : Fin (n + 1) → Fin m} (hf : Function.Injective f)
    (p : Equiv.Perm (Fin m)) {i : Fin (n + 1)} (hi : ∀ j, p (f i) ≤ p (f j)) :
    minimum f p = i :=
  hf (p.injective (le_antisymm (minimum_spec f p i) (hi _)))

theorem minimum_swap {n m : ℕ} {f : Fin (n + 1) → Fin m} (hf : Function.Injective f)
    (p : Equiv.Perm (Fin m)) (i j : Fin (n + 1)) :
    minimum f (p * Equiv.swap (f i) (f j)) = Equiv.swap i j (minimum f p) := by
  apply minimum_eq hf
  intro k
  simp only [Equiv.Perm.mul_apply, hf.swap_apply, Equiv.swap_apply_self]
  exact minimum_spec f p _

theorem card_minimum_fibers {n m : ℕ} {f : Fin (n + 1) → Fin m} (hf : Function.Injective f)
    (i j : Fin (n + 1)) :
    (univ.filter (fun p => minimum f p = i)).card = (univ.filter (fun p => minimum f p = j)).card := by
  classical
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  apply Fintype.card_congr
  refine (Equiv.mulRight (Equiv.swap (f i) (f j))).subtypeEquiv (fun p => ?_)
  change minimum f p = i ↔ minimum f (p * Equiv.swap (f i) (f j)) = j
  rw [minimum_swap hf, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]

theorem card_interior_minimum {n m : ℕ} {f : Fin (n + 3) → Fin m}
    (hf : Function.Injective f) :
    (n + 3) * (univ.filter (fun p => minimum f p ≠ 0 ∧ minimum f p ≠ Fin.last (n + 2))).card =
      (n + 1) * Fintype.card (Equiv.Perm (Fin m)) := by
  classical
  let perms : Finset (Equiv.Perm (Fin m)) := univ
  let interior : Finset (Fin (n + 3)) := (univ.erase 0).erase (Fin.last (n + 2))
  let count := (perms.filter (fun p => minimum f p = 0)).card
  have hlast : Fin.last (n + 2) ≠ (0 : Fin (n + 3)) := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hcard : interior.card = n + 1 := by
    dsimp [interior]
    rw [card_erase_of_mem (by simp [hlast]), card_erase_of_mem (mem_univ 0),
      card_univ, Fintype.card_fin]
    omega
  have hfull : perms.card = (n + 3) * count := calc
    _ = ∑ j : Fin (n + 3), (perms.filter (fun p => minimum f p = j)).card :=
      card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _ = (univ : Finset (Fin (n + 3))).card * count :=
      sum_const_nat (fun j _ => card_minimum_fibers hf j 0)
    _ = _ := by simp
  have hint : (perms.filter (fun p => minimum f p ∈ interior)).card = (n + 1) * count := calc
    _ = ∑ j ∈ interior, (perms.filter (fun p => minimum f p = j)).card :=
      (sum_card_fiberwise_eq_card_filter perms interior (minimum f)).symm
    _ = interior.card * count := sum_const_nat (fun j _ => card_minimum_fibers hf j 0)
    _ = _ := by rw [hcard]
  have hfilter :
      univ.filter (fun p => minimum f p ≠ 0 ∧ minimum f p ≠ Fin.last (n + 2)) =
        perms.filter (fun p => minimum f p ∈ interior) := by
    ext p
    simp only [perms, interior, mem_filter, mem_univ, true_and, mem_erase, and_comm]
  rw [hfilter, hint, ← card_univ, ← show perms = univ from rfl, hfull]
  ac_rfl

theorem neighbors_parity {n m : ℕ} {f : Fin (n + 3) → Fin m} (hf : Function.Injective f)
    (p : Equiv.Perm (Fin m)) (hzero : minimum f p ≠ 0)
    (hlast : minimum f p ≠ Fin.last (n + 2)) :
    (minimum (fun i : Fin (n + 2) => f i.castSucc) p).val % 2 ≠
      (minimum (fun i : Fin (n + 2) => f i.succ) p).val % 2 := by
  have hleft :
      minimum (fun i : Fin (n + 2) => f i.castSucc) p = (minimum f p).castPred hlast := by
    apply minimum_eq (hf.comp (Fin.castSucc_injective _))
    intro j
    simp only [Function.comp_apply, Fin.castSucc_castPred]
    exact minimum_spec f p _
  have hright :
      minimum (fun i : Fin (n + 2) => f i.succ) p = (minimum f p).pred hzero := by
    apply minimum_eq (hf.comp (Fin.succ_injective _))
    intro j
    simp only [Function.comp_apply, Fin.succ_pred]
    exact minimum_spec f p _
  have hpos : 0 < (minimum f p).val := Fin.pos_iff_ne_zero.mpr hzero
  rw [hleft, hright]
  simp only [Fin.coe_castPred, Fin.val_pred]
  omega

/-- A directed cut selected by the parities of the minimum-priority labels. -/
theorem exists_independent_finset {n : ℕ} (s : Finset (Vertex.{u} (n + 2))) :
    ∃ t ⊆ s, (graph (n + 2)).IsIndepSet (t : Set (Vertex.{u} (n + 2))) ∧
      (n + 1) * s.card ≤ 2 * (n + 3) * t.card := by
  classical
  let m := (s.sup (fun v => v.down.1 (Fin.last (n + 2)))) + 1
  let label (a : ℕ) : Fin m := if h : a < m then ⟨a, h⟩ else ⟨0, by dsimp [m]; omega⟩
  have hlabel {v : Vertex.{u} (n + 2)} (hv : v ∈ s) (i : Fin (n + 3)) :
      (label (v.down.1 i)).val = v.down.1 i := by
    have h := (v.down.2.monotone (Fin.le_last i)).trans (le_sup (f := fun w => w.down.1 (Fin.last (n + 2))) hv :
      v.down.1 (Fin.last (n + 2)) ≤ s.sup (fun w => w.down.1 (Fin.last (n + 2))))
    have hi : v.down.1 i < m := Nat.lt_succ_of_le h
    simp [label, hi]
  let parity (p : Equiv.Perm (Fin m)) (v : Vertex.{u} (n + 1)) : Fin 2 :=
    ⟨(minimum (fun i => label (v.down.1 i)) p).val % 2, Nat.mod_lt _ (by decide)⟩
  let keep (q : Equiv.Perm (Fin m) × Fin 2) (v : Vertex.{u} (n + 2)) : Prop :=
    parity q.1 (front v) = q.2 ∧ parity q.1 (back v) ≠ q.2
  let cut (q : Equiv.Perm (Fin m) × Fin 2) := s.filter (keep q)
  let choices : Finset (Equiv.Perm (Fin m) × Fin 2) := univ
  let d := Fintype.card (Equiv.Perm (Fin m))
  have hchoices : choices.card = 2 * d := by
    simp [choices, d, mul_comm]
  have hd : 0 < d := Fintype.card_pos
  have hcount (v : Vertex.{u} (n + 2)) (hv : v ∈ s) :
      (n + 1) * d ≤ (n + 3) * (choices.filter (fun q => keep q v)).card := by
    let f (i : Fin (n + 3)) := label (v.down.1 i)
    have hf : Function.Injective f := by
      intro i j hij
      apply v.down.2.injective
      simpa [f, hlabel hv] using congrArg Fin.val hij
    rw [← card_interior_minimum hf]
    apply Nat.mul_le_mul_left
    let pack (p : Equiv.Perm (Fin m)) := (p, parity p (front v))
    refine card_le_card_of_injOn pack ?_ (fun p _ r _ h => congrArg Prod.fst h)
    intro p hp
    have hp' := (mem_filter.mp hp).2
    refine mem_filter.mpr ⟨mem_univ _, rfl, ?_⟩
    intro h
    exact neighbors_parity hf p hp'.1 hp'.2 (congrArg Fin.val h).symm
  have hsum :
      (∑ q ∈ choices, (cut q).card) =
        ∑ v ∈ s, (choices.filter (fun q => keep q v)).card := by
    simp only [cut, card_filter]
    exact sum_comm
  have htotal : (n + 1) * d * s.card ≤
      ∑ q ∈ choices, (n + 3) * (cut q).card := calc
    _ = ∑ _ ∈ s, (n + 1) * d := by simp [mul_comm]
    _ ≤ ∑ v ∈ s, (n + 3) * (choices.filter (fun q => keep q v)).card :=
      sum_le_sum hcount
    _ = _ := by rw [← mul_sum, ← hsum, mul_sum]
  have havg : ∑ _ ∈ choices, d * ((n + 1) * s.card) ≤
      ∑ q ∈ choices, d * (2 * (n + 3) * (cut q).card) := by
    calc
      _ = (2 * d) * ((n + 1) * d * s.card) := by
        rw [sum_const, smul_eq_mul, hchoices]
        ring
      _ ≤ (2 * d) * ∑ q ∈ choices, (n + 3) * (cut q).card :=
        Nat.mul_le_mul_left _ htotal
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro q _
        ring
  obtain ⟨q, _, hq⟩ := exists_le_of_sum_le (show choices.Nonempty from univ_nonempty) havg
  refine ⟨cut q, filter_subset _ _, ?_, (Nat.le_of_mul_le_mul_left hq hd)⟩
  intro v hv w hw _ hadj
  have hv' := (mem_filter.mp hv).2
  have hw' := (mem_filter.mp hw).2
  rcases hadj with hadj | hadj
  · exact hv'.2 (by rw [back_eq_front hadj]; exact hw'.1)
  · exact hw'.2 (by rw [back_eq_front hadj]; exact hv'.1)

end Erdos750Shift

theorem OMA.solution : type_of% @Erdos750.erdos_750.variants.epsilon := by
  classical
  intro ε hε
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (1 / ε)
  have hk : (1 : ℝ≥0) / (n + 3 : ℕ) ≤ ε := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hn' := (div_lt_iff₀ hε).mp hn
    push_cast
    nlinarith
  refine ⟨Erdos750Shift.Vertex (n + 2), Erdos750Shift.graph (n + 2),
    Erdos750Shift.infinite_chromatic _, ?_⟩
  intro m S hm hS
  have hfin : S.Finite := Set.finite_of_ncard_ne_zero (by omega)
  obtain ⟨t, hsub, hind, hcard⟩ := Erdos750Shift.exists_independent_finset hfin.toFinset
  refine ⟨(t : Set _), ?_, hind, ?_⟩
  · simpa using hsub
  have hs : hfin.toFinset.card = m := by rwa [Set.ncard_eq_toFinset_card S hfin] at hS
  rw [hs] at hcard
  rw [Set.ncard_coe_finset, tsub_le_iff_right]
  have hc : ((n + 1 : ℕ) : ℝ≥0) * m ≤ 2 * ((n + 3 : ℕ) : ℝ≥0) * t.card := by
    exact_mod_cast hcard
  have hmul : (m : ℝ≥0) ≤ ((t.card : ℝ≥0) + ε * m) * 2 := by
    have hlarge : (1 : ℝ≥0) ≤ ε * (n + 3 : ℕ) :=
      (div_le_iff₀ (by positivity)).mp hk
    apply le_of_mul_le_mul_right (a := ((n + 3 : ℕ) : ℝ≥0)) _ (by positivity)
    have he := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ 2 * (m : ℝ≥0) by positivity)
    push_cast at hc hlarge he ⊢
    nlinarith
  exact (div_le_iff₀ (by norm_num)).mpr hmul