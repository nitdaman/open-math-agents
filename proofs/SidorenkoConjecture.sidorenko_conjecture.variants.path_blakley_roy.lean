import FormalConjectures.Wikipedia.SidorenkoConjecture

-- Problem: Case: paths, the Blakley–Roy inequality (1965).
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/SidorenkoConjecture.lean:814 (declaration SidorenkoConjecture.sidorenko_conjecture.variants.path_blakley_roy)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


open Finset SimpleGraph

namespace OMA

variable {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]

/-- walks of length k starting at x -/
def wk : ℕ → W → ℕ
  | 0, _ => 1
  | k + 1, x => ∑ y ∈ G.neighborFinset x, wk k y

lemma wk_succ (k : ℕ) (x : W) : wk G (k + 1) x = ∑ y ∈ G.neighborFinset x, wk G k y := rfl

lemma key (w p q : ℝ) (hw : 0 ≤ w) (hp : 0 < p) (hq : 0 < q) :
    w * (Real.log p - Real.log q) ≤ w * (p / q - 1) := by
  apply mul_le_mul_of_nonneg_left _ hw
  rw [← Real.log_div hp.ne' hq.ne']
  exact Real.log_le_sub_one_of_pos (div_pos hp hq)

lemma dc (F : W → ℝ) :
    ∑ x, ∑ y ∈ G.neighborFinset x, F y = ∑ y, (G.degree y : ℝ) * F y := by
  rw [Finset.sum_comm' (t' := univ) (s' := fun y => G.neighborFinset y)]
  · refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul]
  · intro x y
    simp [mem_neighborFinset, G.adj_comm]

lemma wk_pos (k : ℕ) : ∀ y : W, 0 < G.degree y → 0 < wk G k y := by
  induction k with
  | zero => intro y _; simp [wk]
  | succ k ih =>
    intro y hy
    rw [wk_succ]
    obtain ⟨z, hz⟩ : (G.neighborFinset y).Nonempty := by
      rw [← Finset.card_pos, G.card_neighborFinset_eq_degree]; exact hy
    have hz' : 0 < G.degree z := by
      rw [← G.card_neighborFinset_eq_degree, Finset.card_pos]
      exact ⟨y, by rw [mem_neighborFinset] at hz ⊢; exact hz.symm⟩
    exact lt_of_lt_of_le (ih z hz') (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hz)

lemma jstep (k : ℕ) (x : W) :
    (G.degree x : ℝ) * Real.log (G.degree x) + ∑ y ∈ G.neighborFinset x, Real.log (wk G k y)
      ≤ (G.degree x : ℝ) * Real.log (wk G (k + 1) x) := by
  rcases Nat.eq_zero_or_pos (G.degree x) with h0 | hpos
  · have : G.neighborFinset x = ∅ := by
      rw [← Finset.card_eq_zero, G.card_neighborFinset_eq_degree]; exact h0
    simp [this, h0]
  · set d : ℝ := (G.degree x : ℝ) with hd
    have hdpos : (0 : ℝ) < d := by rw [hd]; exact_mod_cast hpos
    have hmem : ∀ y ∈ G.neighborFinset x, 0 < G.degree y := by
      intro y hy
      rw [← G.card_neighborFinset_eq_degree, Finset.card_pos]
      exact ⟨x, by rw [mem_neighborFinset] at hy ⊢; exact hy.symm⟩
    set A : ℝ := ∑ y ∈ G.neighborFinset x, (wk G k y : ℝ) with hA
    have hAeq : (wk G (k + 1) x : ℝ) = A := by rw [wk_succ, hA]; push_cast; rfl
    have hApos : 0 < A := by
      rw [hA]
      obtain ⟨z, hz⟩ : (G.neighborFinset x).Nonempty := by
        rw [← Finset.card_pos, G.card_neighborFinset_eq_degree]; exact hpos
      exact Finset.sum_pos' (fun y _ => by positivity)
        ⟨z, hz, by exact_mod_cast wk_pos G k z (hmem z hz)⟩
    have hterm : ∀ y ∈ G.neighborFinset x,
        Real.log (wk G k y) - Real.log (A / d) ≤ (wk G k y : ℝ) / (A / d) - 1 := by
      intro y hy
      have := key 1 (wk G k y) (A / d) zero_le_one
        (by exact_mod_cast wk_pos G k y (hmem y hy)) (div_pos hApos hdpos)
      simpa using this
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      G.card_neighborFinset_eq_degree, ← Finset.sum_div, ← hA] at hsum
    simp only [nsmul_eq_mul] at hsum
    rw [← hd] at hsum
    have h1 : A / (A / d) = d := by field_simp
    rw [h1, Real.log_div hApos.ne' hdpos.ne'] at hsum
    rw [hAeq]
    linarith

lemma lemA (k : ℕ) :
    (k : ℝ) * ∑ x, (G.degree x : ℝ) * Real.log (G.degree x)
      ≤ ∑ x, (G.degree x : ℝ) * Real.log (wk G k x) := by
  induction k with
  | zero => simp [wk]
  | succ k ih =>
    have h := Finset.sum_le_sum (fun x (_ : x ∈ (univ : Finset W)) => jstep G k x)
    rw [Finset.sum_add_distrib, dc G (fun y => Real.log (wk G k y))] at h
    push_cast
    linarith

lemma lemB (N D : ℝ) (hN : 0 < N) (hD : D = ∑ x, (G.degree x : ℝ))
    (hcard : (Fintype.card W : ℝ) = N) (hDpos : 0 < D) :
    D * Real.log (D / N) ≤ ∑ x, (G.degree x : ℝ) * Real.log (G.degree x) := by
  have hterm : ∀ x : W, (G.degree x : ℝ) * (Real.log (D / N) - Real.log (G.degree x))
      ≤ D / N - G.degree x := by
    intro x
    rcases Nat.eq_zero_or_pos (G.degree x) with h0 | hpos
    · simp [h0]; positivity
    · have hp : (0 : ℝ) < G.degree x := by exact_mod_cast hpos
      have := key (G.degree x) (D / N) (G.degree x) hp.le (div_pos hDpos hN) hp
      calc _ ≤ _ := this
        _ = D / N - G.degree x := by field_simp
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (univ : Finset W)) => hterm x)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hcard, ← hD] at hs
  have : N * (D / N) = D := by field_simp
  linarith

lemma lemC (m : ℕ) (D : ℝ) (hD : D = ∑ x, (G.degree x : ℝ)) (hDpos : 0 < D) (s : ℝ)
    (hs : s = ∑ y, (G.degree y : ℝ) * wk G m y) :
    0 < s ∧ D * Real.log D + ∑ y, (G.degree y : ℝ) * Real.log (wk G m y) ≤ D * Real.log s := by
  have hspos : 0 < s := by
    obtain ⟨z, -, hz⟩ : ∃ z ∈ (univ : Finset W), (0 : ℝ) < G.degree z := by
      by_contra hc
      push_neg at hc
      have : D ≤ 0 := by rw [hD]; exact Finset.sum_nonpos hc
      linarith
    rw [hs]
    refine Finset.sum_pos' (fun y _ => by positivity) ⟨z, mem_univ _, ?_⟩
    have := wk_pos G m z (by exact_mod_cast hz)
    have : (0 : ℝ) < wk G m z := by exact_mod_cast this
    positivity
  refine ⟨hspos, ?_⟩
  have hterm : ∀ y : W, (G.degree y : ℝ) * (Real.log (wk G m y) - Real.log (s / D))
      ≤ (G.degree y : ℝ) * wk G m y * (D / s) - G.degree y := by
    intro y
    rcases Nat.eq_zero_or_pos (G.degree y) with h0 | hpos
    · simp [h0]
    · have hp : (0 : ℝ) < G.degree y := by exact_mod_cast hpos
      have hg : (0 : ℝ) < wk G m y := by exact_mod_cast wk_pos G m y hpos
      have := key (G.degree y) (wk G m y) (s / D) hp.le hg (div_pos hspos hDpos)
      calc _ ≤ _ := this
        _ = _ := by field_simp
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (univ : Finset W)) => hterm x)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← hs, ← hD] at hsum
  rw [Real.log_div hspos.ne' hDpos.ne'] at hsum
  have : s * (D / s) = D := by field_simp
  nlinarith

lemma walk_bound (m : ℕ) (N D : ℝ) (hN : 0 < N) (hD : D = ∑ x, (G.degree x : ℝ))
    (hcard : (Fintype.card W : ℝ) = N) (hDpos : 0 < D) :
    D * (D / N) ^ m ≤ ∑ y, (G.degree y : ℝ) * wk G m y := by
  set s := ∑ y, (G.degree y : ℝ) * wk G m y with hs
  obtain ⟨hspos, hC⟩ := lemC G m D hD hDpos s hs
  have hA := lemA G m
  have hB := lemB G N D hN hD hcard hDpos
  have h1 : D * (Real.log D + m * Real.log (D / N)) ≤ D * Real.log s := by
    have : (m : ℝ) * (D * Real.log (D / N)) ≤ (m : ℝ) * ∑ x, (G.degree x : ℝ) *
        Real.log (G.degree x) := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg m)
    nlinarith
  have h2 : Real.log D + m * Real.log (D / N) ≤ Real.log s := le_of_mul_le_mul_left h1 hDpos
  have hpos : 0 < D * (D / N) ^ m := by positivity
  rw [← Real.log_le_log_iff hpos hspos, Real.log_mul hDpos.ne' (by positivity), Real.log_pow]
  exact h2

/-- the adjacency predicate on Fin (k+1) to W -/
def P (k : ℕ) (f : Fin (k + 1) → W) : Prop := ∀ i : Fin k, G.Adj (f i.castSucc) (f i.succ)

instance (k : ℕ) : DecidablePred (P G k) := fun f => by unfold P; infer_instance

lemma fiber_card (k : ℕ) : ∀ x : W,
    (univ.filter (fun f : Fin (k + 1) → W => P G k f ∧ f 0 = x)).card = wk G k x := by
  induction k with
  | zero =>
    intro x
    show _ = 1
    rw [Finset.card_eq_one]
    refine ⟨fun _ => x, ?_⟩
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      funext i
      obtain ⟨iv, hi⟩ := i
      have : iv = 0 := by omega
      subst this
      exact h
    · rintro rfl
      exact ⟨fun i => i.elim0, rfl⟩
  | succ k ih =>
    intro x
    rw [card_eq_sum_card_fiberwise (f := fun f => f (Fin.succ 0)) (t := G.neighborFinset x)]
    · rw [wk_succ]
      refine Finset.sum_congr rfl (fun y hy => ?_)
      rw [← ih y]
      rw [mem_neighborFinset] at hy
      refine Finset.card_nbij' (fun f => Fin.tail f) (fun g => Fin.cons x g) ?_ ?_ ?_ ?_
      · intro f hf
        simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hf ⊢
        obtain ⟨⟨hP, -⟩, h1⟩ := hf
        refine ⟨fun i => ?_, h1⟩
        have := hP i.succ
        simp only [Fin.tail, ← Fin.succ_castSucc] at this ⊢
        exact this
      · intro g hg
        simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
        obtain ⟨hP, h0⟩ := hg
        refine ⟨⟨fun i => ?_, rfl⟩, by simp [h0]⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [h0, hy]
        · have := hP j
          simp only [← Fin.succ_castSucc, Fin.cons_succ]
          exact this
      · intro f hf
        simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hf
        obtain ⟨⟨-, h0⟩, -⟩ := hf
        rw [← h0]
        exact Fin.cons_self_tail f
      · intro g _
        funext i
        simp [Fin.tail]
    · intro f hf
      simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hf
      obtain ⟨hP, h0⟩ := hf
      have := hP 0
      simp only [mem_coe, mem_neighborFinset]
      rw [← h0]
      exact this

lemma homCount_path (k : ℕ) [DecidableRel (pathGraph (k + 1)).Adj] :
    homCount (pathGraph (k + 1)) G = ∑ x, wk G k x := by
  unfold homCount
  have e : (pathGraph (k + 1) →g G) ≃ {f : Fin (k + 1) → W // P G k f} :=
    { toFun := fun φ => ⟨φ, fun i => φ.map_adj (by rw [pathGraph_adj]; left; simp)⟩
      invFun := fun f => ⟨f.1, fun {u v} h => by
        rw [pathGraph_adj] at h
        rcases h with h | h
        · have := f.2 ⟨u.val, by omega⟩
          have hu : (⟨u.val, by omega⟩ : Fin k).castSucc = u := Fin.ext rfl
          have hv : (⟨u.val, by omega⟩ : Fin k).succ = v := Fin.ext (by simp [h])
          rw [hu, hv] at this
          exact this
        · have := f.2 ⟨v.val, by omega⟩
          have hu : (⟨v.val, by omega⟩ : Fin k).castSucc = v := Fin.ext rfl
          have hv : (⟨v.val, by omega⟩ : Fin k).succ = u := Fin.ext (by simp [h])
          rw [hu, hv] at this
          exact this.symm⟩
      left_inv := fun φ => rfl
      right_inv := fun f => rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  rw [card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _))]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← fiber_card G k x, Finset.filter_filter]

lemma path_edges (k : ℕ) [DecidableRel (pathGraph (k + 1)).Adj] :
    (pathGraph (k + 1)).edgeFinset.card = k := by
  have : (pathGraph (k + 1)).edgeFinset =
      (univ : Finset (Fin k)).image (fun i => s(i.castSucc, i.succ)) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [mem_edgeFinset, mem_edgeSet, pathGraph_adj, mem_image, mem_univ, true_and,
        Sym2.eq_iff]
      constructor
      · rintro (h | h)
        · exact ⟨⟨u.val, by omega⟩, Or.inl ⟨Fin.ext rfl, Fin.ext (by simp [h])⟩⟩
        · exact ⟨⟨v.val, by omega⟩, Or.inr ⟨Fin.ext rfl, Fin.ext (by simp [h])⟩⟩
      · rintro ⟨i, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
        · left; rw [← h1, ← h2]; simp
        · right; rw [← h1, ← h2]; simp
  rw [this, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro a b h
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact Fin.castSucc_injective _ h1
  · rw [Fin.ext_iff] at h1 h2
    simp at h1 h2
    omega

end OMA

theorem OMA.solution : type_of% @SidorenkoConjecture.sidorenko_conjecture.variants.path_blakley_roy := by
  intro n _ W _ _ _ G _
  set N : ℕ := Fintype.card W with hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Fintype.card_pos
  rcases n with _ | k
  · have h0 : (pathGraph 0).edgeFinset.card = 0 := by
      rw [Finset.card_eq_zero]
      refine Finset.eq_empty_of_forall_notMem (fun e _ => ?_)
      induction e using Sym2.ind with
      | _ u v => exact u.elim0
    have h1 : homCount (pathGraph 0) G = 1 := by
      unfold homCount
      rw [Fintype.card_eq_one_iff]
      exact ⟨⟨Fin.elim0, fun {a} => a.elim0⟩, fun φ => RelHom.ext (fun i => i.elim0)⟩
    rw [h0, pow_zero, homDensity, h1]
    simp
  · rw [OMA.path_edges]
    have hLbase : homDensity (completeGraph (Fin 2)) G
        = (∑ c : W, (G.degree c : ℝ)) / (N : ℝ) ^ 2 := by
      unfold homDensity
      rw [SidorenkoConjecture.homCount_completeGraph_fin_two_eq_two_mul_card_edgeFinset,
        ← G.sum_degrees_eq_twice_card_edges]
      simp only [Fintype.card_fin, ← hN]
      push_cast
      ring
    have hR : homDensity (pathGraph (k + 1)) G = (∑ x, (OMA.wk G k x : ℝ)) / (N : ℝ) ^ (k + 1) := by
      unfold homDensity
      rw [OMA.homCount_path, Fintype.card_fin, ← hN]
      push_cast
      rfl
    rw [hLbase, hR]
    set D : ℝ := ∑ c : W, (G.degree c : ℝ) with hD
    have hD0 : 0 ≤ D := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    clear_value N D
    rcases k with _ | m
    · simp [OMA.wk, ← hN]
      rw [div_self hNpos.ne']
    · have hsum : (∑ x, (OMA.wk G (m + 1) x : ℝ)) = ∑ y, (G.degree y : ℝ) * OMA.wk G m y := by
        rw [← OMA.dc G (fun y => (OMA.wk G m y : ℝ))]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [OMA.wk_succ]
        push_cast
        rfl
      rw [hsum]
      rcases hD0.eq_or_lt with hz | hDpos
      · have h00 : (0 : ℝ) ≤ (∑ y, (G.degree y : ℝ) * OMA.wk G m y) / (N : ℝ) ^ (m + 1 + 1) :=
          div_nonneg (Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _)
            (Nat.cast_nonneg _))) (pow_nonneg hNpos.le _)
        have h01 : (D / (N : ℝ) ^ 2) ^ (m + 1) = 0 := by
          rw [← hz, zero_div]; exact zero_pow (by omega)
        rw [h01]
        exact h00
      · have hb := OMA.walk_bound G m N D hNpos hD (by rw [hN]) hDpos
        rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
        have hb' : D ^ (m + 1) ≤ (∑ y, (G.degree y : ℝ) * OMA.wk G m y) * (N : ℝ) ^ m := by
          rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity)] at hb
          calc D ^ (m + 1) = D * D ^ m := by ring
            _ ≤ _ := hb
        calc D ^ (m + 1) * (N : ℝ) ^ (m + 1 + 1)
            ≤ ((∑ y, (G.degree y : ℝ) * OMA.wk G m y) * (N : ℝ) ^ m) * (N : ℝ) ^ (m + 1 + 1) :=
              mul_le_mul_of_nonneg_right hb' (by positivity)
          _ = (∑ y, (G.degree y : ℝ) * OMA.wk G m y) * ((N : ℝ) ^ 2) ^ (m + 1) := by ring
