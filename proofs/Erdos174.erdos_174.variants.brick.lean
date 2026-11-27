import FormalConjectures.ErdosProblems.«174»

-- Problem: Erdős Problem 174 — brick
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/174.lean:122 (declaration Erdos174.erdos_174.variants.brick)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Erdos174Aux

/-- Product Ramsey theorem: every `k`-colouring of a large grid `[M]^n` contains a
monochromatic combinatorial box `∏ {j0 i, j1 i}`. -/
lemma box_ramsey (k : ℕ) : ∀ n : ℕ, ∃ M : ℕ, ∀ χ : (Fin n → Fin M) → Fin k,
    ∃ j0 j1 : Fin n → Fin M, (∀ i, j0 i ≠ j1 i) ∧ ∃ col : Fin k, ∀ b : Fin n → Bool,
      χ (fun i => if b i then j1 i else j0 i) = col := by
  intro n
  induction n with
  | zero =>
    refine ⟨0, fun χ => ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, χ Fin.elim0, fun b => ?_⟩⟩
    congr 1
    funext i
    exact i.elim0
  | succ n ih =>
    obtain ⟨M, hM⟩ := ih
    let K := Fintype.card ((Fin n → Fin M) → Fin k)
    refine ⟨M + K + 1, fun χ => ?_⟩
    let ψ : Fin (M + K + 1) → (Fin n → Fin M) → Fin k := fun j u =>
      χ (Fin.cons j (fun i => Fin.castLE (by omega) (u i)))
    obtain ⟨j, j', hjj', hψ⟩ := Fintype.exists_ne_map_eq_of_card_lt ψ (by simp [K])
    obtain ⟨u0, u1, hu, col, hcol⟩ := hM (ψ j)
    refine ⟨Fin.cons j (fun i => Fin.castLE (by omega) (u0 i)),
      Fin.cons j' (fun i => Fin.castLE (by omega) (u1 i)), ?_, col, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hjj'
      · simp only [Fin.cons_succ, ne_eq]
        intro h
        exact hu i (Fin.castLE_injective _ h)
    · intro b
      have : (fun i => if b i then
            (Fin.cons j' (fun i => Fin.castLE (by omega) (u1 i)) : Fin (n + 1) → Fin (M + K + 1)) i
          else (Fin.cons j (fun i => Fin.castLE (by omega) (u0 i)) :
            Fin (n + 1) → Fin (M + K + 1)) i) =
          Fin.cons (if b 0 then j' else j)
            (fun i => Fin.castLE (by omega) (if b i.succ then u1 i else u0 i)) := by
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp
        · simp only [Fin.cons_succ]
          split_ifs <;> rfl
      rw [this]
      have h2 : χ (Fin.cons (if b 0 then j' else j)
            (fun i => Fin.castLE (by omega) (if b i.succ then u1 i else u0 i))) =
          ψ (if b 0 then j' else j) (fun i => if b i.succ then u1 i else u0 i) := rfl
      rw [h2]
      have h3 : ψ (if b 0 then j' else j) = ψ j := by
        split_ifs
        · exact hψ.symm
        · rfl
      rw [h3]
      exact hcol (fun i => b i.succ)

end Erdos174Aux

open Erdos174Aux in
theorem OMA.solution : type_of% @Erdos174.erdos_174.variants.brick := by
  intro n a
  refine ⟨?_, fun k hk => ?_⟩
  · -- finiteness
    apply Set.Finite.subset (Set.finite_range
      (fun b : Fin n → Bool => (WithLp.toLp 2 (fun i => if b i then a i else 0) :
        EuclideanSpace ℝ (Fin n))))
    intro x hx
    refine ⟨fun i => decide (x i = a i), ?_⟩
    ext i
    simp only
    rcases hx i with h | h
    · by_cases hai : x i = a i
      · simp [hai]
      · simp [h, eq_comm]
    · simp [h]
  · obtain ⟨M, hM⟩ := box_ramsey k n
    refine ⟨n * M, fun c => ?_⟩
    let s : ℝ := Real.sqrt (1 / 2)
    have hs : s ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
    let G : (Fin n → Fin M) → EuclideanSpace ℝ (Fin (n * M)) := fun J =>
      WithLp.toLp 2 (fun t => let im := finProdFinEquiv.symm t
        if im.2 = J im.1 then s * a im.1 else 0)
    obtain ⟨j0, j1, hj, col, hcol⟩ := hM (fun J => c (G J))
    let p' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n * M)) := fun x =>
      WithLp.toLp 2 (fun t => let im := finProdFinEquiv.symm t
        s * ((if im.2 = j1 im.1 then x im.1 else 0) +
          (if im.2 = j0 im.1 then a im.1 - x im.1 else 0)))
    refine ⟨fun x => p' x, ?_, col, ?_⟩
    · intro x y
      rw [edist_dist, edist_dist]
      congr 1
      rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
      congr 1
      rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [p', PiLp.toLp_apply, Equiv.symm_apply_apply, Real.dist_eq, sq_abs]
      have key : ∀ m : Fin M,
          (s * ((if m = j1 i then (x : EuclideanSpace ℝ (Fin n)) i else 0) +
              (if m = j0 i then a i - (x : EuclideanSpace ℝ (Fin n)) i else 0)) -
            s * ((if m = j1 i then (y : EuclideanSpace ℝ (Fin n)) i else 0) +
              (if m = j0 i then a i - (y : EuclideanSpace ℝ (Fin n)) i else 0))) ^ 2 =
          (if m = j1 i then (1 / 2) * ((x : EuclideanSpace ℝ (Fin n)) i -
              (y : EuclideanSpace ℝ (Fin n)) i) ^ 2 else 0) +
          (if m = j0 i then (1 / 2) * ((x : EuclideanSpace ℝ (Fin n)) i -
              (y : EuclideanSpace ℝ (Fin n)) i) ^ 2 else 0) := by
        intro m
        by_cases h1 : m = j1 i
        · have h0 : ¬ m = j0 i := fun h => hj i (h ▸ h1 ▸ rfl)
          simp only [if_pos h1, if_neg h0]
          rw [← hs]; ring
        · by_cases h0 : m = j0 i
          · simp only [if_neg h1, if_pos h0]
            rw [← hs]; ring
          · simp [h1, h0]
      rw [Finset.sum_congr rfl fun m _ => key m, Finset.sum_add_distrib,
        Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]
      ring
    · intro x
      have hx := x.2
      have : p' x = G (fun i => if decide ((x : EuclideanSpace ℝ (Fin n)) i = a i)
          then j1 i else j0 i) := by
        ext t
        simp only [p', G, PiLp.toLp_apply]
        set i := (finProdFinEquiv.symm t).1
        set m := (finProdFinEquiv.symm t).2
        have hne := hj i
        rcases hx i with h | h
        · by_cases hai : (0 : ℝ) = a i
          · simp only [h, ← hai, decide_true, if_true]
            split_ifs <;> simp
          · have : ¬ (x : EuclideanSpace ℝ (Fin n)) i = a i := by rw [h]; exact hai
            simp only [h, decide_false, Bool.false_eq_true, if_false]
            split_ifs <;> simp_all
        · simp only [h, decide_true, if_true]
          split_ifs <;> simp_all
      show c (p' x) = col
      rw [this]
      exact hcol (fun i => decide ((x : EuclideanSpace ℝ (Fin n)) i = a i))
