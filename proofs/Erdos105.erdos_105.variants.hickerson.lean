import FormalConjectures.ErdosProblems.«105»

-- Problem: Erdős Problem 105 — hickerson
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/105.lean:59 (declaration Erdos105.erdos_105.variants.hickerson)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open EuclideanGeometry

namespace OMA

noncomputable def pt (z : ℤ × ℤ) : ℝ² := !₂[(z.1 : ℝ), (z.2 : ℝ)]

lemma pt_zero (z : ℤ × ℤ) : pt z 0 = z.1 := by simp [pt]
lemma pt_one (z : ℤ × ℤ) : pt z 1 = z.2 := by simp [pt]

lemma pt_ext {u v : ℝ²} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma pt_injective : Function.Injective pt := by
  intro a b h
  have h0 := congrArg (fun u : ℝ² => u 0) h
  have h1 := congrArg (fun u : ℝ² => u 1) h
  simp only [pt_zero, pt_one, Int.cast_inj] at h0 h1
  exact Prod.ext h0 h1

lemma mem_line_of_cross (p q c : ℝ²) (hpq : p ≠ q)
    (h : (q 0 - p 0) * (c 1 - p 1) = (q 1 - p 1) * (c 0 - p 0)) :
    c ∈ line[ℝ, p, q] := by
  by_cases hx : q 0 - p 0 = 0
  · have hy : q 1 - p 1 ≠ 0 := by
      intro hy
      apply hpq
      apply pt_ext <;> linarith
    have hc : c = AffineMap.lineMap p q ((c 1 - p 1) / (q 1 - p 1)) := by
      apply pt_ext
      · simp only [AffineMap.lineMap_apply_module', PiLp.add_apply, PiLp.smul_apply,
          PiLp.sub_apply, smul_eq_mul]
        have : c 0 - p 0 = 0 := by
          rcases mul_eq_zero.mp (by rw [hx, zero_mul] at h; exact h.symm) with h' | h'
          · exact absurd h' hy
          · exact h'
        rw [hx]; linarith
      · simp only [AffineMap.lineMap_apply_module', PiLp.add_apply, PiLp.smul_apply,
          PiLp.sub_apply, smul_eq_mul]
        field_simp
        ring
    rw [hc]
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
  · have hc : c = AffineMap.lineMap p q ((c 0 - p 0) / (q 0 - p 0)) := by
      apply pt_ext
      · simp only [AffineMap.lineMap_apply_module', PiLp.add_apply, PiLp.smul_apply,
          PiLp.sub_apply, smul_eq_mul]
        field_simp
        ring
      · simp only [AffineMap.lineMap_apply_module', PiLp.add_apply, PiLp.smul_apply,
          PiLp.sub_apply, smul_eq_mul]
        field_simp
        linear_combination h
    rw [hc]
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

lemma cross_of_mem_line (p q c : ℝ²) (h : c ∈ line[ℝ, p, q]) :
    (q 0 - p 0) * (c 1 - p 1) = (q 1 - p 1) * (c 0 - p 0) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at h
  obtain ⟨t, rfl⟩ := h
  simp only [AffineMap.lineMap_apply_module', PiLp.add_apply, PiLp.smul_apply,
    PiLp.sub_apply, smul_eq_mul]
  ring

def A0 : Finset (ℤ × ℤ) :=
  {(168,0),(280,560),(280,140),(420,630),(360,240),(504,672),(280,-280),(420,0),(840,840),(0,-840)}

def B0 : Finset (ℤ × ℤ) :=
  {(0,420),(840,3360),(336,336),(280,0),(420,315),(-840,-2520),(1000000,0),(1000000,1)}

lemma key : ∀ p ∈ A0, ∀ q ∈ A0, p ≠ q → ∃ c ∈ B0,
    (q.1 - p.1) * (c.2 - p.2) = (q.2 - p.2) * (c.1 - p.1) := by
  decide +kernel

lemma disj0 : Disjoint A0 B0 := by decide +kernel

lemma cardA : A0.card = 10 := by decide +kernel
lemma cardB : B0.card = 8 := by decide +kernel

lemma triple_mem : ((168,0) : ℤ × ℤ) ∈ A0 ∧ ((280,560) : ℤ × ℤ) ∈ A0 ∧
    ((280,140) : ℤ × ℤ) ∈ A0 := by decide +kernel

end OMA

theorem OMA.solution : type_of% @Erdos105.erdos_105.variants.hickerson := by
  intro h
  have hdisj : Disjoint (OMA.A0.image OMA.pt) (OMA.B0.image OMA.pt) :=
    (Finset.disjoint_image OMA.pt_injective).mpr OMA.disj0
  have hcard : (OMA.A0.image OMA.pt).card = (OMA.B0.image OMA.pt).card + 2 := by
    rw [Finset.card_image_of_injective _ OMA.pt_injective,
      Finset.card_image_of_injective _ OMA.pt_injective, OMA.cardA, OMA.cardB]
  have hnc : ¬ Collinear ℝ ((OMA.A0.image OMA.pt : Finset ℝ²) : Set ℝ²) := by
    intro hcol
    obtain ⟨m1, m2, m3⟩ := OMA.triple_mem
    have hne : OMA.pt (168,0) ≠ OMA.pt (280,560) := by
      intro he
      have := OMA.pt_injective he
      simp at this
    have hmem := hcol.mem_affineSpan_of_mem_of_ne
      (by simpa using Finset.mem_image_of_mem OMA.pt m1)
      (by simpa using Finset.mem_image_of_mem OMA.pt m2)
      (by simpa using Finset.mem_image_of_mem OMA.pt m3) hne
    have hx := OMA.cross_of_mem_line _ _ _ hmem
    simp only [OMA.pt_zero, OMA.pt_one] at hx
    norm_num at hx
  obtain ⟨p, hp, q, hq, hpq, hB⟩ := h _ _ hdisj hcard hnc
  obtain ⟨p0, hp0, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨q0, hq0, rfl⟩ := Finset.mem_image.mp hq
  have hne : p0 ≠ q0 := fun e => hpq (e ▸ rfl)
  obtain ⟨c, hc, hcross⟩ := OMA.key p0 hp0 q0 hq0 hne
  apply hB (OMA.pt c) (Finset.mem_image_of_mem _ hc)
  apply OMA.mem_line_of_cross _ _ _ hpq
  simp only [OMA.pt_zero, OMA.pt_one]
  exact_mod_cast hcross
