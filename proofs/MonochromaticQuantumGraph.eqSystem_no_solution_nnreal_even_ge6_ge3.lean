import FormalConjectures.Paper.MonochromaticQuantumGraph

-- Problem: Monochromatic quantum graphs (inherited vertex colorings) — eqSystem no solution nnreal even ge6 ge3
-- Upstream: formal-conjectures FormalConjectures/Paper/MonochromaticQuantumGraph.lean:353 (declaration MonochromaticQuantumGraph.eqSystem_no_solution_nnreal_even_ge6_ge3)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace MQGW9

def p0 (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

def p1 (j i : ℕ) : ℕ :=
  if i % 2 = 1 then (if i + 1 = j then 0 else i + 1) else (if i = 0 then j - 1 else i - 1)

/-- Conclusion of the chord lemma. -/
def Good (N : ℕ) (s : ℕ → ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ i < N, f i < 3 ∧ (f i = 0 → f (p0 i) = 0) ∧ (f i = 1 → f (p1 N i) = 1) ∧
    (f i = 2 → f (s i) = 2)) ∧ ∃ i < N, ∃ k < N, f i ≠ f k

theorem good_odd (N : ℕ) (s : ℕ → ℕ) (hN : 6 ≤ N) (hNe : N % 2 = 0) (a b : ℕ)
    (hab : a < b) (hb : b < N) (hp : a % 2 ≠ b % 2) (hsa : s a = b) (hsb : s b = a) :
    ∃ f, Good N s f := by
  refine ⟨fun k => if k = a ∨ k = b then 2 else if a < k ∧ k < b then (a + 1) % 2 else a % 2,
    ?_, ?_⟩
  · intro i hi
    refine ⟨by dsimp only; split_ifs <;> omega, ?_, ?_, ?_⟩
    · intro h; dsimp only at h ⊢; simp only [p0] at *; split_ifs at h ⊢ <;> omega
    · intro h; dsimp only at h ⊢; simp only [p1] at *; split_ifs at h ⊢ <;> omega
    · intro h; dsimp only at h ⊢
      split_ifs at h with hh
      · rcases hh with rfl | rfl <;> simp [hsa, hsb]
      · omega
      · omega
  · have : ∃ k < 3, k ≠ a ∧ k ≠ b := by
      by_contra hc; push_neg at hc
      have h0 := hc 0 (by omega); have h1 := hc 1 (by omega); have h2 := hc 2 (by omega)
      omega
    obtain ⟨k, hk, hka, hkb⟩ := this
    refine ⟨a, by omega, k, by omega, ?_⟩
    simp only [true_or, if_true, hka, hkb, or_self, if_false]
    split_ifs <;> omega

theorem good_cross (N : ℕ) (s : ℕ → ℕ) (hN : 6 ≤ N) (hNe : N % 2 = 0) (a a' b b' : ℕ)
    (h1 : a < a') (h2 : a' < b) (h3 : b < b') (hb : b' < N) (hp : a % 2 = b % 2)
    (hp' : a' % 2 = b' % 2) (hpp : a % 2 ≠ a' % 2)
    (hsa : s a = b) (hsb : s b = a) (hsa' : s a' = b') (hsb' : s b' = a') :
    ∃ f, Good N s f := by
  refine ⟨fun k => if k = a ∨ k = a' ∨ k = b ∨ k = b' then 2 else
    if (a < k ∧ k < a') ∨ (b < k ∧ k < b') then (a + 1) % 2 else a % 2, ?_, ?_⟩
  · intro i hi
    refine ⟨by dsimp only; split_ifs <;> omega, ?_, ?_, ?_⟩
    · intro h; dsimp only at h ⊢; simp only [p0] at *; split_ifs at h ⊢ <;> omega
    · intro h; dsimp only at h ⊢; simp only [p1] at *; split_ifs at h ⊢ <;> omega
    · intro h; dsimp only at h ⊢
      split_ifs at h with hh
      · rcases hh with rfl | rfl | rfl | rfl <;> simp [hsa, hsb, hsa', hsb']
      · omega
      · omega
  · have : ∃ k < 5, k ≠ a ∧ k ≠ a' ∧ k ≠ b ∧ k ≠ b' := by
      by_contra hc; push_neg at hc
      have h0 := hc 0 (by omega); have h1 := hc 1 (by omega); have h2 := hc 2 (by omega)
      have h3 := hc 3 (by omega); have h4 := hc 4 (by omega)
      omega
    obtain ⟨k, hk, hka, hka', hkb, hkb'⟩ := this
    refine ⟨a, by omega, k, by omega, ?_⟩
    simp only [true_or, if_true, hka, hka', hkb, hkb', or_self, if_false]
    split_ifs <;> omega

theorem good_exists (N : ℕ) (s : ℕ → ℕ) (hN : 6 ≤ N) (hNe : N % 2 = 0)
    (hs : ∀ i < N, s i < N ∧ s i ≠ i ∧ s (s i) = i) : ∃ f, Good N s f := by
  by_cases hodd : ∃ a < N, s a % 2 ≠ a % 2
  · obtain ⟨a, ha, hpa⟩ := hodd
    obtain ⟨h1, h2, h3⟩ := hs a ha
    rcases lt_or_gt_of_ne h2 with h | h
    · exact good_odd N s hN hNe (s a) a h ha hpa h3 rfl
    · exact good_odd N s hN hNe a (s a) h h1 (Ne.symm hpa) rfl h3
  push_neg at hodd
  have hex : ∃ d, ∃ a < N, a < s a ∧ s a - a = d := by
    obtain ⟨h1, h2, h3⟩ := hs 0 (by omega)
    exact ⟨_, 0, by omega, by omega, rfl⟩
  obtain ⟨a, ha, has, hd⟩ := Nat.find_spec hex
  set b := s a with hb
  obtain ⟨hb1, hb2, hb3⟩ := hs a ha
  have hpar := hodd a ha
  have hab1 : a + 1 < b := by
    have : b ≠ a + 1 := by intro h; rw [← hb] at hpar; omega
    omega
  obtain ⟨hc1, hc2, hc3⟩ := hs (a + 1) (by omega)
  have hpc := hodd (a + 1) (by omega)
  set c := s (a + 1) with hc
  have hca : c ≠ a := by
    intro h; rw [h] at hc3; rw [← hb] at hpar; omega
  have hcb : c ≠ b := by
    intro h; rw [h] at hc3; omega
  rcases lt_or_gt_of_ne hca with h | h
  · exact good_cross N s hN hNe c a (a + 1) b h (by omega) hab1 hb1 (by omega) (by omega)
      (by omega) hc3 hc.symm hb.symm hb3
  · rcases lt_or_gt_of_ne hcb with h' | h'
    · exfalso
      have := Nat.find_min' hex ⟨a + 1, by omega, by omega, rfl⟩
      omega
    · exact good_cross N s hN hNe a (a + 1) b c (by omega) hab1 h' hc1 (by omega) (by omega)
        (by omega) hb.symm hb3 hc.symm hc3

end MQGW9

namespace MQGW9

/-- Fixed-point-free involution. -/
def FPI {N : ℕ} (σ : Fin N → Fin N) : Prop := ∀ x, σ x ≠ x ∧ σ (σ x) = x

def step {N : ℕ} (σ0 σ1 : Fin N → Fin N) (k : ℕ) (y : Fin N) : Fin N :=
  if k % 2 = 0 then σ0 y else σ1 y

def walk {N : ℕ} (σ0 σ1 : Fin N → Fin N) (x0 : Fin N) : ℕ → Fin N
  | 0 => x0
  | k + 1 => step σ0 σ1 k (walk σ0 σ1 x0 k)

section
variable {N : ℕ} {σ0 σ1 : Fin N → Fin N}

theorem step_fpi (h0 : FPI σ0) (h1 : FPI σ1) (k : ℕ) (y : Fin N) :
    step σ0 σ1 k y ≠ y ∧ step σ0 σ1 k (step σ0 σ1 k y) = y := by
  unfold step; split_ifs
  · exact h0 y
  · exact h1 y

theorem step_congr {k l : ℕ} (h : k % 2 = l % 2) : step σ0 σ1 k = step σ0 σ1 l := by
  funext y; unfold step; rw [h]

theorem walk_succ (x0 : Fin N) (k : ℕ) :
    walk σ0 σ1 x0 (k + 1) = step σ0 σ1 k (walk σ0 σ1 x0 k) := rfl

theorem walk_back (h0 : FPI σ0) (h1 : FPI σ1) (x0 : Fin N) (k : ℕ) :
    walk σ0 σ1 x0 k = step σ0 σ1 k (walk σ0 σ1 x0 (k + 1)) := by
  rw [walk_succ, (step_fpi h0 h1 k _).2]

theorem first_return (h0 : FPI σ0) (h1 : FPI σ1) (x0 : Fin N) :
    ∃ j, 0 < j ∧ j % 2 = 0 ∧ j ≤ N ∧ walk σ0 σ1 x0 j = walk σ0 σ1 x0 0 ∧
      ∀ i1 < j, ∀ i2 < j, walk σ0 σ1 x0 i1 = walk σ0 σ1 x0 i2 → i1 = i2 := by
  set c := walk σ0 σ1 x0 with hcdef
  have hex : ∃ j, j ≤ N ∧ ∃ i < j, c i = c j := by
    obtain ⟨k, l, hkl, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (N + 1) => c k) (by simp)
    have hkl' : (k : ℕ) ≠ l := fun h => hkl (Fin.ext h)
    rcases lt_or_gt_of_ne hkl' with h | h
    · exact ⟨l, by omega, k, h, he⟩
    · exact ⟨k, by omega, l, h, he.symm⟩
  obtain ⟨hjN, i, hij, hci⟩ := Nat.find_spec hex
  set j := Nat.find hex with hj
  have inj : ∀ i1 < j, ∀ i2 < j, c i1 = c i2 → i1 = i2 := by
    intro i1 h1 i2 h2 he
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact Nat.find_min hex h2 ⟨by omega, i1, h, he⟩
    · exact Nat.find_min hex h1 ⟨by omega, i2, h, he.symm⟩
  obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hcj' : c j' = step σ0 σ1 j' (c j) := by
    rw [hj', hcdef, walk_back h0 h1]
  have hi0 : i = 0 := by
    by_contra hi0
    obtain ⟨i', hi'⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hci' : c i' = step σ0 σ1 i' (c i) := by rw [hi', hcdef, walk_back h0 h1]
    by_cases hp : j' % 2 = i' % 2
    · rw [step_congr hp, ← hci, ← hci'] at hcj'
      have := inj i' (by omega) j' (by omega) hcj'.symm
      omega
    · have hp2 : j' % 2 = i % 2 := by omega
      rw [step_congr hp2, ← hci, ← walk_succ] at hcj'
      by_cases hij' : i = j'
      · subst hij'
        exact (step_fpi h0 h1 i (c i)).1 hcj'.symm
      · have := inj (i + 1) (by omega) j' (by omega) hcj'.symm
        omega
  subst hi0
  have hje : j % 2 = 0 := by
    by_contra hje
    have hp : j' % 2 = 0 % 2 := by omega
    rw [step_congr hp, ← hci, ← walk_succ] at hcj'
    by_cases h1j : j = 1
    · have := (step_fpi h0 h1 0 (c 0)).1
      rw [← walk_succ, ← hcdef] at this
      apply this
      rw [hci, h1j]
    · have := inj 1 (by omega) j' (by omega) hcj'.symm
      omega
  exact ⟨j, hij, hje, hjN, hci.symm, inj⟩

theorem walk_p0 (h0 : FPI σ0) (h1 : FPI σ1) (x0 : Fin N) {j i : ℕ} (hje : j % 2 = 0)
    (hi : i < j) : σ0 (walk σ0 σ1 x0 i) = walk σ0 σ1 x0 (p0 i) ∧ p0 i < j := by
  unfold p0
  split_ifs with h
  · refine ⟨?_, by omega⟩
    rw [walk_succ]; unfold step; rw [if_pos h]
  · refine ⟨?_, by omega⟩
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [walk_succ]; unfold step; rw [if_pos (by omega), (h0 _).2]; rfl

theorem walk_p1 (h0 : FPI σ0) (h1 : FPI σ1) (x0 : Fin N) {j i : ℕ} (hj0 : 0 < j)
    (hje : j % 2 = 0) (hret : walk σ0 σ1 x0 j = walk σ0 σ1 x0 0)
    (hi : i < j) : σ1 (walk σ0 σ1 x0 i) = walk σ0 σ1 x0 (p1 j i) ∧ p1 j i < j := by
  unfold p1
  split_ifs with h hh hh
  · refine ⟨?_, by omega⟩
    rw [← hret, ← hh, walk_succ]; unfold step; rw [if_neg (by omega)]
  · refine ⟨?_, by omega⟩
    rw [walk_succ]; unfold step; rw [if_neg (by omega)]
  · refine ⟨?_, by omega⟩
    subst hh
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [← hret, walk_succ]; unfold step; rw [if_neg (by omega), (h1 _).2]; rfl
  · refine ⟨?_, by omega⟩
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [walk_succ]; unfold step; rw [if_neg (by omega), (h1 _).2]; rfl

end

theorem comb {N : ℕ} (hN : 6 ≤ N) (hNe : N % 2 = 0) (σ0 σ1 σ2 : Fin N → Fin N)
    (h0 : FPI σ0) (h1 : FPI σ1) (h2 : FPI σ2) :
    ∃ f : Fin N → ℕ, (∀ x, f x < 3 ∧ (f x = 0 → f (σ0 x) = 0) ∧ (f x = 1 → f (σ1 x) = 1) ∧
      (f x = 2 → f (σ2 x) = 2)) ∧ ∃ x y, f x ≠ f y := by
  obtain ⟨j, hj0, hje, hjN, hret, inj⟩ := first_return h0 h1 (⟨0, by omega⟩ : Fin N)
  set c := walk σ0 σ1 (⟨0, by omega⟩ : Fin N) with hc
  set T := (Finset.range j).image c with hT
  have memT : ∀ y, y ∈ T ↔ ∃ i < j, c i = y := by
    intro y; simp [hT]
  rcases lt_or_eq_of_le hjN with hlt | heq
  · have : ∃ y, y ∉ T := by
      by_contra hh
      push_neg at hh
      have h1 := Finset.card_le_card (fun y _ => hh y : Finset.univ ⊆ T)
      have h2 : T.card ≤ j := by
        rw [hT]; exact Finset.card_image_le.trans (by simp)
      simp at h1
      omega
    obtain ⟨y, hy⟩ := this
    refine ⟨fun z => if z ∈ T then 0 else 1, ?_, c 0, y, ?_⟩
    · intro x
      refine ⟨by dsimp only; split_ifs <;> omega, ?_, ?_, by dsimp only; intro h; split_ifs at h <;> omega⟩
      · dsimp only
        intro hx
        have hxT : x ∈ T := by by_contra hh; rw [if_neg hh] at hx; omega
        obtain ⟨i, hi, rfl⟩ := (memT _).1 hxT
        obtain ⟨e, hlt'⟩ := walk_p0 (x0 := ⟨0, by omega⟩) h0 h1 hje hi
        rw [if_pos ((memT _).2 ⟨_, hlt', e.symm⟩)]
      · dsimp only
        intro hx
        have hxT : x ∉ T := by intro hh; rw [if_pos hh] at hx; omega
        rw [if_neg]
        intro hm
        obtain ⟨i, hi, hci⟩ := (memT _).1 hm
        apply hxT
        obtain ⟨e, hlt'⟩ := walk_p1 (x0 := ⟨0, by omega⟩) h0 h1 hj0 hje hret hi
        rw [← hc, hci, (h1 x).2] at e
        exact (memT _).2 ⟨_, hlt', e.symm⟩
    · dsimp only
      rw [if_pos ((memT _).2 ⟨0, hj0, rfl⟩), if_neg hy]
      omega
  · subst heq
    have surj : ∀ y, ∃ i, i < j ∧ c i = y := by
      have hcard : T.card = j := by
        rw [hT, Finset.card_image_of_injOn, Finset.card_range]
        intro a ha b hb hab
        exact inj a (by simpa using ha) b (by simpa using hb) hab
      have : T = Finset.univ := Finset.eq_univ_of_card _ (by simp [hcard])
      intro y
      have hy : y ∈ T := by rw [this]; exact Finset.mem_univ _
      exact (memT y).1 hy
    classical
    let idx : Fin j → ℕ := fun y => Nat.find (surj y)
    have hidx : ∀ y, idx y < j ∧ c (idx y) = y := fun y => Nat.find_spec (surj y)
    have hidxc : ∀ i < j, idx (c i) = i := fun i hi =>
      inj _ (hidx _).1 _ hi (hidx _).2
    let s : ℕ → ℕ := fun i => idx (σ2 (c i))
    have hs : ∀ i < j, s i < j ∧ s i ≠ i ∧ s (s i) = i := by
      intro i hi
      refine ⟨(hidx _).1, ?_, ?_⟩
      · intro h
        apply (h2 (c i)).1
        rw [← (hidx (σ2 (c i))).2]
        exact congrArg c h
      · show idx (σ2 (c (idx (σ2 (c i))))) = i
        rw [(hidx _).2, (h2 _).2, hidxc i hi]
    obtain ⟨g, hg, i, hi, k, hk, hne⟩ := good_exists j s hN hNe hs
    refine ⟨fun y => g (idx y), ?_, c i, c k, ?_⟩
    · intro y
      obtain ⟨hy1, hy2⟩ := hidx y
      obtain ⟨g1, g2, g3, g4⟩ := hg (idx y) hy1
      refine ⟨g1, ?_, ?_, ?_⟩
      · intro hy
        obtain ⟨e, hlt'⟩ := walk_p0 (x0 := ⟨0, by omega⟩) h0 h1 hje hy1
        rw [← hc, hy2] at e
        show g (idx (σ0 y)) = 0
        rw [e, hidxc _ hlt']
        exact g2 hy
      · intro hy
        obtain ⟨e, hlt'⟩ := walk_p1 (x0 := ⟨0, by omega⟩) h0 h1 hj0 hje hret hy1
        rw [← hc, hy2] at e
        show g (idx (σ1 y)) = 1
        rw [e, hidxc _ hlt']
        exact g3 hy
      · intro hy
        show g (idx (σ2 y)) = 2
        have := g4 hy
        rw [← hy2]
        exact this
    · show g (idx (c i)) ≠ g (idx (c k))
      rw [hidxc i hi, hidxc k hk]
      exact hne

end MQGW9

namespace MQGW9
open MonochromaticQuantumGraph
open scoped NNReal

section
variable {N D : ℕ}

theorem aux_cons (W : WeightsN N D ℝ≥0) (ι : V N → Fin D) (n : ℕ) (v : V N) (vs : List (V N)) :
    pmSumListAux W ι (n + 2) (v :: vs) =
      (vs.map (fun u => W (mkEdge v u (ι v) (ι u)) * pmSumListAux W ι n (vs.erase u))).sum := by
  cases vs <;> simp [pmSumListAux]

theorem vert_eq : ∀ N : ℕ, vertices N = List.finRange N
  | 0 => rfl
  | N + 1 => by rw [vertices, vert_eq N, List.finRange_succ]

theorem posA (W : WeightsN N D ℝ≥0) (ι : V N → Fin D) (τ : V N → V N)
    (hτ : ∀ x, τ x ≠ x ∧ τ (τ x) = x) : ∀ n (L : List (V N)), L.length = n →
    L.Pairwise (· < ·) → (∀ x ∈ L, τ x ∈ L) →
    (∀ x ∈ L, x < τ x → 0 < W (mkEdge x (τ x) (ι x) (ι (τ x)))) →
    0 < pmSumListAux W ι n L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hlen hsort hcl hpos
  rcases L with _ | ⟨v, _ | ⟨w, L⟩⟩
  · simp at hlen; subst hlen; simp [pmSumListAux]
  · exfalso
    have := hcl v (by simp)
    simp at this
    exact (hτ v).1 this
  · set vs := w :: L with hvs
    simp only [List.length_cons] at hlen
    have hLv : vs.length = L.length + 1 := by simp [hvs]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [aux_cons]
    have hv : τ v ∈ vs := (List.mem_cons.1 (hcl v (by simp))).resolve_left (hτ v).1
    have hvlt : ∀ u ∈ vs, v < u := fun u hu => List.rel_of_pairwise_cons hsort hu
    have hnd : vs.Nodup := (hsort.of_cons).imp ne_of_lt
    have hvlen : vs.length = k + 1 := by simp [hvs]; omega
    refine lt_of_lt_of_le ?_ (List.le_sum_of_mem (List.mem_map.2 ⟨τ v, hv, rfl⟩))
    refine mul_pos (hpos v (by simp) (hvlt _ hv)) ?_
    refine ih k (by omega) (vs.erase (τ v)) ?_ ?_ ?_ ?_
    · rw [List.length_erase_of_mem hv]; omega
    · exact List.Pairwise.sublist List.erase_sublist hsort.of_cons
    · intro x hx
      rw [hnd.mem_erase_iff] at hx ⊢
      obtain ⟨hx1, hx2⟩ := hx
      have hxv : x ≠ v := fun h => by have := hvlt x hx2; rw [h] at this; exact lt_irrefl _ this
      refine ⟨fun h => hxv ?_, ?_⟩
      · rw [← (hτ x).2, h, (hτ v).2]
      · rcases List.mem_cons.1 (hcl x (List.mem_cons_of_mem _ hx2)) with h | h
        · exact absurd (by rw [← h, (hτ x).2]) hx1
        · exact h
    · intro x hx
      exact hpos x (List.mem_cons_of_mem _ (List.mem_of_mem_erase hx))

theorem extractB (W : WeightsN N D ℝ≥0) (ι : V N → Fin D) : ∀ n (L : List (V N)),
    L.length = n → L.Pairwise (· < ·) → 0 < pmSumListAux W ι n L →
    ∃ τ : V N → V N, ∀ x ∈ L, τ x ∈ L ∧ τ x ≠ x ∧ τ (τ x) = x ∧
      (x < τ x → 0 < W (mkEdge x (τ x) (ι x) (ι (τ x)))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hlen hsort hpos
  rcases L with _ | ⟨v, _ | ⟨w, L⟩⟩
  · exact ⟨id, by simp⟩
  · simp at hlen; subst hlen; simp [pmSumListAux] at hpos
  · set vs := w :: L with hvs
    simp only [List.length_cons] at hlen
    have hLv : vs.length = L.length + 1 := by simp [hvs]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [aux_cons] at hpos
    have hvlt : ∀ u ∈ vs, v < u := fun u hu => List.rel_of_pairwise_cons hsort hu
    have hnd : vs.Nodup := (hsort.of_cons).imp ne_of_lt
    have hvlen : vs.length = k + 1 := by simp [hvs]; omega
    have hvn : v ∉ vs := fun h => lt_irrefl _ (hvlt v h)
    obtain ⟨t, ht, htne⟩ := List.exists_mem_ne_zero_of_sum_ne_zero hpos.ne'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
    have hW := left_ne_zero_of_mul htne
    have hP := right_ne_zero_of_mul htne
    have huv : u ≠ v := fun h => hvn (h ▸ hu)
    obtain ⟨τ', hτ'⟩ := ih k (by omega) (vs.erase u) (by rw [List.length_erase_of_mem hu]; omega)
      (List.Pairwise.sublist List.erase_sublist hsort.of_cons) (pos_iff_ne_zero.2 hP)
    refine ⟨fun x => if x = v then u else if x = u then v else τ' x, ?_⟩
    intro x hx
    by_cases hxv : x = v
    · subst hxv
      simp only [if_true, if_neg huv]
      exact ⟨List.mem_cons_of_mem _ hu, huv, trivial, fun _ => pos_iff_ne_zero.2 hW⟩
    by_cases hxu : x = u
    · subst hxu
      simp only [if_true, if_neg hxv]
      refine ⟨by simp, fun h => hxv h.symm, trivial, fun h => absurd h (not_lt.2 (le_of_lt (hvlt x hu)))⟩
    have hxe : x ∈ vs.erase u := by
      rw [hnd.mem_erase_iff]
      exact ⟨hxu, (List.mem_cons.1 hx).resolve_left hxv⟩
    obtain ⟨h1, h2, h3, h4⟩ := hτ' x hxe
    rw [hnd.mem_erase_iff] at h1
    have hτv : τ' x ≠ v := fun h => hvn (h ▸ h1.2)
    simp only [if_neg hxv, if_neg hxu, if_neg hτv, if_neg h1.1, h3]
    exact ⟨List.mem_cons_of_mem _ h1.2, h2, trivial, h4⟩

theorem chain_eq (ι : V N → Fin D) : ∀ (L : List (V N)) (a : V N),
    allEqualList ι (a :: L) → ∀ x ∈ L, ι x = ι a
  | [], _, _, x, hx => by simp at hx
  | b :: L, a, h, x, hx => by
    unfold allEqualList at h
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1.symm
    · exact (chain_eq ι L b h.2 x hx).trans h.1.symm

theorem chain_const (c : Fin D) : ∀ L : List (V N), allEqualList (fun _ => c) L
  | [] => by unfold allEqualList; exact List.IsChain.nil
  | [_] => by unfold allEqualList; exact List.IsChain.singleton _
  | _ :: b :: L => by
    unfold allEqualList
    rw [List.isChain_cons_cons]
    exact ⟨rfl, chain_const c (b :: L)⟩

end

theorem main : ∀ N D : Nat, N ≥ 6 → Even N → D ≥ 3 →
    ¬ ∃ W : WeightsN N D ℝ≥0, EqSystemN N D W := by
  rintro N D hN hEven hD ⟨W, hW⟩
  have hsort : (vertices N).Pairwise (· < ·) := by rw [vert_eq]; exact List.pairwise_lt_finRange N
  have hmem : ∀ x, x ∈ vertices N := by simp [vert_eq]
  have getσ : ∀ c : Fin D, ∃ σ : V N → V N, FPI σ ∧
      ∀ x, x < σ x → 0 < W (mkEdge x (σ x) c c) := by
    intro c
    have hp : 0 < pmSumListAux W (fun _ => c) (vertices N).length (vertices N) := by
      have := hW (fun _ => c)
      unfold pmSumN pmSumList at this
      rw [this, if_pos (show allEqual (fun _ => c) from chain_const c _)]
      exact one_pos
    obtain ⟨σ, hσ⟩ := extractB W _ _ _ rfl hsort hp
    exact ⟨σ, fun x => ⟨(hσ x (hmem x)).2.1, (hσ x (hmem x)).2.2.1⟩,
      fun x hx => (hσ x (hmem x)).2.2.2 hx⟩
  obtain ⟨σ0, h0, hp0⟩ := getσ ⟨0, by omega⟩
  obtain ⟨σ1, h1, hp1⟩ := getσ ⟨1, by omega⟩
  obtain ⟨σ2, h2, hp2⟩ := getσ ⟨2, by omega⟩
  obtain ⟨f, hf, x, y, hxy⟩ := comb hN (Nat.even_iff.1 hEven) σ0 σ1 σ2 h0 h1 h2
  let ι : V N → Fin D := fun z => ⟨f z, by have := (hf z).1; omega⟩
  let τ : V N → V N := fun z => if f z = 0 then σ0 z else if f z = 1 then σ1 z else σ2 z
  have hτ : ∀ z, τ z ≠ z ∧ τ (τ z) = z ∧
      (z < τ z → 0 < W (mkEdge z (τ z) (ι z) (ι (τ z)))) := by
    intro z
    obtain ⟨hz3, hz0, hz1, hz2⟩ := hf z
    rcases (by omega : f z = 0 ∨ f z = 1 ∨ f z = 2) with h | h | h
    · have e : τ z = σ0 z := by simp [τ, h]
      have e2 : f (σ0 z) = 0 := hz0 h
      have e3 : τ (σ0 z) = σ0 (σ0 z) := by simp [τ, e2]
      refine ⟨by rw [e]; exact (h0 z).1, by rw [e, e3]; exact (h0 z).2, ?_⟩
      rw [e]; intro hlt
      have i1 : ι z = ⟨0, by omega⟩ := Fin.ext h
      have i2 : ι (σ0 z) = ⟨0, by omega⟩ := Fin.ext e2
      rw [i1, i2]; exact hp0 z hlt
    · have e : τ z = σ1 z := by simp [τ, h]
      have e2 : f (σ1 z) = 1 := hz1 h
      have e3 : τ (σ1 z) = σ1 (σ1 z) := by simp [τ, e2]
      refine ⟨by rw [e]; exact (h1 z).1, by rw [e, e3]; exact (h1 z).2, ?_⟩
      rw [e]; intro hlt
      have i1 : ι z = ⟨1, by omega⟩ := Fin.ext h
      have i2 : ι (σ1 z) = ⟨1, by omega⟩ := Fin.ext e2
      rw [i1, i2]; exact hp1 z hlt
    · have e : τ z = σ2 z := by simp [τ, h]
      have e2 : f (σ2 z) = 2 := hz2 h
      have e3 : τ (σ2 z) = σ2 (σ2 z) := by simp [τ, e2]
      refine ⟨by rw [e]; exact (h2 z).1, by rw [e, e3]; exact (h2 z).2, ?_⟩
      rw [e]; intro hlt
      have i1 : ι z = ⟨2, by omega⟩ := Fin.ext h
      have i2 : ι (σ2 z) = ⟨2, by omega⟩ := Fin.ext e2
      rw [i1, i2]; exact hp2 z hlt
  have hpos := posA W ι τ (fun z => ⟨(hτ z).1, (hτ z).2.1⟩) _ (vertices N) rfl hsort
    (fun z _ => hmem _) (fun z _ => (hτ z).2.2)
  have hne : ¬ allEqual ι := by
    intro hall
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have key : ∀ z, ι z = ι 0 := by
      intro z
      by_cases hz : z = 0
      · rw [hz]
      · have hz' : z ∈ (vertices N').map Fin.succ := by
          have := hmem z
          rw [vertices] at this
          exact (List.mem_cons.1 this).resolve_left hz
        exact chain_eq ι _ 0 hall z hz'
    apply hxy
    have := (key x).trans (key y).symm
    exact congrArg Fin.val this
  have := hW ι
  unfold pmSumN pmSumList at this
  rw [this, if_neg hne] at hpos
  exact lt_irrefl _ hpos

end MQGW9

theorem OMA.solution : type_of% @MonochromaticQuantumGraph.eqSystem_no_solution_nnreal_even_ge6_ge3 := by
  exact MQGW9.main
