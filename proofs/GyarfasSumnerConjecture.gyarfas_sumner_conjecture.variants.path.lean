import FormalConjectures.Wikipedia.GyarfasSumnerConjecture

open SimpleGraph

namespace OMA

variable {V : Type*}

def gyarfas (t k : ℕ) : ℕ :=
  match k with
  | 0 => 0
  | k + 1 => 1 + (t - 2) * gyarfas t k

theorem gyarfas_mono (t : ℕ) {k k' : ℕ} (h : k ≤ k') : gyarfas t k ≤ gyarfas t k' := by
  induction k' generalizing k with
  | zero =>
      cases Nat.eq_zero_of_le_zero h
      exact le_rfl
  | succ k' ih =>
      cases k with
      | zero => simp [gyarfas]
      | succ k =>
          have hk := ih (Nat.le_of_succ_le_succ h)
          simpa [gyarfas] using Nat.add_le_add_left (Nat.mul_le_mul_left (t - 2) hk) 1

theorem gyarfas_succ (t k : ℕ) : gyarfas t (k + 1) = 1 + (t - 2) * gyarfas t k := rfl

def IsInducedPathFrom (G : SimpleGraph V) (v : V) (ℓ : ℕ) : Prop :=
  ∃ (hℓ : 0 < ℓ) (f : Fin ℓ → V), f ⟨0, hℓ⟩ = v ∧ Function.Injective f ∧
    ∀ i j, G.Adj (f i) (f j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val

theorem isInducedPathFrom_isIndContained {G : SimpleGraph V} {v : V} {ℓ : ℕ}
    (h : IsInducedPathFrom G v ℓ) : IsIndContained (pathGraph ℓ) G := by
  obtain ⟨_, f, _, hinj, hadj⟩ := h
  exact ⟨⟨f, hinj⟩, fun {i j} ↦ by rw [pathGraph_adj]; exact hadj i j⟩

theorem not_isInducedPathFrom_of_not_contained {G : SimpleGraph V} {t : ℕ}
    (h : ¬ IsIndContained (pathGraph t) G) (v : V) : ¬ IsInducedPathFrom G v t :=
  fun hv ↦ h (isInducedPathFrom_isIndContained hv)

theorem chromaticNumber_induce_le {G : SimpleGraph V} (s : Set V) :
    (G.induce s).chromaticNumber ≤ G.chromaticNumber :=
  chromaticNumber_mono_of_hom (Embedding.induce s).toHom

theorem colorable_of_components {G : SimpleGraph V} {n : ℕ}
    (h : ∀ v, (G.induce {w | G.Reachable v w}).Colorable n) : G.Colorable n := by
  classical
  have hset (v : V) : {w | G.connectedComponentMk w = G.connectedComponentMk v} =
      {w | G.Reachable v w} := by
    ext w
    simp [ConnectedComponent.eq, reachable_comm]
  have hcol : ∀ c : G.ConnectedComponent,
      (G.induce {w | G.connectedComponentMk w = c}).Colorable n := by
    intro c
    refine ConnectedComponent.ind (fun v ↦ ?_) c
    exact hset v ▸ h v
  let chosen (c : G.ConnectedComponent) :
      (G.induce {w | G.connectedComponentMk w = c}).Coloring (Fin n) :=
    Classical.choice (hcol c)
  let color : V → Fin n := fun v ↦ chosen (G.connectedComponentMk v) ⟨v, rfl⟩
  refine ⟨⟨color, ?_⟩⟩
  intro a b hab
  have hmk := ConnectedComponent.connectedComponentMk_eq_of_adj hab
  have hab' : (G.induce {w | G.connectedComponentMk w = G.connectedComponentMk a}).Adj
      ⟨a, rfl⟩ ⟨b, by simp [hmk]⟩ := by simpa [induce_adj] using hab
  have hne := (chosen (G.connectedComponentMk a)).valid hab'
  have happly (c : G.ConnectedComponent) (hc : G.connectedComponentMk b = c)
      (hx : G.connectedComponentMk b = c) :
      chosen c ⟨b, hx⟩ = chosen (G.connectedComponentMk b) ⟨b, rfl⟩ := by
    cases hc
    rfl
  have hbcolor := happly (G.connectedComponentMk a) hmk.symm (by simp [hmk])
  simp only [color, completeGraph_eq_top, top_adj] at hne ⊢
  rw [← hbcolor]
  exact hne

theorem reachable_of_mem_support {G : SimpleGraph V} {a b t : V} (w : G.Walk a b)
    (ht : t ∈ w.support) : G.Reachable a t := by
  induction w with
  | nil =>
      simp at ht
      subst ht
      exact Reachable.rfl
  | cons h w ih =>
      simp only [Walk.support_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact Reachable.rfl
      · exact (Adj.reachable h).trans (ih ht)

theorem extend_induced_path {G : SimpleGraph V} {v u : V} {C : Set V} {m : ℕ}
    (hvu : G.Adj v u) (hfar : ∀ x ∈ C, ¬ G.Adj v x) (_huC : u ∉ C) (hvC : v ∉ C)
    (hf : IsInducedPathFrom (G.induce (insert u C)) ⟨u, by simp⟩ m) :
    IsInducedPathFrom G v (m + 1) := by
  obtain ⟨hm, f, hf0, hinj, hadj⟩ := hf
  let g : Fin (m + 1) → V := Fin.cases v (fun i ↦ (f i).1)
  have hg0 : g 0 = v := rfl
  have hgs (i : Fin m) : g i.succ = (f i).1 := rfl
  have hvne : v ≠ u := G.ne_of_adj hvu
  refine ⟨Nat.succ_pos _, g, hg0, ?_, ?_⟩
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j =>
            rcases Set.mem_insert_iff.mp (f j).2 with hfu | hfc
            · have hfj : f j = ⟨u, by simp⟩ := Subtype.ext hfu
              have hj0 : j = ⟨0, hm⟩ := hinj (hfj.trans hf0.symm)
              have hv_eq : v = u := by
                rw [hg0] at hij
                rw [hgs, hj0, hf0] at hij
                exact hij
              exact (hvne hv_eq).elim
            · exact (hvC (by rw [hg0, hgs] at hij; exact hij.symm ▸ hfc)).elim
    | succ i =>
        cases j using Fin.cases with
        | zero =>
            rcases Set.mem_insert_iff.mp (f i).2 with hfu | hfc
            · have hfi : f i = ⟨u, by simp⟩ := Subtype.ext hfu
              have hi0 : i = ⟨0, hm⟩ := hinj (hfi.trans hf0.symm)
              have hv_eq : u = v := by
                rw [hg0] at hij
                rw [hgs, hi0, hf0] at hij
                exact hij
              exact (hvne hv_eq.symm).elim
            · exact (hvC (by rw [hg0, hgs] at hij; exact hij ▸ hfc)).elim
        | succ j =>
            exact congrArg Fin.succ (hinj (Subtype.ext (by simpa [hgs] using hij)))
  · intro i j
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => simp [hg0]
        | succ j =>
            constructor
            · intro h
              rcases Set.mem_insert_iff.mp (f j).2 with hfu | hfc
              · have hfj : f j = ⟨u, by simp⟩ := Subtype.ext hfu
                have hj0 : j = ⟨0, hm⟩ := hinj (hfj.trans hf0.symm)
                simp [hj0]
              · exact (hfar _ hfc (by simpa [hg0, hgs] using h)).elim
            · intro h
              have hj0 : j = ⟨0, hm⟩ := by
                apply Fin.ext
                rcases h with h | h
                · have hnat : (0 : ℕ) + 1 = j.val + 1 := by
                    simpa [Fin.val_zero, Fin.val_succ] using h
                  exact (Nat.add_right_cancel hnat).symm
                · have hnat : j.val + 2 = 0 := by
                    simpa [Fin.val_zero, Fin.val_succ] using h
                  omega
              simpa [hg0, hgs, show f j = ⟨u, by simp⟩ from hj0.symm ▸ hf0] using hvu
    | succ i =>
        cases j using Fin.cases with
        | zero =>
            constructor
            · intro h
              rcases Set.mem_insert_iff.mp (f i).2 with hfu | hfc
              · have hfi : f i = ⟨u, by simp⟩ := Subtype.ext hfu
                have hi0 : i = ⟨0, hm⟩ := hinj (hfi.trans hf0.symm)
                simp [hi0]
              · exact (hfar _ hfc (by simpa [hg0, hgs] using h.symm)).elim
            · intro h
              have hi0 : i = ⟨0, hm⟩ := by
                apply Fin.ext
                rcases h with h | h
                · have hnat : i.val + 2 = 0 := by
                    simpa [Fin.val_zero, Fin.val_succ] using h
                  omega
                · have hnat : (0 : ℕ) + 1 = i.val + 1 := by
                    simpa [Fin.val_zero, Fin.val_succ] using h
                  exact (Nat.add_right_cancel hnat).symm
              simpa [hg0, hgs, show f i = ⟨u, by simp⟩ from hi0.symm ▸ hf0] using hvu.symm
        | succ j =>
            simpa [hgs, induce_adj, Fin.val_succ] using hadj i j

theorem support_mem_of_induce {G : SimpleGraph V} {s : Set V} {a b : s}
    (w : (G.induce s).Walk a b) {t : V}
    (ht : t ∈ (w.map (Embedding.induce s).toHom).support) : t ∈ s := by
  have heq := Walk.support_map (Embedding.induce s).toHom w
  rw [heq, List.mem_map] at ht
  obtain ⟨u, _, rfl⟩ := ht
  exact u.2

theorem support_subset_of_cut {G : SimpleGraph V} {s : Set V} {a b : V}
    (w : G.Walk a b) (ha : a ∈ s) (hcut : ∀ {x y}, G.Adj x y → (x ∈ s ↔ y ∈ s)) :
    ∀ x ∈ w.support, x ∈ s := by
  induction w with
  | nil =>
      intro x hx
      simp at hx
      subst hx
      exact ha
  | cons h w ih =>
      intro x hx
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha
      · exact ih ((hcut h).mp ha) x hx

theorem singleton_preconnected {G : SimpleGraph V} (u : V) :
    (G.induce ({u} : Set V)).Preconnected := by
  intro a b
  have ha : (a : V) = u := a.2
  have hb : (b : V) = u := b.2
  have hab : a = b := Subtype.ext (ha.trans hb.symm)
  subst hab
  exact Reachable.rfl

theorem connected_chi_le_all (c : ℕ) :
    ∀ ℓ, 2 ≤ ℓ → ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
      (∀ v, (G.induce (G.neighborSet v)).chromaticNumber ≤ c) →
      (∃ v, ¬ IsInducedPathFrom G v ℓ) →
      G.chromaticNumber ≤ (1 + (ℓ - 2) * c : ℕ) := by
  classical
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | h ℓ ih =>
    intro hℓ V _ _ G _ hconn hN ⟨v, hv⟩
    by_cases h3 : 3 ≤ ℓ
    · let N : Set V := G.neighborSet v
      let Far : Set V := {w | w ≠ v ∧ w ∉ N}
      let m : ℕ := 1 + (ℓ - 3) * c
      have hsub : ℓ - 2 = ℓ - 3 + 1 := by
        calc ℓ - 2 = (ℓ - 3 + 3) - 2 := by rw [Nat.sub_add_cancel h3]
          _ = ℓ - 3 + (3 - 2) := Nat.add_sub_assoc (by decide : 2 ≤ 3) _
          _ = ℓ - 3 + 1 := by simp
      have hmbound : c + m = 1 + (ℓ - 2) * c := by
        simp only [m, hsub]
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have hFar : (G.induce Far).chromaticNumber ≤ (m : ℕ) := by
        rw [chromaticNumber_le_iff_colorable]
        refine colorable_of_components ?_
        intro x
        let GF := G.induce Far
        let C : Set V := {y | ∃ hy : y ∈ Far, GF.Reachable x ⟨y, hy⟩}
        have hxC : (x : V) ∈ C := ⟨x.2, Reachable.rfl⟩
        have hvC : v ∉ C := by
          intro h
          obtain ⟨hy, _⟩ := h
          exact hy.1 rfl
        have htouch : ∃ u ∈ N, ∃ y ∈ C, G.Adj u y := by
          by_contra hnone
          push_neg at hnone
          have hcut : ∀ {a b}, G.Adj a b → (a ∈ C ↔ b ∈ C) := by
            intro a b hab
            constructor
            · intro hmem
              obtain ⟨haF, hra⟩ := hmem
              have hbne : b ≠ v := by
                intro hbv
                exact haF.2 (by simpa [N, hbv] using hab.symm)
              have hbN : b ∉ N := fun hb ↦ hnone b hb a ⟨haF, hra⟩ hab.symm
              have hbFar : b ∈ Far := ⟨hbne, hbN⟩
              have hgf : GF.Adj ⟨a, haF⟩ ⟨b, hbFar⟩ := by simpa [GF, induce_adj] using hab
              exact ⟨hbFar, hra.trans (Adj.reachable hgf)⟩
            · intro hmem
              obtain ⟨hbF, hrb⟩ := hmem
              have hane : a ≠ v := by
                intro hav
                exact hbF.2 (by simpa [N, hav] using hab)
              have haN : a ∉ N := fun hNa ↦ hnone a hNa b ⟨hbF, hrb⟩ hab
              have haFar : a ∈ Far := ⟨hane, haN⟩
              have hgf : GF.Adj ⟨b, hbF⟩ ⟨a, haFar⟩ := by simpa [GF, induce_adj] using hab.symm
              exact ⟨haFar, hrb.trans (Adj.reachable hgf)⟩
          obtain ⟨w⟩ := hconn.preconnected (x : V) v
          exact hvC (support_subset_of_cut w hxC hcut v w.end_mem_support)
        obtain ⟨u, huN, y, hyC, huy⟩ := htouch
        have huC : u ∉ C := by
          intro hu
          obtain ⟨hy, _⟩ := hu
          exact hy.2 huN
        have hvu : G.Adj v u := by simpa [N] using huN
        have hCpre : (G.induce C).Preconnected := by
          intro p q
          obtain ⟨pF, hp⟩ := p.2
          obtain ⟨qF, hq⟩ := q.2
          refine (hp.symm.trans hq).elim fun w ↦ ?_
          have hsup : ∀ t ∈ (w.map (Embedding.induce Far).toHom).support, t ∈ C := by
            intro t ht
            have htF := support_mem_of_induce w ht
            have heq := Walk.support_map (Embedding.induce Far).toHom w
            rw [heq, List.mem_map] at ht
            obtain ⟨s, hs, rfl⟩ := ht
            exact ⟨s.2, hp.trans (reachable_of_mem_support w hs)⟩
          exact ⟨(w.map (Embedding.induce Far).toHom).induce C hsup⟩
        have hSconn : (G.induce (insert u C)).Connected := by
          rw [Set.insert_eq]
          exact G.connected_induce_union (singleton_preconnected u) hCpre
            (Set.mem_singleton _) hyC huy
        have hNS : ∀ w : ↑(insert u C),
            ((G.induce (insert u C)).induce
              ((G.induce (insert u C)).neighborSet w)).chromaticNumber ≤ c := by
          intro w
          let G' := G.induce (insert u C)
          let φ : (G'.induce (G'.neighborSet w)) →g G.induce (G.neighborSet w.1) := {
            toFun := fun z ↦ ⟨z.1.1, z.2⟩
            map_rel' := fun {_ _} h ↦ h }
          exact (chromaticNumber_mono_of_hom φ).trans (hN w.1)
        have hno : ¬ IsInducedPathFrom (G.induce (insert u C)) ⟨u, by simp⟩ (ℓ - 1) := by
          intro hpath
          apply hv
          have hfar : ∀ z ∈ C, ¬ G.Adj v z := by
            intro z hz
            obtain ⟨hzF, _⟩ := hz
            simpa [N] using hzF.2
          simpa [Nat.sub_add_cancel (by omega : 1 ≤ ℓ)] using
            extend_induced_path hvu hfar huC hvC hpath
        have hchiS := ih (ℓ - 1) (by omega) (by omega) (G.induce (insert u C)) hSconn hNS
          ⟨⟨u, by simp⟩, hno⟩
        have hnum : 1 + ((ℓ - 1) - 2) * c ≤ m := by
          have : (ℓ - 1) - 2 = ℓ - 3 := by rw [Nat.sub_sub]
          simp [m, this]
        have hcomp : (GF.induce {w | GF.Reachable x w}).chromaticNumber ≤
            (G.induce (insert u C)).chromaticNumber := by
          let φ : (GF.induce {w | GF.Reachable x w}) →g G.induce (insert u C) := {
            toFun := fun p ↦ ⟨p.1.1, Or.inr ⟨p.1.2, p.2⟩⟩
            map_rel' := fun {_ _} h ↦ by simpa [GF, induce_adj] using h }
          exact chromaticNumber_mono_of_hom φ
        exact chromaticNumber_le_iff_colorable.mp
          (hcomp.trans (hchiS.trans (by exact_mod_cast hnum)))
      obtain ⟨colN⟩ := chromaticNumber_le_iff_colorable.mp (hN v)
      obtain ⟨colF⟩ := chromaticNumber_le_iff_colorable.mp hFar
      rw [hmbound.symm, chromaticNumber_le_iff_colorable]
      let color : V → Fin (c + m) := fun z ↦
        if hz : z = v then ⟨c, by simp [m]⟩
        else if hzN : z ∈ N then ⟨colN ⟨z, hzN⟩, by have := (colN ⟨z, hzN⟩).isLt; omega⟩
        else ⟨c + (colF ⟨z, ⟨hz, hzN⟩⟩).1, by
          have := (colF ⟨z, ⟨hz, hzN⟩⟩).isLt
          omega⟩
      refine ⟨⟨color, ?_⟩⟩
      intro a b hab
      by_cases ha : a = v <;> by_cases hb : b = v
      · exact (G.ne_of_adj hab (ha.trans hb.symm)).elim
      · have hbN : b ∈ N := by simpa [N, ha] using hab
        exact Fin.ne_of_val_ne (by
          have hcv : (color a : ℕ) = c := by simp [color, ha, m]
          have hcb : (color b : ℕ) = colN ⟨b, hbN⟩ := by simp [color, hb, hbN]
          have hlt := (colN ⟨b, hbN⟩).isLt
          omega)
      · have haN : a ∈ N := by simpa [N, hb] using hab.symm
        exact Fin.ne_of_val_ne (by
          have hca : (color a : ℕ) = colN ⟨a, haN⟩ := by simp [color, ha, haN]
          have hcb : (color b : ℕ) = c := by simp [color, hb, m]
          have hlt := (colN ⟨a, haN⟩).isLt
          omega)
      · by_cases haN : a ∈ N <;> by_cases hbN : b ∈ N
        · have hne := colN.valid (show (G.induce N).Adj ⟨a, haN⟩ ⟨b, hbN⟩ by
            simpa [induce_adj] using hab)
          exact Fin.ne_of_val_ne (by
            have hca : (color a : ℕ) = colN ⟨a, haN⟩ := by simp [color, ha, haN]
            have hcb : (color b : ℕ) = colN ⟨b, hbN⟩ := by simp [color, hb, hbN]
            omega)
        · exact Fin.ne_of_val_ne (by
            have hca : (color a : ℕ) = colN ⟨a, haN⟩ := by simp [color, ha, haN]
            have hcb : (color b : ℕ) = c + colF ⟨b, ⟨hb, hbN⟩⟩ := by simp [color, hb, hbN]
            have hlt := (colN ⟨a, haN⟩).isLt
            omega)
        · exact Fin.ne_of_val_ne (by
            have hca : (color a : ℕ) = c + colF ⟨a, ⟨ha, haN⟩⟩ := by simp [color, ha, haN]
            have hcb : (color b : ℕ) = colN ⟨b, hbN⟩ := by simp [color, hb, hbN]
            have hlt := (colN ⟨b, hbN⟩).isLt
            omega)
        · have hne := colF.valid (show (G.induce Far).Adj ⟨a, ⟨ha, haN⟩⟩ ⟨b, ⟨hb, hbN⟩⟩ by
            simpa [induce_adj] using hab)
          exact Fin.ne_of_val_ne (by
            have hca : (color a : ℕ) = c + colF ⟨a, ⟨ha, haN⟩⟩ := by simp [color, ha, haN]
            have hcb : (color b : ℕ) = c + colF ⟨b, ⟨hb, hbN⟩⟩ := by simp [color, hb, hbN]
            omega)
    · have hℓ2 : ℓ = 2 := by omega
      subst hℓ2
      have hbot : G = ⊥ := by
        have hiso : ∀ u, ¬ G.Adj v u := by
          intro u hu
          apply hv
          have hne : v ≠ u := G.ne_of_adj hu
          let f : Fin 2 → V := fun i ↦ if i.val = 0 then v else u
          refine ⟨by decide, f, by simp [f], ?_, ?_⟩
          · intro i j hij
            fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;>
              first | rfl | exact (hne hij).elim | exact (hne hij.symm).elim
          · intro i j
            fin_cases i <;> fin_cases j <;> simp [f, hu, hu.symm, hne, hne.symm]
        ext a b
        simp only [bot_adj, iff_false]
        intro hab
        have ha : a = v := by
          obtain ⟨w⟩ := hconn.preconnected v a
          cases w with
          | nil => rfl
          | @cons _ u _ h _ => exact (hiso u h).elim
        have hb : b = v := by
          obtain ⟨w⟩ := hconn.preconnected v b
          cases w with
          | nil => rfl
          | @cons _ u _ h _ => exact (hiso u h).elim
        exact G.ne_of_adj hab (ha.trans hb.symm)
      rw [show (1 + (2 - 2) * c : ℕ) = 1 by simp, chromaticNumber_le_iff_colorable,
        colorable_one_iff]
      exact hbot

theorem chi_le_all (t : ℕ) (ht : 2 ≤ t) :
    ∀ k, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.cliqueNum ≤ k → ¬ IsIndContained (pathGraph t) G →
        G.chromaticNumber ≤ gyarfas t k := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro V _ _ G _ hk hfree
    cases k with
    | zero =>
        have hempty : IsEmpty V := by
          constructor
          intro v
          have h1 : 1 ≤ G.cliqueNum := by
            have hc : G.IsClique ({v} : Finset V) := IsClique.of_subsingleton (by simp)
            simpa using hc.card_le_cliqueNum
          omega
        rw [chromaticNumber_le_iff_colorable, gyarfas]
        exact ⟨⟨isEmptyElim, fun {a} ↦ isEmptyElim a⟩⟩
    | succ k =>
        have hNchi : ∀ v, (G.induce (G.neighborSet v)).chromaticNumber ≤ gyarfas t k := by
          intro v
          have hfreeN : ¬ IsIndContained (pathGraph t) (G.induce (G.neighborSet v)) := by
            intro ⟨f⟩
            exact hfree ⟨Embedding.comp (Embedding.induce _) f⟩
          have hle : (G.induce (G.neighborSet v)).cliqueNum ≤ k := by
            classical
            obtain ⟨s, hs⟩ := (G.induce (G.neighborSet v)).exists_isNClique_cliqueNum
            let img := s.map (⟨Subtype.val, Subtype.val_injective⟩ : _ ↪ V)
            have hs' : G.IsNClique (G.induce (G.neighborSet v)).cliqueNum img :=
              (isNClique_induce_iff _ _ _).1 hs
            have hvmem : v ∉ img := by
              intro h
              obtain ⟨x, _, hxv⟩ := Finset.mem_map.mp h
              exact (G.ne_of_adj x.2 hxv.symm).elim
            have hcl : G.IsClique (insert v img : Finset V) := by
              intro a ha b hb hne
              simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
              rcases ha with ha | ha <;> rcases hb with hb | hb
              · exact (hne (ha.trans hb.symm)).elim
              · rw [ha]
                obtain ⟨x, _, hxb⟩ := Finset.mem_map.mp hb
                exact hxb ▸ x.2
              · rw [hb]
                obtain ⟨x, _, hxa⟩ := Finset.mem_map.mp ha
                exact hxa ▸ x.2.symm
              · exact hs'.isClique ha hb hne
            have hcard : (insert v img).card =
                (G.induce (G.neighborSet v)).cliqueNum + 1 := by
              rw [Finset.card_insert_of_notMem hvmem, hs'.card_eq]
            have := hcl.card_le_cliqueNum
            omega
          exact ih k (by omega) _ hle hfreeN
        rw [gyarfas_succ]
        rw [chromaticNumber_le_iff_colorable]
        refine colorable_of_components ?_
        intro v
        have hconn : (G.induce {w | G.Reachable v w}).Connected := by
          haveI : Nonempty {w | G.Reachable v w} := ⟨⟨v, Reachable.rfl⟩⟩
          exact ⟨fun a b ↦ (a.2.symm.trans b.2).elim fun w ↦
            ⟨w.induce _ (fun t ht ↦ a.2.trans (reachable_of_mem_support w ht))⟩⟩
        have hfreeC : ¬ IsIndContained (pathGraph t)
            (G.induce {w | G.Reachable v w}) := by
          intro ⟨f⟩
          exact hfree ⟨Embedding.comp (Embedding.induce _) f⟩
        have hNC : ∀ w, ((G.induce {w | G.Reachable v w}).induce
            ((G.induce {w | G.Reachable v w}).neighborSet w)).chromaticNumber ≤
            gyarfas t k := by
          intro w
          let GC := G.induce {w | G.Reachable v w}
          let φ : (GC.induce (GC.neighborSet w)) →g G.induce (G.neighborSet w.1) := {
            toFun := fun z ↦ ⟨z.1.1, z.2⟩
            map_rel' := fun {_ _} h ↦ h }
          exact (chromaticNumber_mono_of_hom φ).trans (hNchi w.1)
        have hchi := connected_chi_le_all (gyarfas t k) t (by omega)
          (G.induce {w | G.Reachable v w}) hconn hNC
          ⟨⟨v, Reachable.rfl⟩, not_isInducedPathFrom_of_not_contained hfreeC _⟩
        refine chromaticNumber_le_iff_colorable.mp ?_
        convert hchi using 1

end OMA

theorem OMA.solution :
    type_of% @GyarfasSumnerConjecture.gyarfas_sumner_conjecture.variants.path := by
  intro n
  classical
  by_cases hn : 2 ≤ n
  · refine ⟨OMA.gyarfas n, ?_⟩
    intro V _ _ G _ hfree
    simpa using OMA.chi_le_all n hn G.cliqueNum G (le_rfl) hfree
  · refine ⟨fun _ ↦ 0, ?_⟩
    intro V _ _ G _ hfree
    have hsmall : n = 0 ∨ n = 1 := by omega
    have hembed : IsIndContained (pathGraph n) G ∨ IsEmpty V := by
      rcases hsmall with rfl | rfl
      · left
        exact ⟨⟨⟨Fin.elim0, fun a ↦ Fin.elim0 a⟩, fun {a} ↦ Fin.elim0 a⟩⟩
      · by_cases hV : Nonempty V
        · left
          inhabit V
          exact ⟨⟨⟨fun _ ↦ default, by intro i j _; fin_cases i; fin_cases j; rfl⟩,
            fun {i j} ↦ by fin_cases i; fin_cases j; simp [pathGraph_adj]⟩⟩
        · right
          exact not_nonempty_iff.mp hV
    rcases hembed with hembed | hempty
    · exact (hfree hembed).elim
    · rw [chromaticNumber_le_iff_colorable]
      exact ⟨⟨isEmptyElim, fun {a} ↦ isEmptyElim a⟩⟩

