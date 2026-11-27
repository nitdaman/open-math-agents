import FormalConjectures.ErdosProblems.«650»

/-! A pair of consecutive multiples identifies its common difference. -/

-- Credit: @Halldon
namespace Erdos650Suranyi

-- An image with at least k elements supplies k distinct representatives.
private lemma representatives (A : Finset ℕ) (g : ℕ → ℕ) (k : ℕ)
    (hk : k ≤ (A.image g).card) :
    ∃ a : Fin k → ℕ, Function.Injective a ∧ (∀ i, a i ∈ A) ∧
      Function.Injective (g ∘ a) := by
  classical
  let hcard : k ≤ Fintype.card ↥(A.image g) := by simpa using hk
  let b : Fin k ↪ ↥(A.image g) :=
    (Fin.castLEEmb hcard).trans (Fintype.equivFin ↥(A.image g)).symm.toEmbedding
  have hb (i : Fin k) : ∃ u ∈ A, g u = (b i : ℕ) :=
    Finset.mem_image.mp (b i).property
  choose a ha hab using hb
  have hga : Function.Injective (g ∘ a) := by
    intro i j he
    apply b.injective
    apply Subtype.ext
    simpa only [Function.comp_apply, hab] using he
  exact ⟨a, fun i j h => hga (congrArg g h), ha, hga⟩

-- The first multiple strictly beyond x is at most x + a.
private lemma first_bounds {x : ℝ} (hx : 0 ≤ x) {a : ℕ} (ha : 0 < a) :
    let b := a * (⌊x⌋₊ / a) + a
    x < (b : ℝ) ∧ (b : ℝ) ≤ x + a := by
  have hm := Nat.mod_add_div ⌊x⌋₊ a
  have hr := Nat.mod_lt ⌊x⌋₊ ha
  have hl : ⌊x⌋₊ + 1 ≤ a * (⌊x⌋₊ / a) + a := by omega
  have hu : a * (⌊x⌋₊ / a) + a ≤ ⌊x⌋₊ + a := by omega
  constructor
  · exact lt_of_lt_of_le (Nat.lt_floor_add_one x) (by exact_mod_cast hl)
  · calc
      ((a * (⌊x⌋₊ / a) + a : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) + a := by exact_mod_cast hu
      _ ≤ x + a := by linarith [Nat.floor_le hx]

end Erdos650Suranyi

theorem OMA.solution : type_of% @Erdos650.erdos_650.variants.erdos_suranyi := by
  classical
  intro m
  let k := ⌈Real.sqrt m⌉₊
  apply (Nat.le_ceil (Real.sqrt (m : ℝ))).trans
  exact_mod_cast (show k ≤ Erdos650.f m from by
    unfold Erdos650.f
    apply le_csSup
    · refine ⟨m, ?_⟩
      intro r hr
      obtain ⟨a, _, ha, _, hA, _⟩ :=
        hr m (Finset.Icc 1 m) (fun _ h => h) (by simp) 1 le_rfl
      let e : Fin r → ↥(Finset.Icc 1 m) := fun i => ⟨a i, hA i⟩
      have he : Function.Injective e := fun _ _ h => ha (congrArg Subtype.val h)
      simpa using Fintype.card_le_of_injective e he
    · intro N A hA hcard x hx
      let u : ℕ → ℕ := fun a => a * (⌊x⌋₊ / a) + a
      let v : ℕ → ℕ := fun a => if a = N then u a else u a + a
      have hpos {a} (ha : a ∈ A) := Finset.mem_Icc.mp (hA ha)
      have hpair : Set.InjOn (fun a => (u a, v a)) (↑A : Set ℕ) := by
        intro a ha b hb he
        have hu : u a = u b := congrArg Prod.fst he
        have hv : v a = v b := congrArg Prod.snd he
        have pa := (hpos ha).1
        have pb := (hpos hb).1
        change (if a = N then u a else u a + a) = (if b = N then u b else u b + b) at hv
        split_ifs at hv <;> omega
      have hcount : m ≤ (A.image u).card * (A.image v).card := by
        rw [← hcard, ← Finset.card_product]
        apply Finset.card_le_card_of_injOn (fun a => (u a, v a)) _ hpair
        intro a ha
        exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem u ha, Finset.mem_image_of_mem v ha⟩
      have hup (a) (ha : a ∈ A) : (u a : ℝ) ∈ Set.Ioo x (x + 2 * (N : ℝ)) := by
        obtain ⟨hp, hl⟩ := hpos ha
        obtain ⟨h1, h2⟩ := Erdos650Suranyi.first_bounds (x := x) (by linarith) (a := a) hp
        change x < (u a : ℝ) ∧ (u a : ℝ) < x + 2 * (N : ℝ)
        change (u a : ℝ) ≤ x + a at h2
        exact ⟨h1, by linarith [show (0 : ℝ) < a by exact_mod_cast hp,
          show (a : ℝ) ≤ N by exact_mod_cast hl]⟩
      have hvp (a) (ha : a ∈ A) : (v a : ℝ) ∈ Set.Ioo x (x + 2 * (N : ℝ)) := by
        by_cases h : a = N
        · simpa [v, h] using hup a ha
        · obtain ⟨hp, hl⟩ := hpos ha
          have hlt : a < N := lt_of_le_of_ne hl h
          obtain ⟨h1, h2⟩ := Erdos650Suranyi.first_bounds (x := x) (by linarith) (a := a) hp
          change x < (u a : ℝ) at h1
          change (u a : ℝ) ≤ x + a at h2
          simp only [v, if_neg h, Nat.cast_add, Set.mem_Ioo]
          constructor <;> linarith [show (0 : ℝ) < a by exact_mod_cast hp,
            show (a : ℝ) < N by exact_mod_cast hlt]
      have hu_dvd (a : ℕ) : a ∣ u a := dvd_add (dvd_mul_right _ _) (dvd_refl _)
      have hv_dvd (a : ℕ) : a ∣ v a := by
        change a ∣ (if a = N then u a else u a + a)
        split_ifs
        · exact hu_dvd a
        · exact dvd_add (hu_dvd a) (dvd_refl _)
      have make (g : ℕ → ℕ) (hbig : m ≤ (A.image g).card ^ 2)
          (hinterval : ∀ a ∈ A, (g a : ℝ) ∈ Set.Ioo x (x + 2 * (N : ℝ)))
          (hdvd : ∀ a, a ∣ g a) :
          ∃ a b : Fin k → ℕ, Function.Injective a ∧ Function.Injective b ∧
            (∀ i, a i ∈ A) ∧ (∀ i, (b i : ℝ) ∈ Set.Ioo x (x + 2 * (N : ℝ))) ∧
            (∀ i, a i ∣ b i) := by
        have hk : k ≤ (A.image g).card :=
          Nat.ceil_le.mpr ((Real.sqrt_le_left (by positivity)).mpr (by exact_mod_cast hbig))
        obtain ⟨a, hai, ham, hbi⟩ := Erdos650Suranyi.representatives A g k hk
        exact ⟨a, g ∘ a, hai, hbi, ham, fun i => hinterval _ (ham i), fun i => hdvd _⟩
      rcases le_total (A.image u).card (A.image v).card with h | h
      · exact make v (hcount.trans (by simpa [sq] using Nat.mul_le_mul_right _ h)) hvp hv_dvd
      · exact make u (hcount.trans (by simpa [sq] using Nat.mul_le_mul_left _ h)) hup hu_dvd)
