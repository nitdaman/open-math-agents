import OMAReductions.R_Erdos30_erdos_30_variants_singer_R1

-- Step Erdos30.erdos_30.variants.singer.R1.H2: hypothesis H2 of reduction Erdos30.erdos_30.variants.singer.R1
-- Credit: @ldy985
-- H2 := ∀ p : ℕ, p.Prime → ∃ A : Finset ℕ,     A ⊆ Finset.Icc 1 (p * (p - 1)) ∧ IsSidon (A : Set ℕ) ∧ A.card = p - 1
--
-- Ruzsa's construction. Write p = q + 1 and let g generate the units of ZMod p. For i < q take the
-- integer x_i = i + q * k_i with k_i < p chosen so that x_i ≡ g ^ i (mod p); so x_i ≡ i (mod q).
-- If x_a + x_c = x_b + x_d then a + c ≡ b + d (mod q), hence g^a * g^c = g^b * g^d, and also
-- g^a + g^c = g^b + g^d in the field ZMod p. Equal sum and product force {g^a, g^c} = {g^b, g^d},
-- and g ^ i is injective on i < q. The set is { 1 + x_i : i < q }, inside {1, …, p * (p - 1)}.

namespace OMA.Ruzsa

/-- Ruzsa's construction: for a prime `q + 1`, the `q` integers `1 + i + q * k_i`, `i < q`, where
`k_i` is chosen so that the number is `≡ 1 + g ^ i (mod q + 1)` for a primitive root `g`, form a
Sidon set inside `{1, …, (q + 1) q}`. -/
theorem ruzsa_succ (q : ℕ) (hp : (q + 1).Prime) : ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 ((q + 1) * q) ∧ IsSidon (A : Set ℕ) ∧ A.card = q := by
  have : Fact (q + 1).Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ : ∃ g : (ZMod (q + 1))ˣ, orderOf g = q := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (q + 1))ˣ)
    refine ⟨g, ?_⟩
    rw [hg, Nat.card_eq_fintype_card, ZMod.card_units (q + 1)]
    simp
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ZMod (q + 1), ∀ i, u i = ((g ^ i : (ZMod (q + 1))ˣ) : ZMod (q + 1)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ → ℕ, ∀ i, k i = (i + (q + 1) - (u i).val) % (q + 1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ i, f i = 1 + i + q * k i := ⟨_, fun _ => rfl⟩
  have hk_lt : ∀ i, k i < q + 1 := fun i => by
    rw [hk]
    exact Nat.mod_lt _ (Nat.succ_pos q)
  have hqcast : ((q : ℕ) : ZMod (q + 1)) = -1 := by
    have h0 : ((q + 1 : ℕ) : ZMod (q + 1)) = 0 := ZMod.natCast_self (q + 1)
    push_cast at h0
    linear_combination h0
  have hkcast : ∀ i, ((k i : ℕ) : ZMod (q + 1)) = (i : ZMod (q + 1)) - u i := by
    intro i
    have hval : (u i).val ≤ i + (q + 1) := (ZMod.val_lt (u i)).le.trans (Nat.le_add_left _ _)
    have h0 : ((q + 1 : ℕ) : ZMod (q + 1)) = 0 := ZMod.natCast_self (q + 1)
    rw [hk, ZMod.natCast_mod, Nat.cast_sub hval, Nat.cast_add, h0, ZMod.natCast_zmod_val]
    ring
  have hfcast : ∀ i, ((f i : ℕ) : ZMod (q + 1)) = 1 + u i := by
    intro i
    rw [hf]
    push_cast
    rw [hqcast, hkcast]
    ring
  have hu_inj : ∀ a b, a < q → b < q → u a = u b → a = b := by
    intro a b ha hb hab
    rw [hu, hu] at hab
    have h1 : g ^ a = g ^ b := Units.ext hab
    have h2 : a ≡ b [MOD orderOf g] := pow_eq_pow_iff_modEq.1 h1
    rw [hg] at h2
    exact Nat.ModEq.eq_of_lt_of_lt h2 ha hb
  have hf_mod : ∀ i, f i % q = (1 + i) % q := by
    intro i
    rw [hf]
    exact Nat.add_mul_mod_self_left _ _ _
  refine ⟨(Finset.range q).image f, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    have hi' := Finset.mem_range.1 hi
    have hki := hk_lt i
    rw [Finset.mem_Icc, hf]
    refine ⟨by omega, ?_⟩
    have h1 : q * k i ≤ q * q := Nat.mul_le_mul_left q (by omega)
    have h2 : (q + 1) * q = q * q + q := by ring
    omega
  · intro x hx y hy z hz w hw hsum
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hz)
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hw)
    have ha' := Finset.mem_range.1 ha
    have hb' := Finset.mem_range.1 hb
    have hc' := Finset.mem_range.1 hc
    have hd' := Finset.mem_range.1 hd
    -- the sum of the exponents is determined modulo q
    have hmod : a + c ≡ b + d [MOD q] := by
      have e : a + c + q * (k a + k c + 0) + 2 = b + d + q * (k b + k d + 0) + 2 := by
        have := hsum
        rw [hf a, hf b, hf c, hf d] at this
        simp only [Nat.mul_add, Nat.add_zero]
        omega
      have e' : a + c + q * (k a + k c + 0) = b + d + q * (k b + k d + 0) := by omega
      have e2 := congrArg (· % q) e'
      simp only [Nat.add_mul_mod_self_left] at e2
      exact e2
    have hgpow : g ^ (a + c) = g ^ (b + d) := pow_eq_pow_iff_modEq.2 (by rw [hg]; exact hmod)
    have hprod : u a * u c = u b * u d := by
      rw [hu, hu, hu, hu, ← Units.val_mul, ← Units.val_mul, ← pow_add, ← pow_add, hgpow]
    have hadd : u a + u c = u b + u d := by
      have e := congrArg (Nat.cast : ℕ → ZMod (q + 1)) hsum
      rw [Nat.cast_add, Nat.cast_add, hfcast, hfcast, hfcast, hfcast] at e
      linear_combination e
    have hzero : (u a - u b) * (u a - u d) = 0 := by
      linear_combination (u a) * hadd - hprod
    rcases mul_eq_zero.1 hzero with h | h
    · have hab : a = b := hu_inj a b ha' hb' (sub_eq_zero.1 h)
      have hcd : c = d := by
        apply hu_inj c d hc' hd'
        rw [hab] at hadd
        exact add_left_cancel hadd
      exact Or.inl ⟨by rw [hab], by rw [hcd]⟩
    · have had : a = d := hu_inj a d ha' hd' (sub_eq_zero.1 h)
      have hcb : c = b := by
        apply hu_inj c b hc' hb'
        rw [had] at hadd
        have : u d + u c = u d + u b := by rw [hadd]; ring
        exact add_left_cancel this
      exact Or.inr ⟨by rw [had], by rw [hcb]⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hi' : i < q := Finset.mem_range.1 (Finset.mem_coe.1 hi)
    have hj' : j < q := Finset.mem_range.1 (Finset.mem_coe.1 hj)
    have h1 : (1 + i) % q = (1 + j) % q := by rw [← hf_mod, ← hf_mod, hij]
    have h2 : (1 + i) ≡ (1 + j) [MOD q] := h1
    have h3 : i ≡ j [MOD q] := Nat.ModEq.add_left_cancel' 1 h2
    exact Nat.ModEq.eq_of_lt_of_lt h3 hi' hj'

theorem ruzsa (p : ℕ) (hp : p.Prime) : ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 (p * (p - 1)) ∧ IsSidon (A : Set ℕ) ∧ A.card = p - 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  simpa using ruzsa_succ q hp

end OMA.Ruzsa

theorem OMA.solution : OMA.R_Erdos30_erdos_30_variants_singer_R1.H2 :=
  fun p hp => OMA.Ruzsa.ruzsa p hp
