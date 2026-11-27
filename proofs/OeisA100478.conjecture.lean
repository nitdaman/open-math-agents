import FormalConjectures.OEIS.«100478»

/-! The pentanacci prime-counting sequence stabilizes at a positive fixed point. -/

open scoped Nat.Prime
open OeisA100478

namespace Pentanacci

private theorem step (v : Fin 5 → ℕ) (i : ℕ) :
    aGeneral v (i + 5) = π (aGeneral v (i + 4) + aGeneral v (i + 3) +
      aGeneral v (i + 2) + aGeneral v (i + 1) + aGeneral v i) := by
  rw [aGeneral]

private lemma phi2310 : Nat.totient 2310 = 480 := by
  have factor (p n : ℕ) (hp : p.Prime) (hc : p.Coprime n) :
      (p * n).totient = (p - 1) * n.totient := by
    rw [Nat.totient_mul hc, Nat.totient_prime hp]
  change (2 * (3 * (5 * (7 * 11)))).totient = 480
  rw [factor 2 _ (by decide) (by decide), factor 3 _ (by decide) (by decide),
    factor 5 _ (by decide) (by decide), factor 7 _ (by decide) (by decide),
    Nat.totient_prime (by decide : Nat.Prime 11)]

private lemma phi30030 : Nat.totient 30030 = 5760 := by
  change (13 * 2310).totient = 5760
  rw [Nat.totient_mul (by decide : Nat.Coprime 13 2310),
    Nat.totient_prime (by decide : Nat.Prime 13), phi2310]

private def checkpoints : List (ℕ × ℕ) :=
  [(73, 72), (74, 73), (75, 74), (76, 75), (77, 76),
    (79, 77), (81, 79), (84, 81), (87, 84), (91, 87),
    (95, 91), (100, 95), (109, 100), (120, 109), (132, 120),
    (150, 132), (175, 150), (209, 175), (258, 209), (327, 258),
    (440, 327), (616, 440), (909, 615), (1420, 909), (2367, 1420),
    (2400, 1438)]

private def trialDivisors : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59,
    61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109]

private def survives (n : ℕ) : Bool :=
  decide (2 ≤ n) && trialDivisors.all (fun d => decide (d = n ∨ ¬d ∣ n))

private lemma prime_survives {n : ℕ} (hn : n.Prime) : survives n = true := by
  have hD : trialDivisors.all (fun d => decide (2 ≤ d)) = true := by decide +kernel
  simp only [survives, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨hn.two_le, fun d hd => ?_⟩
  have htwo : 2 ≤ d := of_decide_eq_true (List.all_eq_true.mp hD d hd)
  by_cases h : d ∣ n
  · exact Or.inl (((Nat.dvd_prime hn).mp h).resolve_left (by omega))
  · exact Or.inr h

private def segment (start len : ℕ) : ℕ :=
  Nat.count (fun j => survives (start+j) = true) len

/-- Each checkpoint accounts only for numbers beyond the preceding checkpoint. -/
private def certify (start cap : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | p :: ps => decide (cap + segment start (5*p.1+1-start) ≤ p.2) &&
      certify (5*p.1+1) p.2 ps

private theorem certify_sound (ps : List (ℕ × ℕ)) (start cap : ℕ)
    (hc : Nat.count Nat.Prime start ≤ cap) (h : certify start cap ps = true) :
    ∀ p ∈ ps, π (5*p.1) ≤ p.2 := by
  induction ps generalizing start cap with
  | nil => simp
  | cons p ps ih =>
    simp only [certify, Bool.and_eq_true, decide_eq_true_eq] at h
    have hpc : π (5*p.1) ≤ p.2 := by
      change Nat.count Nat.Prime (5*p.1+1) ≤ p.2
      calc
        _ ≤ Nat.count Nat.Prime (start + (5*p.1+1-start)) :=
          Nat.count_monotone _ (by omega)
        _ = Nat.count Nat.Prime start +
            Nat.count (fun j => (start+j).Prime) (5*p.1+1-start) :=
          Nat.count_add _ _ _
        _ ≤ cap + segment start (5*p.1+1-start) :=
          Nat.add_le_add hc (Nat.count_mono_left fun _ _ hp => prime_survives hp)
        _ ≤ p.2 := h.1
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hpc
    · exact ih _ _ hpc h.2 _ hq

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private theorem checkpoint_counts : ∀ p ∈ checkpoints, π (5*p.1) ≤ p.2 := by
  apply certify_sound checkpoints 0 0 (by simp)
  decide +kernel

private lemma finite_upper (m : ℕ) (hm : 73 ≤ m) (hm' : m ≤ 2400) : π (5*m) < m := by
  have cover : ∃ p ∈ checkpoints, m ≤ p.1 ∧ p.2 < m := by
    simp [checkpoints]
    omega
  obtain ⟨p, hp, hmp, hpm⟩ := cover
  exact (Nat.monotone_primeCounting (Nat.mul_le_mul_left 5 hmp)).trans_lt
    ((checkpoint_counts p hp).trans_lt hpm)

private lemma pi12000 : π 12000 ≤ 1438 :=
  checkpoint_counts (2400, 1438) (by decide)

private lemma upper (m : ℕ) (hm : 73 ≤ m) : π (5 * m) < m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hsmall : m ≤ 2400
    · exact finite_upper m hm hsmall
    by_cases hmid : m ≤ 12010
    · have h := Nat.primeCounting_add_le (a := 2310) (k := 12000) (by decide) (by decide)
          (5 * m - 12000)
      rw [phi2310, show 12000 + (5 * m - 12000) = 5 * m by omega] at h
      have hbase := pi12000
      omega
    · have prior := ih (m - 6005) (by omega) (by omega)
      have h := Nat.primeCounting_add_le (a := 30030) (k := 5 * (m - 6005))
        (by decide) (by omega) 30025
      rw [phi30030, show 5 * (m - 6005) + 30025 = 5 * m by omega] at h
      omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
private lemma fixed_small : ∀ i : Fin 73, 0 < i.val → π (5 * i.val) = i.val →
    i.val ∈ ({66, 67, 68, 70, 71, 72} : Finset ℕ) := by
  decide +kernel

private lemma bounded (v : Fin 5 → ℕ) : ∃ M, ∀ n, aGeneral v n ≤ M := by
  let M := 73 + v 0 + v 1 + v 2 + v 3 + v 4
  have hM : 73 ≤ M := by dsimp [M]; omega
  refine ⟨M, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 5
    · interval_cases n <;> simp [aGeneral, M] <;> omega
    · obtain ⟨i, rfl⟩ : ∃ i, n = i + 5 := ⟨n - 5, by omega⟩
      rw [step]
      apply (Nat.monotone_primeCounting _).trans (upper M hM).le
      have h0 := ih i (by omega)
      have h1 := ih (i+1) (by omega)
      have h2 := ih (i+2) (by omega)
      have h3 := ih (i+3) (by omega)
      have h4 := ih (i+4) (by omega)
      omega

private lemma positive (v : Fin 5 → ℕ) (hv : ∀ j, 0 < v j) (n : ℕ) :
    0 < aGeneral v n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 5
    · interval_cases n <;> simp [aGeneral] <;> apply hv
    · obtain ⟨i, rfl⟩ : ∃ i, n = i + 5 := ⟨n - 5, by omega⟩
      rw [step]
      have h0 := ih i (by omega)
      have h1 := ih (i+1) (by omega)
      apply Nat.pos_of_ne_zero
      rw [Ne, Nat.primeCounting_eq_zero_iff]
      omega

private lemma advance (v : Fin 5 → ℕ) (i : ℕ) (h : aGeneral v i ≤ aGeneral v (i + 5)) :
    aGeneral v (i + 5) ≤ aGeneral v (i + 6) := by
  have h' := Nat.monotone_primeCounting (show
    aGeneral v (i+4) + aGeneral v (i+3) + aGeneral v (i+2) + aGeneral v (i+1) + aGeneral v i ≤
    aGeneral v (i+5) + aGeneral v (i+4) + aGeneral v (i+3) + aGeneral v (i+2) + aGeneral v (i+1)
      by omega)
  simpa only [step v i, step v (i+1), Nat.add_assoc, Nat.reduceAdd] using h'

private lemma stabilizes (v : Fin 5 → ℕ) : ∃ c t, ∀ n, aGeneral v (t + n) = c := by
  classical
  let B (m : ℕ) : Prop := ∃ k, ∀ n ≥ k, aGeneral v n ≤ m
  obtain ⟨M, hM⟩ := bounded v
  have hex : ∃ m, B m := ⟨M, 0, fun n _ => hM n⟩
  let c := Nat.find hex
  obtain ⟨k, hk⟩ := Nat.find_spec hex
  have hhit : ∃ t ≥ k + 5, aGeneral v t = c := by
    by_contra! h
    have hd : B (c - 1) := ⟨k + 5, fun n hn => by
      have hle := hk n (by omega)
      have hne := h n hn
      change aGeneral v n ≤ c at hle
      omega⟩
    have hc : c ≤ c - 1 := Nat.find_min' hex hd
    have hle := hk (k+5) (by omega)
    change aGeneral v (k+5) ≤ c at hle
    have hne := h (k+5) le_rfl
    omega
  obtain ⟨t, ht, htc⟩ := hhit
  refine ⟨c, t, ?_⟩
  intro n
  induction n with
  | zero => simpa using htc
  | succ n ih =>
    let i := t + n - 5
    have hi : k ≤ i := by dsimp [i]; omega
    have heq : i + 5 = t+n := by dsimp [i]; omega
    have hnext : i + 6 = t+(n+1) := by omega
    have hle : aGeneral v i ≤ c := hk i hi
    have hprev : aGeneral v i ≤ aGeneral v (i+5) := by simpa [heq, ih] using hle
    have hge := advance v i hprev
    rw [heq, hnext, ih] at hge
    exact le_antisymm (hk _ (by omega)) hge

end Pentanacci

theorem OMA.solution : type_of% @OeisA100478.conjecture := by
  intro v hv
  obtain ⟨c, t, hc⟩ := Pentanacci.stabilizes v
  have hfix := Pentanacci.step v t
  rw [hc 5, hc 4, hc 3, hc 2, hc 1, show aGeneral v t = c by simpa using hc 0] at hfix
  have hfix' : π (5 * c) = c := by simpa [Nat.mul_comm, Nat.mul_succ, ← Nat.add_assoc] using hfix.symm
  have hpos := Pentanacci.positive v hv t
  have hct : aGeneral v t = c := by simpa using hc 0
  have hsmall : c < 73 := by
    by_contra! h
    have := Pentanacci.upper c h
    omega
  refine ⟨c, Pentanacci.fixed_small ⟨c, hsmall⟩ (by simpa [hct] using hpos) hfix', ?_⟩
  apply Filter.eventually_atTop.2
  refine ⟨t, ?_⟩
  intro n hn
  simpa only [Nat.add_sub_of_le hn] using hc (n - t)
