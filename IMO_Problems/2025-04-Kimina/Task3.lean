import Mathlib
/-
theorem sublemma1 (p q : ℕ) (hdiv2 : q ∣ 5 ^ p + 1) : (5 ^ (2 * p) : ZMod q) = 1 := by
  have h1 : (5 ^ p : ZMod q) = -1 := by
    have : (5 : ZMod q) ^ p + 1 = ((5 ^ p + 1 : ℕ) : ZMod q) := by simp
    rwa [eq_neg_iff_add_eq_zero, this, ZMod.natCast_zmod_eq_zero_iff_dvd]
  have h2 : (5 ^ (2 * p) : ZMod q) = (5 ^ p : ZMod q) ^ 2 := by ring
  rw [h2, h1]
  simp

theorem sublemma2 (α p : ℕ) (hp : p.Prime) (h : α ∣ 2 * p) :
    α = 1 ∨ α = 2 ∨ α = p ∨ α = 2 * p := by
  have h_two_p_pos : 0 < 2 * p := mul_pos Nat.zero_lt_two hp.pos
  have hα_pos : 0 < α := Nat.pos_of_dvd_of_pos h h_two_p_pos
  by_cases h_p_div_α : p ∣ α
  · obtain ⟨k, hk_eq⟩ := h_p_div_α -- Now we have hk_eq : α = p * k
    rw [hk_eq, mul_comm] at h -- Now h is : p * k ∣ 2 * p
    have hk_dvd_2 : k ∣ 2 := (Nat.mul_dvd_mul_iff_right hp.pos).mp h
    have hk_one_or_two : k = 1 ∨ k = 2 := by refine (Nat.dvd_prime Nat.prime_two).mp hk_dvd_2
    rcases hk_one_or_two with rfl | rfl
    · simp [hk_eq]
    · repeat right
      rw [hk_eq, Nat.mul_comm p 2]
  · have h_coprime_p_α : Nat.Coprime p α := (Nat.Prime.coprime_iff_not_dvd hp).mpr h_p_div_α
    have h_coprime_α_p : Nat.Coprime α p := h_coprime_p_α.symm
    have h_α_dvd_p_mul_2 : α ∣ p * 2 := by rwa [mul_comm] at h
    have hα_dvd_2 : α ∣ 2 := Nat.Coprime.dvd_of_dvd_mul_left h_coprime_α_p h_α_dvd_p_mul_2
    have hα_one_or_two : α = 1 ∨ α = 2 := (Nat.dvd_prime Nat.prime_two).mp hα_dvd_2
    rcases hα_one_or_two with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

theorem sublemma3 (q : ℕ) (hq : q.Prime) (dvd : q ∣ 24) : q = 2 ∨ q = 3 := by
  have : q ≤ 24 := Nat.le_of_dvd (by norm_num) dvd
  interval_cases q <;> tauto

/- Find all prime numbers $p$ and $q$ such that $p$ divides $5^q+1$ and $q$ divides $5^p+1$. -/
theorem number_theory_607522 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hdiv1 : p ∣ 5^q + 1) (hdiv2 : q ∣ 5 ^ p + 1) :
    (p, q) = (2, 2) ∨ (p, q) = (3, 3) ∨ (p, q) = (13, 2) ∨ (p, q) = (2, 13) ∨
    (p, q) = (3, 7) ∨ (p, q) = (7, 3) := by
  wlog le : p ≥ q
  · simp at le
    rcases this q p hq hp hdiv2 hdiv1 (Nat.le_of_succ_le le) with ch | ch | ch | ch | ch | ch | ch
    repeat {simp at ch; simp [ch]}
    tauto

  --1. Let $\alpha$ be the order of 5 modulo $q$ and $\beta$ be the order of 5 modulo $p$.
  set α := orderOf (5 : ZMod q) with hα
  set β := orderOf (5 : ZMod p) with hβ
  have ha : q ∣ 5 ^ α - 1 := by
    have eq : (5 : ZMod q) ^ α - 1 = 0 := by simp [hα, pow_orderOf_eq_one]
    have : (5 : ZMod q) ^ α - 1 = ((5 ^ α - 1 : ℕ) : ZMod q) := by simp
    rwa [this, ZMod.natCast_zmod_eq_zero_iff_dvd] at eq
  -- Since $5^{2 p} \equiv 1(\bmod q)$, we deduce that $\alpha$ divides $2 p$.
  have : α ∣ 2 * p := orderOf_dvd_of_pow_eq_one (sublemma1 p q hdiv2)
  -- Therefore, $\alpha=1,2, p$, or $2 p$.

  -- If $q=2$, then $p$ divides $5^2+1$, so $p=2$ or $p=13$.
  -- Conversely, $(2,2)$ and $(13,2)$ are solutions.
  have case1 : q = 2 → (p, q) = (2, 2) ∨ (p, q) = (3, 3) ∨ (p, q) = (13, 2) ∨ (p, q) = (2, 13) ∨
    (p, q) = (3, 7) ∨ (p, q) = (7, 3) := fun h ↦ by
    simp [h] at *
    have : p ≤ 26 := Nat.le_of_dvd (by norm_num) hdiv1
    interval_cases p <;> tauto
  -- If $q=3$, then $p$ divides $5^3+1$, so $p=2,3$, or 7 .
  -- Conversely, we verify that $(3,3),(7,3)$ are solutions, but $(2,3)$ is not.
  have case2 : q = 3 → (p, q) = (2, 2) ∨ (p, q) = (3, 3) ∨ (p, q) = (13, 2) ∨ (p, q) = (2, 13) ∨
    (p, q) = (3, 7) ∨ (p, q) = (7, 3) := fun h ↦ by
    simp [h] at *
    have : p ≤ 126 := Nat.le_of_dvd (by norm_num) hdiv1
    interval_cases p <;> tauto

  have sublemma : α = 2 * p → q = 2 ∨ q = 3 := fun ch ↦ by
    have : (5 : ZMod q) ^ (q - 1) = 1 := by
      have : (5 : ZMod q) ^ (q - 1) - 1 = 0 := by
        have : (5 : ZMod q) ^ (q - 1) - 1 = ((5 ^ (q - 1) - 1 : ℕ) : ZMod q) := by simp
        rw [this]
        simp [sub_eq_zero]
        have : (5 : ZMod q) ≠ 0 := by
          by_contra! nh
          have := (ZMod.natCast_zmod_eq_zero_iff_dvd 5 q).mp nh
          have : q = 5 := (prime_dvd_prime_iff_eq (Nat.prime_iff.mp hq)
            (Nat.prime_iff.mp (Nat.prime_five))).mp this
          have dvd1 : 5 ∣ 5 ^ p + 1 := by rwa [this] at hdiv2
          have dvd2 : 5 ∣ 5 ^ p := Dvd.dvd.pow (Nat.dvd_of_mod_eq_zero rfl) (Nat.Prime.ne_zero hp)
          have : 5 ∣ 1 := (Nat.dvd_add_iff_right dvd2).mpr dvd1
          simp at this
        have temp : Fact (Nat.Prime q) := { out := hq }
        --By Fermat's Little Theorem, $5^{p-1} \equiv 1(\bmod p)$ and $5^{q-1} \equiv 1(\bmod q)$.
        exact ZMod.pow_card_sub_one_eq_one this
      simpa [sub_eq_iff_eq_add'] using this
    have : α ∣ q - 1 := by
      simp [hα, orderOf_dvd_of_pow_eq_one this]
    rw [ch] at this
    -- Therefore, $q$ divides $p-1$ and $p$ divides $q-1$. So, $q \leq p-1$ and $p \leq q-1$.
    -- This leads to the contradiction $q \leq q-2$, which is absurd.
    have : 2 * p ≤ q - 1 := by
      refine Nat.le_of_dvd ?_ this
      simp [Nat.Prime.one_lt hq]
    have : 2 * q ≤ q - 1 := by linarith
    have : q ≥ 1 := Nat.Prime.one_le hq
    omega

  have : α = 1 ∨ α = 2 ∨ α = p ∨ α = 2 * p := sublemma2 α p hp this

  have : q = 2 ∨ q = 3 := by
    rcases this with ch | ch | ch | ch
    · simp [ch] at ha
      have h1 : q ≤ 4 := Nat.le_of_dvd (by norm_num) ha
      interval_cases q <;> tauto
    · simp [ch] at ha
      exact sublemma3 q hq ha
    · rw [ch] at ha
      have dvd : q ∣ (5 ^ p + 1) - (5 ^ p - 1) := Nat.dvd_sub hdiv2 ha
      have eq : (5 ^ p + 1) - (5 ^ p - 1) = 2 := by
        have : 5 ^ p ≥ 1 := Nat.one_le_pow' p 4
        omega
      rw [eq] at dvd
      have : q ≤ 2 := (Nat.Prime.dvd_factorial hq).mp dvd
      interval_cases q <;> tauto
    · exact sublemma ch

  rcases this with ch | ch
  · exact case1 ch
  · exact case2 ch

/- There is a unique triple $(a,b,c)$ of two-digit positive integers $a,\,b,$ and $c$ that satisfy the equation $$a^3+3b^3+9c^3=9abc+1.$$ Compute $a+b+c$. -/
theorem number_theory_56488 (a b c : ℕ) (ha : a ∈ Finset.Icc 10 99) (hb : b ∈ Finset.Icc 10 99)
    (hc : c ∈ Finset.Icc 10 99) (h : a^3 + 3 * b^3 + 9 * c^3 = 9 * a * b * c + 1) :
    a + b + c = 9 := by

  sorry
-/
