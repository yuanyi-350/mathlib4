import Mathlib

theorem sublemma (x y p : ℕ) (hx : 0 < x) (hy : 0 < y) (hp : Nat.Prime p) (ch : Odd p)
    (eq0 : y ^ p + 1 = p ^ x) (le1 : p ^ (x - 1) ≤ y + 1) : (x = 1 ∧ y = 1 ∧ p = 2) ∨
    (x = 2 ∧ y = 2 ∧ p = 3) := by
  -- When $p$ or $y$ is too big, it is trivial that $y ^ p + 1 = p ^ x$ and $p ^ (x - 1) ≤ y + 1$
  -- contradicts
  have le3 : y ^ p ≤ 2 * p * y ^ 1 := by calc
    _ ≤ p ^ x := by omega
    _ = p * p ^ (x - 1) := Eq.symm (mul_pow_sub_one (Nat.ne_zero_of_lt hx) p)
    _ ≤ p * (y + 1) := Nat.mul_le_mul_left p le1
    _ ≤ _ := by
      ring_nf
      simpa [Nat.mul_two] using Nat.le_mul_of_pos_right p hy
  have le2 : y ^ (p - 1) ≤ 2 * p := by
    have : y ^ (p - 1) * y ^ 1 ≤ (2 * p) * y ^ 1 := by
      have : p > 1 := Nat.Prime.one_lt hp
      have : 1 + (p - 1) = p := by omega
      rwa [← Nat.pow_add', this]
    rwa [Nat.mul_le_mul_right_iff] at this
    simp [hy]

  by_cases ch1 : p ≤ 4
  · -- When p < 4, it is trivial
    have hp : p = 3 := by interval_cases p <;> tauto
    simp [hp] at le2
    have : y ≤ 2 := by
      by_contra! nh
      have : y ^ 2 ≥ 3 ^ 2 := Nat.pow_le_pow_left nh 2
      linarith
    interval_cases y
    · simp [hp] at eq0
      have : 3 ∣ 3 ^ x := Nat.pow_dvd_pow_iff_le_right'.mpr hx
      norm_num [← eq0] at this
    · simp [hp] at eq0
      simp [hp]
      have : x < 3 := by
        by_contra! nh
        have : 3 ^ x ≥ 3 ^ 3 := Nat.pow_le_pow_right (Nat.zero_lt_succ 2) nh
        linarith
      interval_cases x <;> tauto
  · simp at ch1
    have y_le : y ≤ 3 := by
      by_contra! nh
      have : y ≥ 4 := by omega
      have : 2 ^ (2 * (p - 1)) ≤ 2 ^ p := by calc
        _ = 4 ^ (p - 1) := Mathlib.Tactic.Ring.pow_nat rfl rfl rfl
        _ ≤ y ^ (p - 1) := Nat.pow_le_pow_left nh (p - 1)
        _ ≤ 2 * p := le2
        _ ≤ _ := Nat.mul_le_pow (Nat.succ_succ_ne_one 0) p
      have : 2 * (p - 1) ≤ p := by rwa [pow_le_pow_iff_right₀ (by norm_num)] at this
      omega
    have x_le : x ≤ 2 := by
      have : 4 ^ (x - 1) ≤ p ^ (x - 1) := Nat.pow_le_pow_left (Nat.le_of_succ_le ch1) (x - 1)
      have : 4 ^ (x - 1) ≤ 4 ^ 1 := by omega
      have : x - 1 ≤ 1 := by rwa [pow_le_pow_iff_right₀ (by norm_num)] at this
      omega
    interval_cases x
    · interval_cases y
      · simp at *
        linarith
      · simp at *
        have : 2 ^ p ≥ 2 * p := Nat.mul_le_pow (a := 2) (Nat.succ_succ_ne_one 0) p
        linarith
      · simp at *
        have : 3 ^ p ≥ 3 * p := Nat.mul_le_pow (a := 3) (Nat.succ_succ_ne_one 1) p
        linarith
    · simp at le1
      omega

theorem sublemma3 : ∀ y : ℕ, ¬ 4 ∣ y ^ 2 + 1 := by
  intro y
  by_contra h
  have h1 : y ^ 2 % 4 = 0 ∨ y ^ 2 % 4 = 1 := by
    have h1 : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1) <;> simp [Nat.pow_mod, h1]
  have h2 : (y ^ 2 + 1) % 4 = 0 := by
    exact Nat.dvd_iff_mod_eq_zero.mp h
  have h3 : (y ^ 2 + 1) % 4 = 1 ∨ (y ^ 2 + 1) % 4 = 2 := by
    rcases h1 with (h1 | h1)
    · omega
    · omega
  omega

theorem sublemma2 (x y : ℕ) (hx : 0 < x):
    2 ^ x - y ^ 2 = 1 → x = 1 ∧ y = 1 ∧ 2 = 2 ∨ x = 2 ∧ y = 2 ∧ 2 = 3 := by
  intro h
  have eq : 2 ^ x = y ^ 2 + 1 := (Nat.sub_eq_iff_eq_add' (by omega)).mp h
  have : ¬ 4 ∣ 2 ^ x := by simpa [eq] using sublemma3 y
  have : x < 2 := by
    by_contra! nh
    have : 2 ^ 2 ∣ 2 ^ x := Nat.pow_dvd_pow_iff_le_right'.mpr nh
    norm_num at this
    contradiction
  interval_cases x
  simpa using eq

/- (French-Slovak Competition 1996) Find all strictly positive integers $x, y, p$ such that
 $p^{x}-y^{p}=1$ with $p$ prime.
-/
theorem number_theorem_141903 (x y p : ℕ) (hx : 0 < x) (hy : 0 < y) (hp : Nat.Prime p) :
    p ^ x - y ^ p = 1 ↔ (x = 1 ∧ y = 1 ∧ p = 2) ∨ (x = 2 ∧ y = 2 ∧ p = 3) := by
  constructor
  · rcases Nat.even_or_odd p with ch | ch
    · -- When p = 2, it is trivial
      have : p = 2 := (Nat.Prime.even_iff hp).mp ch
      simpa [this] using fun a ↦ sublemma2 x y hx a
    · intro h
      have eq0 : y ^ p + 1 = p ^ x := by omega
      have pdvd : p ∣ y + 1 := by
        have : y + 1 ∣ y ^ p + 1 ^ p := Odd.nat_add_dvd_pow_add_pow y 1 ch
        simp [eq0] at this
        obtain ⟨m, hm⟩ := (Nat.dvd_prime_pow hp).mp this
        have : m > 0 := by
          by_contra! nh
          have : m = 0 := by omega
          simp [this] at hm
          omega
        simpa [hm.2] using Dvd.dvd.pow (Nat.dvd_refl p) (Nat.ne_zero_of_lt this)
      -- using LTE lemma, then $v_p(y ^ p + 1) = v_p(y + 1) + 1$
      have eq : emultiplicity p (y ^ p + 1 ^ p) = emultiplicity p (y + 1) + emultiplicity p p := by
        refine Nat.emultiplicity_pow_add_pow hp ch pdvd ?_ ch
        by_contra! nh
        have : p ∣ 1 := (Nat.dvd_add_iff_right nh).mpr pdvd
        simp at this
        rw [this] at hp
        exact Nat.prime_one_false hp
      have : FiniteMultiplicity p (y + 1) :=
        FiniteMultiplicity.of_prime_left (Nat.prime_iff.mp hp) (Ne.symm (Nat.zero_ne_add_one y))
      have : emultiplicity p (y + 1) = multiplicity p (y + 1) :=
        FiniteMultiplicity.emultiplicity_eq_multiplicity this
      rw [one_pow, eq0, Nat.Prime.emultiplicity_self hp, Nat.Prime.emultiplicity_pow_self hp] at eq
      rw [this] at eq
      have eq : x = (multiplicity p (y + 1)) + 1 := ENat.coe_inj.mp eq
      have eq : multiplicity p (y + 1) = x - 1 := by omega
      have : p ^ multiplicity p (y + 1) ∣ y + 1 := pow_multiplicity_dvd p (y + 1)
      rw [eq] at this
      -- thus $p ^ (x - 1) ≤ y + 1$
      have le1 := Nat.le_of_dvd (Nat.add_pos_left hy 1) this
      exact sublemma x y p hx hy hp ch eq0 le1
  · intro h
    rcases h with ch | ch
    repeat {rw[ch.1, ch.2.1, ch.2.2]; norm_num}
