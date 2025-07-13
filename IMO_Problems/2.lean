import Mathlib

open Finset

variable {m : ℕ}

open Finset

variable {m : ℕ}

-- First, let's determine $v_5\left(P_m\right)$.
-- $$v_5\left(P_m\right)=v_5\left(\prod_{k=1}^m(2 k)^{2 k+1}\right)$$
theorem Step1 (hm : 0 < m) :
    (Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 5) =
    ∑ k ∈ Icc 1 m, (2 * k + 1) * Nat.factorization k 5 := by
    -- We shall prove by induction
    induction hm using Nat.leRec with
    | refl => simp [Nat.factorization_eq_zero_iff 8 5]
    | @le_succ_of_le k hm ih =>
      -- Using the properties of the $p$-adic valuation $v_p(a b)=v_p(a)+v_p(b)$ and
      -- $v_p\left(a^n\right)=n v_p(a)$ :
      have k1tok : ∏ k ∈ Icc 1 (k + 1), (2 * k) ^ (2 * k + 1)
        = (∏ k ∈ Icc 1 k, (2 * k) ^ (2 * k + 1)) * (2 * k + 2) ^ (2 * k + 3) := by
        rw [Finset.prod_Icc_succ_top (by norm_num)]
        ring
      have h1neqz: ∏ k ∈ Icc 1 k, (2 * k) ^ (2 * k + 1) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro a ha
        refine pow_ne_zero (2 * a + 1) ?_
        simp at ha
        linarith
      rw [k1tok, Nat.factorization_mul h1neqz (pow_ne_zero (2 * k + 3) (by linarith)),
        Finsupp.add_apply, ih, Finset.sum_Icc_succ_top (by linarith)]
      have t1 : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
      have t2 : 2 * k + 2 = 2 * (k + 1) := by ring
      simp [t1, t2]
      norm_num

lemma v5eqzero : ¬ (5 : ℕ) ∣ ∏ k ∈ Icc 1 m, 2 ^ (2 * k + 1) := by
  induction' m with m ih
  · simp
  · rw [prod_Icc_succ_top (by norm_num)]
    intro five_div_prod
    have fivenotdvd2pow: ¬ 5 ∣ 2 ^ (2 * (m + 1) + 1) := fun hx5 ↦ by
      have (h5: Nat.Prime 5): 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hx5
      contradiction
    have := Prime.not_dvd_mul (Nat.prime_iff.mp (by norm_num)) ih fivenotdvd2pow
    contradiction

lemma imp {a : ℕ} (ha : a ∈ Icc 1 m) : a ≠ 0 := by simp at ha; linarith

theorem Step2_1 : Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 5=
    Nat.factorization (∏ k ∈ Icc 1 m, k ^ (2 * k + 1)) 5 := by
  have pow_eq: ∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1) =
      ∏ k ∈ Icc 1 m,  2 ^ (2 * k + 1) * k ^ (2 * k + 1) := by
    congr; ext k; exact Nat.mul_pow 2 k (2 * k + 1)
  have prod_fg: ∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1) =
      (∏ k ∈ Icc 1 m, 2 ^ (2 * k + 1)) * (∏ k ∈ Icc 1 m, k ^ (2 * k + 1)):= by
    rw [pow_eq]
    exact prod_mul_distrib
  have : Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) =
      Nat.factorization (∏ k ∈ Icc 1 m, 2 ^ (2 * k + 1)) +
      Nat.factorization (∏ k ∈ Icc 1 m,  k ^ (2 * k + 1)) := by
      rw [prod_fg, Nat.factorization_mul]
      · rw [prod_ne_zero_iff]
        exact fun a a_1 => Ne.symm (NeZero.ne' (2 ^ (2 * a + 1)))
      · rw [prod_ne_zero_iff]
        exact fun a ha ↦ pow_ne_zero (2 * a + 1) (imp ha)
  rw [this, Finsupp.add_apply, Nat.add_eq_right]
  simp [Nat.factorization_eq_zero_iff , v5eqzero]

lemma powk_dvd_powm : (∏ k ∈ Icc 1 m, k ^ (2 * k + 1)) ∣
    (∏ k ∈ Icc 1 m, k ^ (2 * m + 1)) := by
  apply Finset.prod_dvd_prod_of_dvd
  exact fun i ih ↦ pow_dvd_pow i (by simp at ih; linarith)

lemma le (hm : 0 < m) : (((2 * m + 1) * m.factorial.factorization 5 : ℕ) : ℝ) ≤ (m ^ 2 : ℕ) := by
  have eq : 4 * (m.factorial).factorization 5 ≤ m := by -- in ℕ
    have : 4 = 5 - 1 := by norm_num
    rw [this, Nat.factorization_def m.factorial Nat.prime_five]
    have : Fact (Nat.Prime 5) := { out := Nat.prime_five}
    rw [sub_one_mul_padicValNat_factorial m]
    exact Nat.sub_le m (Nat.digits 5 m).sum
  have le_with_padic : ((m.factorial).factorization 5 : ℝ) ≤ (m : ℝ) / 4:= by
    refine (le_div_iff₀' (by norm_num)).mpr ?_
    have eq2 : ((4 * (m.factorial).factorization 5 : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr eq
    have : (4 : ℝ) * ((m.factorial).factorization 5 : ℝ)
        = ((4 * (m.factorial).factorization 5 : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
    rwa [← this] at eq2
  calc
    _ = (2 * m + 1 : ℝ) * (m.factorial.factorization 5 : ℝ) := by simp
    _ ≤ (2 * m + 1 : ℝ) * ((m : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left le_with_padic (by linarith)
    _ ≤ m ^ 2 := by
      rw [← mul_comm_div (2 * m + 1 : ℝ) 4 m, sq]
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg' m)
      rw [div_le_iff₀' (by norm_num)]
      have : (m : ℝ) ≥ 1 := Nat.one_le_cast.mpr hm
      linarith
    _ = _ := by simp

theorem sum_icc_id: ∑ k ∈ Icc 1 m, (2 * k + 1) = m ^ 2 + 2 * m := by
  induction' m  with m ih
  · simp
  · rw [Finset.sum_Icc_succ_top (by norm_num), ih, add_sq]
    ring

lemma v2ge: Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 2 ≥ m ^ 2:= by
  have powk_dvd_pow2k : (∏ k ∈ Icc 1 m, 2 ^ (2 * k + 1)) ∣
      (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) := by
    apply Finset.prod_dvd_prod_of_dvd
    intro i ih
    simp only [Finset.mem_Icc] at ih
    exact pow_dvd_pow_of_dvd (Nat.dvd_mul_right 2 i) (2 * i + 1)
  have pow_neqz: ∏ k ∈ Icc 1 m, 2 ^ (2 * k + 1) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    exact fun a ha ↦ pow_ne_zero (2 * a + 1) (by norm_num)
  have kpow_neqz: ∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    exact fun a ha ↦ pow_ne_zero (2 * a + 1) (by simp at ha; linarith)
  have step2: (∏ k ∈ Icc 1 m, 2 ^ (2 * k + 1)).factorization 2 = ∑ k ∈ Icc 1 m, (2 * k + 1) := by
    rw [Finset.prod_pow_eq_pow_sum]
    norm_num
  calc
    _ ≥ Nat.factorization (∏ k ∈ Icc 1 m, 2 ^ (2 * k + 1)) 2 :=
      (Nat.factorization_le_iff_dvd pow_neqz kpow_neqz).mpr (powk_dvd_pow2k) 2
    _ ≥ _ := by
      rw [step2, sum_icc_id]
      linarith

-- We need to show that $v_2(P) \ge v_5(P)$
theorem Step2 : Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 5
    ≤ Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 2 := by
  rcases Nat.eq_zero_or_pos m with ch | hm
  · simp [ch]
  ·   calc
    _ = Nat.factorization (∏ k ∈ Icc 1 m, k ^ (2 * k + 1)) 5 := Step2_1
    -- This is because $v_5(P) \le v_5(\prod_{k = 1}^{m} k^{2m + 1})$
    -- $= (2m + 1) \cdot v_5(m!) \le (2m + 1) \cdot \frac{m}4$ by Lucas Theorem
    _ ≤ Nat.factorization (∏ k ∈ Icc 1 m, k ^ (2 * m + 1)) 5 :=
      have kpow_neqz : ∏ k ∈ Icc 1 m, k ^ (2 * k + 1) ≠ 0 := by
        simpa only [prod_ne_zero_iff] using fun a ha ↦ pow_ne_zero (2 * a + 1) (imp ha)
      have mpow_neqz : ∏ k ∈ Icc 1 m, k ^ (2 * m + 1) ≠ 0 := by
        simpa only [prod_ne_zero_iff] using fun a ha ↦ pow_ne_zero (2 * m + 1) (imp ha)
      (Nat.factorization_le_iff_dvd kpow_neqz mpow_neqz).mpr powk_dvd_powm 5
    -- Thus it $\le m ^ 2 + 2 * m = v_2(\prod_{k = 1}^m 2 ^ (2k + 1)) \le v_2(P)$
    _ = (2 * m + 1) * (m.factorial).factorization 5 := by
      simpa only [prod_pow, Nat.factorization_pow, ← Finset.prod_Ico_id_eq_factorial] using by rfl
    _ ≤ m ^ 2 := Nat.cast_le.mp (le hm)
    _ ≤ _ := v2ge

/- Let $m$ be a positive integer. Determine the number of trailing zeros in the expansion of the
product $P_m = \prod_{k=1}^{m} (2k)^{2k+1}$. Show that this number is equal to $\sum_{k=1}^{m}
(2k+1)v_5(k)$, where $v_5(k)$ is the exponent of the highest power of 5 dividing $k$.
-/
theorem main {l : ℕ} (hl1 : 10 ^ l ∣ ∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1))
    (hl2 : ¬ 10 ^ (l + 1) ∣ ∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) :
    l = Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 5 := by
  -- Now we have $l \le v_5(P)$ since $10^l \dvd P$
  have : Nat.factorization (5 ^ l) ≤ Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) := by
    refine (Nat.factorization_le_iff_dvd (Ne.symm (NeZero.ne' (5 ^ l))) ?_).mpr
      (Nat.dvd_trans (pow_dvd_pow_of_dvd (by norm_num) l) hl1)
    rw [prod_ne_zero_iff]
    exact fun a ha ↦ pow_ne_zero (2 * a + 1) (by simp at ha; linarith)
  have le : Nat.factorization (5 ^ l) 5
      ≤ Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 5 := this 5
  have eq : Nat.factorization (5 ^ l) 5 = l := by simp; norm_num
  rw [eq] at le
  -- Also $l \ge v_5(P)$ because if $l \le v_5(p) - 1 \le v_2(P)$
  have ge : Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 5 ≤ l := by
    by_contra! nh
    have : l + 1 ≤ Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 5 := by omega
    have dvd1 : 5 ^ (l + 1) ∣ ∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1) := by
      refine (Nat.Prime.pow_dvd_iff_dvd_ordProj Nat.prime_five ?_).mpr
        (Nat.pow_dvd_pow_iff_le_right'.mpr nh)
      rw [prod_ne_zero_iff]
      exact fun a ha ↦ pow_ne_zero (2 * a + 1) (by simp at ha; linarith)
    have dvd2 : 2 ^ (l + 1) ∣ ∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1) := by
      refine (Nat.Prime.pow_dvd_iff_dvd_ordProj Nat.prime_two ?_).mpr ?_
      rw [prod_ne_zero_iff]
      exact fun a ha ↦ pow_ne_zero (2 * a + 1) (by simp at ha; linarith)
      refine Nat.pow_dvd_pow_iff_le_right'.mpr ?_
      linarith [Step2 (m := m)]
    --then we have $10 ^ (l + 1) \dvd P$ and contradiciton!
    have : 5 ^ (l + 1) * 2 ^ (l + 1) ∣ ∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1) := by
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ dvd1 dvd2
      simpa using Odd.pow (Nat.odd_iff.mpr rfl)
    rw [← Nat.mul_pow] at this
    contradiction
  exact Nat.le_antisymm le ge
