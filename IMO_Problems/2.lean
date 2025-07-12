import Mathlib

open Finset

theorem Step1 {m : ℕ} (hm : 0 < m) :
    (Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 5) =
    ∑ k ∈ Icc 1 m, (2 * k + 1) * Nat.factorization k 5 := by
    induction hm using Nat.leRec with
    | refl => simp [Nat.factorization_eq_zero_iff 8 5]
    | @le_succ_of_le k hm ih =>
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

lemma v5eqzero {m : ℕ} : ¬ (5 : ℕ) ∣ ∏ k ∈ Finset.Icc 1 m, 2 ^ (2 * k + 1) := by
  induction' m with m ih
  · simp
  · rw [Finset.prod_Icc_succ_top (by norm_num)]
    intro five_div_prod
    have fivenotdvd2pow: ¬ 5 ∣ 2 ^ (2 * (m + 1) + 1) := fun hx5 ↦ by
      have (h5: Nat.Prime 5): 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hx5
      contradiction
    have := Prime.not_dvd_mul (Nat.prime_iff.mp (by norm_num)) ih fivenotdvd2pow
    contradiction

theorem v5factSimp {m : ℕ} : Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 5=
    Nat.factorization (∏ k ∈ Icc 1 m, k ^ (2 * k + 1)) 5 := by
    have pow_eq: ∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1) =
        ∏ k ∈ Icc 1 m,  2 ^ (2 * k + 1) * k ^ (2 * k + 1) := by
      congr
      ext k
      exact Nat.mul_pow 2 k (2 * k + 1)
    have prod_fg: ∏ k ∈ Finset.Icc 1 m, (2 * k) ^ (2 * k + 1) =
        (∏ k ∈ Finset.Icc 1 m, 2 ^ (2 * k + 1) )* (∏ k ∈ Finset.Icc 1 m,  k ^ (2 * k + 1)):= by
      rw [pow_eq]
      exact prod_mul_distrib
    have : Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1))  =
        Nat.factorization (∏ k ∈ Finset.Icc 1 m, 2 ^ (2 * k + 1) )  +
        Nat.factorization (∏ k ∈ Finset.Icc 1 m,  k ^ (2 * k + 1)) := by
        rw [prod_fg, Nat.factorization_mul]
        · rw [Finset.prod_ne_zero_iff]
          exact fun a a_1 => Ne.symm (NeZero.ne' (2 ^ (2 * a + 1)))
        · rw [Finset.prod_ne_zero_iff]
          intro a ha
          simp at ha
          exact pow_ne_zero (2 * a + 1) (by linarith)
    rw [this, Finsupp.add_apply]
    refine Nat.add_eq_right.mpr ?_
    simp [Nat.factorization_eq_zero_iff , v5eqzero]

theorem Step2 {m : ℕ} (hm : 0 < m) :
      Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 5
    ≤ Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 2 := by
  rw [v5factSimp]
  have powk_dvd_powm (hm : 0< m) : (∏ k ∈ Finset.Icc 1 m, k ^ (2 * k + 1)) ∣
      (∏ k ∈ Finset.Icc 1 m, k ^ (2 * m + 1)) := by
    apply Finset.prod_dvd_prod_of_dvd
    intro i ih
    simp only [Finset.mem_Icc] at ih
    have i_le_m: i <= m :=  ih.2
    have ipow_le_mpow : 2 * i + 1 ≤ 2* m +1 := by linarith
    apply pow_dvd_pow i ipow_le_mpow
  have powk_le_powm:Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 5 ≤
      Nat.factorization (∏ k ∈ Icc 1 m, k ^ (2 * m + 1)) 5 := by
    rw [v5factSimp]
    have := powk_dvd_powm hm
    simp [this]
    have kpow_neqz: ∏ k ∈ Finset.Icc 1 m, k ^ (2 * k + 1) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro a ha
      refine pow_ne_zero (2 * a + 1) ?_
      simp at ha
      linarith
    have mpow_neqz: ∏ k ∈ Finset.Icc 1 m, k ^ (2 * m + 1) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro a ha
      refine pow_ne_zero (2 * m + 1) ?_
      simp at ha
      linarith
    exact (Nat.factorization_le_iff_dvd kpow_neqz mpow_neqz).mpr (powk_dvd_powm hm) 5
  have turntofact  (m: ℕ ): (∏ k ∈ Icc 1 m, k ^ (2 * m + 1)).factorization 5  =
      (2 * m + 1) * (m.factorial).factorization 5 := by
    rw [Finset.prod_pow, Nat.factorization_pow, ← Finset.prod_Ico_id_eq_factorial]
    exact rfl
  have le_with_padic(n : ℕ) : ((n.factorial).factorization 5 : ℝ) ≤ (n : ℝ) / 4:= by
    have pp: Nat.Prime 5 := Nat.prime_five
    have eq : 4 * (n.factorial).factorization 5 ≤ n := by -- in ℕ
      have : 4 = 5 -1 := by norm_num
      rw [this, Nat.factorization_def n.factorial pp]
      have : Fact (Nat.Prime 5) := { out := pp }
      rw [sub_one_mul_padicValNat_factorial n]
      apply Nat.sub_le
    refine (le_div_iff₀' (by norm_num)).mpr ?_
    have eq2 : ((4 * (n.factorial).factorization 5 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr eq
    have : (4 : ℝ) * ((n.factorial).factorization 5 : ℝ)
        = ((4 * (n.factorial).factorization 5 : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
    rwa [← this] at eq2
  have : Nat.factorization (∏ k ∈ Icc 1 m, k ^ (2 * m + 1)) 5 ≤ m ^ 2 := by
    have hm : (m : ℝ) ≥ 1 := Nat.one_le_cast.mpr hm
    have : (((2 * m + 1) * m.factorial.factorization 5 : ℕ) : ℝ) ≤ ((m : ℕ) ^ 2 : ℕ) := by calc
      _ = (2 * m + 1 : ℝ) * (m.factorial.factorization 5 : ℝ) := by simp
      _ ≤ (2 * m + 1 : ℝ) * ((m : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left (le_with_padic m) (by linarith)
      _ ≤ m ^ 2 := by
        rw [← mul_comm_div (2 * m + 1 : ℝ) 4 ↑m, sq]
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg' m)
        rw [div_le_iff₀' (by norm_num)]
        linarith
      _ = _ := by simp
    rw [turntofact]
    exact Nat.cast_le.mp this
  have: Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 5 ≤ m ^ 2 := by calc
    Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 5 ≤
      Nat.factorization (∏ k ∈ Icc 1 m, k ^ (2 * m + 1)) 5 := powk_le_powm
    _ ≤ _ := this

  sorry
