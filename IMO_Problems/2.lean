import Mathlib

open Finset

variable {m : ℕ}

theorem Step1 (hm : 0 < m) :
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

theorem Step2 (hm : 0 < m) : Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 5
    ≤ Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 2 := by calc
  _ = Nat.factorization (∏ k ∈ Icc 1 m, k ^ (2 * k + 1)) 5 := Step2_1
  _ ≤ Nat.factorization (∏ k ∈ Icc 1 m, k ^ (2 * m + 1)) 5 :=
    have kpow_neqz : ∏ k ∈ Icc 1 m, k ^ (2 * k + 1) ≠ 0 := by
      simpa only [prod_ne_zero_iff] using fun a ha ↦ pow_ne_zero (2 * a + 1) (imp ha)
    have mpow_neqz : ∏ k ∈ Icc 1 m, k ^ (2 * m + 1) ≠ 0 := by
      simpa only [prod_ne_zero_iff] using fun a ha ↦ pow_ne_zero (2 * m + 1) (imp ha)
    (Nat.factorization_le_iff_dvd kpow_neqz mpow_neqz).mpr powk_dvd_powm 5
  _ = (2 * m + 1) * (m.factorial).factorization 5 := by
    simpa only [prod_pow, Nat.factorization_pow, ← Finset.prod_Ico_id_eq_factorial] using by rfl
  _ ≤ m ^ 2 := Nat.cast_le.mp (le hm)
  _ ≤ _ := by
    sorry
