import Mathlib

open Finset

theorem my_favorite_theorem {m : ℕ} (hm : 0 < m) :
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


theorem my_favorite_theorem2 {m : ℕ} (hm : 0 < m) :
    Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 5 ≤ ∑ k ∈ Icc 1 m, (2 * k + 1) := by

  sorry

example {s : Finset ℝ} (f g: ℝ → ℝ) (hs : ∀ i ∈ s, f i = g i) : ∏ i ∈ s, f i = ∏ i ∈ s, g i := by
  exact prod_congr rfl hs


lemma lm1{m : ℕ}: ¬(5:ℕ)∣(∏ k ∈ Finset.Icc 1 m, 2 ^ (2 * k + 1)) := by
    induction' m with m ih
    · sorry
    · rw [Finset.prod_Icc_succ_top (Nat.le_add_left 1 m)]
      
      sorry


theorem my_favorite_theorem3 {m : ℕ} (hm : 0 < m) :
    Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 5 ≤
    Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) 2 := by
  have powsimp (k : ℕ): (2 * k) ^ (2 * k + 1) = 2 ^ (2 * k + 1) * k ^ (2 * k + 1) := by
    apply mul_pow
  have prodeq: ∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1) =
      ∏ k ∈ Icc 1 m,  2 ^ (2 * k + 1) * k ^ (2 * k + 1) := by
    congr
    ext k

    sorry
  have prodfg: ∏ k ∈ Finset.Icc 1 m, (2 * k) ^ (2 * k + 1) =
     (∏ k ∈ Finset.Icc 1 m, 2 ^ (2 * k + 1)) * (∏ k ∈ Finset.Icc 1 m, k ^ (2 * k + 1)):= by
    --rw [prodeq]
   -- apply my_smul _ (b (k: ℕ): fun k ↦ 2 ^ (2 * k + 1)) (f (k: ℕ): fun k ↦ k ^ (2 * k + 1))
    sorry

  have : Nat.factorization (∏ k ∈ Icc 1 m, (2 * k) ^ (2 * k + 1)) =
    Nat.factorization (∏ k ∈ Finset.Icc 1 m, 2 ^ (2 * k + 1) ) +
    Nat.factorization (∏ k ∈ Finset.Icc 1 m, k ^ (2 * k + 1)) := by
    rw[prodfg]
    #check Nat.factorization_mul
    rw [Nat.factorization_mul]
    · sorry
    · sorry


  sorry

theorem tt {p : ℕ} (n : ℕ) :
  (p.digits n).sum ≥ 0 := by
  simp
