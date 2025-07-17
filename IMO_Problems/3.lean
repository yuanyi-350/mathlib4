import Mathlib

open Finset
open Nat

lemma step1 {n c k p : ℕ} : ∑ i ∈ Ico 1 (k + 1), n * (n + c) / p ^ (i + k)
    = ∑ i ∈ Ico (k + 1) (k + k + 1), n * (n + c) / p ^ i := by
  set f : ℕ → ℕ := fun i ↦ i + k
  have : ∀ i ∈ Ico 1 (k + 1), f i ∈ Ico (k + 1) (k + k + 1) := fun i hi ↦ by
    simp at hi; simp [f]; omega
  have f_inj : Set.InjOn f (Ico 1 (k + 1)) := by simp [f]
  have f_surj : Set.SurjOn f (Ico 1 (k + 1)) (Ico (k + 1) (k + k + 1)) := fun y hy ↦ by
    use y - k; simp at hy; simp [f]; omega
  have h : ∀ a ∈ Ico 1 (k + 1), n * (n + c) / p ^ (a + k) = n * (n + c) / p ^ (f a) := by simp [f]
  exact sum_nbij f this f_inj f_surj h

lemma le1 {n c k p : ℕ} (hp : p > 0) (hn : p ^ k ≤ n + c):
    (n + 1 + c) * ∑ i ∈ Ico 1 (k + 1), n / p ^ i
    ≤ (∑ i ∈ Ico 1 (k + 1), (n * (n + c))/(p ^ i))
    + (∑ i ∈ Ico (k + 1) (k + k + 1), (n * (n + c))/(p ^ i)):= by
  have : ∑ i ∈ Ico 1 (k + 1), n / p ^ i ≤ ∑ i ∈ Ico (k + 1) (k + k + 1), n * (n + c) / p ^ i := by
    rw [← step1]
    have : ∀ i ∈ Ico 1 (k + 1), n / p ^ i ≤ n * (n + c) / p ^ (i + k) := fun i hi ↦ by
      rw [Nat.pow_add p i k]
      have : (n / p ^ i) * (p ^ i * p ^ k) ≤ n * (n + c) := by
        rw [← mul_assoc]
        exact Nat.mul_le_mul (div_mul_le_self n (p ^ i)) hn
      refine (Nat.le_div_iff_mul_le ?_).mpr this
      simpa using ⟨Nat.pow_pos hp, Nat.pow_pos hp⟩
    exact sum_le_sum this
  have : (n + c) * ∑ i ∈ Ico 1 (k + 1), n / p ^ i ≤ ∑ i ∈ Ico 1 (k + 1), n * (n + c) / p ^ i := by
    -- (n+c) \cdot floor(\frac{n}{p^k}) \le floor(\frac{n(n+c)}{p^k})
    have : ∀ i ∈ Ico 1 (k + 1), (n + c) * (n / p ^ i) ≤ n * (n + c) / p ^ i := fun i hi ↦
      have : (n / p ^ i) * p ^ i ≤ n:= div_mul_le_self n (p ^ i)
      have : (n + c) * (n / p ^ i) * p ^ i ≤ n * (n + c) := by
        rw [mul_comm n (n + c), mul_assoc]
        exact Nat.mul_le_mul_left (n + c) this
      (Nat.le_div_iff_mul_le (Nat.pow_pos hp)).mpr this
    rw [mul_sum]
    exact sum_le_sum this
  calc
  _ = (n + c) * ∑ i ∈ Ico 1 (k + 1), n / p ^ i + ∑ i ∈ Ico 1 (k + 1), n / p ^ i:= by
    rw [Nat.add_right_comm, Nat.right_distrib, one_mul, Nat.add_left_cancel_iff]
  _ ≤ _ := by linarith

/- Let $c$ be a non-negative integer. Prove that for all $n \in \mathbb{N}$ (the set of non-negative
 integers), $(n!)^{n+1+c}$ divides $(n(n+c))!$.
-/
theorem my_favorite_theorem {c : ℕ} (n : ℕ) (hn : n ≠ 0) :
    (n !) ^ (n + 1 + c) ∣ (n * (n + c)) ! := by
  rw [← Nat.factorization_prime_le_iff_dvd]
  · intro p hp
    set t := Nat.factorization n p
    -- Suppose $p^k \leq n < p^{k+1}$
    set k := Nat.log p n with hk
    have hnb : Nat.log p n < k + 1 := lt_add_one (log p n)
    set k1 := Nat.log p (n * (n + c))
    have t1 : p ^ k ≤ n := by
      rw [hk]
      exact pow_log_le_self p hn
    -- Therefore $n(n+c) \geqslant p^{2 k}$
    have k1_le_2k : k1 ≥ 2 * k := by
      refine le_log_of_pow_le (Prime.one_lt hp) ?_
      have t21: p ^ (2 * k) ≤ n ^ 2 := by
        rw [Nat.pow_mul' p 2 k]
        exact Nat.pow_le_pow_left t1 2
      have t22: n ^ 2 ≤ n * (n + c) := by
        rw [pow_two]
        exact Nat.mul_le_mul_left n (Nat.le_add_right n c)
      exact Nat.le_trans t21 t22
    have: Fact (Nat.Prime p):= { out := hp }
    -- $V_p L = (n+1+c) \cdot \left(floor(\frac{n}{p}) + floor(\frac{n}{p^2}) + \cdots +
    -- floor(\frac{n}{p k})\right)$
    have VpL : (n ! ^ (n + 1 + c)).factorization p
        = (n + 1 + c) * (∑ i ∈ Ico 1 (k + 1), n / (p ^ i)):= by
      simp [Nat.factorization_pow, Nat.factorization_def (pp := hp), padicValNat_factorial hnb]
    -- V_p R \ge (floor(\frac{n(n+c)}{p}) + floor(\frac{n(n+c)}{p^2}) + \cdots +
    -- floor(\frac{n(n+c)}{p^k}) + floor(\frac{n(n+c)}{p^{k+1}}) + \cdots +
    -- floor(\frac{n(n+c)}{p^{k+k}})
    have VpR:  (n * (n + c))!.factorization p
        ≥ (∑ i ∈ Ico 1 (k + 1), (n * (n + c))/(p ^ i))
        + (∑ i ∈ Ico (k + 1) (k + k + 1), (n * (n + c))/(p ^ i)) := by
      have hnb : Nat.log p (n * (n + c)) < k1 + 1 := lt_add_one (log p (n * (n + c)))
      have IcoMerge1: ∑ i ∈ Ico 1 (k1 + 1), n * (n + c) / p ^ i =
          ∑ i ∈ Ico 1 (k + 1), n * (n + c) / p ^ i +
          ∑ i ∈ Ico (k + 1) (k1 + 1), n * (n + c) / p ^ i := by
        have hmn : 1 ≤ k + 1 := Nat.le_add_left 1 k
        have hnk : k + 1 ≤ k1 + 1 := by omega
        rw [Finset.sum_Ico_consecutive (fun i ↦ n * (n + c) / p ^ i) hmn hnk]
      rw [Nat.factorization_def (pp := hp), padicValNat_factorial hnb, IcoMerge1]
      apply Nat.add_le_add_iff_left.mpr
      have IcoMerge2: ∑ i ∈ Ico (k + 1) (k1 + 1), n * (n + c) / p ^ i =
          ∑ i ∈ Ico (k + 1) (k + k + 1), n * (n + c) / p ^ i +
          ∑ i ∈ Ico (k + k + 1) (k1 + 1), n * (n + c) / p ^ i := by
        rw [Finset.sum_Ico_consecutive (fun i ↦ n * (n + c) / p ^ i) (by omega) (by omega)]
      simp [IcoMerge2]
    rw [VpL]
    exact Nat.le_trans (le1 (pos_of_neZero p) (le_add_right_of_le t1)) VpR
  · simpa using factorial_ne_zero n
  · simpa using factorial_ne_zero (n * (n + c))
