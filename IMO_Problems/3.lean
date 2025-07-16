import Mathlib

open Finset
open Nat

variable(t k: ℕ)

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem my_favorite_theorem {c : ℕ} (n : ℕ) (hn : n ≠ 0) :
    (n !) ^ (n + 1 + c) ∣ (n * (n + c)) ! := by
  rw [← Nat.factorization_prime_le_iff_dvd]
  · intro p hp
    set t := Nat.factorization n p
    set k := Nat.log p n
    have plt1: p>1:= Prime.one_lt hp
    have hnb : Nat.log p n < k + 1 := by exact lt_add_one (log p n)
    have tlek: t ≤ k := by
      have t_pow_le_t: p ^ t ≤ n:= by
        apply Nat.ordProj_le
        exact hn
      have t_lt_kpow: n < p ^ (k + 1) := by
        refine lt_pow_succ_log_self plt1 n
      have t_pow_lt_kpow: p ^ t < p ^ (k + 1) := by
        apply LT.lt.trans_le' t_lt_kpow t_pow_le_t
      have : t < k + 1 := by
        apply (pow_lt_pow_iff_right₀ plt1).mp t_pow_lt_kpow
      exact (pow_le_iff_le_log plt1 hn).mp t_pow_le_t
    have VpL : (n ! ^ (n + 1 + c)).factorization p = (n + 1 + c) * (∑ i ∈ Ico 1 (t + 1), n/(p ^ i))
        +  (n + 1 + c) * (∑ i ∈ Ico (t + 1) (k + 1), n/(p ^ i)) := by
      simp [Nat.factorization_pow]
      rw [Nat.factorization_def (pp := hp)]   --Note:feed pp, so that avoid to add one goal

      have: Fact (Nat.Prime p):= { out := hp }
      rw [padicValNat_factorial hnb]

      have IcoMerge: ∑ i ∈ Ico 1 (k + 1), n / p ^ i =
          ∑ i ∈ Ico 1 (t + 1), n / p ^ i +
          ∑ i ∈ Ico (t + 1) (k + 1), n / p ^ i := by
        have hmn: 1 ≤ t+1 := Nat.le_add_left 1 t
        have hnk: t+1 ≤ k+1 := Nat.add_le_add_right tlek 1
        #check Finset.sum_Ico_consecutive (fun i ↦ n / p ^ i) hmn hnk
        -- rw [Finset.sum_Ico_consecutive (fun i ↦ n / p ^ i) hmn hnk]
        rw [Finset.sum_Ico_consecutive _ hmn hnk]

      have IcoMerge: ∑ i ∈ Ico 1 (k + 1), n / p ^ i =
          ∑ i ∈ Ico 1 (t + 1), n / p ^ i +
          ∑ i ∈ Ico (t + 1) (k + 1), n / p ^ i := by
        have hmn: 1 ≤ t+1 := by sorry
        have hnk: t+1 ≤ k+1 := by sorry

        --apply Finset.sum_Ico_consecutive (fun: i ↦ p ^ i) hmn hnk
        sorry
      sorry






    have VpR:  (n * (n + c))!.factorization p ≥ n * (n + c) * (∑ a ∈ Icc 1 t, n/(p ^ a))
        + n * (n + c) * (∑ a ∈ Icc (t + 1) k, n/(p ^ a))
        + n * (n + c) * (∑ a ∈ Icc (k + 1) (k + t), n/(p ^ a)) := by
      sorry
    sorry
  · simpa using factorial_ne_zero n
  · simpa using factorial_ne_zero (n * (n + c))
