import Mathlib

open Nat

lemma lemma1 (n : ℕ) (hnp : Nat.lcm n (factorial 5) = 5 * Nat.gcd n (factorial 10)) :
    n.primeFactors ⊆ {2, 3, 5, 7} := by
  have dvd1 : n ∣ Nat.lcm n (factorial 5) := Nat.dvd_lcm_left n (factorial 5)
  rw [hnp] at dvd1
  have dvd : n ∣ 5 * factorial 10 := Nat.dvd_mul_gcd_iff_dvd_mul.mp dvd1
  have : (5 * factorial 10).primeFactors = {2, 3, 5, 7} := by native_decide
  rw [← this]
  refine primeFactors_mono dvd ?_
  norm_num

lemma imp (a b n : ℕ)(h : min n a = max n b): b ≤ n ∧ n ≤ a := by
  constructor
  · linarith [min_le_left n a, le_max_right n b]
  · linarith [min_le_right n a, le_max_left n b]

lemma lemma2 (n : ℕ) (hn : n ≠ 0) (hnp : Nat.lcm n (factorial 5) =
    5 * Nat.gcd n (factorial 10)) : 3 ≤ n.factorization 2 ∧ n.factorization 2 ≤ 8 := by
  have eq : (Nat.lcm n (factorial 5)).factorization 2 =
    (5 * Nat.gcd n (factorial 10)).factorization 2 := by rw [hnp]
  have h1 : (Nat.factorization 5) 2 = 0 := by native_decide
  have h2 : (factorial 5).factorization 2 = 3 := by native_decide
  have h3 : (factorial 10).factorization 2 = 8 := by native_decide
  rw [Nat.factorization_lcm hn (by norm_num), Nat.factorization_mul (by norm_num),
    Finsupp.add_apply, h1, zero_add, factorization_gcd hn (by norm_num)] at eq
  · have eq : max (n.factorization 2) ((factorial 5).factorization 2) =
        min (n.factorization 2) ((factorial 10).factorization 2) := eq
    have : min (n.factorization 2) 8 = max (n.factorization 2) 3 := by rw [h2, h3] at eq; rw [eq]
    exact imp 8 3 (n.factorization 2) this
  · exact Nat.gcd_ne_zero_left hn

lemma lemma3 (n : ℕ) (hn : n ≠ 0) (hnp : Nat.lcm n (factorial 5) =
    5 * Nat.gcd n (factorial 10)) : 1 ≤ n.factorization 3 ∧ n.factorization 3 ≤ 4 := by
  have eq : (Nat.lcm n (factorial 5)).factorization 3 =
    (5 * Nat.gcd n (factorial 10)).factorization 3 := by rw [hnp]
  have h1 : (Nat.factorization 5) 3 = 0 := by native_decide
  have h2 : (factorial 5).factorization 3 = 1 := by native_decide
  have h3 : (factorial 10).factorization 3 = 4 := by native_decide
  rw [Nat.factorization_lcm hn (by norm_num), Nat.factorization_mul (by norm_num),
    Finsupp.add_apply, h1, zero_add, Nat.factorization_gcd hn (by norm_num)] at eq
  · have eq : max (n.factorization 3) ((factorial 5).factorization 3) =
        min (n.factorization 3) ((factorial 10).factorization 3) := eq
    have : min (n.factorization 3) 4 = max (n.factorization 3) 1 := by rw [h2, h3] at eq; rw [eq]
    exact imp 4 1 (n.factorization 3) this
  · exact Nat.gcd_ne_zero_left hn

lemma lemma4 (n : ℕ) (hn : n ≠ 0) (hnp : Nat.lcm n (factorial 5) =
    5 * Nat.gcd n (factorial 10)) : n.factorization 5 = 3 := by sorry

lemma lemma5 (n : ℕ) (hn : n ≠ 0) (hnp : Nat.lcm n (factorial 5) =
    5 * Nat.gcd n (factorial 10)) : n.factorization 7 ≤ 1 := by sorry

#check Nat.factorization_inj

-- def iso : {n : ℕ // n ≠ 0 ∧ 5 ∣ n ∧ Nat.lcm n (factorial 5) = 5 * Nat.gcd n (factorial 10)} ≃
--  {α : ℕ // 3 ≤ α ∧ α ≤ 8} × {β : ℕ // 1 ≤ β ∧ β ≤ 4} ×
--   {γ : ℕ // γ = 3} × {τ : ℕ // τ ≤ 1} where
--   toFun := fun ⟨n, ne, hn1, hn2⟩ ↦ by
--     use ⟨n.factorization 2, lemma2 n ne hn2⟩
--     use ⟨n.factorization 3, lemma3 n ne hn2⟩
--     use ⟨n.factorization 5, lemma4 n ne hn2⟩
--     use (⟨n.factorization 7, lemma5 n ne hn2⟩ : {τ : ℕ // τ ≤ 1})
--     simp
--     exact lemma5 n ne hn2
--   invFun := by
--     intro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩
--     use 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d
--     constructor
--     · exact Ne.symm (NeZero.ne' (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d))
--     · constructor
--       · have dvd1 : 5 ^ c ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := by
--           use 2 ^ a * 3 ^ b * 7 ^ d
--           ring
--         have dvd2 : 5 ∣ 5 ^ c := by simp [hc]
--         exact Nat.dvd_trans dvd2 dvd1
--       ·
--         have : (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d).lcm (factorial 5) = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d
--           := by

--           have : factorial 5 ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := by
--             sorry
--           -- apply?
--           sorry
--         sorry
--   left_inv := by
--     intro n

--     sorry
--   right_inv := sorry

theorem my_favorite_theorem : Nat.card {n : ℕ // n ≠ 0 ∧ n % 5 = 0 ∧ Nat.lcm n (factorial 5) =
    5 * Nat.gcd n (factorial 10)} = 48 := by
  sorry
