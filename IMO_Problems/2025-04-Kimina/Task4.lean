import Mathlib

def a (n : ℕ) : ℝ := match n with
  | 0 => 1
  | 1 => 1
  | n + 2 => a (n + 1) + 2 * a n

-- We can solve the first recurrence relation to give
-- $a_{n}=\left(2^{n}+(-\right.$ $\left.1)^{n+1}\right) / 3$.
lemma sublemma1 : ∀ n, a n = ((2 : ℝ) ^ (n + 1) + (-1 : ℝ) ^ n) / (3 : ℝ) := by
  intro n
  induction' n using Nat.twoStepInduction with n ih₁ ih₂
  · simp
    norm_num
    rfl
  · simp
    norm_num
    rfl
  · have : a (n + 2) = a (n + 1) + 2 * a n := rfl
    rw [this, ih₁, ih₂]
    ring

def b (n : ℕ) : ℝ := match n with
  | 0 => 1
  | 1 => 7
  | n + 2 => 2 * b (n + 1) + 3 * b n

-- Similarly, for the second recurrence relation we get $b_{n}=2 \cdot 3^{n-1}+(-1)^{n}$.
lemma sublemma2 : ∀ n, b n = (2 : ℝ) * (3 : ℝ) ^ n + (-1 : ℝ) ^ (n + 1) := by
  intro n
  induction' n using Nat.twoStepInduction with n ih₁ ih₂
  · simp
    norm_num
    rfl
  · simp
    norm_num
    rfl
  · have : b (n + 2) = 2 * b (n + 1) + 3 * b n := rfl
    rw [this, ih₁, ih₂]
    ring

lemma sublemma3 (m n : ℕ) : (-1) ^ m ≡ (-1) ^ n * 3 [ZMOD 8] → False := by
  intro h
  rw [neg_one_pow_eq_ite, neg_one_pow_eq_ite] at h
  split_ifs at h
  <;> repeat simp [Int.modEq_iff_dvd] at h

lemma sublemma4 (m n : ℕ) : 2 ^ (m + 1) + (-1) ^ m = (2 * 3 ^ n + (-1) ^ (n + 1)) * 3 → m ≤ 2 := by
  intro h
  by_contra! nh
  -- If $\mathrm{m}&gt;2$, then $2^{\mathrm{m}}=0 \bmod 8$.
  have : 2 ^ (m + 1) ≡ 0 [ZMOD 8] := by
    have : (8 : ℤ) = (2 : ℤ) ^ 3 := by norm_num
    rw [Int.modEq_zero_iff_dvd, this]
    exact pow_dvd_pow 2 (Nat.le_add_right_of_le nh)
  have : 2 ^ (m + 1) + (-1) ^ m ≡ (-1) ^ m [ZMOD 8] := by
    have := Int.ModEq.add_right ((-1) ^ m) this
    simpa using this
  have h : (-1) ^ m ≡ (2 * 3 ^ n + (-1) ^ (n + 1)) * 3 [ZMOD 8] :=
    Int.ModEq.trans (id (Int.ModEq.symm this)) (congrFun (congrArg HMod.hMod h) 8)
  -- But $3^{\mathrm{n}}=(-1)^{\mathrm{n}} \bmod 4$,
  have : 3 ^ n ≡ (-1) ^ n [ZMOD 4] := by
    refine Int.ModEq.pow n ?_
    refine Int.modEq_of_dvd ?_
    norm_num

  have : 2 * 3 ^ n + (-1) ^ (n + 1) ≡ (-1) ^ n [ZMOD 8] := by
    have : 2 * 3 ^ n ≡ 2 * (-1) ^ n [ZMOD 2 * 4] := Int.ModEq.mul_left' this
    norm_num at this
    have eq1 : 2 * 3 ^ n + (-1) ^ (n + 1) ≡ 2 * (-1) ^ n + (-1) ^ (n + 1) [ZMOD 8] :=
      Int.ModEq.add this rfl
    have eq2 : 2 * (-1) ^ n + (-1) ^ (n + 1) ≡ (-1) ^ n [ZMOD 8] := by
      congr
      ring
    exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm eq2)) (id (Int.ModEq.symm eq1)))
  -- so $2.3^{\mathrm{n}}+3(-1)^{\mathrm{n}}+(-1)^{\mathrm{m}}=
  -- 5(-1)^{\mathrm{n}}+(-1)^{\mathrm{m}} \bmod 8$  which cannot be $0 \bmod 8$.
  have : (2 * 3 ^ n + (-1) ^ (n + 1)) * 3 ≡ (-1) ^ n * 3 [ZMOD 8] :=
    Int.ModEq.mul this rfl
  have : (-1) ^ m ≡ (-1) ^ n * 3 [ZMOD 8] := Int.ModEq.trans h this
  exact sublemma3 m n this

lemma sublemma5 (n : ℕ) : 2 * 3 ^ n + (-1) ^ (n + 1) = 1 → n = 0 := by
  intro h
  by_contra! nh
  have : n ≥ 1 := by omega
  have : 3 ^ n ≥ 3 := Nat.le_pow this
  have : 2 * 3 ^ n ≥ 6 := by linarith
  have : (-1) ^ (n + 1) ≥ -1 := by
    rw [neg_one_pow_eq_ite]
    split_ifs <;> simp
  linarith

/- The sequence $a_{n}$ is defined by $a_{1}=a_{2}=1, a_{n+2}=a_{n+1}+2 a_{n}$.
The sequence $b_{n}$ is defined by $b_{1}=1, b_{2}=7$, $b_{n+2}=2 b_{n+1}+3 b_{n}$.
Show that the only integer in both sequences is 1 . -/
theorem my_favorite_theorem :
    ∀ m n, a m = b n ↔ ((m, n) = (0, 0) ∨ (m, n) = (1, 0)) := by
  intro m n
  constructor
  · intro h
    simp [sublemma1 m, sublemma2 n, div_eq_iff] at h
    have eq1: (2 : ℝ) ^ (m + 1) + (-1 : ℝ) ^ m = (((2 : ℤ) ^ (m + 1) + (-1 : ℤ) ^ m : ℤ) : ℝ) := by
      simp
    have eq2: (2 * (3 : ℝ) ^ n + (-1 : ℝ) ^ (n + 1)) * (3 : ℝ)
            = (((2 * 3 ^ n + (-1) ^ (n + 1)) * 3 : ℤ) : ℝ) := by simp
    -- So if $a_{m}=b_{n}$
    -- then $2 \cdot 3^{n}+3(-$ $1)^{\mathrm{n}}=2^{\mathrm{m}}+(-1)^{\mathrm{m}+1}$ or
    -- $2^{\mathrm{m}}=2.3^{\mathrm{n}}+3(-1)^{\mathrm{n}}+(-1)^{\mathrm{m}}$.
    rw [eq1, eq2, Int.cast_inj] at h
    -- there are no solutions for $\mathrm{m}&gt;2$.
    have : m ≤ 2 := sublemma4 m n h
    interval_cases m <;>
    simp at h
    -- If $m=1$ or 2 , then we find $n=1$ is the only solution,
    -- corresponding to the fact that the term 1 is in both sequences.
    · simp [sublemma5 n h]
    · simp [sublemma5 n h]
    have : 2 * 3 ^ n + (-1) ^ (n + 1) = 9 / 3 :=
      Int.eq_ediv_of_mul_eq_left (Ne.symm (NeZero.ne' 3)) (id (Eq.symm h))
    norm_num at this
    have dvd1 : 3 ∣ 2 * 3 ^ n + (-1) ^ (n + 1) := by rw [this]
    have dvd2 : (3 : ℤ) ∣ 2 * (3 : ℤ) ^ n := by
      refine Dvd.dvd.mul_left ?_ 2
      refine dvd_pow_self 3 ?_
      by_contra! nh
      simp [nh] at this
    have : 3 ∣ (-1) ^ (n + 1) := (Int.dvd_iff_dvd_of_dvd_add dvd1).mp dvd2
    rw [neg_one_pow_eq_ite] at this
    split_ifs at this
    <;> simp at this
  · intro h
    rcases h with h | h
    repeat simp at h; rw [h.1, h.2]; rfl
