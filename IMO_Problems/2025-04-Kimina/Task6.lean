import Mathlib

open Real Set

-- $x+3-3 \sqrt{x+1}=x+1-3 \sqrt{x+1}+2=(\sqrt{x+1})^{2}-3 \sqrt{x+1}+2=(\sqrt{x+1}-1)
-- (\sqrt{x+1}-2)$
theorem sublemma {x : ℝ} (hx2 : x + 1 ≥ 0): x + 3 - 3 * sqrt (x + 1) = (sqrt (x + 1) - 1) *
    (sqrt (x + 1) - 2) := by
  have h1 : (sqrt (x + 1)) ^ 2 = x + 1 := by rwa [Real.sq_sqrt]
  nlinarith [h1, Real.sqrt_nonneg (x + 1)]

theorem sublemma1 {x : ℝ} (hx2 : x + 1 ≥ 0) : 0 < (√(x + 1) - 1) * (√(x + 1) - 2) → x ∈ Ioi 3 ∪
    Ico (-1) 0:= by
  intro h
  rcases mul_pos_iff.mp h with ⟨pos1, pos2⟩ | ⟨neg1, neg2⟩
  · have t2 : 3 < x := by
      have h3 : (Real.sqrt (x + 1)) ^ 2 = x + 1 := Real.sq_sqrt (show 0 ≤ x + 1 by linarith)
      linarith [h3]
    simp [t2]
  · have h6 : Real.sqrt (x + 1) ^ 2 < (1 : ℝ) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x + 1)]
    have h7 : Real.sqrt (x + 1) ^ 2 = x + 1 := Real.sq_sqrt (show x + 1 ≥ 0 by linarith)
    norm_num [h7] at h6
    have h9 : x < 0 := by linarith
    have h10 : -1 ≤ x := by linarith
    right
    exact ⟨h10, h9⟩

theorem sublemma2 {x : ℝ} (hx2 : x + 1 ≥ 0) : 0 > (√(x + 1) - 1) * (√(x + 1) - 2) → x ∈ Ioo 0 3:=by
  intro h
  have h1 : (√(x + 1) - 1) * (√(x + 1) - 2) < 0 := by linarith
  cases mul_neg_iff.mp h1 with
  | inl h2 =>
    have h5 : 0 < x := by
      have h7 : (1 : ℝ) ^ 2 < (√(x + 1) : ℝ) ^ 2 := by nlinarith [Real.sqrt_nonneg (x + 1)]
      have h9 : (√(x + 1) : ℝ) ^ 2 = x + 1 := by rwa [Real.sq_sqrt]
      nlinarith [h9]
    have h10 : x < 3 := by
      have h13 : (√(x + 1) : ℝ) ^ 2 = x + 1 := by rwa [Real.sq_sqrt]
      nlinarith [h13]
    exact ⟨h5, h10⟩
  | inr h2 =>
    linarith [show (1 : ℝ) ≤ √(x + 1) from by
      have h6 : 0 ≤ √(x + 1) := Real.sqrt_nonneg (x + 1)
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x + 1 by linarith)]
    , show (2 : ℝ) > 0 by norm_num]

theorem sublemma3 {x : ℝ} : 0 < x ^ 2 - 4 * x → x ∈ Ioi 4 ∪ Iio 0 := by
  intro hx
  have h1 : x ^ 2 - 4 * x = x * (x - 4) := by ring
  rw [h1] at hx
  cases mul_pos_iff.mp hx with
  | inl h =>
    have h4 : x > 4 := by linarith
    simp [h4]
  | inr h =>
    have h2 : x < 0 := by linarith [h.1]
    simp [h2]

theorem sublemma4 (x : ℝ) (hx : x ∈ Set.Ico (-1) 0) :
    (sqrt (x + 1) - 1) * (sqrt (x + 1) - 2) / (x ^ 2 - 4 * x) > 0 := by
  rcases hx with ⟨h1, h2⟩
  have h4 : sqrt (x + 1) < 1 := by rw [Real.sqrt_lt] <;> (try norm_num) <;> linarith
  have h5 : (sqrt (x + 1) - 1) * (sqrt (x + 1) - 2) > 0 :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have h8 : x ^ 2 - 4 * x > 0 := by nlinarith [sq_nonneg x, show x < 0 by linarith]
  apply div_pos (by linarith) (by linarith)

theorem sublemma5 (x : ℝ) (hx : x ∈ Set.Ioo 0 3) :
    (√(x + 1) - 1) * (√(x + 1) - 2) / (x ^ 2 - 4 * x) > 0 := by
  rcases hx with ⟨hx1, hx2⟩
  have h2 : 1 < √(x + 1) := by
    rw [Real.lt_sqrt] <;> (try norm_num)
    exact hx1
  have h3 : √(x + 1) < 2 := by
    rw [Real.sqrt_lt] <;> (try norm_num) <;> linarith
  have num_neg : (√(x + 1) - 1) * (√(x + 1) - 2) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have denom_neg : x ^ 2 - 4 * x < 0 := by
    have h4 : x ^ 2 - 4 * x = x * (x - 4) := by ring
    rw [h4]
    apply mul_neg_of_pos_of_neg (by linarith) (by linarith)
  apply div_pos_of_neg_of_neg (by linarith) (by linarith)

theorem sublemma6 {x : ℝ} (hx : x > 4) :
    (sqrt (x + 1) - 1) * (sqrt (x + 1) - 2) / (x ^ 2 - 4 * x) > 0 := by
  have h1 : sqrt (x + 1) > 2 := by
    have h3 : sqrt (x + 1) > sqrt 5 := Real.sqrt_lt_sqrt (by linarith) (by linarith)
    have h4 : sqrt 5 > 2 := by
      have h5 : sqrt 5 > sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h6 : sqrt 4 = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
      linarith [h5, h6]
    linarith [h3, h4]
  have h2 : x ^ 2 - 4 * x > 0 := by
    have h5 : x * (x - 4) > 0 := mul_pos (by linarith) (by linarith)
    nlinarith
  have h3 : (sqrt (x + 1) - 1) * (sqrt (x + 1) - 2) > 0 := mul_pos (by linarith) (by linarith)
  apply div_pos h3 h2


-- 5. Solve the inequality $\frac{x+3-3 \sqrt{x+1}}{x^{2}-4 x}>0$ (10 points)
theorem my_favorite_theorem {x : ℝ} (hx2 : x + 1 ≥ 0) :
    (x + 3 - 3 * sqrt (x + 1)) / (x^2 - 4 * x) > 0 ↔ x ∈ Ico (-1) 0 ∪ Ioo 0 3 ∪ Ioi 4 := by
  rw [sublemma hx2]
  constructor
  · intro h
    -- С учетом ОДЗ имеем $x \in[-1 ; 0) \cup(0 ; 3) \cup(4 ;+\infty)$
    rcases div_pos_iff.mp h with ⟨pos1, pos2⟩ | ⟨neg1, neg2⟩
    · rcases (sublemma3 pos2) with ch | ch
      · simp [ch]
      · rcases (sublemma1 hx2 pos1) with ch2 | ch2
        · have h1 : x ∈ Iio 0 ∩ Ioi 3 := mem_inter ch ch2
          have h2 : Iio (0 : ℝ) ∩ Ioi 3 = ∅ := by ext x; simp; intro h; linarith
          rw [h2] at h1
          contradiction
        · simp [ch2]
    · simp [sublemma2 hx2 neg1]
  · intro h
    rcases h with ch | ch
    · rcases ch with ch | ch
      · exact sublemma4 x ch
      · exact sublemma5 x ch
    · exact sublemma6 ch
