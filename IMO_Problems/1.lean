import Mathlib

open Nat

lemma lcm_div_eq {m n k : ℕ} (hm : m > 0) (hn : n > 0) (hkm : m ∣ k) (hkn : n ∣ k) :
    (k / m).lcm (k / n) = k / (m.gcd n) := by
  rw [Nat.lcm_eq_iff]
  constructor
  · refine dvd_div_of_mul_dvd ?_
    rw [← Nat.mul_div_assoc (m.gcd n) hkm]
    refine (div_dvd_iff_dvd_mul ?_ hm).mpr ?_
    · exact Nat.dvd_mul_left_of_dvd hkm (m.gcd n)
    · exact Nat.mul_dvd_mul_right (Nat.gcd_dvd_left m n) k
  · constructor
    · refine dvd_div_of_mul_dvd ?_
      rw [← Nat.mul_div_assoc (m.gcd n) hkn]
      refine (div_dvd_iff_dvd_mul ?_ hn).mpr ?_
      · exact Nat.dvd_mul_left_of_dvd hkn (m.gcd n)
      · exact Nat.mul_dvd_mul_right (Nat.gcd_dvd_right m n) k
    . intro c hmc hnc
      rw [Nat.div_dvd_iff_dvd_mul hkm hm] at hmc
      rw [Nat.div_dvd_iff_dvd_mul hkn hn] at hnc
      rw [Nat.div_dvd_iff_dvd_mul (Nat.dvd_trans (Nat.gcd_dvd_left m n) hkm)
        (gcd_pos_of_pos_left n hm)]
      have : k ∣ (m * c).gcd (n * c) := Nat.dvd_gcd hmc hnc
      rwa [Nat.gcd_mul_right m c n] at this

theorem my_favorite_theorem' (L : ℕ) (hL : L > 0) (v : Fin 3 → ℕ)
    (hv0 : v 0 = 155) (hv1 : v 1 = 200) (hv2 : v 2 = 275)
    (t : ℕ) (ht : IsLeast {t | 0 < t ∧ ∀ i, v i * t % L = 0} t)
    (g : Fin 3 → ℕ) (hg : ∀ i, g i = Nat.gcd (v i) L)
    (N : Fin 3 → ℕ) (hN : ∀ i, N i = L / g i)
    (D : Fin 3 → ℕ) (hD : ∀ i, D i = v i / g i) :
    t = Nat.lcm (Nat.lcm (N 0) (N 1)) (N 2) / Nat.gcd (Nat.gcd (D 0) (D 1)) (D 2) := by
  have gpos : ∀ i, g i > 0 := fun i ↦ by
    rw [hg i]
    exact gcd_pos_of_pos_right (v i) hL
  have hN1 : ∀ i, g i * N i = L := fun i ↦ by
    rw [hN, Nat.mul_div_cancel']
    simpa [hg i] using Nat.gcd_dvd_right (v i) L
  have Ndvd : ∀ i, g i ∣ L := fun i ↦ by use N i; rw [hN1 i]
  have dvd : ((D 0).gcd (D 1)).gcd (D 2) ∣ ((N 0).lcm (N 1)).lcm (N 2) := by
    have : (L / g 0).lcm (L / g 1) = L / ((g 0).gcd (g 1)) :=
      lcm_div_eq (gpos 0) (gpos 1) (Ndvd 0) (Ndvd 1)
    have : ((L / g 0).lcm (L / g 1)).lcm (L / g 2) = L / ((g 0).gcd (g 1)).gcd (g 2) := by
      rw [this]
      refine lcm_div_eq (gcd_pos_of_pos_left (g 1) (gpos 0)) (gpos 2) ?_ (Ndvd 2)
      exact Nat.dvd_trans (Nat.gcd_dvd_left (g 0) (g 1)) (Ndvd 0)
    rw [hN 0, hN 1, hN 2, this]

    sorry
  have hD : ∀ i, g i * D i = v i := fun i ↦ by
    rw [hD, Nat.mul_div_cancel']
    simpa [hg i] using Nat.gcd_dvd_left (v i) L
  rcases ht with ⟨⟨tlt, tdvd⟩, tlb⟩
  dsimp [lowerBounds] at tlb
  set a0 := Nat.lcm (Nat.lcm (N 0) (N 1)) (N 2) / Nat.gcd (Nat.gcd (D 0) (D 1)) (D 2) with ha0
  have : ∀ (i : Fin 3), v i * a0 % L = 0 := by
    intro i
    rw [ha0, mod_eq_zero_of_dvd]
    have : N i ∣ D i * (((N 0).lcm (N 1)).lcm (N 2) / ((D 0).gcd (D 1)).gcd (D 2)) := by
      have : D i * (((N 0).lcm (N 1)).lcm (N 2) / ((D 0).gcd (D 1)).gcd (D 2))
          = ((N 0).lcm (N 1)).lcm (N 2) * (D i  / ((D 0).gcd (D 1)).gcd (D 2)) := by calc
        _ = (D i * ((N 0).lcm (N 1)).lcm (N 2)) / ((D 0).gcd (D 1)).gcd (D 2) := by
          refine Eq.symm (Nat.mul_div_assoc (D i) ?_)

          sorry
        _ = ((N 0).lcm (N 1)).lcm (N 2) * D i / ((D 0).gcd (D 1)).gcd (D 2) := by rw [mul_comm]
        _ = _ := by
          refine Nat.mul_div_assoc (((N 0).lcm (N 1)).lcm (N 2)) ?_
          fin_cases i
          · simpa [Nat.gcd_assoc] using Nat.gcd_dvd_left (D 0) ((D 1).gcd (D 2))
          · simp
            have dvd1 : (D 0).gcd (D 1) ∣ D 1 := Nat.gcd_dvd_right (D 0) (D 1)
            have dvd2 : ((D 0).gcd (D 1)).gcd (D 2) ∣ (D 0).gcd (D 1) :=
              Nat.gcd_dvd_left ((D 0).gcd (D 1)) (D 2)
            exact Nat.dvd_trans dvd2 dvd1
          · simpa using Nat.gcd_dvd_right ((D 0).gcd (D 1)) (D 2)
      sorry
    have : g i * N i ∣ g i * (D i * (((N 0).lcm (N 1)).lcm (N 2) / ((D 0).gcd (D 1)).gcd (D 2))) :=
      Nat.mul_dvd_mul_left (g i) this
    rwa [← mul_assoc, hN1 i, hD i] at this
  have : 0 < a0 ∧ ∀ (i : Fin 3), v i * a0 % L = 0 := by
    constructor
    · rw [ha0]
      refine Nat.div_pos ?_ ?_
      · sorry
      · sorry
    · exact this
  have le1 := tlb this
  sorry
