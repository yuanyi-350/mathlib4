import Mathlib

theorem Macdonald_1_7 {R : Type*} [CommRing R] (p : Ideal R) [hp : p.IsPrime]
    (h : ∀ x : R, ∃ n > 1, x ^ n = x) : p.IsMaximal :=
  -- consider the quotient ring $R/\mathfrak{p}$,
  Ideal.Quotient.maximal_of_isField p {
    exists_pair_ne := exists_pair_ne (R ⧸ p)
    mul_comm x y := CommMonoid.mul_comm x y
    mul_inv_cancel := by
      intro a ha
      obtain⟨a₀, ha₀⟩ : ∃ a₀ : R, Ideal.Quotient.mk p a₀ = a := Quotient.exists_rep a
      obtain⟨n, h1, hn⟩ := h a₀
      -- $\forall x \in R/\mathfrak{p}$, there exist $n$ which $x^n = x$.
      have : a ^ n = a := by
        have : (Ideal.Quotient.mk p a₀) ^ n = (Ideal.Quotient.mk p (a₀ ^ n)) := rfl
        rw [← ha₀, this, hn]
      have eq : a ^ (n - 1) - 1 = 0 := by
        -- as $\mathfrak{p}$ is a prime ideal, it is a intergral domain.
        refine (mul_eq_zero_iff_right ha).mp ?_
        -- Therefore $(x^{n -1} - 1) \cdot x = 0 \implies x^{n - 1} - 1 = 0$
        rw [sub_mul, pow_sub_one_mul (Nat.ne_zero_of_lt h1) a, this, one_mul, sub_self]
      use a ^ (n - 2)
      nth_rw 1 [← pow_one a]
      have : 1 + (n - 2) = n - 1 := by omega
      rwa [← npow_add, this, ← sub_eq_zero]
      -- We have proved that $R/\mathfrak{p}$ is a field. We are done
  }

theorem Macdonald_2_9 {R : Type u_1} [CommRing R] {M : Type u_2} [AddCommGroup M] [Module R M]
  {M' : Type u_3} [AddCommGroup M'] [Module R M'] {f : M →ₗ[R] M'} {M'' : Type u_4}
  [AddCommGroup M''] [Module R M''] [DecidableEq M'] {g : M' →ₗ[R] M''}
  (hf : Function.Injective ⇑f) (hfg : Function.Exact ⇑f ⇑g) (hg : Function.Surjective ⇑g)
  (FGM : (⊤ : Submodule R M).FG) (FGM'' : (⊤ : Submodule R M'').FG) :
  (⊤ : Submodule R M').FG := by
    obtain ⟨S, hS⟩ := FGM
    obtain ⟨S'', hS''⟩ := FGM''
    set A : Finset M' := Set.Finite.toFinset (Finite.Set.finite_image S ⇑f) with hA
    have : A = ⇑f '' S := by simp [hA]

    set h : S'' → M' := fun x ↦ Classical.choose (hg x) with hh
    set B := Set.Finite.toFinset (Finite.Set.finite_image (⊤ : Set S'') h) with hB
    have comp : ∀ x : S'', g (h x) = x := fun x ↦ by
        simpa [hh] using Classical.choose_spec (hg x)
    have comp_eq_id : g ∘ h = fun (x : S'') ↦ ↑x :=
      (Set.eqOn_univ (⇑g ∘ h) fun x => ↑x).mp fun ⦃x⦄ a => comp x

    have : g '' B = S'' := by
      have : Set.range h = h '' ⊤ := by rw [Set.top_eq_univ, Set.image_univ]
      simp only [hB, Set.top_eq_univ, Set.image_univ, Set.Finite.coe_toFinset]
      rw [this, ← Set.image_comp (⇑g) h ⊤, comp_eq_id]
      simp

    set iso : B ≃ S'' := {
      toFun := fun x ↦ by
        use g x
        have gxin : g ↑x ∈ ⇑g '' ↑B := by use x; simp
        rwa [this] at gxin
      invFun := fun x ↦ by
        use h x
        simp [hB]
      left_inv x := by
        simp
        refine Eq.symm (Subtype.coe_eq_of_eq_mk ?_)
        simp [hh]
        
        sorry
      right_inv x := Subtype.eq (comp x)
    }

    -- have :

    use A ∪ B
    refine Submodule.eq_top_iff'.mpr fun x => ?_

    have : g x ∈ Submodule.span R S'' := by simp [hB, hS'']
    rw [Submodule.mem_span_finset] at this
    obtain⟨k, ksupp, keq⟩ := this

    have : g (x - ∑ a ∈ B, k (g a) • a) = 0 := by
      simp [← keq]
      have : ∑ a ∈ S'', k a • a = ∑ x ∈ B, k (g x) • g x := by
        #check Finset.sum_bijective
        sorry
      -- have : ∑ x ∈ B, k (g x) • g x  = ∑ x ∈ B, k (g x) • g x



      sorry





    rw [Submodule.mem_span_finset]





    -- rw [Submodule.mem_span_iff_exists_finset_subset] at this

    --   obtain ⟨k, t, tsub, fsub, eq⟩ := this
    --   -- have : x - ∑ a ∈ t, k a •


    -- #check A ∪ B

    sorry
    -- obtain ⟨S, S_Finite, hS⟩ := Submodule.fg_def.mp FGM
    -- obtain ⟨S'', S''_Finite, hS''⟩ := Submodule.fg_def.mp FGM''
    -- have Finite_A : Finite (⇑f '' S) :=
    --   have : Finite ↑S := S_Finite
    --   Finite.Set.finite_image S ⇑f
    -- set A : Set M' := ⇑f '' S with hA
    -- obtain⟨B, Finite_B, hB⟩ : ∃ B : Set M', Finite B ∧ g '' B = S'' := by
    --   set h : S'' → M' := fun x ↦ Classical.choose (hg x) with hh
    --   use h '' (⊤ : Set S'')
    --   constructor
    --   · have : Finite (⊤ : Set S'') :=
    --       have : Finite S'' := S''_Finite
    --       Subtype.finite
    --     exact Finite.Set.finite_image (⊤ : Set S'') h
    --   · have : ∀ x : S'', g (h x) = x := fun x ↦ by
    --       simpa [hh] using Classical.choose_spec (hg x)
    --     have : g ∘ h = fun (x : S'') ↦ ↑x :=
    --       (Set.eqOn_univ (⇑g ∘ h) fun x => ↑x).mp fun ⦃x⦄ a => this x
    --     rw [← Set.image_comp (⇑g) h ⊤, this, Set.top_eq_univ, Set.image_univ,
    --       Subtype.range_coe_subtype, Set.setOf_mem_eq]
    -- rw [Submodule.fg_def]
    -- use A ∪ B
    -- constructor
    -- · exact Set.Finite.union Finite_A Finite_B
    -- ·
    --
    --   set B' := Set.Finite.toFinset (Finite.Set.finite_image B ⇑g)
    --   -- #check (⟨, this⟩ : Finset M'')





      -- sorry
