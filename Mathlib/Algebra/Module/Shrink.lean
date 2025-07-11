/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.Ring.Shrink

/-!
# Transfer module and algebra structures from `α` to `Shrink α`.
-/

noncomputable section

variable {α β : Type*}

instance [Semiring α] [AddCommMonoid β] [Module α β] [Small β] : Module α (Shrink β) :=
  (equivShrink _).symm.module α

/-- A small module is linearly equivalent to its small model. -/
def linearEquivShrink (α β) [Semiring α] [AddCommMonoid β] [Module α β] [Small β] :
    β ≃ₗ[α] Shrink β :=
  ((equivShrink β).symm.linearEquiv α).symm

instance [CommSemiring α] [Semiring β] [Algebra α β] [Small β] : Algebra α (Shrink β) :=
  (equivShrink _).symm.algebra α

/-- A small algebra is algebra equivalent to its small model. -/
def algEquivShrink (α β) [CommSemiring α] [Semiring β] [Algebra α β] [Small β] :
    β ≃ₐ[α] Shrink β :=
  ((equivShrink β).symm.algEquiv α).symm
