/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Sigma

/-!
# Darts in graphs

A `Dart` or half-edge or bond in a graph is an ordered pair of adjacent vertices, regarded as an
oriented edge. This file defines darts and proves some of their basic properties.
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A `Dart` is an oriented edge, implemented as an ordered pair of adjacent vertices.
This terminology comes from combinatorial maps, and they are also known as "half-edges"
or "bonds." -/
structure Dart extends V × V where
  adj : G.Adj fst snd
  deriving DecidableEq

initialize_simps_projections Dart (+toProd, -fst, -snd)

attribute [simp] Dart.adj

variable {G}

theorem Dart.ext_iff (d₁ d₂ : G.Dart) : d₁ = d₂ ↔ d₁.toProd = d₂.toProd := by
  cases d₁; cases d₂; simp

@[ext]
theorem Dart.ext (d₁ d₂ : G.Dart) (h : d₁.toProd = d₂.toProd) : d₁ = d₂ :=
  (Dart.ext_iff d₁ d₂).mpr h

@[simp]
theorem Dart.fst_ne_snd (d : G.Dart) : d.fst ≠ d.snd :=
  fun h ↦ G.irrefl (h ▸ d.adj)

@[simp]
theorem Dart.snd_ne_fst (d : G.Dart) : d.snd ≠ d.fst :=
  fun h ↦ G.irrefl (h ▸ d.adj)

theorem Dart.toProd_injective : Function.Injective (Dart.toProd : G.Dart → V × V) :=
  Dart.ext

instance Dart.fintype [Fintype V] [DecidableRel G.Adj] : Fintype G.Dart :=
  Fintype.ofEquiv (Σ v, G.neighborSet v)
    { toFun := fun s => ⟨(s.fst, s.snd), s.snd.property⟩
      invFun := fun d => ⟨d.fst, d.snd, d.adj⟩ }

/-- The edge associated to the dart. -/
def Dart.edge (d : G.Dart) : Sym2 V :=
  Sym2.mk d.toProd

@[simp]
theorem Dart.edge_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).edge = Sym2.mk p :=
  rfl

@[simp]
theorem Dart.edge_mem (d : G.Dart) : d.edge ∈ G.edgeSet :=
  d.adj

/-- The dart with reversed orientation from a given dart. -/
@[simps]
def Dart.symm (d : G.Dart) : G.Dart :=
  ⟨d.toProd.swap, G.symm d.adj⟩

@[simp]
theorem Dart.symm_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).symm = Dart.mk p.swap h.symm :=
  rfl

@[simp]
theorem Dart.edge_symm (d : G.Dart) : d.symm.edge = d.edge :=
  Sym2.mk_prod_swap_eq

@[simp]
theorem Dart.edge_comp_symm : Dart.edge ∘ Dart.symm = (Dart.edge : G.Dart → Sym2 V) :=
  funext Dart.edge_symm

@[simp]
theorem Dart.symm_symm (d : G.Dart) : d.symm.symm = d :=
  Dart.ext _ _ <| Prod.swap_swap _

@[simp]
theorem Dart.symm_involutive : Function.Involutive (Dart.symm : G.Dart → G.Dart) :=
  Dart.symm_symm

theorem Dart.symm_ne (d : G.Dart) : d.symm ≠ d :=
  ne_of_apply_ne (Prod.snd ∘ Dart.toProd) d.adj.ne

theorem dart_edge_eq_iff : ∀ d₁ d₂ : G.Dart, d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  simp

theorem dart_edge_eq_mk'_iff :
    ∀ {d : G.Dart} {p : V × V}, d.edge = Sym2.mk p ↔ d.toProd = p ∨ d.toProd = p.swap := by
  rintro ⟨p, h⟩
  apply Sym2.mk_eq_mk_iff

theorem dart_edge_eq_mk'_iff' :
    ∀ {d : G.Dart} {u v : V},
      d.edge = s(u, v) ↔ d.fst = u ∧ d.snd = v ∨ d.fst = v ∧ d.snd = u := by
  rintro ⟨⟨a, b⟩, h⟩ u v
  rw [dart_edge_eq_mk'_iff]
  simp

variable (G)

/-- Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex. -/
def DartAdj (d d' : G.Dart) : Prop :=
  d.snd = d'.fst

/-- For a given vertex `v`, this is the bijective map from the neighbor set at `v`
to the darts `d` with `d.fst = v`. -/
@[simps]
def dartOfNeighborSet (v : V) (w : G.neighborSet v) : G.Dart :=
  ⟨(v, w), w.property⟩

theorem dartOfNeighborSet_injective (v : V) : Function.Injective (G.dartOfNeighborSet v) :=
  fun e₁ e₂ h =>
  Subtype.ext <| by
    injection h with h'
    convert congr_arg Prod.snd h'

instance nonempty_dart_top [Nontrivial V] : Nonempty (⊤ : SimpleGraph V).Dart := by
  obtain ⟨v, w, h⟩ := exists_pair_ne V
  exact ⟨⟨(v, w), h⟩⟩

end SimpleGraph
