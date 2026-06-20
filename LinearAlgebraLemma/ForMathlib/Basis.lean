import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Small basis API candidates

Definitional compatibility lemmas for `Basis.map` and `Basis.reindex`.
-/

open Module

open Basis in
theorem basis_map_comp
    (R : Type) [CommRing R]
    (I : Type) [Fintype I] [DecidableEq I]
    (U : Type) [AddCommGroup U] [Module R U]
    (V : Type) [AddCommGroup V] [Module R V]
    (W : Type) [AddCommGroup W] [Module R W]
    (b : Basis I R U)
    (f : U ≃ₗ[R] V)
    (g : V ≃ₗ[R] W)
    : b.map (f ≪≫ₗ g) = (b.map f).map g := rfl

open Basis in
theorem basis_map_cancel
    (R : Type) [CommRing R]
    {I : Type} [Fintype I] [DecidableEq I]
    {U : Type} [AddCommGroup U] [Module R U]
    {V : Type} [AddCommGroup V] [Module R V]
    (b : Basis I R U)
    (f : U ≃ₗ[R] V)
    : (b.map f).map (f.symm) = b := by
  simp only [← basis_map_comp, LinearEquiv.self_trans_symm]
  rfl

open Basis in
theorem basis_map_cancel'
    (R : Type) [CommRing R]
    {I : Type} [Fintype I] [DecidableEq I]
    {U : Type} [AddCommGroup U] [Module R U]
    {V : Type} [AddCommGroup V] [Module R V]
    (b : Basis I R U)
    (f : V ≃ₗ[R] U)
    : (b.map f.symm).map f = b := by
  simp only [← basis_map_comp, LinearEquiv.symm_trans_self]
  rfl

open Basis in
theorem basis_map_commutes_reindex
    (R : Type) [CommRing R]
    (U : Type) [AddCommGroup U] [Module R U]
    (V : Type) [AddCommGroup V] [Module R V]
    (I : Type) [Fintype I] [DecidableEq I]
    (J : Type) [Fintype J] [DecidableEq J]
    (b : Basis I R U)
    (e : I ≃ J)
    (f : U ≃ₗ[R] V)
    : (b.map f).reindex e = (b.reindex e).map f := by rfl
