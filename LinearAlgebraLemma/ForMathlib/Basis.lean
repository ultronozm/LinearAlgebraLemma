import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Small basis API candidates

Definitional compatibility lemmas for `Basis.map` and `Basis.reindex`.
-/

open Module

namespace Module.Basis

theorem map_trans
    {R : Type} [CommSemiring R]
    {I : Type}
    {U : Type} [AddCommMonoid U] [Module R U]
    {V : Type} [AddCommMonoid V] [Module R V]
    {W : Type} [AddCommMonoid W] [Module R W]
    (b : Basis I R U)
    (f : U ≃ₗ[R] V)
    (g : V ≃ₗ[R] W)
    : b.map (f ≪≫ₗ g) = (b.map f).map g := rfl

theorem map_symm
    {R : Type} [CommSemiring R]
    {I : Type}
    {U : Type} [AddCommMonoid U] [Module R U]
    {V : Type} [AddCommMonoid V] [Module R V]
    (b : Basis I R U)
    (f : U ≃ₗ[R] V)
    : (b.map f).map (f.symm) = b := by
  simp only [← map_trans, LinearEquiv.self_trans_symm]
  rfl

theorem map_symm_self
    {R : Type} [CommSemiring R]
    {I : Type}
    {U : Type} [AddCommMonoid U] [Module R U]
    {V : Type} [AddCommMonoid V] [Module R V]
    (b : Basis I R U)
    (f : V ≃ₗ[R] U)
    : (b.map f.symm).map f = b := by
  simpa only [LinearEquiv.symm_symm] using map_symm b f.symm

theorem reindex_map
    {R : Type} [CommSemiring R]
    {U : Type} [AddCommMonoid U] [Module R U]
    {V : Type} [AddCommMonoid V] [Module R V]
    {I J : Type}
    (b : Basis I R U)
    (e : I ≃ J)
    (f : U ≃ₗ[R] V)
    : (b.map f).reindex e = (b.reindex e).map f := by rfl

end Module.Basis
