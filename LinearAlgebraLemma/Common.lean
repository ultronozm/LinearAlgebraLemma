import Mathlib

/-!

This file contains the theorem `charpoly_eq_conj_charpoly`, which is
used in two other files.

-/

open LinearMap in
theorem toMatrix_conj
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    {W : Type} [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]
    (τ : Module.End R V)
    (f : V ≃ₗ[R] W)
    {I : Type} [Fintype I] [DecidableEq I]
    (b : Basis I R V)
    : (toMatrix b b) τ = (toMatrix (b.map f) (b.map f)) (f ∘ₗ τ ∘ₗ f.symm)
    := by
  ext i j
  rw [toMatrix_apply, toMatrix_apply]
  simp

open LinearMap LinearEquiv in
theorem charpoly_eq_conj_charpoly
    {R : Type} [CommRing R] [Nontrivial R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    {W : Type} [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]
    (f : V ≃ₗ[R] W)
    (τ : Module.End R V)
    : τ.charpoly = (conj f τ).charpoly
    := by
  let b := Module.Free.chooseBasis R V
  rw [← charpoly_toMatrix τ b]
  let b' := Basis.map b f
  rw [conj_apply f τ]
  rw [← charpoly_toMatrix ((f.toLinearMap ∘ₗ τ) ∘ₗ f.symm.toLinearMap) b']
  apply congrArg Matrix.charpoly
  exact toMatrix_conj τ f b
