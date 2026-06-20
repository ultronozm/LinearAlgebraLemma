import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Module.LinearMap.End

/-!
# Small `LinearEquiv` API candidates

Cancellation facts for conjugation by a linear equivalence.
-/

open LinearEquiv in
theorem conj_cancel {R : Type} [CommRing R]
    (U : Type) [AddCommGroup U] [Module R U]
    (V : Type) [AddCommGroup V] [Module R V]
    (f : U ≃ₗ[R] V)
    (x : Module.End R U)
    : conj f.symm (conj f x) = x
    := (eq_symm_apply (conj (LinearEquiv.symm f))).mp rfl

open LinearEquiv in
theorem conj_cancel' {R : Type} [CommRing R]
    (U : Type) [AddCommGroup U] [Module R U]
    (V : Type) [AddCommGroup V] [Module R V]
    (f : V ≃ₗ[R] U)
    (x : Module.End R U)
    : conj f (conj f.symm x) = x
    := (eq_symm_apply (conj f)).mp rfl

