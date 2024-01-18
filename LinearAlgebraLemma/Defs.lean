import Mathlib

/-!

# Main definitions:

* `upperLeftProj`: the upper-left part of an endomorphism of a product.

* `upperLeftIncl`: the endomorphism of a product extending an
  endomorphism of the first factor.

* `EvalMap`: given an endomorphism τ and a vector v, `EvalMap τ v`
  sends a polynomial p to p(τ)v.

* `Cyclic`: we call (τ, v) cyclic if every vector arises as p(τ)v.

-/

def upperLeftProj
    (R : Type) [CommSemiring R]
    (V₁ : Type) [AddCommGroup V₁] [Module R V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module R V₂]
    : Module.End R (V₁ × V₂) →ₗ[R] Module.End R V₁ :=
  (LinearMap.lcomp _ _ $ LinearMap.inl R V₁ V₂)
    ∘ₗ (LinearMap.compRight $ LinearMap.fst R V₁ V₂)

@[simp]
theorem upperLeftProj_apply
    (R : Type) [CommSemiring R]
    (V₁ : Type) [AddCommGroup V₁] [Module R V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module R V₂]
    (x : Module.End R (V₁ × V₂))
    : upperLeftProj R V₁ V₂ x = (LinearMap.fst R V₁ V₂) ∘ₗ x ∘ₗ (LinearMap.inl R V₁ V₂) := rfl

def upperLeftIncl
    (R : Type) [CommSemiring R]
    (V₁ : Type) [AddCommGroup V₁] [Module R V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module R V₂]
    : Module.End R V₁ →ₗ[R] Module.End R (V₁ × V₂) :=
  (LinearMap.lcomp _ _ $ LinearMap.fst R V₁ V₂)
    ∘ₗ (LinearMap.compRight $ LinearMap.inl R V₁ V₂)

@[simp]
theorem upperLeftIncl_apply
    (R : Type) [CommSemiring R]
    (V₁ : Type) [AddCommGroup V₁] [Module R V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module R V₂]
    (x : Module.End R V₁)
    : upperLeftIncl R V₁ V₂ x = (LinearMap.inl R V₁ V₂) ∘ₗ x ∘ₗ (LinearMap.fst R V₁ V₂) := rfl

open Polynomial in
def EvalMap
    {R : Type} [CommSemiring R]
    {V : Type} [AddCommGroup V] [Module R V]
    (τ : Module.End R V) (v : V)
    : R[X] →ₗ[R] V :=
  ((aeval (R := R) τ) : R[X] →ₗ[R] Module.End R V).smulRight v

open Polynomial in
@[simp]
theorem EvalMap_apply
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    {τ : Module.End R V}
    {v : V}
    {p : R[X]}
    : (EvalMap τ v) p = (aeval (R := R) τ p) v := by rfl

def Cyclic
    (R : Type) [CommSemiring R]
    {V : Type} [AddCommGroup V] [Module R V]
    (τ : Module.End R V)
    (v : V) 
    : Prop := Function.Surjective (EvalMap τ v)

