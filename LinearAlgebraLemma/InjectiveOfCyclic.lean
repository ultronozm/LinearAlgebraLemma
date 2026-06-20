import LinearAlgebraLemma.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Cyclic-vector injectivity

The definitions and lemmas in this file are general, but they are part of this
project's cyclic-vector argument rather than polished Mathlib staging.
-/

/- Mathlib no longer registers the commutator-bracket Lie ring structure on
associative rings as a global instance; restore it locally for this file. -/
attribute [local instance 100] LieRing.ofAssociativeRing

open Polynomial in
noncomputable def EvalMap
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

open Polynomial in
theorem subalg_closed_under_poly
    {R : Type} [CommRing R]
    {A : Type} [Ring A] [Algebra R A]
    (s : Subalgebra R A)
    (x : A)
    (hx : x ∈ s)
    (p : R[X])
    : (aeval (R := R) x) p ∈ s := by
  rw [← Polynomial.aeval_subalgebra_coe p s ⟨x, hx⟩]
  exact SetLike.coe_mem _

private theorem mul_eq_lie_add_mul
    {A : Type} [Ring A]
    (a b : A)
    : a * b = ⁅a, b⁆ + b * a := by
  exact eq_add_of_sub_eq rfl

open Polynomial in
theorem comm_poly_of_comm
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    (τ : Module.End R V)
    (x : Module.End R V) (hx : ⁅x, τ⁆ = 0)
    (p : R[X])
    : ⁅x, (aeval (R := R) τ) p⁆ = 0 := by
  let s := Subalgebra.centralizer R {x}
  have hτ : τ ∈ s := by
    rw [Subalgebra.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    rw [mul_eq_lie_add_mul x τ, hx]
    simp only [zero_add]
  have : (aeval (R := R) τ) p ∈ s := subalg_closed_under_poly s τ hτ p
  rw [Subalgebra.mem_centralizer_iff] at this
  simp only [Set.mem_singleton_iff, forall_eq] at this
  rw [mul_eq_lie_add_mul] at this
  simp only [add_eq_right] at this
  exact this

theorem aux_ann
    {A : Type} [Ring A]
    {V : Type} [AddCommGroup V] [Module A V]
    (a b : A)
    (v : V)
    (h₁ : a • v = 0)
    (h₂ : ⁅a, b⁆ = 0)
    : a • (b • v) = 0 := by
  rw [smul_smul a b v, mul_eq_lie_add_mul a b, add_smul, ← smul_smul b a v, h₁, h₂]
  simp only [zero_smul, smul_zero, add_zero]

open Polynomial in
theorem injective_of_cyclic_0
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (τ : Module.End R V)
    (e : V)
    (hcyc : Cyclic R τ e)
    (x : Module.End R V) (hx : ⁅x, τ⁆ = 0)
    (h : x e = 0)
    : x = 0 := by
  ext v
  rcases hcyc v with ⟨p, hp⟩
  simp only [LinearMap.zero_apply]
  rw [← hp]
  have := comm_poly_of_comm τ x hx p
  unfold EvalMap at hp ⊢
  simp only [LinearMap.coe_smulRight, Module.End.smul_def] at hp ⊢
  exact aux_ann x ((aeval (R := R) τ) p) e h this

theorem injective_of_cyclic
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (τ : Module.End R V)
    (e : V)
    (hcyc : Cyclic R τ e)
    (x : Module.End R V) (hx : ⁅x, τ⁆ = 0)
    (y : Module.End R V) (hy : ⁅y, τ⁆ = 0)
    (h : x e = y e)
    : x = y := by
  replace h := sub_eq_zero_of_eq h
  have : x e - y e = (x - y) e := by rfl
  rw [this] at h
  have hxsuby : ⁅x - y, τ⁆ = 0 := by
    rw [sub_lie x y τ]
    rw [hx, hy]
    simp only [sub_self]
  replace h := injective_of_cyclic_0 τ e hcyc (x - y) hxsuby h
  exact sub_eq_zero.mp h

open LinearMap in
theorem aux_lie_zero
    (R : Type) [CommRing R]
    (V : Type) [AddCommGroup V] [Module R V]
    (a b : Module.End R V)
    (h : ⁅a, b⁆ = 0)
    : ⁅a.dualMap, b.dualMap⁆ = 0 := by
  have : ⁅a, b⁆.dualMap = 0 := by
    rw [h]
    unfold dualMap
    exact map_zero Module.Dual.transpose
  rw [lie_dual] at this
  rw [(lie_skew _ _).symm, this]
  simp

open LinearMap in
theorem injective_of_cyclic'
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (τ : Module.End R V)
    (e' : Module.Dual R V)
    (hcyc : Cyclic R τ.dualMap e')
    (x : Module.End R V) (hx : ⁅x, τ⁆ = 0)
    (y : Module.End R V) (hy : ⁅y, τ⁆ = 0)
    (h : e' ∘ₗ x = e' ∘ₗ y)
    : x = y := by
  have hex : e' ∘ₗ x = x.dualMap e' := by rfl
  have hey : e' ∘ₗ y = y.dualMap e' := by rfl
  rw [hex, hey] at h
  replace hx := aux_lie_zero R V x τ hx
  replace hy := aux_lie_zero R V y τ hy
  have := injective_of_cyclic τ.dualMap e' hcyc x.dualMap hx y.dualMap hy h
  unfold dualMap at this
  exact transpose_injective this

