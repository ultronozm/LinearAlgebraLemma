import Mathlib
import LinearAlgebraLemma.Defs

/-!

# Main results:

* `injective_of_cyclic`

* `injective_of_cyclic'`

-/

/-

If x lies in a subalgebra, then so does p(x) for every polynomial p.

-/
open Polynomial in
theorem subalg_closed_under_poly
    {R : Type} [CommRing R]
    {A : Type} [Ring A] [Algebra R A]
    (s : Subalgebra R A)
    (x : A)
    (hx : x ∈ s)
    (p : R[X])
    : (aeval (R := R) x) p ∈ s
    := by
  rw [← Polynomial.aeval_subalgebra_coe p s ⟨x, hx⟩]
  exact SetLike.coe_mem _

theorem aux_comm
    {A : Type} [Ring A]
    (a b : A)
    : a * b = ⁅a, b⁆ + b * a
    := by
  exact eq_add_of_sub_eq rfl

/-

If x commutes with τ, then so does p(x) for every polynomial p.

-/
open Polynomial in
theorem comm_poly_of_comm
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    (τ : Module.End R V)
    (x : Module.End R V) (hx : ⁅x, τ⁆ = 0)
    (p : R[X])
    : ⁅x, (aeval (R := R) τ) p⁆ = 0
    := by
  let s := Subalgebra.centralizer R {x}
  have hτ : τ ∈ s := by
    rw [Subalgebra.mem_centralizer_iff]
    simp
    rw [aux_comm x τ, hx]
    simp
  have : (aeval (R := R) τ) p ∈ s := subalg_closed_under_poly s τ hτ p
  rw [Subalgebra.mem_centralizer_iff] at this
  simp at this
  rw [aux_comm] at this
  simp at this
  exact this

/-

If [a,b]=0 and av=0, then abv=0.

-/
theorem aux_ann
    {A : Type} [Ring A]
    {V : Type} [AddCommGroup V] [Module A V]
    (a b : A)
    (v : V)
    (h₁ : a • v = 0)
    (h₂ : ⁅a, b⁆ = 0)
    : a • (b • v) = 0 := by
  rw [smul_smul a b v, aux_comm a b, add_smul, ← smul_smul b a v, h₁, h₂]
  simp

/-

If e is a cyclic vector for τ, then

  (centralizer of τ) ∋ x ↦ x e

has trivial kernel.

-/
open Polynomial in
theorem injective_of_cyclic_0
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (τ : Module.End R V)
    (e : V)
    (hcyc : Cyclic R τ e)
    (x : Module.End R V) (hx : ⁅x, τ⁆ = 0)
    (h : x e = 0)
    : x = 0
    := by
  ext v
  rcases hcyc v with ⟨p, hp⟩
  simp
  rw [← hp]
  have := comm_poly_of_comm τ x hx p
  unfold EvalMap at hp ⊢ 
  simp at hp ⊢
  exact aux_ann x ((aeval (R := R) τ) p) e h this

/-

If e is a cyclic vector for τ, then

  (centralizer of τ) ∋ x ↦ x e

is injective.

-/
theorem injective_of_cyclic
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (τ : Module.End R V)
    (e : V)
    (hcyc : Cyclic R τ e)
    (x : Module.End R V) (hx : ⁅x, τ⁆ = 0)
    (y : Module.End R V) (hy : ⁅y, τ⁆ = 0)
    (h : x e = y e)
    : x = y
    := by
  replace h := sub_eq_zero_of_eq h
  have : x e - y e = (x - y) e := by rfl
  rw [this] at h
  have hxsuby: ⁅x-y, τ⁆ = 0 := by
    rw [sub_lie x y τ]
    rw [hx, hy]
    simp
  replace h := injective_of_cyclic_0 τ e hcyc (x - y) hxsuby h
  exact sub_eq_zero.mp h

/-

Duality anti-commutes with Lie brackets.

-/
open LinearMap in
theorem lie_dual
    (R : Type) [CommRing R]
    (V : Type) [AddCommGroup V] [Module R V]
    (a b : Module.End R V)
    : ⁅a, b⁆.dualMap = ⁅b.dualMap, a.dualMap⁆ := by
  show (a * b - b * a).dualMap = b.dualMap * a.dualMap - a.dualMap * b.dualMap
  calc 
  (a * b - b * a).dualMap = (a * b).dualMap - (b * a).dualMap := by
    unfold dualMap
    rw [LinearMap.map_sub]              
  _ = (b.dualMap * a.dualMap) - (a.dualMap * b.dualMap) := by rfl

/-

Duality preserves vanishing of the Lie bracket.

-/
open LinearMap in
theorem aux_lie_zero
    (R : Type) [CommRing R]
    (V : Type) [AddCommGroup V] [Module R V]
    (a b : Module.End R V)
    (h : ⁅a, b⁆ = 0)
    : ⁅a.dualMap, b.dualMap⁆ = 0
    := by
  have : ⁅a, b⁆.dualMap = 0 := by
    rw [h]
    unfold dualMap
    exact map_zero Module.Dual.transpose
  rw [lie_dual] at this
  rw [(lie_skew _ _).symm, this]
  simp

section transpose

open Matrix

variable {K V₁ V₂ ι₁ ι₂ : Type*} [CommRing K] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
  [Module K V₂] [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] {B₁ : Basis ι₁ K V₁}
  {B₂ : Basis ι₂ K V₂}

/-

Generalized from mathlib's `LinearMap.toMatrix_transpose' by replacing
"Field" with "CommSemiring".

-/
@[simp]
theorem LinearMap.toMatrix_transpose' (u : V₁ →ₗ[K] V₂) :
    LinearMap.toMatrix B₂.dualBasis B₁.dualBasis (Module.Dual.transpose (R := K) u) =
    (LinearMap.toMatrix B₁ B₂ u)ᵀ := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Dual.transpose_apply, B₁.dualBasis_repr,
    B₂.dualBasis_apply, Matrix.transpose_apply, LinearMap.comp_apply]

end transpose

/-

Duality on finite free modules over a ring is injective.

-/
open LinearMap Module in
theorem transpose_injective
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V] [Free R V] [Finite R V]
    {a b : End R V}
    (h : a.dualMap = b.dualMap)
    : a = b := by
  let ι : Type := Module.Free.ChooseBasisIndex R V
  haveI : DecidableEq ι := inferInstance
  let B : Basis ι R V := Module.Free.chooseBasis R V
  let B' : Basis ι R (Dual R V) := Basis.dualBasis B
  have ha : (toMatrix B' B' (Dual.transpose a)) = (toMatrix B B a).transpose := toMatrix_transpose' (K := R) (B₁ := B) (B₂ := B) a
  have hb : (toMatrix B' B' (Dual.transpose b)) = (toMatrix B B b).transpose := toMatrix_transpose' (K := R) (B₁ := B) (B₂ := B) b
  unfold dualMap at h
  rw [h] at ha
  rw [ha] at hb
  exact (toMatrix B B).injective (Matrix.transpose_injective hb)
  
/-

If e is a cyclic covector for τ, then

  (centralizer of τ) ∋ x ↦ x e

is injective.

-/
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
    : x = y
    := by
  have hex : e' ∘ₗ x = x.dualMap e' := by rfl
  have hey : e' ∘ₗ y = y.dualMap e' := by rfl
  rw [hex, hey] at h
  replace hx := aux_lie_zero R V x τ hx
  replace hy := aux_lie_zero R V y τ hy
  have := injective_of_cyclic τ.dualMap e' hcyc x.dualMap hx y.dualMap hy h
  unfold dualMap at this
  exact transpose_injective this
