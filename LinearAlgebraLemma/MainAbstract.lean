import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import LinearAlgebraLemma.Defs
import LinearAlgebraLemma.InjectiveOfCyclic
import LinearAlgebraLemma.CyclicOfCoprime

/- Mathlib no longer registers the commutator-bracket Lie ring structure on
associative rings as a global instance; restore it locally. -/
attribute [local instance 100] LieRing.ofAssociativeRing

/-!

# Main results:

* `MainAbstract`

-/

/-

This is the matrix identity

  diag(1, ..., 1, 0) = diag(1, ..., 1, 1) - diag(0, ..., 0, 1)

written in the language of endomorphisms, thinking

  diag(0, ..., 0, 1) = (0, ..., 0, 1) ⊗ (0, ..., 0, 1)^t.

In the code that follows, we use the notation

  e     = (0, ..., 0, 1),

  e'    = (0, ..., 0, 1)^t,

  ee'   = diag(0, ..., 0, 1) = e ⊗ e',

  one_H = diag(1, ..., 1, 0) = 1 - e ⊗ e'.

-/
open LinearMap Module in
theorem one_H_eq_one_sub_ee'
    (R : Type) [CommRing R]
    (V : Type) [AddCommGroup V] [Module R V] [Free R V] [Module.Finite R V]
    :
  let e : V × R := (0, 1)
  let e' : Dual R (V × R) := snd R V R
  let ee' : End R (V × R) := (toSpanSingleton R (V × R) e).comp e'
  (upperLeftIncl R V R) 1 = 1 - ee'
    := by
  ext v <;> simp [upperLeftIncl_apply, toSpanSingleton_apply, Module.End.one_apply]

/-

We have

  [x, diag(1, ..., 1, 0)] = e e' x - x e e'.

-/
open LinearMap Module in
theorem comm_one_H
    (R : Type) [CommRing R]
    (V : Type) [AddCommGroup V] [Module R V] [Free R V] [Module.Finite R V]
    (x : End R (V × R))
    :
    let e : V × R := (0, 1)
    let e' : Dual R (V × R) := snd R V R
    let ee' : End R (V × R) := (toSpanSingleton R (V × R) e).comp e'
    ⁅x, (upperLeftIncl R V R) 1⁆ = ee' * x - x * ee' := by
  intro e e' ee'
  rw [one_H_eq_one_sub_ee']
  show ⁅x, 1 - ee'⁆ = ee' * x - x * ee' 
  calc
  _ = ⁅x, 1⁆ - ⁅x, ee'⁆ := lie_sub x 1 ee'
  _ = 0 - ⁅x, ee'⁆ := by
    have : ⁅x, (1 : End R (V × R))⁆ = 0 := by
      exact Commute.lie_eq rfl
    rw [this]
  _ = - ⁅x, ee'⁆ := by simp only [zero_sub, lie_skew]
  _ = - (x * ee' - ee' * x) := by rfl
  _  = ee' * x - x * ee' := neg_sub _ _

/-

We have

  [x, diag(1, ..., 1, 0)] e = - (x - (e' x e)) e.

-/
open LinearMap Module in
theorem aux_commutators
    (R : Type) [CommRing R]
    (V : Type) [AddCommGroup V] [Module R V] [Free R V] [Module.Finite R V]
    (x : End R (V × R))
    :
    let e : V × R := (0, 1)
    let e' : Dual R (V × R) := snd R V R
    ⁅x, (upperLeftIncl R V R) 1⁆ e = - (x - (e' (x e)) • 1) e := by
  rw [comm_one_H]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, coe_comp, Function.comp_apply, snd_apply,
    toSpanSingleton_apply, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, one_smul,
    LinearMap.smul_apply, Module.End.one_apply, neg_sub]

/-

We have

  e' [x, diag(1, ..., 1, 0)] = e' (x - (e' x e)).

-/
open LinearMap Module in
theorem aux_commutators'
    (R : Type) [CommRing R]
    (V : Type) [AddCommGroup V] [Module R V] [Free R V] [Module.Finite R V]
    (x : End R (V × R))
    :
    let e : V × R := (0, 1)
    let e' : Dual R (V × R) := snd R V R
    e' ∘ₗ ⁅x, (upperLeftIncl R V R) 1⁆ = e' ∘ₗ (x - (e' (x e)) • (1 : End R (V × R))) := by
  rw [comm_one_H]
  ext v
  · simp only [coe_comp, coe_inl, Function.comp_apply, LinearMap.sub_apply, Module.End.mul_apply,
    snd_apply, toSpanSingleton_apply, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, map_zero,
    sub_zero, LinearMap.smul_apply, Module.End.one_apply, mul_zero, map_sub]
  · simp only [coe_comp, coe_inr, Function.comp_apply, LinearMap.sub_apply, Module.End.mul_apply,
    snd_apply, toSpanSingleton_apply, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, one_smul,
    map_sub, sub_self, LinearMap.smul_apply, Module.End.one_apply]

/-

If τ and its upper left block have coprime characteristic polynomials,
then the map

  (centralizer of tau) ∋ x ↦ x (0, ..., 0, 1)    

is injective.

-/
open Module in
theorem injective_e_of_coprime_charpoly
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Free R V] [Module.Finite R V]
    (τ : End R (V × R)) (hτ : IsCoprime τ.charpoly (upperLeftProj R V R τ).charpoly)
    (x : End R (V × R)) (hx : ⁅x, τ⁆ = 0)
    (y : End R (V × R)) (hy : ⁅y, τ⁆ = 0)
    :
    let e : V × R := (0, 1)
    (x e = y e) → x = y := by
  intro e hxy
  have h := cyclic_e_of_coprime_charpoly R V τ hτ
  exact injective_of_cyclic τ e h x hx y hy hxy

/-

If τ and its upper left block have coprime characteristic polynomials,
then the map

  (centralizer of tau) ∋ x ↦ (0, ..., 0, 1)^t x

is injective.

-/
open LinearMap Module in
theorem injective_e'_of_coprime_charpoly
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Free R V] [Module.Finite R V]
    (τ : End R (V × R)) (hτ : IsCoprime τ.charpoly (upperLeftProj R V R τ).charpoly)
    (x : End R (V × R)) (hx : ⁅x, τ⁆ = 0)
    (y : End R (V × R)) (hy : ⁅y, τ⁆ = 0)
    :
    let e' : Dual R (V × R) := snd R V R
    e' ∘ₗ x = e' ∘ₗ y → x = y := by
  intro e' hxy
  have h := cyclic_e'_of_coprime_charpoly R V τ hτ
  exact injective_of_cyclic' τ e' h x hx y hy hxy

/-

If x commutes with τ, then so does -(x-c) for any scalar c.

-/
open Module in
theorem aux_ez_comm_zero
    (R : Type) [CommRing R]
    (V : Type) [AddCommGroup V] [Module R V]
    (τ : End R V)
    (x : End R V) (hx : ⁅x, τ⁆ = 0)
    (c : R)
    : ⁅(- (x - c • 1)), τ⁆ = 0
    := by
  simp only [neg_sub, sub_lie, smul_lie]
  have : ⁅(1 : End R V), τ⁆ = 0 := by
    exact Commute.lie_eq rfl
  rw [this]
  rw [hx]
  simp only [smul_zero, sub_self]

/-

If x commutes with τ, then so does (x-c) for any scalar c.

-/
open Module in
theorem aux_ez_comm_zero'
    (R : Type) [CommRing R]
    (V : Type) [AddCommGroup V] [Module R V]
    (τ : End R V)
    (x : End R V) (hx : ⁅x, τ⁆ = 0)
    (c : R)
    : ⁅(x - c • (1 : End R V)), τ⁆ = 0
    := by
  rw [sub_lie, hx]
  simp only [smul_lie, zero_sub, neg_eq_zero]
  have : ⁅(1 : End R V), τ⁆ = 0 := by
    exact Commute.lie_eq rfl
  rw [this]
  simp only [smul_zero]
  
/-

If -(x-y) = (x-y) and 2 is a unit, then x = y.

-/
open Module nonZeroDivisors in
theorem aux_cancel_two
    (R : Type) [CommRing R]
    (hR : (2 : R) ∈ R⁰)
    (V : Type) [AddCommGroup V] [Module R V] [IsTorsionFree R V]
    (x y : Module.End R V) 
    (h : (-(x - y) = (x - y)))
    : x = y
    := by
  simp only [neg_sub] at h 
  have := sub_eq_sub_iff_add_eq_add.mp (id h.symm)
  rw [(two_smul R x).symm, (two_smul R y).symm] at this
  rw [mem_nonZeroDivisors_iff] at hR
  apply eq_of_sub_eq_zero
  replace this := sub_eq_zero_of_eq this
  rw [← smul_sub 2 x y] at this
  have hreg : IsRegular (2 : R) := (isRegular_iff_mem_nonZeroDivisors).2 hR
  exact (hreg.smul_eq_zero_iff_right (m := (x-y))).1 this

/-

Let x, t, τ be (n+1)×(n+1).  Let y be n×n, extended by zero to
(n+1)×(n+1).  Let z = diag(1,...,1,0).  If τ and its upper left block
have coprime characteristic polynomials, and

  [x, τ] = [t, τ] = 0 and [x, z] = y + t,

then x is a scalar.  Stated in the language of endomorphisms.

-/
open LinearMap Module nonZeroDivisors in
theorem aux_main
    (R : Type) [CommRing R] [Nontrivial R]
    (hR : (2 : R) ∈ R⁰)
    (V : Type) [AddCommGroup V] [Module R V] [Free R V] [Module.Finite R V]
    (τ : End R (V × R)) (hτ : IsCoprime τ.charpoly (upperLeftProj R V R τ).charpoly)
    (x : End R (V × R)) (hx : ⁅x, τ⁆ = 0)
    (y : End R V)
    (t : End R (V × R))
    (hxyt : ⁅x, upperLeftIncl R V R 1⁆ = (upperLeftIncl R V R y) + t)
    (ht : ⁅t, τ⁆ = 0)
    : ∃ (r : R), x = r • (1 : End R (V × R)) := by
  let e : V × R := (0, 1)
  let e' : Dual R (V × R) := snd R V R
  have he : t e = ⁅x, (upperLeftIncl R V R) 1⁆ e := by
    have hxyt' := congrArg (fun f => f e) hxyt
    have hye : (upperLeftIncl R V R y) e = 0 := by
      simp [upperLeftIncl_apply, e]
    -- hxyt' : ⁅x, upperLeftIncl 1⁆ e = (upperLeftIncl y) e + t e
    -- so t e = ⁅x, upperLeftIncl 1⁆ e
    calc
      t e = (upperLeftIncl R V R y) e + t e := by
        have h : (upperLeftIncl R V R y) e + t e = 0 + t e := by
          rw [hye]
        simpa using h.symm
      _ = ⁅x, (upperLeftIncl R V R) 1⁆ e := by simpa using hxyt'.symm
  have he2 : ⁅x, (upperLeftIncl R V R) 1⁆ e = - (x - (e' (x e)) • 1) e := aux_commutators R V x
  have he3 : t = -(x - (e' (x e)) • 1) := by
    have recap : t e = - (x - (e' (x e)) • 1) e := by
      rw [he, he2]
    have ez : ⁅(- (x - (e' (x e)) • 1)), τ⁆ = 0 := aux_ez_comm_zero R (V × R) τ x hx (e' (x e))
    apply injective_e_of_coprime_charpoly R V τ hτ t ht (- (x - (e' (x e)) • 1)) ez recap
  have he' : e' ∘ₗ t = e' ∘ₗ ⁅x, (upperLeftIncl R V R) 1⁆ := by
    rw [hxyt]
    have : e' ∘ₗ ((upperLeftIncl R V R) y) = 0 := by
      ext v <;> simp [upperLeftIncl_apply, e']
    rw [comp_add]
    rw [this]
    simp only [zero_add]
  have he'2 : e' ∘ₗ ⁅x, (upperLeftIncl R V R) 1⁆ = e' ∘ₗ (x - (e' (x e)) • (1 : End R (V × R))) := aux_commutators' R V x
  have he'3 : t = (x - (e' (x e)) • 1) := by
    have recap : e' ∘ₗ t = e' ∘ₗ (x - (e' (x e)) • (1 : End R (V × R))) := by
      rw [he', he'2]
    have ez : ⁅(x - (e' (x e)) • (1 : End R (V × R))), τ⁆ = 0 := aux_ez_comm_zero' R (V × R) τ x hx (e' (x e))
    apply injective_e'_of_coprime_charpoly R V τ hτ t ht (x - (e' (x e)) • (1 : End R (V × R))) ez recap
  have h :  x = e' (x e) • 1 := by
    rw [he3] at he'3
    exact aux_cancel_two R hR (V × R) x (e' (x e) • 1) he'3
  use (e' (x e))

/-

If [x,τ] = 0 and [x, [z, τ]] = [y, τ], then [[x, z], τ] - [y, τ] = 0.

-/
open Module in
theorem aux_jacobi_appl
    {R : Type} [CommRing R] [Nontrivial R]
    {V : Type} [AddCommGroup V] [Module R V] [Free R V] [Module.Finite R V]
    (τ : End R V)
    (x : End R V) (hx : ⁅x, τ⁆ = 0)
    (y : End R V)
    (z : End R V)
    (heq : ⁅x, ⁅z, τ⁆⁆ = ⁅y, τ⁆)
    : ⁅⁅x, z⁆, τ⁆ - ⁅y, τ⁆ = 0 := by
  rw [lie_lie (L := End R V) (M := End R V) x z τ]
  rw [heq]
  rw [hx]
  simp only [lie_zero, sub_zero, sub_self]

/-

Let x, τ be (n+1)×(n+1).  Let y be n×n, extended by zero to
(n+1)×(n+1).  Let z = diag(1,...,1,0).  If τ and its upper left block
have coprime characteristic polynomials, and

  [x, τ] = 0 and [x, [z, τ]] = [y, τ],

then x is a scalar.  Stated in the language of endomorphisms.

-/
open Module nonZeroDivisors in
theorem MainAbstract
    (R : Type) [CommRing R] [Nontrivial R]
    (hR : (2 : R) ∈ R⁰)
    (V : Type) [AddCommGroup V] [Module R V] [Free R V] [Module.Finite R V]
    (τ : End R (V × R)) (hτ : IsCoprime τ.charpoly (upperLeftProj R V R τ).charpoly)
    (x : End R (V × R)) (hx : ⁅x, τ⁆ = 0)
    (y : End R V)
    (heq : ⁅x, ⁅upperLeftIncl R V R 1, τ⁆⁆ = ⁅upperLeftIncl R V R y, τ⁆)
    : ∃ (r : R), x = r • (1 : End R (V × R))
    := by
  let t : End R (V × R) := ⁅x, upperLeftIncl R V R 1⁆ - (upperLeftIncl R V R y)
  have hxyt : ⁅x, upperLeftIncl R V R 1⁆ = (upperLeftIncl R V R y) + t := by
    simp only [upperLeftIncl_apply]
    exact eq_add_of_sub_eq' (G := End R (V × R)) rfl
  have ht : ⁅t, τ⁆ = 0 := by
    dsimp [t]
    rw [sub_lie]
    exact aux_jacobi_appl τ x hx _ _ heq
  exact aux_main R hR V τ hτ x hx y t hxyt ht
