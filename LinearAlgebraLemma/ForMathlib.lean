import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.Tactic

/-!
# General-purpose declarations staged for mathlib

This file collects declarations from the project that are not specific to the
main theorem.  Names and placement are intentionally still provisional; the goal
is to make the project's genuinely local code easier to distinguish from
candidate mathlib API.
-/

/- Mathlib no longer registers the commutator-bracket Lie ring structure on
associative rings as a global instance; restore it locally. -/
attribute [local instance 100] LieRing.ofAssociativeRing

open Module

open LinearMap Sum LinearEquiv in
theorem toMatrix_basis_map
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    {W : Type} [AddCommGroup W] [Module R W]
    {V' : Type} [AddCommGroup V'] [Module R V']
    {W' : Type} [AddCommGroup W'] [Module R W']
    (fV : V ≃ₗ[R] V')
    (fW : W ≃ₗ[R] W')
    {I : Type} [Fintype I] [DecidableEq I]
    {J : Type} [Fintype J] [DecidableEq J]
    (bV : Basis J R V)
    (bW : Basis I R W)
    (x : V →ₗ[R] W)
  :
    (toMatrix (bV.map fV) (bW.map fW) (fW ∘ₗ x ∘ₗ fV.symm)) = (toMatrix bV bW x) := by
  ext i j
  simp [toMatrix, Basis.map_equivFun, LinearEquiv.trans_apply, toMatrix'_apply,
    LinearEquiv.arrowCongr_apply, LinearEquiv.trans_symm, symm_symm, Basis.equivFun_symm_apply,
    one_smul, coe_comp,
    Function.comp_apply, LinearEquiv.symm_apply_apply,
    Basis.equivFun_apply]

open LinearMap Sum LinearEquiv in
theorem matrix_conj
    (R : Type) [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    {W : Type} [AddCommGroup W] [Module R W]
    (I : Type) [Fintype I] [DecidableEq I]
    (f : V ≃ₗ[R] W)
    (b : Basis I R V)
    (x : Module.End R V)
    :
    (toMatrix (b.map f) (b.map f) (conj f x)) = (toMatrix b b x) := by
  have : conj f x = f ∘ₗ x ∘ₗ f.symm := rfl
  rw [this]
  simp only [toMatrix_basis_map]

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

open LinearMap Sum LinearEquiv in
theorem matrix_conj'
    (R : Type) [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    {W : Type} [AddCommGroup W] [Module R W]
    (I : Type) [Fintype I] [DecidableEq I]
    (f : V ≃ₗ[R] W)
    (b : Basis I R W)
    (x : Module.End R V)
    :
    (toMatrix b b (conj f x)) = (toMatrix (b.map f.symm) (b.map f.symm) x) := by
  convert matrix_conj R I f (b.map f.symm) x
  nth_rw 1 [← basis_map_cancel' R b f]
  nth_rw 1 [← basis_map_cancel' R b f]

open LinearMap in
theorem matrix_basis_reindex
    (R : Type) [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    {I : Type} [Fintype I] [DecidableEq I]
    {J : Type} [Fintype J] [DecidableEq J]
    (b : Basis J R V)
    (e : J ≃ I)
    (x : Module.End R V)
    (i j : I)
    :
    (toMatrix (b.reindex e) (b.reindex e) x) i j
    = (toMatrix b b x) (e.symm i) (e.symm j) := by
  simp [toMatrix, LinearEquiv.trans_apply, toMatrix'_apply, LinearEquiv.arrowCongr_apply,
    Basis.equivFun_symm_apply, Basis.coe_reindex, Function.comp_apply, Basis.equivFun_apply,
    Basis.repr_reindex, Finsupp.mapDomain_equiv_apply]

open Module Matrix LinearEquiv LinearMap in
theorem matrix_conj''
    (R : Type) [CommRing R]
    (U : Type) [AddCommGroup U] [Module R U]
    (V : Type) [AddCommGroup V] [Module R V]
    {I : Type} [Fintype I] [DecidableEq I]
    {J : Type} [Fintype J] [DecidableEq J]
    (bU : Basis I R U)
    (bV : Basis J R V)
    (e : I ≃ J)
    (f : U ≃ₗ[R] V)
    (hbef : bU.map f = bV.reindex e.symm)
    (x : Matrix J J R)
    (i j : I)
    :
    (toMatrix bU bU (conj f.symm (toLin bV bV x))) i j
    = x (e i) (e j) := by
  rw [matrix_conj']
  simp only [symm_symm]
  rw [hbef]
  rw [matrix_basis_reindex R bV e.symm (toLin bV bV x) i j]
  simp only [Equiv.symm_symm, toMatrix_toLin]

/-

Extend an endomorphism of V₁ by zero to an endomorphism of V₁ × V₂ has the
expected effect on matrices.

-/
open LinearMap Sum Basis in
theorem matrix_incl_entries
    (R : Type) [CommRing R]
    (V₁ : Type) [AddCommGroup V₁] [Module R V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module R V₂]
    {I₁ I₂ : Type} [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
    (b₁ : Basis I₁ R V₁)
    (b₂ : Basis I₂ R V₂)
    (x : Module.End R V₁)
    (i j : I₁ ⊕ I₂)
    :
    (toMatrix (b₁.prod b₂) (b₁.prod b₂) ((inl R V₁ V₂) ∘ₗ x ∘ₗ (fst R V₁ V₂))) i j
    = match i, j with
    | Sum.inl i, Sum.inl j => (toMatrix b₁ b₁ x) i j
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr _, Sum.inl _ => 0
    | Sum.inr _, Sum.inr _ => 0 := by
  cases i <;> cases j <;>
    simp [LinearMap.toMatrix, LinearEquiv.trans_apply, toMatrix'_apply,
      LinearEquiv.arrowCongr_apply, Basis.prod_apply, coe_inl, coe_inr,
      Function.comp_apply, coe_comp, equivFun_apply, prod_repr_inl, prod_repr_inr]

/-

A variant of `matrix_incl_entries` where we start with a matrix and
allow reindexing of the product basis.

-/
open Module Matrix LinearEquiv LinearMap in
theorem matrix_incl_entries'
    (R : Type) [CommRing R]
    (V₁ V₂ : Type) [AddCommGroup V₁] [Module R V₁] [AddCommGroup V₂] [Module R V₂]
    {I₁ : Type} [Fintype I₁] [DecidableEq I₁]
    {I₂ : Type} [Fintype I₂] [DecidableEq I₂]
    (b₁ : Basis I₁ R V₁) (b₂ : Basis I₂ R V₂)
    {I : Type} [Fintype I] [DecidableEq I]
    (e : I ≃ I₁ ⊕ I₂)
    (f : (I → R) ≃ₗ[R] (V₁ × V₂))
    (hbef : (Pi.basisFun R I).map f = (b₁.prod b₂).reindex e.symm)
    (x : Matrix I₁ I₁ R)
    :
    toMatrix' (conj f.symm ((inl R V₁ V₂) ∘ₗ (toLin b₁ b₁ x) ∘ₗ (fst R V₁ V₂)))
    = (fun i j ↦ match e i, e j with
    | Sum.inl i, Sum.inl j => x i j
    | _, _ => 0) := by
  set b := b₁.prod b₂
  set y := (toMatrix b b ((inl R V₁ V₂) ∘ₗ (toLin b₁ b₁ x) ∘ₗ (fst R V₁ V₂)))
  have : (inl R V₁ V₂) ∘ₗ (toLin b₁ b₁ x) ∘ₗ (fst R V₁ V₂) = toLin b b y := by
    simp [y, toLin_toMatrix]
  rw [this]
  ext i j
  rw [← toMatrix_eq_toMatrix']
  rw [matrix_conj'' R (I → R) (V₁ × V₂) (Pi.basisFun R I) b e f hbef y i j]
  simp [y]
  rw [matrix_incl_entries R V₁ V₂ b₁ b₂ ((toLin b₁ b₁) x) (e i) (e j)]
  simp only [toMatrix_toLin]
  cases hi : e i <;> cases hj : e j <;> simp only

/-

Projecting an endomorphism of V₁ × V₂ to one of V₁ has the expected
effect on matrices.

-/
open LinearMap Sum in
theorem matrix_proj_entries
    (R : Type) [CommRing R]
    (V₁ : Type) [AddCommGroup V₁] [Module R V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module R V₂]
    {I₁ I₂ : Type} [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
    (b₁ : Basis I₁ R V₁)
    (b₂ : Basis I₂ R V₂)
    (x : Module.End R (V₁ × V₂))
    (i j : I₁)
    :
    (toMatrix b₁ b₁ ((fst R V₁ V₂) ∘ₗ x ∘ₗ (inl R V₁ V₂))) i j
    = (toMatrix (Basis.prod b₁ b₂) (Basis.prod b₁ b₂) x) (inl i) (inl j) := by
  simp [toMatrix, LinearEquiv.trans_apply, toMatrix'_apply, LinearEquiv.arrowCongr_apply,
    Basis.equivFun_symm_apply, one_smul,
    coe_comp, coe_inl, Function.comp_apply, Basis.equivFun_apply,
    Basis.prod_apply, coe_inr, elim_inl, Basis.prod_repr_inl]

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

/-

A variant of `matrix_proj_entries` where we start with a matrix and
allow reindexing of the product basis.

-/
open Module Matrix LinearEquiv LinearMap in
theorem matrix_proj_entries'
    (R : Type) [CommRing R]
    (V₁ V₂ : Type) [AddCommGroup V₁] [Module R V₁] [AddCommGroup V₂] [Module R V₂]
    {I₁ : Type} [Fintype I₁] [DecidableEq I₁]
    {I₂ : Type} [Fintype I₂] [DecidableEq I₂]
    (b₁ : Basis I₁ R V₁) (b₂ : Basis I₂ R V₂)
    {I : Type} [Fintype I] [DecidableEq I]
    (e : I ≃ I₁ ⊕ I₂)
    (f : (I → R) ≃ₗ[R] (V₁ × V₂))
    (hbef : (Pi.basisFun R I).map f = (b₁.prod b₂).reindex e.symm)
    (x : Matrix I I R)
    :
    toMatrix b₁ b₁ ((fst R V₁ V₂) ∘ₗ (conj f (toLin' x)) ∘ₗ (inl R V₁ V₂))
    = x.submatrix (e.symm ∘ Sum.inl) (e.symm ∘ Sum.inl) := by
  ext i j
  rw [matrix_proj_entries R V₁ V₂ b₁ b₂ ((conj f (toLin' x))) i j]
  set b := b₁.prod b₂
  rw [← Matrix.toLin_eq_toLin']
  have : f = f.symm.symm := rfl
  rw [this]
  have hbef' : b.map f.symm = (Pi.basisFun R I).reindex e.symm.symm := by
    simp only [Equiv.symm_symm]
    have : (Pi.basisFun R I) = (b.reindex e.symm).map f.symm := by
      calc
      _ = ((Pi.basisFun R I).map f).map f.symm := by
        ext i
        simp only [Pi.basisFun_apply, Pi.basisFun_apply, Basis.map_apply, symm_apply_apply]
      _ = (b.reindex e.symm).map f.symm := by
        rw [hbef]
    rw [this]
    have : b.map f.symm = ((b.map f.symm).reindex e.symm).reindex e := by
      ext i
      simp only [Basis.map_apply, Basis.coe_reindex,
        Equiv.symm_symm, Function.comp_apply, Equiv.apply_symm_apply]
    rw [this]
    rw [basis_map_commutes_reindex]
  rw [matrix_conj'' R (V₁ × V₂) (I → R) b (Pi.basisFun R I) e.symm f.symm hbef' _ _ _]
  simp only [submatrix_apply, Function.comp_apply]

abbrev Mat (R : Type) [Ring R] (n : ℕ) := Matrix (Fin n) (Fin n) R

open LinearMap in
theorem toMatrix_charpoly_eq_charpoly {R : Type} [CommRing R] [Nontrivial R] {n : ℕ}
    (y : Module.End R (Fin n → R)) : (toMatrix' y).charpoly = y.charpoly := by
  calc
  _ = Matrix.charpoly ((toMatrix (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin n))) y) := by rfl
  _ = y.charpoly := (y.charpoly_toMatrix (Pi.basisFun R (Fin n)))

open LinearMap Matrix in
theorem charpoly_eq_toLin_charpoly {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (x : Mat R n)
    : x.charpoly = (toLin' x).charpoly := by
  let y := toLin' x
  calc
  _ = Matrix.charpoly x := by rfl
  _ = Matrix.charpoly (toMatrix' y) := by simp [y, toMatrix'_toLin']
  _ = y.charpoly := toMatrix_charpoly_eq_charpoly y

/-

The isomorphism R^{n+1} ≅ R^n × R.

-/
def decomp {R : Type} [CommRing R] {n : ℕ}
    : (Fin (n + 1) → R) ≃ₗ[R] (Fin n → R) × R
    := ((LinearEquiv.piCongrLeft' R (fun _ => R) finSumFinEquiv).symm)
    ≪≫ₗ (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin 1) R R)
    ≪≫ₗ (LinearEquiv.prodCongr (LinearEquiv.refl R (Fin n → R))
          (LinearEquiv.funUnique (Fin 1) R R))

open LinearMap LinearEquiv in
theorem charpoly_eq_conj_decomp_symm_charpoly {R : Type} [CommRing R] [Nontrivial R] {n : ℕ}
    (y : Module.End R ((Fin n → R) × R))
    : y.charpoly = (conj decomp.symm y).charpoly := by
  rw [LinearEquiv.charpoly_conj]

open LinearMap LinearEquiv in
theorem charpoly_eq_toMatrix_conj_decomp_symm_charpoly
    {R : Type} [CommRing R] [Nontrivial R] {n : ℕ}
    (y : Module.End R ((Fin n → R) × R))
    : y.charpoly = (toMatrix' $ conj decomp.symm y).charpoly := by
  rw [charpoly_eq_conj_decomp_symm_charpoly y]
  let u := conj decomp.symm y
  have : conj decomp.symm y = u := by rfl
  rw [this]
  have : (toMatrix' $ conj decomp.symm y) = toMatrix' u := by rfl
  rw [this]
  exact (toMatrix_charpoly_eq_charpoly u).symm

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

open LinearEquiv LinearMap Matrix in
theorem charpoly_eq_conj_decomp_toLin_charpoly {R : Type} [CommRing R] [Nontrivial R] {n : ℕ}
    (x : Mat R (n+1))
    : x.charpoly = (conj decomp $ toLin' x).charpoly := by
  let y := (conj decomp $ toLin' x)
  have hy : x = (toMatrix' $ conj decomp.symm y) := by
    simp [y, toMatrix'_toLin']
  show Matrix.charpoly x = LinearMap.charpoly (conj decomp $ toLin' x)
  rw [charpoly_eq_toMatrix_conj_decomp_symm_charpoly y, hy]

theorem lie_map_of_ring_hom
    (R : Type) [CommRing R]
    {A : Type} [Ring A] [Algebra R A]
    {B : Type} [Ring B] [Algebra R B]
    (f : A →+* B)
    (x y : A)
    (h : ⁅x, y⁆ = 0)
    : ⁅f x, f y⁆ = 0 := by
  rw [Ring.lie_def] at *
  rw [←f.map_mul, ←f.map_mul, ←f.map_sub]
  rw [h]
  simp only [map_zero]

theorem lie_map_of_ring_hom'
    (R : Type) [CommRing R]
    {A : Type} [Ring A] [Algebra R A]
    {B : Type} [Ring B] [Algebra R B]
    (f : A →+* B)
    (x y : A)
    : ⁅f x, f y⁆ = f ⁅x, y⁆ := by
  rw [Ring.lie_def, Ring.lie_def] at *
  rw [←f.map_mul, ←f.map_mul, ←f.map_sub]

theorem castAdd_one_ne_last (n : ℕ) (i : Fin n) : ¬Fin.castAdd 1 i = Fin.last n := by
  have : Fin.castAdd 1 i = Fin.castSucc i := rfl
  rw [this]
  intro h
  apply Fin.exists_castSucc_eq.mp ⟨i, h⟩
  rfl

theorem natAdd_fin_one_eq_last (n : ℕ) (i : Fin 1) : Fin.natAdd n i = Fin.last n := by
  rw [Fin.eq_zero i]
  rfl

theorem finSumFinEquiv_one_eq_last_iff (n : ℕ)
    (i : Fin n ⊕ Fin 1)
    : (finSumFinEquiv i = Fin.last n)
    = match i with
    | Sum.inl _ => False
    | Sum.inr _ => True
    := by
  unfold finSumFinEquiv
  simp only [Equiv.coe_fn_mk, eq_iff_iff]
  induction' i with i i
  · simp only [Sum.elim_inl, iff_false]
    exact castAdd_one_ne_last n i
  simp only [Sum.elim_inr, iff_true]
  exact natAdd_fin_one_eq_last n i

/-

Extending an n×n matrix to an (n+1)×(n+1) matrix.

Here we do it directly, by checking whether the indices i : Fin n are
equal to Fin.last n or not.

-/
def matrixIncl {R : Type} [Ring R] {n : ℕ}
    (x : Mat R n) : Mat R (n+1) :=
  fun i j ↦ if h : i  ≠ Fin.last n ∧ j ≠ Fin.last n
    then x ⟨i, Fin.val_lt_last h.1⟩ ⟨j, Fin.val_lt_last h.2 ⟩
    else 0

/-

Extend an n×n matrix to an (n+1)×(n+1) matrix, part two.

Here we do it using finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n+1).  This
is sometimes more convenient than the direct approach.

-/
def matrixIncl' {R : Type} [Ring R] {n : ℕ}
    (x : Mat R n) : Mat R (n+1) :=
  fun i j => match finSumFinEquiv.symm i, finSumFinEquiv.symm j with
    | Sum.inl i, Sum.inl j => x i j
    | _, _ => 0

@[simp]
theorem matrixIncl'_apply {R : Type} [Ring R] {n : ℕ}
    (x : Mat R n)
    (i j : Fin (n+1))
    : matrixIncl' x i j = match finSumFinEquiv.symm i, finSumFinEquiv.symm j with
    | Sum.inl i, Sum.inl j => x i j
    | _, _ => 0 := rfl

theorem matrixIncl_eq_matrixIncl' {R : Type} [Ring R]
    (x : Mat R n)
    : matrixIncl x = matrixIncl' x := by
  ext i j
  unfold matrixIncl
  unfold matrixIncl'
  by_cases h : i ≠ Fin.last n ∧ j ≠ Fin.last n
  simp only [ne_eq, h, not_false_eq_true, and_self, dite_true]
  induction' hi : finSumFinEquiv.symm i with i' i'
  induction' hj : finSumFinEquiv.symm j with j' j'
  · simp only
    have : i = finSumFinEquiv (Sum.inl i') := by
     rw [← hi]
     simp only [Equiv.apply_symm_apply]
    simp only [this, finSumFinEquiv_apply_left, Fin.val_castAdd, Fin.eta]
    have : j = finSumFinEquiv (Sum.inl j') := by
      rw [← hj]
      simp only [Equiv.apply_symm_apply]
    simp only [this, finSumFinEquiv_apply_left, Fin.val_castAdd, Fin.eta]
  · simp only
    have : j = finSumFinEquiv (Sum.inr j') := by
      rw [← hj]
      simp only [Equiv.apply_symm_apply]
    replace h := h.2
    rw [this] at h
    have := finSumFinEquiv_one_eq_last_iff n (Sum.inr j')
    absurd h
    rw [this]
    simp only
  induction' hj : finSumFinEquiv.symm j with j' j'
  · simp only
    have : i = finSumFinEquiv (Sum.inr i') := by
     rw [← hi]
     simp only [Equiv.apply_symm_apply]
    replace h := h.1
    rw [this] at h
    have := finSumFinEquiv_one_eq_last_iff n (Sum.inr i')
    absurd h
    rw [this]
    simp only
  · simp only
    have : i = finSumFinEquiv (Sum.inr i') := by
     rw [← hi]
     simp only [Equiv.apply_symm_apply]
    replace h := h.1
    rw [this] at h
    have := finSumFinEquiv_one_eq_last_iff n (Sum.inr i')
    absurd h
    rw [this]
    simp only
  push Not at h
  simp only [ne_eq]
  by_cases h' : i = Fin.last n
  · simp only [h', not_true_eq_false, false_and, Fin.val_last, dite_false,
    finSumFinEquiv_symm_last]
  simp only [h', not_false_eq_true, true_and, dite_not]
  replace h := h h'
  rw [h]
  simp [finSumFinEquiv_symm_last]

def upperLeftProj
    (R : Type) [CommSemiring R]
    (V₁ : Type) [AddCommGroup V₁] [Module R V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module R V₂]
    : Module.End R (V₁ × V₂) →ₗ[R] Module.End R V₁ where
  toFun x := (LinearMap.fst R V₁ V₂) ∘ₗ x ∘ₗ (LinearMap.inl R V₁ V₂)
  map_add' x y := by simp only [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' r x := by simp only [LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]

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
    : Module.End R V₁ →ₗ[R] Module.End R (V₁ × V₂) where
  toFun x := (LinearMap.inl R V₁ V₂) ∘ₗ x ∘ₗ (LinearMap.fst R V₁ V₂)
  map_add' x y := by simp only [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' r x := by simp only [LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]

@[simp]
theorem upperLeftIncl_apply
    (R : Type) [CommSemiring R]
    (V₁ : Type) [AddCommGroup V₁] [Module R V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module R V₂]
    (x : Module.End R V₁)
    : upperLeftIncl R V₁ V₂ x = (LinearMap.inl R V₁ V₂) ∘ₗ x ∘ₗ (LinearMap.fst R V₁ V₂) := rfl

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

theorem aux_comm
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
    rw [aux_comm x τ, hx]
    simp only [zero_add]
  have : (aeval (R := R) τ) p ∈ s := subalg_closed_under_poly s τ hτ p
  rw [Subalgebra.mem_centralizer_iff] at this
  simp only [Set.mem_singleton_iff, forall_eq] at this
  rw [aux_comm] at this
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
  rw [smul_smul a b v, aux_comm a b, add_smul, ← smul_smul b a v, h₁, h₂]
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
theorem lie_dual
    (R : Type) [CommRing R]
    (V : Type) [AddCommGroup V] [Module R V]
    (a b : Module.End R V)
    : ⁅a, b⁆.dualMap = ⁅b.dualMap, a.dualMap⁆ := by
  show (a * b - b * a).dualMap = b.dualMap * a.dualMap - a.dualMap * b.dualMap
  calc
  (a * b - b * a).dualMap = (a * b).dualMap - (b * a).dualMap := by
    unfold dualMap
    simp only [map_sub]
  _ = (b.dualMap * a.dualMap) - (a.dualMap * b.dualMap) := by rfl

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

open LinearMap Module in
theorem transpose_injective
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    {a b : End R V}
    (h : a.dualMap = b.dualMap)
    : a = b := by
  have h' : a.dualMap.dualMap = b.dualMap.dualMap := by
    rw [h]
  exact (Module.dualMap_dualMap_eq_iff (R := R) (M := V)).mp h'

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

theorem upper_left_action
    (R : Type) [CommRing R]
    (V₁ : Type) [AddCommGroup V₁] [Module R V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module R V₂]
    (x : Module.End R (V₁ × V₂))
    (v₁ : V₁)
    : (x (v₁, 0)).1 = (upperLeftProj R V₁ V₂ x) v₁ := rfl

open scoped TensorProduct

theorem eV_smul_baseChange
  (R : Type) [CommRing R]
  (V : Type) [AddCommGroup V] [Module R V]
  (P : Ideal R)
  (a : R ⧸ P) (x : (R ⧸ P) ⊗[R] V) :
    (TensorProduct.quotTensorEquivQuotSMul V P) (a • x) =
      a • (TensorProduct.quotTensorEquivQuotSMul V P) x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp only [smul_zero, map_zero]
  · intro r v
    refine Quot.induction_on r ?_
    intro r
    refine Quot.induction_on a ?_
    intro a
    have hmul : (Ideal.Quotient.mk P a) * (Ideal.Quotient.mk P r) =
        Ideal.Quotient.mk P (a * r) := by
      simp only [map_mul]
    calc
      (TensorProduct.quotTensorEquivQuotSMul V P)
          ((Ideal.Quotient.mk P a * Ideal.Quotient.mk P r) ⊗ₜ[R] v)
          =
          (TensorProduct.quotTensorEquivQuotSMul V P)
            (Ideal.Quotient.mk P (a * r) ⊗ₜ[R] v) := by
              rw [hmul]
      _ = Submodule.Quotient.mk ((a * r) • v) := by
            simpa using
              (TensorProduct.quotTensorEquivQuotSMul_mk_tmul (M := V) (I := P) (r := a * r)
                (x := v))
      _ = Ideal.Quotient.mk P a • Submodule.Quotient.mk (r • v) := by
            calc
              Submodule.Quotient.mk ((a * r) • v)
                  = Submodule.Quotient.mk (a • (r • v)) := by
                      simp only [mul_smul, Submodule.Quotient.mk_smul]
              _ = Ideal.Quotient.mk P a • Submodule.Quotient.mk (r • v) := by
                      simp only [Submodule.Quotient.mk_smul, Module.IsTorsionBySet.mk_smul]
  · intro x y hx hy
    simp [hx, hy, map_add, smul_add]

theorem eR_smul_baseChange
  (R : Type) [CommRing R]
  (P : Ideal R)
  (a : R ⧸ P) (x : (R ⧸ P) ⊗[R] R) :
    (TensorProduct.rid R (R ⧸ P)) (a • x) =
      a • (TensorProduct.rid R (R ⧸ P)) x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro r s
    refine Quot.induction_on r ?_
    intro r
    refine Quot.induction_on a ?_
    intro a
    have hmul : (Ideal.Quotient.mk P a) * (Ideal.Quotient.mk P r) =
        Ideal.Quotient.mk P (a * r) := by
      simp only [map_mul]
    calc
      (TensorProduct.rid R (R ⧸ P))
          ((Ideal.Quotient.mk P a * Ideal.Quotient.mk P r) ⊗ₜ[R] s)
          =
          (TensorProduct.rid R (R ⧸ P))
            (Ideal.Quotient.mk P (a * r) ⊗ₜ[R] s) := by
              rw [hmul]
      _ = s • Ideal.Quotient.mk P (a * r) := by
            simp [TensorProduct.rid_tmul]
      _ = Ideal.Quotient.mk P a • (s • Ideal.Quotient.mk P r) := by
            simp [smul_eq_mul, mul_comm]
      _ = Ideal.Quotient.mk P a •
            (TensorProduct.rid R (R ⧸ P) (Ideal.Quotient.mk P r ⊗ₜ[R] s)) := by
            simp [TensorProduct.rid_tmul]
  · intro x y hx hy
    simp [hx, hy, map_add, smul_add, mul_add]

lemma upperLeftProj_conj_prodCongr
    {R : Type} [CommRing R]
    {V₁ V₂ V₁' V₂' : Type}
    [AddCommGroup V₁] [Module R V₁]
    [AddCommGroup V₂] [Module R V₂]
    [AddCommGroup V₁'] [Module R V₁']
    [AddCommGroup V₂'] [Module R V₂']
    (eV : V₁ ≃ₗ[R] V₁') (eW : V₂ ≃ₗ[R] V₂')
    (τ : Module.End R (V₁ × V₂)) :
    upperLeftProj R V₁' V₂' ((LinearEquiv.prodCongr eV eW).conj τ) =
      eV.conj (upperLeftProj R V₁ V₂ τ) := by
  ext v
  simp [upperLeftProj_apply, LinearEquiv.conj_apply, LinearEquiv.prodCongr_symm]

lemma upperLeftProj_baseChange_tmul
    (R : Type) [CommRing R]
    (V : Type) [AddCommGroup V] [Module R V]
    (P : Ideal R)
    (τ : Module.End R (V × R))
    (a : R ⧸ P) (v : V) :
    let R_mod_P := R ⧸ P
    let e1 := TensorProduct.prodRight R R_mod_P R_mod_P V R
    let τ1 : Module.End R_mod_P (R_mod_P ⊗[R] V × R_mod_P ⊗[R] R) :=
      e1.conj (τ.baseChange R_mod_P)
    (upperLeftProj R_mod_P (R_mod_P ⊗[R] V) (R_mod_P ⊗[R] R) τ1) (a ⊗ₜ[R] v) =
      (LinearMap.baseChange R_mod_P (upperLeftProj R V R τ)) (a ⊗ₜ[R] v) := by
  classical
  have hsymm :
      (TensorProduct.prodRight R (R ⧸ P) (R ⧸ P) V R).symm (a ⊗ₜ[R] v, 0) =
        a ⊗ₜ[R] (v, 0) := by
    simpa using
      (TensorProduct.prodRight_symm_tmul (R := R) (S := R ⧸ P) (M₁ := R ⧸ P)
        (M₂ := V) (M₃ := R) a v (0 : R))
  calc
    ((TensorProduct.prodRight R (R ⧸ P) (R ⧸ P) V R)
        ((LinearMap.baseChange (R ⧸ P) τ)
          ((TensorProduct.prodRight R (R ⧸ P) (R ⧸ P) V R).symm (a ⊗ₜ[R] v, 0)))).1
        =
      ((TensorProduct.prodRight R (R ⧸ P) (R ⧸ P) V R)
        ((LinearMap.baseChange (R ⧸ P) τ) (a ⊗ₜ[R] (v, 0)))).1 := by
          simp [hsymm]
    _ =
      ((TensorProduct.prodRight R (R ⧸ P) (R ⧸ P) V R)
        (a ⊗ₜ[R] (τ (v, 0)))).1 := by
          simp [LinearMap.baseChange_tmul]
    _ = a ⊗ₜ[R] (τ (v, 0)).1 := by
          simp [TensorProduct.prodRight_tmul]
    _ = a ⊗ₜ[R] ((upperLeftProj R V R τ) v) := by
          rw [upper_left_action R V R τ v]

lemma upperLeftProj_baseChange_add
    (R : Type) [CommRing R]
    (V : Type) [AddCommGroup V] [Module R V]
    (P : Ideal R)
    (τ : Module.End R (V × R))
    (x y : (R ⧸ P) ⊗[R] V)
    (hx :
      let R_mod_P := R ⧸ P
      let e1 := TensorProduct.prodRight R R_mod_P R_mod_P V R
      let τ1 : Module.End R_mod_P (R_mod_P ⊗[R] V × R_mod_P ⊗[R] R) :=
        e1.conj (τ.baseChange R_mod_P)
      (upperLeftProj R_mod_P (R_mod_P ⊗[R] V) (R_mod_P ⊗[R] R) τ1) x =
        (LinearMap.baseChange R_mod_P (upperLeftProj R V R τ)) x)
    (hy :
      let R_mod_P := R ⧸ P
      let e1 := TensorProduct.prodRight R R_mod_P R_mod_P V R
      let τ1 : Module.End R_mod_P (R_mod_P ⊗[R] V × R_mod_P ⊗[R] R) :=
        e1.conj (τ.baseChange R_mod_P)
      (upperLeftProj R_mod_P (R_mod_P ⊗[R] V) (R_mod_P ⊗[R] R) τ1) y =
        (LinearMap.baseChange R_mod_P (upperLeftProj R V R τ)) y) :
    let R_mod_P := R ⧸ P
    let e1 := TensorProduct.prodRight R R_mod_P R_mod_P V R
    let τ1 : Module.End R_mod_P (R_mod_P ⊗[R] V × R_mod_P ⊗[R] R) :=
      e1.conj (τ.baseChange R_mod_P)
    (upperLeftProj R_mod_P (R_mod_P ⊗[R] V) (R_mod_P ⊗[R] R) τ1) (x + y) =
    (LinearMap.baseChange R_mod_P (upperLeftProj R V R τ)) (x + y) := by
  dsimp at hx hy
  dsimp
  let R_mod_P := R ⧸ P
  let e1 := TensorProduct.prodRight R R_mod_P R_mod_P V R
  let τ1 : Module.End R_mod_P (R_mod_P ⊗[R] V × R_mod_P ⊗[R] R) :=
    e1.conj (τ.baseChange R_mod_P)
  let f : Module.End R_mod_P (R_mod_P ⊗[R] V) :=
    upperLeftProj R_mod_P (R_mod_P ⊗[R] V) (R_mod_P ⊗[R] R) τ1
  let g : Module.End R_mod_P (R_mod_P ⊗[R] V) :=
    LinearMap.baseChange R_mod_P (upperLeftProj R V R τ)
  have hleft (z : R_mod_P ⊗[R] V) : f z = (τ1 (z, 0)).1 := by
    simp only [upperLeftProj_apply, LinearMap.coe_comp, LinearMap.coe_fst, LinearMap.coe_inl,
      Function.comp_apply, f]
  have hx' : f x = g x := by
    simpa [f, g, hleft, τ1, e1] using hx
  have hy' : f y = g y := by
    simpa [f, g, hleft, τ1, e1] using hy
  calc
    f (x + y) = f x + f y := by simp only [map_add]
    _ = g x + g y := by simp only [hx', hy']
    _ = g (x + y) := by simp only [map_add]

lemma upperLeftProj_baseChange_prodRight
    (R : Type) [CommRing R]
    (V : Type) [AddCommGroup V] [Module R V]
    (P : Ideal R)
    (τ : Module.End R (V × R)) :
    let R_mod_P := R ⧸ P
    let e1 := TensorProduct.prodRight R R_mod_P R_mod_P V R
    let τ1 : Module.End R_mod_P (R_mod_P ⊗[R] V × R_mod_P ⊗[R] R) :=
      e1.conj (τ.baseChange R_mod_P)
    upperLeftProj R_mod_P (R_mod_P ⊗[R] V) (R_mod_P ⊗[R] R) τ1 =
      (upperLeftProj R V R τ).baseChange R_mod_P := by
  classical
  apply LinearMap.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  ·
    have hsymm :
        (TensorProduct.prodRight R (R ⧸ P) (R ⧸ P) V R).symm (0, 0) =
          (0 : (R ⧸ P) ⊗[R] (V × R)) := by
      simp
    calc
      ((TensorProduct.prodRight R (R ⧸ P) (R ⧸ P) V R)
          ((LinearMap.baseChange (R ⧸ P) τ)
            ((TensorProduct.prodRight R (R ⧸ P) (R ⧸ P) V R).symm (0, 0)))).1
          =
        ((TensorProduct.prodRight R (R ⧸ P) (R ⧸ P) V R)
          ((LinearMap.baseChange (R ⧸ P) τ) (0 : (R ⧸ P) ⊗[R] (V × R)))).1 := by
            simp [hsymm]
      _ = 0 := by simp
  · intro a v
    simpa using
      (upperLeftProj_baseChange_tmul (R := R) (V := V) (P := P) (τ := τ) a v)
  · intro x y hx hy
    simpa using
      (upperLeftProj_baseChange_add (R := R) (V := V) (P := P) (τ := τ) x y hx hy)

theorem upper_left_action_on_invariant_subspace
    {R : Type} [CommRing R]
    {V₁ : Type} [AddCommGroup V₁] [Module R V₁]
    {V₂ : Type} [AddCommGroup V₂] [Module R V₂]
    {U : Submodule R (V₁ × V₂)}
    (hU : U ≤ Submodule.fst R V₁ V₂)
    {x : Module.End R (V₁ × V₂)}
    (hx : ∀ u ∈ U, x u ∈ U)
    {v₁ : V₁}
    (hv₁ : (v₁, 0) ∈ U)
    : x (v₁, 0) = ((upperLeftProj R V₁ V₂ x) v₁, 0) := by
  have h : x (v₁, 0) ∈ U := hx (v₁, 0) hv₁
  replace h := hU h
  have h₂ : (x (v₁, 0)).2 = 0 := by exact h
  have h₃ : (x (v₁, 0)) = ((x (v₁, 0)).1, (x (v₁, 0)).2) := by simp only [Prod.mk.eta]
  rw [h₃, h₂, upper_left_action R V₁ V₂ x v₁]

open Polynomial in
theorem monomial_induction_helper
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    (c : R)
    (n : ℕ)
    (τ : Module.End R V)
    (v : V)
    : ((aeval (R := R) τ) ((monomial (Nat.succ n)) c)) v =
      τ (((aeval (R := R) τ) ((monomial n) c)) v) := by
  rw [(X_mul_monomial n c).symm, aeval_mul τ, aeval_X τ]
  rfl

open Polynomial in
theorem polynomial_of_stabilizing_element_stabilizes
    (R : Type) [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    {U : Submodule R V}
    (τ : Module.End R V)
    (h : ∀ v ∈ U, τ v ∈ U)
    (p : R[X])
    : ∀ v ∈ U, ((aeval (R := R) τ) p) v ∈ U := by
  induction' p using Polynomial.induction_on' with p q hp hq n a
  · intro v hv
    simp only [map_add, LinearMap.add_apply]
    exact Submodule.add_mem U (hp v hv) (hq v hv)
  induction' n with n hn
  · simp only [monomial_zero_left, aeval_C, Module.algebraMap_end_apply]
    exact fun v a_1 => Submodule.smul_mem U a a_1
  intro v hv
  rw [monomial_induction_helper a n τ v]
  apply h
  exact hn v hv

/-

Suppose that (v, 0) lies in a τ-stable subspace of the first summand of
V₁ × V₂.  Then for any polynomial p, we have

  p(τ) (v, 0) = p(τ₀) (v, 0),

where 0 means "upper-left block".

-/
open Polynomial in
theorem apply_polynomials_upper_left
    (R : Type) [CommRing R]
    (V₁ : Type) [AddCommGroup V₁] [Module R V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module R V₂]
    (U : Submodule R (V₁ × V₂))
    (hU : U ≤ (Submodule.fst R V₁ V₂))
    (τ : Module.End R (V₁ × V₂))
    (hτ : ∀ v ∈ U, τ v ∈ U)
    (f : R[X])
    (v : V₁)
    (hv : (v, 0) ∈ U)
    : (aeval (R := R) τ f) (v, 0) = ((aeval (R := R) (upperLeftProj R V₁ V₂ τ) f) v, 0)
    := by
  let τ₀ : Module.End R V₁ := (upperLeftProj R V₁ V₂ τ)
  induction' f using Polynomial.induction_on' with p q hp hq f_n f_a
  · simp only [map_add, LinearMap.add_apply, hp, upperLeftProj_apply, hq, Prod.mk_add_mk, add_zero]
  · induction' f_n with f_n hf_n
    · simp only [monomial_zero_left, aeval_C, Module.algebraMap_end_apply,
      Prod.smul_mk, smul_zero, upperLeftProj_apply]
    calc
    _ = τ (((aeval (R := R) τ) ((monomial f_n) f_a)) (v, 0))
      := monomial_induction_helper f_a f_n τ (v, 0)
    _ = τ (((aeval (R := R) τ₀) ((monomial f_n) f_a)) v, 0) := by rw [hf_n]
    _ = (τ₀ (((aeval (R := R) τ₀) ((monomial f_n) f_a)) v), 0) := by
      have h' : (((aeval (R := R) τ₀) ((monomial f_n) f_a)) v, 0) ∈ U := by
        rw [← hf_n]
        apply polynomial_of_stabilizing_element_stabilizes R τ hτ _
        exact hv
      exact upper_left_action_on_invariant_subspace hU hτ h'
    _ = (((aeval (R := R) τ₀) ((monomial (Nat.succ f_n)) f_a)) v, 0) := by
      rw [← monomial_induction_helper f_a f_n τ₀ v]

/-

An endomorphism of R^{n+1} ≃ R^n × R whose characteristic polynomial
is coprime to that of its upper-left n×n block admits no nontrivial
invariant subspace contained in the first summand R^n.

-/
open Polynomial in
theorem no_invariant_subspaces_of_coprime_charpoly
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (τ : Module.End R (V × R))
    (hτ : IsCoprime τ.charpoly (upperLeftProj R V R τ).charpoly)
    (U : Submodule R (V × R))
    (hU : U ≤ (Submodule.fst R V R))
    (hτU : ∀ v ∈ U, τ v ∈ U)
    : U = ⊥
    := by
  rcases hτ with ⟨ x, y, hxy ⟩
  have CH : (aeval (R := R) τ) τ.charpoly = 0 := LinearMap.aeval_self_charpoly τ
  rw [Submodule.eq_bot_iff]
  intro u hu
  have h : u = ((aeval (R := R) τ) (1 : R[X])) u := by simp only [map_one, Module.End.one_apply]
  rw [← hxy] at h
  rw [map_add, map_mul, CH] at h
  simp only [mul_zero, upperLeftProj_apply, map_mul, zero_add, Module.End.mul_apply] at h
  have ez1 : u ∈ Submodule.fst R V R := hU hu
  have ez2 : u = (u.1, u.2) := by simp only [Prod.mk.eta]
  have ez3 : u = (u.1, 0) := by
    unfold Submodule.fst at ez1
    simp only [Submodule.comap_bot, LinearMap.mem_ker, LinearMap.snd_apply] at ez1
    rw [ez1] at ez2
    exact ez2
  let pH : R[X] := (LinearMap.charpoly ((upperLeftProj R V R) τ))
  let τH : Module.End R V := ((upperLeftProj R V R) τ)
  have key1 : ((aeval (R := R) τ) pH) u = (((aeval (R := R) τH) pH) u.1, 0) := by
    nth_rw 1 [ez3]
    have ez4 : (u.1, 0) ∈ U := by
      rw [ez3] at hu
      exact hu
    exact apply_polynomials_upper_left R V R U hU τ hτU pH u.1 ez4
  have CH2 : ((aeval (R := R) τH) pH) = 0 := LinearMap.aeval_self_charpoly τH
  rw [CH2] at key1
  simp only [LinearMap.zero_apply] at key1
  have h' : u = ((aeval (R := R) τ) y) (((aeval (R := R) τ) pH) u) := by
    simpa [pH, upperLeftProj_apply] using h
  rw [key1] at h'
  have h'' : u = ((aeval (R := R) τ) y) (0 : V × R) := by
    simpa [Prod.zero_eq_mk] using h'
  rw [map_zero] at h''
  exact h''

open Polynomial in
theorem dual_evalmap_stable_range
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    (τ : Module.End R V)
    (e' : Module.Dual R V)
    :
    let W : Submodule R (Module.Dual R V) := LinearMap.range (EvalMap τ.dualMap e')
    ∀ w ∈ W, τ.dualMap w ∈ W := by
  intro W w hw
  rcases hw with ⟨ p, hp ⟩
  rw [LinearMap.mem_range]
  use (X * p : R[X])
  rw [EvalMap_apply, ← hp]
  simp only [map_mul, aeval_X, Module.End.mul_apply, EvalMap_apply]

theorem stable_coannihilator_of_stable_module
    (R : Type) [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    (τ : Module.End R V)
    {W : Submodule R (Module.Dual R V)}
    (hW : ∀ w ∈ W, τ.dualMap w ∈ W)
    : ∀ v ∈ Submodule.dualCoannihilator W, τ v ∈ Submodule.dualCoannihilator W := by
  intro v hv
  simp only [Submodule.dualCoannihilator, Submodule.mem_comap, Submodule.mem_dualAnnihilator,
    Module.Dual.eval_apply] at hv ⊢
  intro w hw
  have h : τ.dualMap w ∈ W := hW w hw
  exact hv (τ.dualMap w) h

theorem exists_maximal_smul_le_of_ne_bot_of_fg {R : Type} [CommRing R]
    {M : Type} [AddCommGroup M] [Module R M]
    (N : Submodule R M)
    (hN : Submodule.FG N)
    (hN' : N ≠ ⊥)
    : ∃ P : Ideal R, P.IsMaximal ∧ P • N < N := by
  set A := Submodule.annihilator N
  have hA : A ≠ ⊤ := fun h => hN' (Submodule.annihilator_eq_top_iff.mp h)
  have : ∃ P : Ideal R, P.IsMaximal ∧ A ≤ P := Ideal.exists_le_maximal A hA
  rcases this with ⟨P, hP, hP'⟩
  use P
  use hP
  show P • N < N
  by_contra hPN
  have : P • N ≤ N := Submodule.smul_le_right
  have : P • N = N ∨ P • N < N := LE.le.eq_or_lt this
  have : P • N = N := by
    cases this
    · assumption
    contradiction
  have hPN' : N ≤ P • N := Eq.le (id this.symm)
  have := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul P N hN hPN'
  rcases this with ⟨r, hr, hr'⟩
  have : r ∈ A := by
    rw [Submodule.mem_annihilator]
    exact hr'
  have : r ∈ P := hP' this
  have := (Submodule.sub_mem_iff_right P this).mp hr
  have : P = ⊤ := (Ideal.eq_top_iff_one P).mpr this
  exact Ideal.IsPrime.ne_top' this

instance
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Finite R V]
    (I : Ideal R)
    : Module.Finite (R ⧸ I) (V ⧸ (I • (⊤ : Submodule R V) : Submodule R V)) := by
  haveI : Module.Finite R (V ⧸ (I • (⊤ : Submodule R V) : Submodule R V)) := by
    infer_instance
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I)
    (V ⧸ (I • (⊤ : Submodule R V) : Submodule R V))

theorem aux_isom_thms
    (R : Type) [CommRing R]
    (V : Type) [AddCommGroup V] [Module R V]
    (W : Submodule R V)
    (P : Ideal R)
    :
    (⊤ : Submodule R V) ≤ W ⊔ (P • (⊤ : Submodule R V)) →
      (⊤ : Submodule R (V ⧸ W)) ≤ (P • (⊤ : Submodule R (V ⧸ W))) := by
  intro h x hx
  have hsup : W ⊔ (P • (⊤ : Submodule R V)) = ⊤ := (top_le_iff.mp h)
  have hmap :
      Submodule.map (Submodule.mkQ W) (P • (⊤ : Submodule R V)) = ⊤ := by
    exact (Submodule.map_mkQ_eq_top (p := W) (p' := P • (⊤ : Submodule R V))).2 hsup
  have hx' : x ∈ Submodule.map (Submodule.mkQ W) (P • (⊤ : Submodule R V)) := by
    simp only [hmap, Submodule.mem_top]
  have hmap_le : Submodule.map (Submodule.mkQ W) (P • (⊤ : Submodule R V)) ≤
      (P • (⊤ : Submodule R (V ⧸ W))) := by
    refine (Submodule.map_le_iff_le_comap).2 ?_
    refine (Submodule.smul_le).2 ?_
    intro r hr v hv
    have hv' : (Submodule.mkQ W) v ∈ (⊤ : Submodule R (V ⧸ W)) := by
      exact Submodule.mem_top
    have hmem : r • (Submodule.mkQ W v) ∈ P • (⊤ : Submodule R (V ⧸ W)) :=
      Submodule.smul_mem_smul hr hv'
    simpa [map_smul] using hmem
  exact hmap_le hx'

open Polynomial in
lemma dualMap_pow_apply
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    (τ : Module.End R V) :
    ∀ n (y : Module.Dual R V) (v : V), ((τ.dualMap) ^ n) y v = y ((τ ^ n) v) := by
  intro n
  induction n with
  | zero =>
      intro y v
      simp
  | succ n hn =>
      intro y v
      have h := hn (τ.dualMap y) v
      have h' : (τ.dualMap y) ((τ ^ n) v) = y ((τ ^ n) (τ v)) := by
        calc
          (τ.dualMap y) ((τ ^ n) v) = y (τ ((τ ^ n) v)) := by
            simp [LinearMap.dualMap_apply]
          _ = y ((τ ^ (n + 1)) v) := by
            simp [pow_succ', Module.End.mul_apply]
          _ = y ((τ ^ n) (τ v)) := by
            simp [pow_succ, Module.End.mul_apply]
      simpa [pow_succ, Module.End.mul_apply, h'] using h

open Polynomial in
lemma eval_dual_apply
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    (τ : Module.End R V) (y : Module.Dual R V) (p : R[X]) (v : V) :
    (EvalMap τ.dualMap y p) v = y ((aeval (R := R) τ p) v) := by
  classical
  induction' p using Polynomial.induction_on' with p q hp hq n c
  ·
    have hp' : ((aeval τ.dualMap p) y) v = y ((aeval (R := R) τ p) v) := by
      simpa [EvalMap_apply] using hp
    have hq' : ((aeval τ.dualMap q) y) v = y ((aeval (R := R) τ q) v) := by
      simpa [EvalMap_apply] using hq
    calc
      (EvalMap τ.dualMap y (p + q)) v
          = (((aeval τ.dualMap p) y) v + ((aeval τ.dualMap q) y) v) := by
              simp [EvalMap_apply, aeval_add, LinearMap.add_apply]
      _ = y ((aeval (R := R) τ p) v) + y ((aeval (R := R) τ q) v) := by
              simp only [hp', hq']
      _ = y ((aeval (R := R) τ (p + q)) v) := by
          simp [aeval_add, LinearMap.add_apply]
  induction' n with n hn
  · simp [EvalMap_apply, monomial_zero_left, aeval_C, Module.algebraMap_end_apply]
  calc
    (EvalMap τ.dualMap y (monomial (Nat.succ n) c)) v
        = (c • (((τ.dualMap) ^ (n + 1)) y)) v := by
            simp [EvalMap_apply, aeval_monomial, LinearMap.smul_apply]
    _ = c • y ((τ ^ (n + 1)) v) := by
            simp [dualMap_pow_apply]
    _ = y ((aeval (R := R) τ (monomial (Nat.succ n) c)) v) := by
            simp [aeval_monomial]

open Polynomial in
lemma endHom_pow_apply
    {R : Type} [CommRing R]
    {S : Type} [CommRing S] [Algebra R S]
    {M : Type} [AddCommGroup M] [Module R M]
    {P : Type} [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
    {j : M →ₗ[R] P} (ibc : IsBaseChange S j)
    [Module.Free R M] [Module.Finite R M]
    (τ : Module.End R M) :
    ∀ n (m : M), ((ibc.endHom τ) ^ n) (j m) = j ((τ ^ n) m) := by
  intro n
  induction n with
  | zero =>
      intro m
      simp
  | succ n hn =>
      intro m
      have h1 : (ibc.endHom τ) (j m) = j (τ m) := by
        simpa using (IsBaseChange.endHom_comp_apply (j := ibc) (f := τ) (m := m))
      simp [pow_succ, Module.End.mul_apply, hn, h1]

open Polynomial in
lemma aeval_endHom_comp_apply
    {R : Type} [CommRing R]
    {S : Type} [CommRing S] [Algebra R S]
    {M : Type} [AddCommGroup M] [Module R M]
    {P : Type} [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
    {j : M →ₗ[R] P} (ibc : IsBaseChange S j)
    [Module.Free R M] [Module.Finite R M]
    (τ : Module.End R M) (p : R[X]) (m : M) :
    (aeval (R := S) (ibc.endHom τ) (p.map (algebraMap R S))) (j m)
      = j ((aeval (R := R) τ p) m) := by
  classical
  induction' p using Polynomial.induction_on' with p q hp hq n c
  ·
    calc
      (aeval (R := S) (ibc.endHom τ) ((p + q).map (algebraMap R S))) (j m)
          = (aeval (R := S) (ibc.endHom τ)
              ((p.map (algebraMap R S)) + (q.map (algebraMap R S)))) (j m) := by
              simp [Polynomial.map_add]
      _ = (aeval (R := S) (ibc.endHom τ) (p.map (algebraMap R S))) (j m)
            + (aeval (R := S) (ibc.endHom τ) (q.map (algebraMap R S))) (j m) := by
              simp [aeval_add, LinearMap.add_apply]
      _ = j ((aeval (R := R) τ p) m) + j ((aeval (R := R) τ q) m) := by
              rw [hp, hq]
      _ = j ((aeval (R := R) τ (p + q)) m) := by
              simp [aeval_add, LinearMap.add_apply]
  induction' n with n hn
  · simp [monomial_zero_left, aeval_C, Module.algebraMap_end_apply]
  calc
    (aeval (R := S) (ibc.endHom τ) ((monomial (Nat.succ n) c).map (algebraMap R S))) (j m)
        = (algebraMap R S c) • (((ibc.endHom τ) ^ (n + 1)) (j m)) := by
            simp [aeval_monomial]
    _ = (algebraMap R S c) • j ((τ ^ (n + 1)) m) := by
            simp [endHom_pow_apply (ibc := ibc)]
    _ = j ((aeval (R := R) τ (monomial (Nat.succ n) c)) m) := by
            simp [aeval_monomial]

open LinearMap Module in
theorem charpoly_dualmap_eq_charpoly
    {R : Type} [CommRing R] [Nontrivial R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (τ : End R V)
    : τ.dualMap.charpoly = τ.charpoly := by
  let b := Module.Free.chooseBasis R V
  rw [← charpoly_toMatrix τ b]
  let b' := b.dualBasis
  rw [← charpoly_toMatrix τ.dualMap b']
  have hmat :
      LinearMap.toMatrix b' b' τ.dualMap = Matrix.transpose (LinearMap.toMatrix b b τ) := by
    simp [b', LinearMap.dualMap_def]
  rw [hmat]
  exact Matrix.charpoly_transpose (LinearMap.toMatrix b b τ)
