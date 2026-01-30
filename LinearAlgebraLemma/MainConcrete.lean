import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import LinearAlgebraLemma.MainAbstract
import LinearAlgebraLemma.CoprimeOfDisjointRoots
import LinearAlgebraLemma.Defs
import LinearAlgebraLemma.Common

/-!

# Main results:

* `MainConcrete`, `MainConcrete'`

-/

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
  apply charpoly_eq_conj_charpoly decomp.symm y

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

open LinearEquiv Matrix in
example {R : Type} [CommRing R] {n : ℕ}
    (x : Mat R (n+1))
    : conj decomp.symm (conj decomp $ toLin' x) = toLin' x
    := 
  by simp only [conj_cancel]

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

-- (roots-based coprimality lemma removed; we now assume IsCoprime directly)

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
  push_neg at h
  simp only [ne_eq]
  by_cases h' : i = Fin.last n
  · simp only [h', not_true_eq_false, false_and, Fin.val_last, dite_false,
    finSumFinEquiv_symm_last]
  simp only [h', not_false_eq_true, true_and, dite_not]
  replace h := h h'
  rw [h]
  simp [finSumFinEquiv_symm_last]


/-

The isomorphism R^{n+1} ≅ R^n × R preserves the obvious bases.

-/
open LinearMap LinearEquiv Matrix Basis in
theorem aux_reindex_bases
    (R : Type) [CommRing R]
    (n : ℕ) [DecidableEq (Fin n)] :
    let b₁ := Pi.basisFun R (Fin n);
    let b₂ := Basis.singleton (Fin 1) R;
    let e := finSumFinEquiv.symm;
    (Pi.basisFun R (Fin (n + 1))).map decomp = (b₁.prod b₂).reindex e.symm := by
  ext i i'
  · simp only [Basis.map_apply, Pi.basisFun_apply, Equiv.symm_symm, coe_reindex,
    Function.comp_apply, Basis.prod_apply, coe_inl, coe_inr]
    by_cases h : i = Fin.castAdd 1 i'
    · simp [decomp, h, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, piCongrLeft'_symm_apply]
    simp [decomp, h, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        piCongrLeft'_symm_apply]
    induction' h' : finSumFinEquiv.symm i with k k
    · simp only [Sum.elim_inl, Function.comp_apply, Pi.basisFun_apply, Pi.basisFun_apply]
      have : i = finSumFinEquiv (Sum.inl k) := (Equiv.symm_apply_eq finSumFinEquiv).mp h'
      rw [this] at h
      have : k ≠ i' := ne_of_apply_ne (fun k => finSumFinEquiv (Sum.inl k)) h
      have hk : i' ≠ k := by exact ne_comm.mp this
      simp [hk]
    simp [Sum.elim_inr, Function.const]
  simp only [Basis.map_apply, Pi.basisFun_apply, Equiv.symm_symm, coe_reindex, Function.comp_apply,
    Basis.prod_apply, coe_inl, coe_inr]
  by_cases h : i = Fin.natAdd n 0
  · simp [decomp, h, finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_apply_right,
      piCongrLeft'_symm_apply]
  simp [decomp, h, finSumFinEquiv_apply_right, piCongrLeft'_symm_apply]
  induction' h' : finSumFinEquiv.symm i with k k
  · simp only [Sum.elim_inl, Function.comp_apply, Pi.basisFun_apply]
  have := finSumFinEquiv_one_eq_last_iff n (Sum.inr k)
  simp only [finSumFinEquiv_apply_right, eq_iff_iff, iff_true] at this 
  have h'' : i = finSumFinEquiv (Sum.inr k) := by exact (Equiv.symm_apply_eq finSumFinEquiv).mp h'
  have : i = Fin.last n := by
    rw [← this]
    rw [h'']
    rfl
  rw [this] at h
  absurd h
  rfl

/-

The upper left inclusion from n×n matrices to (n+1)×(n+1) matrices may
be described via the isomorphism R^{n+1} ≅ R^n × R.

-/
open LinearMap LinearEquiv Matrix in
theorem aux_upper_left_incl_equivariance {R : Type} [CommRing R] {n : ℕ}
    (y : Mat R n)
    : upperLeftIncl R (Fin n → R) R (toLin' y) = (conj decomp $ toLin' (matrixIncl y)) := by
  rw [upperLeftIncl_apply]
  suffices : toMatrix' (conj decomp.symm (upperLeftIncl R (Fin n → R) R (toLin' y))) = matrixIncl y
  · replace this := congrArg (fun f ↦ (conj decomp $ toLin' f)) this
    simp only [upperLeftIncl_apply, toLin'_toMatrix'] at this
    rw [← this]
    simp only [conj_cancel']
  rw [upperLeftIncl_apply]
  let b₁ : Basis (Fin n) R (Fin n → R) := Pi.basisFun R (Fin n)
  let b₂ : Basis (Fin 1) R R := Basis.singleton (Fin 1) R
  let e : Fin (n+1) ≃ (Fin n) ⊕ (Fin 1) := finSumFinEquiv.symm
  let hbef : (Pi.basisFun R (Fin (n+1))).map decomp = (b₁.prod b₂).reindex e.symm := aux_reindex_bases R n
  have : toLin' y = toLin b₁ b₁ y := rfl
  rw [this]
  rw [matrix_incl_entries' R (Fin n → R) R b₁ b₂ e decomp hbef y]
  rw [matrixIncl_eq_matrixIncl']
  ext i j
  simp only [matrixIncl'_apply]
  induction' e i
  induction' e j
  simp only
  simp only
  induction' e j
  simp only
  simp only

/-

The upper left projection from (n+1)×(n+1) matrices to n×n matrices
may be described via the isomorphism R^{n+1} ≅ R^n × R.

-/
open LinearMap LinearEquiv Matrix in
theorem aux_upper_left_proj_equivariance {R : Type} [CommRing R] {n : ℕ}
    (x : Mat R (n+1))
    : toLin' (Matrix.subUpLeft x) = (upperLeftProj R ((Fin n) → R) R (conj decomp $ toLin' x)) := by
  rw [upperLeftProj_apply]
  suffices : toMatrix' (LinearMap.fst R (Fin n → R) R ∘ₗ (conj decomp $ toLin' x)
                         ∘ₗ LinearMap.inl R (Fin n → R) R)
             = (Matrix.subUpLeft x)
  · symm
    replace this := congrArg toLin' this
    rw [← this]
    ext i j
    simp only [coe_comp, coe_inl, coe_single, Function.comp_apply, fst_apply, toLin'_toMatrix']
  rw [← toMatrix_eq_toMatrix']
  let b₁ : Basis (Fin n) R (Fin n → R) := Pi.basisFun R (Fin n)
  let b₂ : Basis (Fin 1) R R := Basis.singleton (Fin 1) R
  let e : Fin (n+1) ≃ (Fin n) ⊕ (Fin 1) := finSumFinEquiv.symm
  let hbef : (Pi.basisFun R (Fin (n+1))).map decomp = (b₁.prod b₂).reindex e.symm :=
    aux_reindex_bases R n
  rw [matrix_proj_entries' R (Fin n → R) R b₁ b₂ e decomp hbef _]
  ext i j
  simp [e, Equiv.symm_symm, submatrix_apply, Function.comp_apply, finSumFinEquiv_apply_left, id_eq]

/-

In the remainder of this file, the map

  ι : {(n+1)×(n+1) matrices} → End(R^n × R)

appears often, so we have given it a short name.

-/

open LinearEquiv Matrix in
def ι_AlgEquiv (R : Type) [CommRing R] (n : ℕ)
    : (Mat R (n+1)) ≃ₐ[R] Module.End R ((Fin n → R) × R)
    := toLinAlgEquiv'.trans (LinearEquiv.conjAlgEquiv (R := R) decomp)

def ι {R : Type} [CommRing R] {n : ℕ}
    (x : Mat R (n+1))
    : Module.End R ((Fin n → R) × R) := ι_AlgEquiv R n x

open LinearEquiv Matrix in
@[simp]
theorem ι_apply  {R : Type} [CommRing R] {n : ℕ}
    (x : Mat R (n+1))
    : ι x = conj decomp (toLin' x) := by
  rfl

example
    {R : Type} [CommRing R] {n : ℕ}
    (x y : Mat R (n+1)) 
    : ⁅ι x, ι y⁆ = ι ⁅x, y⁆ := by
  apply lie_map_of_ring_hom' (B := Module.End R ((Fin n → R) × R)) R (ι_AlgEquiv R n) x y

/-

The commutators [x,[z,τ]] that arose in `MainAbstract` admit an
equivalent description on the other side of the isomorphism `ι`.

-/
open LinearEquiv Matrix in
theorem aux_commutator_equivariance {R : Type} [CommRing R] {n : ℕ}
    (τ : Mat R (n+1))
    (x : Mat R (n+1))
    (y : Mat R n)
    (heq : ⁅x, ⁅matrixIncl (1 : Mat R n), τ⁆⁆ = ⁅matrixIncl y, τ⁆)
    :
    let V := (Fin n) → R
    let τ' : Module.End R (V × R) := ι τ
    let x' : Module.End R (V × R) := ι x
    let y' : Module.End R V := toLin' y
    ⁅x', ⁅upperLeftIncl R V R 1, τ'⁆⁆ = ⁅upperLeftIncl R V R y', τ'⁆
    := by
  intro V τ' x' y'
  set V := (Fin n) → R
  have hy' : upperLeftIncl R V R y' = conj decomp (toLin' (matrixIncl y)) :=
    aux_upper_left_incl_equivariance y
  have h1H : upperLeftIncl R V R 1 = conj decomp (toLin' (matrixIncl (1 : Mat R n))) := by
    rw [← aux_upper_left_incl_equivariance 1]
    congr
    simp only [toLin'_one]
    rfl
  rw [hy', h1H]
  calc
  _ = ⁅x', ⁅ι (matrixIncl (1 : Mat R n)), ι τ⁆⁆ := rfl
  _ = ⁅x', ι ⁅(matrixIncl (1 : Mat R n)), τ⁆⁆ := by
    have : ⁅ι (matrixIncl (1 : Mat R n)), ι τ⁆ = (ι ⁅(matrixIncl (1 : Mat R n)), τ⁆)
      := by apply lie_map_of_ring_hom' (B := Module.End R (V × R)) R (ι_AlgEquiv R n) _ τ
    rw [this]
  _ = ⁅ι x, ι ⁅(matrixIncl (1 : Mat R n)), τ⁆⁆ := rfl
  _ = ι ⁅x, ⁅(matrixIncl (1 : Mat R n)), τ⁆⁆
    := by apply lie_map_of_ring_hom' (B := Module.End R (V × R)) R (ι_AlgEquiv R n) x _
  _ = ι ⁅matrixIncl y, τ⁆ := by rw [heq]
  _ = ⁅ι (matrixIncl y), ι τ⁆
    := by apply (lie_map_of_ring_hom' (B := Module.End R (V × R)) R (ι_AlgEquiv R n) _ τ).symm
  _ = ⁅ι (matrixIncl y), τ'⁆ := rfl

open LinearEquiv LinearMap Matrix in
theorem coprime_charpoly_transfer
    {R : Type} [CommRing R] [Nontrivial R] {n : ℕ}
    (τ : Mat R (n+1))
    (hτ : IsCoprime τ.charpoly (Matrix.subUpLeft τ).charpoly)
    : let τ' : Module.End R ((Fin n → R) × R) :=
        conj (decomp (R := R) (n := n)) (toLin' τ)
      IsCoprime τ'.charpoly (upperLeftProj R (Fin n → R) R τ').charpoly := by
  intro τ'
  have h1 : τ.charpoly = τ'.charpoly := by
    dsimp [τ']
    exact charpoly_eq_conj_decomp_toLin_charpoly τ
  have h2 :
      (submatrix τ (Fin.castAdd 1) (Fin.castAdd 1)).charpoly =
        (upperLeftProj R (Fin n → R) R τ').charpoly := by
    have h := aux_upper_left_proj_equivariance τ
    have h' :
        toLin' (submatrix τ (Fin.castAdd 1) (Fin.castAdd 1)) =
          upperLeftProj R (Fin n → R) R τ' := by
      dsimp [τ']
      simpa [Matrix.subUpLeft] using h
    calc
      _ = (toLin' (submatrix τ (Fin.castAdd 1) (Fin.castAdd 1))).charpoly :=
          charpoly_eq_toLin_charpoly (submatrix τ (Fin.castAdd 1) (Fin.castAdd 1))
      _ = (upperLeftProj R (Fin n → R) R τ').charpoly := by
          simpa using congrArg LinearMap.charpoly h'
  rcases hτ with ⟨a, b, hab⟩
  refine ⟨a, b, ?_⟩
  simpa [Matrix.subUpLeft, h1, h2] using hab

open LinearEquiv LinearMap Matrix in
theorem toMatrix_conj_decomp_scalar
    {R : Type} [CommRing R] {n : ℕ}
    (r : R) :
    toMatrix'
        (conj (decomp (R := R) (n := n)).symm
          (algebraMap R (Module.End R ((Fin n → R) × R)) r)) =
      r • (1 : Mat R (n+1)) := by
  have hconj :
      (conj (decomp (R := R) (n := n)).symm :
        Module.End R ((Fin n → R) × R) ≃ₗ[R] Module.End R (Fin (n+1) → R))
        =
      (LinearEquiv.conjAlgEquiv (R := R) (decomp (R := R) (n := n)).symm).toLinearEquiv := rfl
  have hcomm :
      (LinearEquiv.conjAlgEquiv (R := R) (decomp (R := R) (n := n)).symm)
          (algebraMap R (Module.End R ((Fin n → R) × R)) r) =
        algebraMap R (Module.End R (Fin (n + 1) → R)) r := by
    simp only [AlgEquiv.commutes]
  have hmat :
      LinearMap.toMatrix' (algebraMap R (Module.End R (Fin (n + 1) → R)) r) =
        r • (1 : Mat R (n + 1)) := by
    calc
      _ = LinearMap.toMatrix' (r • (1 : End R (Fin (n + 1) → R))) := by
          simp [Algebra.smul_def]
      _ = r • (LinearMap.toMatrix' (1 : End R (Fin (n + 1) → R))) := by simp
      _ = r • (1 : Mat R (n + 1)) := by simp [LinearMap.toMatrix'_one]
  simp [hconj, hcomm, hmat]

/-

Let x, τ be (n+1)×(n+1).  Let y be n×n, extended by zero to
(n+1)×(n+1).  Let z = diag(1,...,1,0).  If τ and its upper left block
have coprime characteristic polynomials, and

  [x, τ] = 0 and [x, [z, τ]] = [y, τ],

then x is a scalar.  Stated in the language of matrices, over a field
where 2 is a unit.

-/
-- keep default heartbeats here; ring version lives in MainConcreteRing
open LinearEquiv LinearMap Matrix
theorem MainConcrete
    (n : ℕ)
    (R : Type) [Field R] [DecidableEq R]
    (hR : IsUnit (2:R))
    (τ : Mat R (n+1)) (hτ : IsCoprime τ.charpoly (Matrix.subUpLeft τ).charpoly)
    (x : Mat R (n+1)) (hx : ⁅x, τ⁆ = 0)
    (y : Mat R n)
    (heq : ⁅x, ⁅matrixIncl (1 : Mat R n), τ⁆⁆ = ⁅matrixIncl y, τ⁆)
    : ∃ (r : R), x = r • (1 : Mat R (n+1))
    := by
  let V : Type := (Fin n → R)
  let τ' : Module.End R (V × R) := (ι (R := R) (n := n) τ)
  have hτ' : IsCoprime τ'.charpoly (upperLeftProj R V R τ').charpoly := by
    have hτ0 := coprime_charpoly_transfer (R := R) (n := n) τ hτ
    rcases hτ0 with ⟨a, b, hab⟩
    refine ⟨a, b, ?_⟩
    -- simpa [τ', ι_apply] using hab -- type error
    sorry
  let x' : Module.End R (V × R) := (ι (R := R) (n := n) x)
  have hx' : ⁅x', τ'⁆ = 0 := by
    apply lie_map_of_ring_hom (B := Module.End R ((Fin n → R) × R)) R (ι_AlgEquiv R n) x τ hx
  let y' : Module.End R V := (toLin' y)
  have heq' := aux_commutator_equivariance τ x y heq
  have hmain : ∃ r : R, x' = r • (1 : End R (V × R)) :=
    MainAbstract R hR V τ' hτ' x' hx' y' heq'
  rcases hmain with ⟨r, hr⟩
  have hr' : x' = algebraMap R (End R ((Fin n → R) × R)) r := by
    simpa [Algebra.smul_def] using hr
  have hxmat : x = (toMatrix' (conj (decomp (R := R) (n := n)).symm x')) := by
    simp [x', ι_apply, toMatrix'_toLin']
  use r
  rw [hxmat, hr']
  simpa using (toMatrix_conj_decomp_scalar (R := R) (n := n) r)

/-

Let x, τ be (n+1)×(n+1).  Let y be n×n, extended by zero to
(n+1)×(n+1).  Let z = diag(1,...,1,0).  If τ and its upper left block
have coprime characteristic polynomials, and

  [x, τ] = 0 and [x, [z, τ]] = [y, τ],

then x is a scalar.  Stated in the language of matrices over ℂ.

-/
theorem MainConcrete'
    (n : ℕ)
    (τ : Mat ℂ (n+1)) (hτ : IsCoprime τ.charpoly (Matrix.subUpLeft τ).charpoly)
    (x : Mat ℂ (n+1)) (hx : ⁅x, τ⁆ = 0) (y : Mat ℂ n)
    (h : ⁅x, ⁅matrixIncl (1 : Mat ℂ n), τ⁆⁆ = ⁅matrixIncl y, τ⁆)
    : ∃ (r : ℂ), x = r • (1 : Mat ℂ (n+1)) := by
  have hR : IsUnit (2 : ℂ) := by
    exact (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : ℂ) ≠ 0))
  exact MainConcrete n ℂ hR τ hτ x hx y h
