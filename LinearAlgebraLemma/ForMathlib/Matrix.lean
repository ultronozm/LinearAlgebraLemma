import LinearAlgebraLemma.ForMathlib.Basis
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi

/-!
# Small matrix/linear-map API candidates

These lemmas say how `LinearMap.toMatrix` behaves under basis transport and
reindexing, and bridge `toMatrix'`/`toLin'` with characteristic polynomials.
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

open LinearMap in
theorem toMatrix_charpoly_eq_charpoly {R : Type} [CommRing R] [Nontrivial R] {n : ℕ}
    (y : Module.End R (Fin n → R)) : (toMatrix' y).charpoly = y.charpoly := by
  calc
  _ = Matrix.charpoly ((toMatrix (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin n))) y) := by rfl
  _ = y.charpoly := (y.charpoly_toMatrix (Pi.basisFun R (Fin n)))

open LinearMap Matrix in
theorem charpoly_eq_toLin_charpoly {R : Type} [CommRing R] [Nontrivial R] {n : ℕ}
    (x : Matrix (Fin n) (Fin n) R) : x.charpoly = (toLin' x).charpoly := by
  let y := toLin' x
  calc
  _ = Matrix.charpoly x := by rfl
  _ = Matrix.charpoly (toMatrix' y) := by simp [y, toMatrix'_toLin']
  _ = y.charpoly := toMatrix_charpoly_eq_charpoly y
