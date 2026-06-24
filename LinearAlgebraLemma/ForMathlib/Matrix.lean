import LinearAlgebraLemma.ForMathlib.Basis
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi

/-!
# Small matrix/linear-map API candidates

These lemmas say how `LinearMap.toMatrix` behaves under basis transport and
reindexing.
-/

open Module

namespace LinearMap

open LinearEquiv in
theorem toMatrix_map_equiv
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
  rw [toMatrix_map_left, toMatrix_map_right]
  congr 1
  ext v
  simp

open LinearEquiv in
theorem toMatrix_conj
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
  simp only [toMatrix_map_equiv]

theorem toMatrix_reindex
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

end LinearMap
