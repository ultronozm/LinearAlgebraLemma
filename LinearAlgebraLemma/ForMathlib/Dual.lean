import LinearAlgebraLemma.ForMathlib.Lie
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Small dual API candidates

Facts about `LinearMap.dualMap` that are independent of the project.
-/

namespace LinearMap

theorem dualMap_lie
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

theorem dualMap_injective_on_end
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V] :
    Function.Injective (fun τ : Module.End R V ↦ τ.dualMap) := by
  intro a b h
  change a.dualMap = b.dualMap at h
  have h' : a.dualMap.dualMap = b.dualMap.dualMap := by
    rw [h]
  exact (Module.dualMap_dualMap_eq_iff (R := R) (M := V)).mp h'

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

theorem charpoly_dualMap
    {R : Type} [CommRing R] [Nontrivial R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (τ : Module.End R V)
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

end LinearMap
