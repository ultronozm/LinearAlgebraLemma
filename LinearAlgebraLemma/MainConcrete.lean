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
import LinearAlgebraLemma.BlockMatrix
import LinearAlgebraLemma.MainAbstract
import LinearAlgebraLemma.Defs

open Module

/-!

# Main results:

* `MainConcrete`, `MainConcrete'`

-/

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
    simp only [LinearEquiv.conj_conj_symm]
  rw [upperLeftIncl_apply]
  let b₁ : Basis (Fin n) R (Fin n → R) := Pi.basisFun R (Fin n)
  let b₂ : Basis (Fin 1) R R := Basis.singleton (Fin 1) R
  let e : Fin (n+1) ≃ (Fin n) ⊕ (Fin 1) := finSumFinEquiv.symm
  let hbef : (Pi.basisFun R (Fin (n+1))).map decomp = (b₁.prod b₂).reindex e.symm := aux_reindex_bases R n
  have : toLin' y = toLin b₁ b₁ y := rfl
  rw [this]
  rw [matrix_incl_entries_reindexed R (Fin n → R) R b₁ b₂ e decomp hbef y]
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
  rw [matrix_proj_entries_reindexed R (Fin n → R) R b₁ b₂ e decomp hbef _]
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
  exact (RingHom.map_lie (ι_AlgEquiv R n).toRingEquiv.toRingHom x y).symm

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
      := (RingHom.map_lie (ι_AlgEquiv R n).toRingEquiv.toRingHom _ τ).symm
    rw [this]
  _ = ⁅ι x, ι ⁅(matrixIncl (1 : Mat R n)), τ⁆⁆ := rfl
  _ = ι ⁅x, ⁅(matrixIncl (1 : Mat R n)), τ⁆⁆
    := (RingHom.map_lie (ι_AlgEquiv R n).toRingEquiv.toRingHom x _).symm
  _ = ι ⁅matrixIncl y, τ⁆ := by rw [heq]
  _ = ⁅ι (matrixIncl y), ι τ⁆
    := RingHom.map_lie (ι_AlgEquiv R n).toRingEquiv.toRingHom _ τ
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
          (Matrix.charpoly_toLin' (submatrix τ (Fin.castAdd 1) (Fin.castAdd 1))).symm
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
open LinearEquiv LinearMap Matrix nonZeroDivisors in
theorem MainConcrete
    (n : ℕ)
    (R : Type) [Field R] [DecidableEq R]
    (hR : (2 : R) ∈ R⁰)
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
    have h1 :
        (conj (decomp (R := R) (n := n)) (toLin' τ)).charpoly =
          Matrix.charpoly τ := (charpoly_eq_conj_decomp_toLin_charpoly (x := τ)).symm
    have h1' : τ'.charpoly = Matrix.charpoly τ := by
      dsimp [τ', ι_apply]
      exact h1
    rw [h1']
    -- unfold upperLeftProj and τ' to match hτ0
    simp [upperLeftProj, τ', ι_apply] at *
    exact hτ0
  let x' : Module.End R (V × R) := (ι (R := R) (n := n) x)
  have hx' : ⁅x', τ'⁆ = 0 := by
    exact RingHom.map_lie_eq_zero (ι_AlgEquiv R n).toRingEquiv.toRingHom x τ hx
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
open nonZeroDivisors in
theorem MainConcrete'
    (n : ℕ)
    (τ : Mat ℂ (n+1)) (hτ : IsCoprime τ.charpoly (Matrix.subUpLeft τ).charpoly)
    (x : Mat ℂ (n+1)) (hx : ⁅x, τ⁆ = 0) (y : Mat ℂ n)
    (h : ⁅x, ⁅matrixIncl (1 : Mat ℂ n), τ⁆⁆ = ⁅matrixIncl y, τ⁆)
    : ∃ (r : ℂ), x = r • (1 : Mat ℂ (n+1)) := by
  have hR : (2 : ℂ) ∈ ℂ⁰ := by
    have : IsUnit (2 : ℂ) := by exact (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : ℂ) ≠ 0))
    exact IsUnit.mem_nonZeroDivisors this
  exact MainConcrete n ℂ hR τ hτ x hx y h
