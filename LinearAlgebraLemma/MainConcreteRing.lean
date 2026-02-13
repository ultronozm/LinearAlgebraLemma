import LinearAlgebraLemma.MainConcrete
import LinearAlgebraLemma.MainAbstract

open LinearEquiv LinearMap Matrix nonZeroDivisors

/-- Ring-level matrix version (coprime charpoly hypothesis). -/
theorem MainConcreteRing
    (n : ℕ)
    (R : Type) [CommRing R] [Nontrivial R] [DecidableEq R]
    (hR : (2 : R) ∈ R⁰)
    (τ : Mat R (n+1)) (hτ : IsCoprime τ.charpoly (Matrix.subUpLeft τ).charpoly)
    (x : Mat R (n+1)) (hx : ⁅x, τ⁆ = 0)
    (y : Mat R n)
    (heq : ⁅x, ⁅matrixIncl (1 : Mat R n), τ⁆⁆ = ⁅matrixIncl y, τ⁆)
    : ∃ (r : R), x = r • (1 : Mat R (n+1)) := by
  set V : Type := (Fin n) → R
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
    simp [upperLeftProj, τ', ι_apply] at *
    exact hτ0
  let x' : Module.End R (V × R) := (ι (R := R) (n := n) x)
  have hx' : ⁅x', τ'⁆ = 0 := by
    apply lie_map_of_ring_hom (B := Module.End R ((Fin n → R) × R)) R (ι_AlgEquiv R n) x τ hx
  let y' : Module.End R V := (toLin' y)
  have heq' := aux_commutator_equivariance τ x y heq
  have hmain : ∃ r : R, x' = r • (1 : Module.End R (V × R)) :=
    MainAbstract R hR V τ' hτ' x' hx' y' heq'
  rcases hmain with ⟨r, hr⟩
  have hr' : x' = algebraMap R (Module.End R ((Fin n → R) × R)) r := by
    simpa [Algebra.smul_def] using hr
  have hxmat : x = (toMatrix' (conj (decomp (R := R) (n := n)).symm x')) := by
    simp [x', ι_apply, toMatrix'_toLin']
  use r
  rw [hxmat, hr']
  simpa using (toMatrix_conj_decomp_scalar (R := R) (n := n) r)
