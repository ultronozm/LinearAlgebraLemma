import LinearAlgebraLemma.ForMathlib
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic

/-!
# Project definitions

This file contains the concrete block-decomposition vocabulary used by the
project.  These declarations are intentionally not staged in `ForMathlib`.
-/

abbrev Mat (R : Type) [Ring R] (n : ℕ) := Matrix (Fin n) (Fin n) R

/- The isomorphism `R^{n+1} ≃ R^n × R`. -/
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

private theorem toMatrix'_charpoly_eq_charpoly
    {R : Type} [CommRing R] [Nontrivial R] {n : ℕ}
    (y : Module.End R (Fin n → R)) : (LinearMap.toMatrix' y).charpoly = y.charpoly := by
  calc
    _ = Matrix.charpoly
        ((LinearMap.toMatrix (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin n))) y) := by rfl
    _ = y.charpoly := y.charpoly_toMatrix (Pi.basisFun R (Fin n))

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
  exact (toMatrix'_charpoly_eq_charpoly u).symm

open LinearEquiv LinearMap Matrix in
theorem charpoly_eq_conj_decomp_toLin_charpoly {R : Type} [CommRing R] [Nontrivial R] {n : ℕ}
    (x : Mat R (n+1))
    : x.charpoly = (conj decomp $ toLin' x).charpoly := by
  let y := (conj decomp $ toLin' x)
  have hy : x = (toMatrix' $ conj decomp.symm y) := by
    simp [y, toMatrix'_toLin']
  show Matrix.charpoly x = LinearMap.charpoly (conj decomp $ toLin' x)
  rw [charpoly_eq_toMatrix_conj_decomp_symm_charpoly y, hy]

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

/- Extend an `n × n` matrix by zero to an `(n+1) × (n+1)` matrix. -/
def matrixIncl {R : Type} [Ring R] {n : ℕ}
    (x : Mat R n) : Mat R (n+1) :=
  fun i j ↦ if h : i  ≠ Fin.last n ∧ j ≠ Fin.last n
    then x ⟨i, Fin.val_lt_last h.1⟩ ⟨j, Fin.val_lt_last h.2 ⟩
    else 0

/- The same extension, expressed through `finSumFinEquiv`. -/
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

@[simp]
theorem upperLeftProj_comp_upperLeftIncl
    (R : Type) [CommSemiring R]
    (V₁ : Type) [AddCommGroup V₁] [Module R V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module R V₂]
    (x : Module.End R V₁)
    : upperLeftProj R V₁ V₂ (upperLeftIncl R V₁ V₂ x) = x := by
  ext v
  rfl

@[simp]
theorem upperLeftIncl_comp_upperLeftProj
    (R : Type) [CommSemiring R]
    (V₁ : Type) [AddCommGroup V₁] [Module R V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module R V₂]
    (x : Module.End R V₁)
    : upperLeftIncl R V₁ V₂ (upperLeftProj R V₁ V₂ (upperLeftIncl R V₁ V₂ x)) =
        upperLeftIncl R V₁ V₂ x := by
  rw [upperLeftProj_comp_upperLeftIncl]

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
