import LinearAlgebraLemma.ForMathlib.Matrix
import Mathlib.LinearAlgebra.Prod

/-!
# Product-basis block matrix helpers

These lemmas support the concrete matrix model used by the project.  They are
kept out of `ForMathlib` because the statements are tailored to this proof's
block decomposition workflow.
-/

open Module

open LinearMap Sum LinearEquiv in
theorem matrix_conj_symm_basis
    (R : Type) [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    {W : Type} [AddCommGroup W] [Module R W]
    (I : Type) [Fintype I] [DecidableEq I]
    (f : V ≃ₗ[R] W)
    (b : Basis I R W)
    (x : Module.End R V)
    :
    (toMatrix b b (conj f x)) = (toMatrix (b.map f.symm) (b.map f.symm) x) := by
  convert LinearMap.toMatrix_conj R I f (b.map f.symm) x
  · exact (Module.Basis.map_symm_self b f).symm
  · exact (Module.Basis.map_symm_self b f).symm

open Module Matrix LinearEquiv LinearMap in
theorem matrix_conj_reindex_entries
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
  rw [matrix_conj_symm_basis]
  simp only [symm_symm]
  rw [hbef]
  rw [LinearMap.toMatrix_reindex R bV e.symm (toLin bV bV x) i j]
  simp only [Equiv.symm_symm, toMatrix_toLin]

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

open Module Matrix LinearEquiv LinearMap in
theorem matrix_incl_entries_reindexed
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
  rw [matrix_conj_reindex_entries R (I → R) (V₁ × V₂) (Pi.basisFun R I) b e f hbef y i j]
  simp [y]
  rw [matrix_incl_entries R V₁ V₂ b₁ b₂ ((toLin b₁ b₁) x) (e i) (e j)]
  simp only [toMatrix_toLin]
  cases hi : e i <;> cases hj : e j <;> simp only

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

open Module Matrix LinearEquiv LinearMap in
theorem matrix_proj_entries_reindexed
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
    rw [Module.Basis.reindex_map]
  rw [matrix_conj_reindex_entries R (V₁ × V₂) (I → R) b (Pi.basisFun R I) e.symm f.symm hbef' _ _ _]
  simp only [submatrix_apply, Function.comp_apply]
