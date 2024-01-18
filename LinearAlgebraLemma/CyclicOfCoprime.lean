import Mathlib
import LinearAlgebraLemma.Defs
import LinearAlgebraLemma.Common

/-!

# Main results:

* `cyclic_e_of_coprime_charpoly`

* `cyclic_e'_of_coprime_charpoly`

The latter is proved directly.  The formed is deduced from the latter
via a duality argument.

-/

/-

For (v, 0) in the first summand of V₁ × V₂, and any endomorphism x,
we have

  x (v, 0) = (x₀ v, ?),

where 0 means "upper-left block".

-/
theorem upper_left_action
    (R : Type) [CommRing R]
    (V₁ : Type) [AddCommGroup V₁] [Module R V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module R V₂]
    (x : Module.End R (V₁ × V₂))
    (v₁ : V₁)
    : (x (v₁, 0)).1 = (upperLeftProj R V₁ V₂ x) v₁
    := by
  unfold upperLeftProj
  simp

/-

Suppose that (v, 0) lies in a τ-stable subspace U of the first summand of
V₁ × V₂.  Then for any endomorphism x that stabilizes U, we have

  x (v, 0) = (x₀ v, 0),

where a subscripted 0 means "upper-left block".

-/
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
    : x (v₁, 0) = ((upperLeftProj R V₁ V₂ x) v₁, 0)
    := by
  have h : x (v₁, 0) ∈ U := hx (v₁, 0) hv₁
  replace h := hU h
  have h₂ : (x (v₁, 0)).2 = 0 := by exact h
  have h₃ : (x (v₁, 0)) = ((x (v₁, 0)).1, (x (v₁, 0)).2) := by simp
  rw [h₃, h₂, upper_left_action R V₁ V₂ x v₁]

/-

For a scalar c, vector v and endomorphism τ, we have
  
  (c τ^{n+1}) v = τ ((c τ^n) v).

-/
open Polynomial in
theorem monomial_induction_helper
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    (c : R)
    (n : ℕ)
    (τ : Module.End R V)
    (v : V)
    : ((aeval (R := R) τ) ((monomial (Nat.succ n)) c)) v = τ (((aeval (R := R) τ) ((monomial n) c)) v)
    := by
  rw [(X_mul_monomial n c).symm, aeval_mul τ, aeval_X τ]
  rfl

/-

If τ stabilizes a submodule U, then so does p(τ) for any polynomial p.

-/
open Polynomial in
theorem polynomial_of_stabilizing_element_stabilizes
    (R : Type) [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    {U : Submodule R V}
    (τ : Module.End R V)
    (h : ∀ v ∈ U, τ v ∈ U)
    (p : R[X])
    : ∀ v ∈ U, ((aeval (R := R) τ) p) v ∈ U
    := by
  induction' p using Polynomial.induction_on' with p q hp hq n a
  · intro v hv
    simp
    exact Submodule.add_mem U (hp v hv) (hq v hv)
  induction' n with n hn
  · simp
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
  · simp [hp, hq]
  · induction' f_n with f_n hf_n
    · simp
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
  have h : u = ((aeval (R := R) τ) (1 : R[X])) u := by simp
  rw [← hxy] at h
  rw [map_add, map_mul, CH] at h
  simp at h
  have ez1 : u ∈ Submodule.fst R V R := hU hu
  have ez2 : u = (u.1, u.2) := by simp
  have ez3 : u = (u.1, 0) := by
    unfold Submodule.fst at ez1
    simp at ez1
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
  simp at key1
  rw [key1] at h
  have : ((0 : V), (0 : R)) = (0 : V × R) := by
    simp
  rw [this] at h
  simp at h
  exact h

/-

If we apply polynomials in some endomorphism τ to some dual vector,
then we get a τ-stable submodule of the dual space.

-/
open Polynomial in
theorem dual_evalmap_stable_range
    {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    (τ : Module.End R V)
    (e' : Module.Dual R V)
    :
    let W : Submodule R (Module.Dual R V) := LinearMap.range (EvalMap τ.dualMap e')
    ∀ w ∈ W, τ.dualMap w ∈ W 
    := by
  intro W w hw
  rcases hw with ⟨ p, hp ⟩
  simp
  use (X*p : R[X])
  rw [← hp]
  simp [EvalMap]

/-

The annihilator of a τ-stable submodule is likewise τ-stable.

-/
theorem stable_coannihilator_of_stable_module
    (R : Type) [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V]
    (τ : Module.End R V)
    {W : Submodule R (Module.Dual R V)}
    (hW : ∀ w ∈ W, τ.dualMap w ∈ W)
    : ∀ v ∈ Submodule.dualCoannihilator W, τ v ∈ Submodule.dualCoannihilator W
    := by
  intro v hv
  simp [Submodule.dualCoannihilator] at hv ⊢
  intro w hw
  have h : τ.dualMap w ∈ W := hW w hw
  exact hv (τ.dualMap w) h

/-

Let τ be an endomorphism of R^{n+1} ≃ R^n × R whose characteristic
polynomial is coprime to that of its upper-left n×n block.  Then the
row-vector (0,1) is τ-cyclic.

(Proved here over a field, but should be provably true over any
nontrivial commutative ring.  To reduce the general case to that of
fields, we need that modules can be compared after localizing at
primes to reduce to the local case, where we can appeal to Nakayama's
lemma.)

-/
theorem cyclic_e'_of_coprime_charpoly
    (R : Type) [Field R] -- [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (τ : Module.End R (V × R)) 
    (hτ : IsCoprime τ.charpoly (upperLeftProj R V R τ).charpoly)
    :
    let e' : Module.Dual R (V × R) := LinearMap.snd R V R
    Cyclic R τ.dualMap e'
    := by
  intro e'
  let W : Submodule R (Module.Dual R (V × R)) := LinearMap.range (EvalMap τ.dualMap e')
  suffices : W = ⊤
  · unfold Cyclic
    rw [LinearMap.range_eq_top] at this
    exact this
  let U : Submodule R (V × R) := Submodule.dualCoannihilator W
  suffices : U = ⊥
  · have h : W = Submodule.dualAnnihilator U := 
      Subspace.dualCoannihilator_dualAnnihilator_eq.symm
    rw [h, this]
    exact Submodule.dualAnnihilator_bot
  have hU : U ≤ Submodule.fst R V R := by
    intro u hu
    simp only [Submodule.dualCoannihilator, Submodule.mem_comap, Submodule.mem_dualAnnihilator,
      LinearMap.mem_range, EvalMap_apply, Module.Dual.eval_apply, forall_exists_index,
      forall_apply_eq_imp_iff] at hu 
    replace hu := hu (1 : Polynomial R)
    simp only [map_one, LinearMap.one_apply, LinearMap.snd_apply] at hu 
    exact hu
  have hτW : ∀ w ∈ W, τ.dualMap w ∈ W := dual_evalmap_stable_range τ e'
  have hτU : ∀ u ∈ U, τ u ∈ U := stable_coannihilator_of_stable_module R τ hτW
  exact no_invariant_subspaces_of_coprime_charpoly R V τ hτ U hU hτU

/-

********************************************************************************

The remainder of this file is devoted to proving the "transpose" of
the above theorem, namely, `cyclic_e_of_coprime_charpoly` below.
I could have just imitated the above arguments, but thought it might
be slicker to pass from `cyclic_e'_of_coprime_charpoly` to
`cyclic_e_of_coprime_charpoly` by taking tranposes in the obvious
way, using conjugation by the map `κ` defined below.  For better or
worse, the details of this reduction turned out to be much lengthier
than a direct proof would have been.

In retrospect, it might have been simpler to express everything in
terms of matrices all along, so that the "transpose" operation behaves
much more simply.  Alas.


********************************************************************************

-/

  
/-

(V × R) → (V' × R)'

-/
open Module LinearMap LinearEquiv in
noncomputable def κ
    (R : Type) [Field R]
    (V : Type) [AddCommGroup V] [Module R V] [Finite R V]
    : (V × R) ≃ₗ[R] (Dual R ((Dual R V) × R))
    := -- (V × R) → (V × R)'' → (V' × R')' → (V' × R)'
  evalEquiv R (V × R) 
  ≪≫ₗ (dualMap $ coprodEquiv R)
  ≪≫ₗ (dualMap $ (refl R $ Dual R V).prod (symm $ ringLmapEquivSelf R R R))

open Module LinearMap in
theorem κ_e
    (R : Type) [Field R]
    (V : Type) [AddCommGroup V] [Module R V] [Finite R V]
    : κ R V (0,1) = snd R (Dual R V) R
    := by
  unfold κ
  ext v
  simp
  simp

/-

(V × R)' → V' × R

-/
open Module LinearMap LinearEquiv in
noncomputable def κ'
    (R : Type) [Field R]
    (V : Type) [AddCommGroup V] [Module R V] [Finite R V]
    : (Dual R (V × R)) ≃ₗ[R] ((Dual R V) × R)
    -- (V × R)' → V' × R' → V' × R
    := (coprodEquiv R).symm ≪≫ₗ (refl R $ Dual R V).prod (ringLmapEquivSelf R R R)

/-

V' × W' ≃ (V × W)'

-/
open Module LinearMap LinearEquiv in
theorem fst_κ'
    {R : Type} [Field R]
    {V : Type} [AddCommGroup V] [Module R V] [Finite R V]
    : (fst R (Dual R V) R) ∘ₗ (κ' R V).toLinearMap = (fst R (Dual R V) (Dual R R)) ∘ₗ ((coprodEquiv R).symm : Dual R (V × R) ≃ₗ[R] (Dual R V) × (Dual R R))
    := by
  unfold κ'
  rfl

open Module LinearMap in
theorem fst_κ'_apply
    {R : Type} [Field R]
    {V : Type} [AddCommGroup V] [Module R V] [Finite R V]
    (v : Dual R (V × R))
    : ((κ' R V) v).1 = (((coprodEquiv R).symm : Dual R (V × R) ≃ₗ[R] (Dual R V) × (Dual R R)) v).1
    := by
  unfold κ'
  rfl

open Module LinearMap LinearEquiv in
theorem κ'_symm
    (R : Type) [Field R]
    (V : Type) [AddCommGroup V] [Module R V] [Finite R V]
    : (κ' R V).symm = ((refl R $ Dual R V).prod (ringLmapEquivSelf R R R)).symm ≪≫ₗ (coprodEquiv R)
    := by rfl

open Module LinearMap LinearEquiv in
theorem κ'_symm_apply
    (R : Type) [Field R]
    (V : Type) [AddCommGroup V] [Module R V] [Finite R V]
    (v : (Dual R V) × R)
    : (κ' R V).symm v = (coprodEquiv R) (((refl R $ Dual R V).prod (ringLmapEquivSelf R R R)).symm v)
    := by rfl

open Module LinearMap LinearEquiv in
theorem κ'_symm_inl_lem1
    {R : Type} [Field R]
    {V : Type} [AddCommGroup V] [Module R V] [Finite R V]
    (w : Dual R V)
    : ((refl R $ Dual R V).prod (ringLmapEquivSelf R R R)).symm (w, 0) = (w,0)
    := (symm_apply_eq ((refl R (Dual R V)).prod (ringLmapEquivSelf R R R))).mpr rfl

open Module LinearMap LinearEquiv in
theorem κ'_symm_inl_lem2
    {R : Type} [Field R]
    {V : Type} [AddCommGroup V] [Module R V] [Finite R V]
    (w : Dual R V)
    : (coprodEquiv R) ((w, 0) : (Dual R V) × (Dual R R)) = w ∘ₗ fst R V R
    := by
  simp
  exact coprod_zero_right w

open Module LinearMap LinearEquiv in
theorem κ'_symm_inl
    {R : Type} [Field R]
    {V : Type} [AddCommGroup V] [Module R V] [Finite R V]
    (w : Dual R V)
    : (κ' R V).symm (w, 0) = w ∘ₗ fst R V R := by
  rw [κ'_symm_apply, κ'_symm_inl_lem1, κ'_symm_inl_lem2]


open Module LinearMap LinearEquiv in
theorem upper_left_conj_κ'
    {R : Type} [Field R]
    {V : Type} [AddCommGroup V] [Module R V] [Free R V] [Finite R V]
    (τ : End R (V × R)) 
    :
    let V' := Dual R V
    (upperLeftProj R V' R ((conj (κ' R V)) τ.dualMap)) = (upperLeftProj R V R τ).dualMap := by
  unfold upperLeftProj
  ext w v
  simp [conj]
  rw [κ'_symm_inl w]
  rw [fst_κ'_apply]
  simp

open Module LinearMap LinearEquiv in
theorem dual_dual
    (R : Type) [Field R]
    (V : Type) [AddCommGroup V] [Module R V] [Free R V] [Finite R V]
    (x : End R V)
    :
    x.dualMap.dualMap = (evalEquiv R V) ∘ₗ x ∘ₗ ((evalEquiv R V).symm : Dual R (Dual R V) ≃ₗ[R] V)
    := by
  calc
  _ = x.dualMap.dualMap ∘ₗ (refl R (Dual R (Dual R V))) := rfl
  _ = x.dualMap.dualMap ∘ₗ ((evalEquiv R V).symm ≪≫ₗ (evalEquiv R V)) := by rw [(symm_trans_self _)]
  _ = (x.dualMap.dualMap ∘ₗ (evalEquiv R V) : V →ₗ[R] Dual R (Dual R V)) ∘ₗ ((evalEquiv R V).symm : Dual R (Dual R V) ≃ₗ[R] V) := by rfl
  _ = ((evalEquiv R V) ∘ₗ x) ∘ₗ ((evalEquiv R V).symm : Dual R (Dual R V) ≃ₗ[R] V) := by rfl
  _ = (conj (evalEquiv R V)) x := by rfl

open Module in
theorem relate_κ_κ'
    (R : Type) [Field R]
    (V : Type) [AddCommGroup V] [Module R V] [Free R V] [Finite R V]
    (τ : End R (V × R)) 
    : ((κ' R V) ∘ₗ τ.dualMap ∘ₗ (κ' R V).symm).dualMap
    = (κ R V).toLinearMap ∘ₗ τ ∘ₗ (κ R V).symm.toLinearMap
    := by
  calc
  ((κ' R V) ∘ₗ τ.dualMap ∘ₗ (κ' R V).symm).dualMap
    = (κ' R V).symm.dualMap ∘ₗ τ.dualMap.dualMap ∘ₗ (κ' R V).dualMap := by rfl
  _ = (κ' R V).symm.dualMap
    ∘ₗ ((evalEquiv R (V × R)).toLinearMap ∘ₗ τ ∘ₗ (evalEquiv R (V × R)).symm.toLinearMap)
    ∘ₗ (κ' R V).dualMap := by 
    rw [dual_dual R (V × R) τ]
  _ = ((evalEquiv R (V × R)) ≪≫ₗ (κ' R V).symm.dualMap) ∘ₗ τ ∘ₗ ((κ' R V).dualMap ≪≫ₗ (evalEquiv R (V × R)).symm) := by rfl
  _ = (κ R V).toLinearMap ∘ₗ τ ∘ₗ (κ R V).symm.toLinearMap := by rfl

open Matrix in
theorem charmatrix_transpose
    {R : Type} [CommRing R]
    {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I R)
    : charmatrix (Aᵀ) = (charmatrix A)ᵀ
    := by
  ext i j n
  simp [charmatrix]
  simp [diagonal]
  by_cases h : i = j
  · simp [h]
  have h' : j ≠ i := Ne.symm h
  simp [h, h']

open Matrix in
theorem charpoly_transpose
    (R : Type) [CommRing R]
    (I : Type) [Fintype I] [DecidableEq I]
    (A : Matrix I I R)
    : A.charpoly = (Aᵀ).charpoly
    := by
  unfold Matrix.charpoly
  rw [charmatrix_transpose, det_transpose]

open LinearMap Module in
theorem charpoly_dualmap_eq_charpoly
    {R : Type} [Field R]
    {V : Type} [AddCommGroup V] [Module R V] [Free R V] [Finite R V]
    (τ : End R V) 
    : τ.dualMap.charpoly = τ.charpoly
    := by
  let b := Module.Free.chooseBasis R V
  rw [← charpoly_toMatrix τ b]
  let b' := Basis.dualBasis b
  rw [← charpoly_toMatrix τ.dualMap b']
  nth_rw 1 [charpoly_transpose]
  apply congrArg Matrix.charpoly
  ext i j
  simp [dualMap]

/-

The condiiton that a matrix and its upper-left block have coprime
characteristic polynomials is invariant under conjugation by κ.

-/
open Module LinearEquiv in
theorem upper_left_coprimality_dual
    (R : Type) [Field R]
    (V : Type) [AddCommGroup V] [Module R V] [Free R V] [Finite R V]
    (τ : End R (V × R)) 
    (hτ : IsCoprime τ.charpoly (upperLeftProj R V R τ).charpoly)
    :
    let V' := Dual R V
    let τ' : End R (V' × R) := (κ' R V).conj τ.dualMap
    IsCoprime τ'.charpoly (upperLeftProj R V' R τ').charpoly := by
  intro V' τ'
  have h₁ : τ.charpoly = τ'.charpoly := by
    calc
    _ = τ.dualMap.charpoly := (charpoly_dualmap_eq_charpoly τ).symm
    _ = τ'.charpoly := charpoly_eq_conj_charpoly (κ' R V) τ.dualMap
  have h₂ : (upperLeftProj R V R τ).charpoly = (upperLeftProj R V' R τ').charpoly := by
    rw [upper_left_conj_κ']
    rw [← charpoly_dualmap_eq_charpoly]
  rw [h₁, h₂] at hτ
  exact hτ

open Module LinearEquiv in
theorem madness1
    (R : Type) [Field R]
    (V : Type) [AddCommGroup V] [Module R V] [Free R V] [Finite R V]
    (τ : End R (V × R)) 
    :
    (κ R V).toLinearMap ∘ₗ τ = ((κ R V).toLinearMap ∘ₗ τ ∘ₗ (κ R V).symm.toLinearMap) ∘ₗ (κ R V) := by
  calc
  (κ R V).toLinearMap ∘ₗ τ = (κ R V).toLinearMap ∘ₗ τ ∘ₗ (refl R (V × R)) := rfl
  _ = (κ R V).toLinearMap ∘ₗ τ ∘ₗ ((κ R V) ≪≫ₗ (κ R V).symm).toLinearMap := by rw [(self_trans_symm _)]
  _ = (κ R V).toLinearMap ∘ₗ τ ∘ₗ (κ R V).symm.toLinearMap ∘ₗ (κ R V) := by rfl
  _ = ((κ R V).toLinearMap ∘ₗ τ ∘ₗ (κ R V).symm.toLinearMap) ∘ₗ (κ R V) := by rfl

open Module in
theorem madness2
    (R : Type) [Field R]
    (V : Type) [AddCommGroup V] [Module R V] [Free R V] [Finite R V]
    (τ : End R (V × R)) 
    :
    let τ' := ((κ' R V).toLinearMap ∘ₗ τ.dualMap ∘ₗ (κ' R V).symm.toLinearMap)
    (κ R V) ∘ₗ τ = τ'.dualMap ∘ₗ (κ R V) := by
  intro τ'
  rw [madness1 R V τ]
  rw [← relate_κ_κ' R V τ]

open LinearMap LinearEquiv Module Polynomial in
theorem necessary_equivariance
    (R : Type) [Field R]
    (V : Type) [AddCommGroup V] [Module R V] [Free R V] [Finite R V]
    (τ : End R (V × R)) 
    :
    let τ' := ((κ' R V).toLinearMap ∘ₗ τ.dualMap ∘ₗ (κ' R V).symm.toLinearMap)
    ∀ p : R[X], (κ R V) ∘ₗ (aeval (R := R) τ p) = (aeval (R := R) τ'.dualMap p) ∘ₗ (κ R V).toLinearMap
    := by
  intro τ' p
  induction' p using Polynomial.induction_on' with p q hp hq n c
  · rw [aeval_add τ, aeval_add _, comp_add, add_comp _ _ _, hp, hq]
  induction' n with n hn
  · refine LinearMap.ext fun v => ?_
    simp
  rw [(monomial_mul_X n c).symm, aeval_mul, aeval_X, aeval_mul, aeval_X]
  have : (κ R V) ∘ₗ τ = τ'.dualMap ∘ₗ (κ R V) := madness2 R V τ
  calc
  (κ R V) ∘ₗ ((aeval (R := R) τ) ((monomial n) c) * τ)
      = ((κ R V) ∘ₗ ((aeval (R := R) τ) ((monomial n) c))) ∘ₗ τ
    := rfl
  _ = ((aeval (R := R) τ'.dualMap) ((monomial n) c) ∘ₗ (κ R V)) ∘ₗ τ := by rw [hn]
  _ = (aeval (R := R) τ'.dualMap) ((monomial n) c) ∘ₗ (κ R V) ∘ₗ τ := rfl
  _ = (aeval (R := R) τ'.dualMap) ((monomial n) c) ∘ₗ τ'.dualMap ∘ₗ (κ R V) := by rw [this]

open LinearMap LinearEquiv Module Polynomial in
theorem necessary_equivariance'
    (R : Type) [Field R]
    (V : Type) [AddCommGroup V] [Module R V] [Free R V] [Finite R V]
    (τ : End R (V × R))
    (v : V × R)
    :
    let τ' : End R ((Dual R V) × R) := conj (κ' R V) τ.dualMap
    ∀ p : R[X], (κ R V).symm (EvalMap τ'.dualMap (κ R V v) p) = EvalMap τ v p := by
  intro τ' p
  suffices : (κ R V) (EvalMap τ v p) = EvalMap τ'.dualMap (κ R V v) p
  · symm
    apply LinearEquiv.injective (κ R V)
    rw [this]
    simp
  rw [EvalMap_apply, EvalMap_apply]
  calc
  (κ R V) (((aeval (R := R) τ) p) v) = ((κ R V) ∘ₗ ((aeval (R := R) τ) p)) v := by rfl
  _ = ((κ R V) ∘ₗ ((aeval (R := R) τ) p)) v := by rfl
  _ = ((aeval (R := R) τ'.dualMap p) ∘ₗ (κ R V).toLinearMap) v := by 
    rw [necessary_equivariance R V τ]
    rfl
  _ = ((aeval (R := R) τ'.dualMap) p) (κ R V v) := by rfl

/-

Let τ be an endomorphism of R^{n+1} ≃ R^n × R whose characteristic
polynomial is coprime to that of its upper-left n×n block.  Then the
column-vector (0,1)^t is τ-cyclic.

-/
open LinearMap LinearEquiv Module Polynomial LinearMap in
theorem cyclic_e_of_coprime_charpoly
    (R : Type) [Field R] -- [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Free R V] [Finite R V]
    (τ : End R (V × R)) 
    (hτ : IsCoprime τ.charpoly (upperLeftProj R V R τ).charpoly)
    :
    let e : (V × R) := (0,1)
    Cyclic R τ e
    := by
  intro e
  set V' := Dual R V
  set e' : Dual R (V' × R) := snd R V' R
  have he' : e' = κ R V e := (κ_e R V).symm
  set τ' : End R (V' × R) := conj (κ' R V) τ.dualMap
  have equiv : ∀ p : R[X], (κ R V).symm (EvalMap τ'.dualMap e' p) = EvalMap τ e p := by
    rw [he']
    exact necessary_equivariance' R V τ e
  let W : Submodule R (V × R) := range (EvalMap τ e)
  suffices : W = ⊤
  · unfold Cyclic
    rw [range_eq_top] at this
    exact this
  set W' : Submodule R (Dual R (V' × R)) := range (EvalMap τ'.dualMap e')
  have hτ' : IsCoprime τ'.charpoly (upperLeftProj R V' R τ').charpoly
    := upper_left_coprimality_dual R V τ hτ
  rw [eq_top_iff]
  intro w _
  set w' : Dual R (V' × R) := (κ R V) w with hw'
  have := cyclic_e'_of_coprime_charpoly R V' τ' hτ'
  have := this w'
  rcases this with ⟨ p, hp ⟩
  have := equiv p
  rw [hp, hw'] at this
  simp at this
  rw [this]
  simp
