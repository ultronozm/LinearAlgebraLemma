import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.Tactic
import LinearAlgebraLemma.Defs

open scoped TensorProduct

/-!

# Main results:

* `cyclic_e_of_coprime_charpoly`

* `cyclic_e'_of_coprime_charpoly`

The latter is proved directly.  The formed is deduced from the latter
via a duality argument.

-/

noncomputable section

-- Helper: R_mod_P-linearity for `quotTensorEquivQuotSMul`
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

-- Helper: R_mod_P-linearity for `TensorProduct.rid`
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

-- Helper: upperLeftProj commutes with conjugation by prodCongr
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

end

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
    := rfl

-- Helper: baseChange of upper-left block for prodRight
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
  have h₃ : (x (v₁, 0)) = ((x (v₁, 0)).1, (x (v₁, 0)).2) := by simp only [Prod.mk.eta]
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
  rw [LinearMap.mem_range]
  use (X*p : R[X])
  rw [EvalMap_apply, ← hp]
  simp only [map_mul, aeval_X, Module.End.mul_apply, EvalMap_apply]

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
  simp only [Submodule.dualCoannihilator, Submodule.mem_comap, Submodule.mem_dualAnnihilator,
    Module.Dual.eval_apply] at hv ⊢
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
theorem cyclic_e'_of_coprime_charpoly_field
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
    have hu' : ∀ φ ∈ W, (φ u : R) = 0 :=
      (Submodule.mem_dualCoannihilator (Φ := W) (x := u)).1 hu
    have hu'' : (EvalMap τ.dualMap e' (1 : Polynomial R)) u = 0 := by
      apply hu'
      exact ⟨1, rfl⟩
    have : u.2 = 0 := by
      simpa [EvalMap_apply, map_one, Module.End.one_apply, e', LinearMap.snd_apply] using hu''
    simp [Submodule.fst, LinearMap.snd_apply, this]
  have hτW : ∀ w ∈ W, τ.dualMap w ∈ W := dual_evalmap_stable_range τ e'
  have hτU : ∀ u ∈ U, τ u ∈ U := stable_coannihilator_of_stable_module R τ hτW
  exact no_invariant_subspaces_of_coprime_charpoly R V τ hτ U hU hτU


/-

The following result would be useful for extending the above from
fields to general rings.

-/
theorem exists_maximal_smul_le_of_ne_bot_of_fg {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
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



/-

We have an isomorphism R^n → V.

We want to say that it induces an isomorphism (R/P)^N → V/PV.

-/



instance
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Finite R V]
    (I : Ideal R)
    : Module.Finite (R ⧸ I) (V ⧸ (I • (⊤ : Submodule R V) : Submodule R V))
    := by
    -- Use finiteness over R and restrict scalars along R → R⧸I
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
  · -- add
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
  · -- n = 0
    simp [EvalMap_apply, monomial_zero_left, aeval_C, Module.algebraMap_end_apply]
  -- monomial (n+1)
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
  · -- add
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
  · -- n = 0
    simp [monomial_zero_left, aeval_C, Module.algebraMap_end_apply]
  -- monomial (n+1)
  calc
    (aeval (R := S) (ibc.endHom τ) ((monomial (Nat.succ n) c).map (algebraMap R S))) (j m)
        = (algebraMap R S c) • (((ibc.endHom τ) ^ (n + 1)) (j m)) := by
            simp [aeval_monomial]
    _ = (algebraMap R S c) • j ((τ ^ (n + 1)) m) := by
            simp [endHom_pow_apply (ibc := ibc)]
    _ = j ((aeval (R := R) τ (monomial (Nat.succ n) c)) m) := by
            simp [aeval_monomial]


/-

Let τ be an endomorphism of R^{n+1} ≃ R^n × R whose characteristic
polynomial is coprime to that of its upper-left n×n block.  Then the
row-vector (0,1) is τ-cyclic.  R is any nontrivial commutative ring.

-/
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000
open Module Polynomial in
theorem cyclic_e'_of_coprime_charpoly
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (τ : End R (V × R))
    (hτ : IsCoprime τ.charpoly (upperLeftProj R V R τ).charpoly)
    :
    let e' : Dual R (V × R) := LinearMap.snd R V R
    Cyclic R τ.dualMap e'
    := by
  intro e'
  let W : Submodule R (Dual R (V × R)) := LinearMap.range (EvalMap τ.dualMap e')
  suffices : W = ⊤
  · unfold Cyclic
    rw [LinearMap.range_eq_top] at this
    exact this
  by_contra hW_ne_top
  let M := (Dual R (V × R)) ⧸ W
  have Mdef : M = ((Dual R (V × R)) ⧸ W) := rfl
  let N : Submodule R M := ⊤
  have hN_ne_bot : N ≠ ⊥ := by
    letI : Nontrivial M := (Submodule.Quotient.nontrivial_iff (p := W)).2 hW_ne_top
    exact top_ne_bot
  have hN_fg : Submodule.FG N := by
    simpa [N] using (Module.Finite.fg_top (R := R) (M := M))
  have : ∃ P : Ideal R, P.IsMaximal ∧ P • N < N :=
    exists_maximal_smul_le_of_ne_bot_of_fg N hN_fg hN_ne_bot
  rcases this with ⟨P, hP, hP'⟩
  absurd hP'
  suffices : N ≤ P • N
  · exact not_lt_of_ge this
  set Xmod := (⊤ : Submodule R (Dual R (V × R)))
  suffices : Xmod ≤ W ⊔ (P • Xmod)
  · have blah' : (⊤ : Submodule R (Dual R (V × R))) ≤
        W ⊔ ((P : Submodule R R) • (⊤ : Submodule R (Dual R (V × R)))) := by
      simpa [Xmod] using this
    have hN : (⊤ : Submodule R M) ≤ ((P : Submodule R R) • (⊤ : Submodule R M)) :=
      aux_isom_thms R (Dual R (V × R)) W P blah'
    have Ndef : N = ⊤ := rfl
    -- avoid definitional-equality issues with M
    simpa [M, Ndef] using hN
  let R_mod_P := R ⧸ P
  let V_mod_P := V ⧸ (P • (⊤ : Submodule R V) : Submodule R V)
  letI : Field R_mod_P := (Ideal.Quotient.field P)
  haveI : Module.Free R_mod_P V_mod_P := by infer_instance
  intro x _
  have hx : ∃ p : R[X], EvalMap τ.dualMap e' p - x ∈ P • Xmod := by
    classical
    -- Quotient map V × R → V/PV × R/P and its kernel.
    let qVR : (V × R) →ₗ[R] (V_mod_P × R_mod_P) :=
      ((Submodule.mkQ (P • (⊤ : Submodule R V) : Submodule R V)).comp
          (LinearMap.fst R V R)).prod
        ((Submodule.mkQ (P : Submodule R R)).comp (LinearMap.snd R V R))
    have hqVR_surj : Function.Surjective qVR := by
      rintro ⟨vbar, rbar⟩
      rcases (Submodule.mkQ_surjective (p := (P • (⊤ : Submodule R V) : Submodule R V)) vbar)
        with ⟨v, rfl⟩
      rcases (Submodule.mkQ_surjective (p := (P : Submodule R R)) rbar) with ⟨r, rfl⟩
      refine ⟨(v, r), ?_⟩
      -- spell out the components
      change
        (((Submodule.mkQ (P • (⊤ : Submodule R V) : Submodule R V)).comp
              (LinearMap.fst R V R)).prod
            ((Submodule.mkQ (P : Submodule R R)).comp (LinearMap.snd R V R))) (v, r) =
          (Submodule.Quotient.mk v, Ideal.Quotient.mk P r)
      simp
    have hqVR_ker :
        LinearMap.ker qVR =
          (P • (⊤ : Submodule R V) : Submodule R V).prod (P : Submodule R R) := by
      ext x
      rcases x with ⟨v, r⟩
      constructor
      · intro hx
        have hx' : qVR (v, r) = 0 := by
          simpa [LinearMap.mem_ker] using hx
        have hv0 : (Submodule.mkQ (P • (⊤ : Submodule R V)) v) = 0 := by
          simpa [qVR, Submodule.mkQ_apply, -Submodule.Quotient.mk_eq_zero] using
            congrArg Prod.fst hx'
        have hr0 : (Submodule.mkQ (P : Submodule R R) r) = 0 := by
          simpa [qVR, Submodule.mkQ_apply, -Submodule.Quotient.mk_eq_zero] using
            congrArg Prod.snd hx'
        have hv' : v ∈ (P • (⊤ : Submodule R V)) := by
          simpa [Submodule.Quotient.mk_eq_zero] using hv0
        have hr' : r ∈ (P : Submodule R R) := by
          have hr0' : (Submodule.Quotient.mk (p := (P : Submodule R R)) r) = 0 := by
            simpa [Submodule.mkQ_apply] using hr0
          exact (Submodule.Quotient.mk_eq_zero (p := (P : Submodule R R)) (x := r)).1 hr0'
        exact ⟨hv', hr'⟩
      · rintro ⟨hv, hr⟩
        have hv' : (Submodule.mkQ (P • (⊤ : Submodule R V)) v) = 0 := by
          simpa [Submodule.mkQ_apply] using
            (Submodule.Quotient.mk_eq_zero (p := (P • (⊤ : Submodule R V))) (x := v)).2 hv
        have hr' : (Submodule.mkQ (P : Submodule R R) r) = 0 := by
          simpa [Submodule.mkQ_apply, Ideal.Quotient.eq_zero_iff_mem] using hr
        have : qVR (v, r) = 0 := by
          apply Prod.ext
          · -- fst
            simpa [qVR, LinearMap.comp_apply, -Submodule.Quotient.mk_eq_zero] using hv'
          · -- snd
            simpa [qVR, LinearMap.comp_apply, -Submodule.Quotient.mk_eq_zero] using hr'
        simpa [LinearMap.mem_ker] using this
    have hqVR_ker_smul :
        LinearMap.ker qVR = (P • (⊤ : Submodule R (V × R))) := by
      ext x
      constructor
      · intro hx
        have hx' :
            x ∈ (P • (⊤ : Submodule R V) : Submodule R V).prod (P : Submodule R R) := by
          simpa [hqVR_ker] using hx
        rcases hx' with ⟨hx1, hx2⟩
        have h_inl :
            Submodule.map (LinearMap.inl R V R) (P • (⊤ : Submodule R V)) ≤
              (P • (⊤ : Submodule R (V × R))) := by
          refine (Submodule.map_le_iff_le_comap).2 ?_
          refine (Submodule.smul_le).2 ?_
          intro r hr v hv
          have hv' : (LinearMap.inl R V R) v ∈ (⊤ : Submodule R (V × R)) := by
            exact Submodule.mem_top
          have hmem : r • (LinearMap.inl R V R v) ∈ (P • (⊤ : Submodule R (V × R))) :=
            Submodule.smul_mem_smul hr hv'
          simpa [map_smul] using hmem
        have hx1' : (x.1, (0 : R)) ∈ (P • (⊤ : Submodule R (V × R))) := by
          have : (LinearMap.inl R V R) x.1 ∈
              Submodule.map (LinearMap.inl R V R) (P • (⊤ : Submodule R V)) := by
            exact ⟨x.1, hx1, rfl⟩
          exact h_inl this
        have hx2' : ((0 : V), x.2) ∈ (P • (⊤ : Submodule R (V × R))) := by
          have htop : ((0 : V), (1 : R)) ∈ (⊤ : Submodule R (V × R)) := by
            exact Submodule.mem_top
          have hmem : x.2 • ((0 : V), (1 : R)) ∈ (P • (⊤ : Submodule R (V × R))) :=
            Submodule.smul_mem_smul hx2 htop
          simpa using hmem
        have hsum : x = (x.1, (0 : R)) + ((0 : V), x.2) := by
          cases x
          simp
        have hxsum : (x.1, (0 : R)) + ((0 : V), x.2) ∈ (P • (⊤ : Submodule R (V × R))) :=
          Submodule.add_mem _ hx1' hx2'
        exact hsum ▸ hxsum
      · intro hx
        have hfst :
            Submodule.map (LinearMap.fst R V R) (P • (⊤ : Submodule R (V × R))) ≤
              (P • (⊤ : Submodule R V)) := by
          refine (Submodule.map_le_iff_le_comap).2 ?_
          refine (Submodule.smul_le).2 ?_
          intro r hr v hv
          have hv' : (LinearMap.fst R V R) v ∈ (⊤ : Submodule R V) := by
            exact Submodule.mem_top
          have hmem : r • (LinearMap.fst R V R v) ∈ P • (⊤ : Submodule R V) :=
            Submodule.smul_mem_smul hr hv'
          simpa [map_smul] using hmem
        have hsnd :
            Submodule.map (LinearMap.snd R V R) (P • (⊤ : Submodule R (V × R))) ≤
              (P : Submodule R R) := by
          refine (Submodule.map_le_iff_le_comap).2 ?_
          refine (Submodule.smul_le).2 ?_
          intro r hr v hv
          have hmem : (LinearMap.snd R V R v) * r ∈ P := P.mul_mem_left _ hr
          simpa [smul_eq_mul, mul_comm] using hmem
        have hx1 : x.1 ∈ (P • (⊤ : Submodule R V)) := by
          have : (LinearMap.fst R V R) x ∈
              Submodule.map (LinearMap.fst R V R) (P • (⊤ : Submodule R (V × R))) := by
            exact ⟨x, hx, rfl⟩
          exact hfst this
        have hx2 : x.2 ∈ (P : Submodule R R) := by
          have : (LinearMap.snd R V R) x ∈
              Submodule.map (LinearMap.snd R V R) (P • (⊤ : Submodule R (V × R))) := by
            exact ⟨x, hx, rfl⟩
          exact hsnd this
        have : x ∈ (P • (⊤ : Submodule R V) : Submodule R V).prod (P : Submodule R R) :=
          ⟨hx1, hx2⟩
        simpa [hqVR_ker] using this
    have hqVR_ker_invariant :
        LinearMap.ker qVR ≤ Submodule.comap τ (LinearMap.ker qVR) := by
      intro x hx
      have hx' : x ∈ (P • (⊤ : Submodule R (V × R))) := by
        simpa [hqVR_ker_smul] using hx
      have hsmul :
          (P • (⊤ : Submodule R (V × R))) ≤
            Submodule.comap τ (P • (⊤ : Submodule R (V × R))) := by
        refine (Submodule.smul_le).2 ?_
        intro r hr v hv
        have hv' : τ v ∈ (⊤ : Submodule R (V × R)) := by
          exact Submodule.mem_top
        have hmem : r • τ v ∈ (P • (⊤ : Submodule R (V × R))) :=
          Submodule.smul_mem_smul hr hv'
        simpa [map_smul] using hmem
      have : x ∈ Submodule.comap τ (P • (⊤ : Submodule R (V × R))) := hsmul hx'
      have : x ∈ Submodule.comap τ (LinearMap.ker qVR) := by
        simpa [hqVR_ker_smul] using this
      exact this
    -- R-linear equivalence: R/P ⊗ (V × R) ≃ V/PV × R/P (for base-change on duals)
    let e1 := (TensorProduct.prodRight R R_mod_P R_mod_P V R)
    let eV := (TensorProduct.quotTensorEquivQuotSMul V P)
    -- R_mod_P-linearity for eV (used later for base-change on duals)
    have eV_smul (a : R_mod_P) (x : (R_mod_P ⊗[R] V)) :
        eV (a • x) = a • eV x := by
      simpa [eV] using (eV_smul_baseChange (R := R) (V := V) (P := P) a x)
    let eV_S : (R_mod_P ⊗[R] V) ≃ₗ[R_mod_P] V_mod_P :=
      { toLinearMap :=
          { toFun := eV
            map_add' := by intro x y; simp only [map_add]
            map_smul' := by intro a x; exact eV_smul a x }
        invFun := eV.symm
        left_inv := eV.left_inv
        right_inv := eV.right_inv }
    let eR := (TensorProduct.rid R R_mod_P)
    -- R_mod_P-linearity for eR
    have eR_smul (a : R_mod_P) (x : (R_mod_P ⊗[R] R)) :
        eR (a • x) = a • eR x := by
      simpa [eR] using (eR_smul_baseChange (R := R) (P := P) a x)
    let eR_S : (R_mod_P ⊗[R] R) ≃ₗ[R_mod_P] R_mod_P :=
      { toLinearMap :=
          { toFun := eR
            map_add' := by intro x y; simp only [map_add]
            map_smul' := by intro a x; exact eR_smul a x }
        invFun := eR.symm
        left_inv := eR.left_inv
        right_inv := eR.right_inv }
    let e2 := (LinearEquiv.prodCongr eV eR)
    let e2_S := (LinearEquiv.prodCongr eV_S eR_S)
    let eVR_S := e1.trans e2_S
    let τ_mod_P : End R_mod_P (V_mod_P × R_mod_P) :=
      (eVR_S.conj (τ.baseChange R_mod_P))
    have hτ_mod_P : IsCoprime τ_mod_P.charpoly (upperLeftProj R_mod_P V_mod_P R_mod_P τ_mod_P).charpoly := by
      classical
      -- charpoly for τ_mod_P is charpoly of baseChange
      have hτ_char :
          (τ.baseChange R_mod_P).charpoly = τ_mod_P.charpoly := by
        simp only [LinearMap.charpoly_baseChange, LinearEquiv.charpoly_conj, τ_mod_P]
      -- relate upper-left block to baseChange
      let τ1 : End R_mod_P (R_mod_P ⊗[R] V × R_mod_P ⊗[R] R) :=
        (e1.conj (τ.baseChange R_mod_P))
      have hτ_mod_P' : τ_mod_P = e2_S.conj τ1 := by
        have h :=
          congrArg (fun f => f (τ.baseChange R_mod_P))
            (LinearEquiv.conj_trans (e₁ := e1) (e₂ := e2_S))
        simpa [τ1, τ_mod_P, eVR_S] using h.symm
      have hupper_conj :
          upperLeftProj R_mod_P V_mod_P R_mod_P τ_mod_P =
            eV_S.conj (upperLeftProj R_mod_P (R_mod_P ⊗[R] V) (R_mod_P ⊗[R] R) τ1) := by
        simpa [hτ_mod_P', e2_S] using
          (upperLeftProj_conj_prodCongr (eV := eV_S) (eW := eR_S) (τ := τ1))
      have hupper_baseChange :
          upperLeftProj R_mod_P (R_mod_P ⊗[R] V) (R_mod_P ⊗[R] R) τ1 =
            (upperLeftProj R V R τ).baseChange R_mod_P := by
        simpa using
          (upperLeftProj_baseChange_prodRight (R := R) (V := V) (P := P) (τ := τ))
      have hupper_char :
          (upperLeftProj R_mod_P V_mod_P R_mod_P τ_mod_P).charpoly =
            ((upperLeftProj R V R τ).baseChange R_mod_P).charpoly := by
        calc
          (upperLeftProj R_mod_P V_mod_P R_mod_P τ_mod_P).charpoly
              =
            (eV_S.conj (upperLeftProj R_mod_P (R_mod_P ⊗[R] V) (R_mod_P ⊗[R] R) τ1)).charpoly := by
              simp only [hupper_conj, upperLeftProj_apply, LinearEquiv.charpoly_conj]
          _ = (upperLeftProj R_mod_P (R_mod_P ⊗[R] V) (R_mod_P ⊗[R] R) τ1).charpoly := by
              symm
              simp only [upperLeftProj_apply, LinearEquiv.charpoly_conj]
          _ = ((upperLeftProj R V R τ).baseChange R_mod_P).charpoly := by
              simp only [hupper_baseChange, upperLeftProj_apply, LinearMap.charpoly_baseChange]
      have hupper_char' :
          (LinearMap.fst R_mod_P V_mod_P R_mod_P ∘ₗ τ_mod_P ∘ₗ
              LinearMap.inl R_mod_P V_mod_P R_mod_P).charpoly =
            map (algebraMap R R_mod_P)
              (LinearMap.fst R V R ∘ₗ τ ∘ₗ LinearMap.inl R V R).charpoly := by
        simpa [LinearMap.charpoly_baseChange, upperLeftProj_apply] using hupper_char
      have hτ_char' :
          τ_mod_P.charpoly = τ.charpoly.map (algebraMap R R_mod_P) := by
        simpa [LinearMap.charpoly_baseChange] using hτ_char.symm
      -- map coprimality along algebraMap
      have hτ_map :
          IsCoprime
            (τ.charpoly.map (algebraMap R R_mod_P))
            ((LinearMap.fst R V R ∘ₗ τ ∘ₗ LinearMap.inl R V R).charpoly.map
              (algebraMap R R_mod_P)) := by
        simpa [upperLeftProj_apply] using
          (IsCoprime.map (H := hτ) (f := Polynomial.mapRingHom (algebraMap R R_mod_P)))
      have hτ_base' :
          IsCoprime τ_mod_P.charpoly
            (map (algebraMap R R_mod_P)
              (LinearMap.fst R V R ∘ₗ τ ∘ₗ LinearMap.inl R V R).charpoly) := by
        simpa [hτ_char'] using hτ_map
      -- combine equalities
      simpa [hupper_char'] using hτ_base'
    set π : R →ₐ[R] R ⧸ P := Ideal.Quotient.mkₐ R P
    let X_mod_P := (⊤ : Submodule R_mod_P (Dual R_mod_P (V_mod_P × R_mod_P)))
    have field_case := cyclic_e'_of_coprime_charpoly_field R_mod_P V_mod_P τ_mod_P hτ_mod_P
    have ibc_qVR : IsBaseChange R_mod_P qVR := by
      refine IsBaseChange.of_equiv (S := R_mod_P) (M := V × R) (N := V_mod_P × R_mod_P)
          (f := qVR) eVR_S ?_
      intro x
      cases x with
      | mk v r =>
          ext
          ·
            have h :
                (TensorProduct.quotTensorEquivQuotSMul V P) (1 ⊗ₜ[R] v) =
                  (Submodule.Quotient.mk (p := (P • ⊤ : Submodule R V)) v) := by
              simp
            simp +zetaDelta [Submodule.mkQ_apply, h]
          ·
            have h :
                (r • (1 : R_mod_P)) = (Ideal.Quotient.mk P r) := by
              dsimp [R_mod_P]
              simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
            simpa +zetaDelta [qVR, Submodule.mkQ_apply] using h
    let πX : (Dual R (V × R)) →ₗ[R] (Dual R_mod_P (V_mod_P × R_mod_P)) :=
      (IsBaseChange.toDual (ibc := ibc_qVR))
    let x_mod_P : X_mod_P := by
      use πX x
      exact Submodule.mem_top
    rcases field_case x_mod_P with ⟨ p_mod_P, hp_mod_P ⟩
    rcases Polynomial.map_surjective (algebraMap R R_mod_P) Ideal.Quotient.mk_surjective p_mod_P
      with ⟨ p, hp ⟩
    use p
    have eval_commutes_reduction : ∀ y : Dual R (V × R), πX ((EvalMap τ.dualMap y) p) = ((EvalMap τ_mod_P.dualMap (πX y)) p_mod_P) := by
      intro y
      -- relate τ_mod_P to endHom base change
      have hqVR_tmul : ∀ x, eVR_S (1 ⊗ₜ[R] x) = qVR x := by
        intro x
        cases x with
        | mk v r =>
            ext
            ·
              have h :
                  (TensorProduct.quotTensorEquivQuotSMul V P) (1 ⊗ₜ[R] v) =
                    (Submodule.Quotient.mk (p := (P • ⊤ : Submodule R V)) v) := by
                simp
              simp +zetaDelta [Submodule.mkQ_apply, h]
            ·
              have h :
                  (r • (1 : R_mod_P)) = (Ideal.Quotient.mk P r) := by
                dsimp [R_mod_P]
                simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
              simpa +zetaDelta [qVR, Submodule.mkQ_apply] using h
      have hqVR_symm : ∀ x, eVR_S.symm (qVR x) = (1 : R_mod_P) ⊗ₜ[R] x := by
        intro x
        apply (LinearEquiv.symm_apply_eq eVR_S).mpr
        exact (hqVR_tmul x).symm
      have hτ_mod_P_comp : ∀ x, τ_mod_P (qVR x) = qVR (τ x) := by
        intro x
        calc
          τ_mod_P (qVR x)
              = eVR_S (τ.baseChange R_mod_P (eVR_S.symm (qVR x))) := by
                  simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
                    Function.comp_apply, τ_mod_P]
          _ = eVR_S (τ.baseChange R_mod_P ((1 : R_mod_P) ⊗ₜ[R] x)) := by
                  simp only [hqVR_symm, LinearMap.baseChange_tmul]
          _ = eVR_S ((1 : R_mod_P) ⊗ₜ[R] (τ x)) := by
                  simp only [LinearMap.baseChange_tmul]
          _ = qVR (τ x) := by
                  simp only [hqVR_tmul]
      have hτ_mod_P_eq : τ_mod_P = ibc_qVR.endHom τ := by
        apply LinearMap.ext
        intro z
        rcases hqVR_surj z with ⟨x, rfl⟩
        have h1 := hτ_mod_P_comp x
        have h2 : (ibc_qVR.endHom τ) (qVR x) = qVR (τ x) := by
          simpa using (IsBaseChange.endHom_comp_apply (j := ibc_qVR) (f := τ) (m := x))
        simpa [h2] using h1
      -- ext on qVR images
      apply LinearMap.ext
      intro z
      rcases hqVR_surj z with ⟨x, rfl⟩
      have h_aeval :
          (aeval (R := R_mod_P) τ_mod_P p_mod_P) (qVR x) =
            qVR ((aeval (R := R) τ p) x) := by
        -- rewrite p_mod_P via hp and τ_mod_P via hτ_mod_P_eq
        have hp' : p_mod_P = p.map (algebraMap R R_mod_P) := hp.symm
        simpa [hτ_mod_P_eq, hp'] using
          (aeval_endHom_comp_apply (ibc := ibc_qVR) (τ := τ) (p := p) (m := x))
      -- finish by evaluating both sides at qVR x
      have hleft :
          (πX ((EvalMap τ.dualMap y) p)) (qVR x) =
            algebraMap R R_mod_P (y ((aeval (R := R) τ p) x)) := by
        have h :=
          (IsBaseChange.toDual_comp_apply (ibc := ibc_qVR) (f := (EvalMap τ.dualMap y p)) (v := x))
        have h' : (EvalMap τ.dualMap y p) x = y ((aeval (R := R) τ p) x) := by
          simpa using (eval_dual_apply (τ := τ) (y := y) (p := p) (v := x))
        calc
          (πX ((EvalMap τ.dualMap y) p)) (qVR x)
              = algebraMap R R_mod_P ((EvalMap τ.dualMap y p) x) := by
                  simpa [πX] using h
          _ = algebraMap R R_mod_P (y ((aeval (R := R) τ p) x)) := by
                  exact congrArg (fun t => algebraMap R R_mod_P t) h'
      have hright :
          ((EvalMap τ_mod_P.dualMap (πX y)) p_mod_P) (qVR x) =
            (πX y) ((aeval (R := R_mod_P) τ_mod_P p_mod_P) (qVR x)) := by
        simpa using
          (eval_dual_apply (τ := τ_mod_P) (y := πX y) (p := p_mod_P) (v := qVR x))
      calc
        (πX ((EvalMap τ.dualMap y) p)) (qVR x)
            = algebraMap R R_mod_P (y ((aeval (R := R) τ p) x)) := hleft
        _ = (πX y) (qVR ((aeval (R := R) τ p) x)) := by
            simp [πX, IsBaseChange.toDual_comp_apply]
        _ = (πX y) ((aeval (R := R_mod_P) τ_mod_P p_mod_P) (qVR x)) := by
            simp [h_aeval]
        _ = ((EvalMap τ_mod_P.dualMap (πX y)) p_mod_P) (qVR x) := by
            simpa using hright.symm
    have kernel_eval : ∀ y : Dual R (V × R), πX y = 0 → y ∈ P • Xmod := by
      intro y hy
      -- all evaluations land in P
      have hy' : ∀ x, algebraMap R R_mod_P (y x) = 0 := by
        intro x
        have hyx : πX y (qVR x) = 0 := by
          simpa using congrArg (fun f => f (qVR x)) hy
        simpa [πX, IsBaseChange.toDual_comp_apply] using hyx
      classical
      -- use a basis and dual basis to express y with coefficients in P
      let b := Module.Free.chooseBasis R (V × R)
      have hb : Fintype (Module.Free.ChooseBasisIndex R (V × R)) := by infer_instance
      have hcoeff : ∀ i, b.dualBasis.repr y i ∈ P := by
        intro i
        have : Ideal.Quotient.mk P (y (b i)) = 0 := by
          simpa [R_mod_P] using hy' (b i)
        simpa using (Ideal.Quotient.eq_zero_iff_mem).1 this
      have hy_eq :
          y = Finsupp.linearCombination R b.dualBasis (b.dualBasis.repr y) := by
        simpa using (b.dualBasis.linearCombination_repr y).symm
      have hy_mem :
          Finsupp.linearCombination R b.dualBasis (b.dualBasis.repr y) ∈ P • Xmod := by
        classical
        have hsum :
            Finsupp.linearCombination R b.dualBasis (b.dualBasis.repr y)
              = (b.dualBasis.repr y).sum (fun i a => a • b.dualBasis i) := by
            simp [Finsupp.linearCombination_apply]
        refine hsum ▸ ?_
        refine Submodule.sum_mem (P • Xmod) ?_
        intro i hi
        have hiP : (b.dualBasis.repr y) i ∈ P := hcoeff i
        have htop : (b.dualBasis i : Dual R (V × R)) ∈ Xmod := by
          simp only [Basis.coe_dualBasis, Submodule.mem_top, Xmod]
        exact Submodule.smul_mem_smul hiP htop
      exact hy_eq ▸ hy_mem
    set y := (EvalMap (LinearMap.dualMap τ) e') p - x
    show y ∈ P • Xmod
    have this : πX y = 0 := by
      -- use eval_commutes_reduction at y = e' and hp_mod_P
      have h1 := eval_commutes_reduction e'
      -- identify πX e' with the quotient snd
      have hπX_e' : πX e' = LinearMap.snd R_mod_P V_mod_P R_mod_P := by
        apply LinearMap.ext
        intro z
        rcases hqVR_surj z with ⟨x, rfl⟩
        cases x with
        | mk v r =>
            -- evaluate on qVR (v,r)
            have h :=
              (IsBaseChange.toDual_comp_apply (ibc := ibc_qVR) (f := e') (v := (v, r)))
            calc
              (πX e') (qVR (v, r)) = algebraMap R R_mod_P (e' (v, r)) := by
                simpa [πX] using h
              _ = algebraMap R R_mod_P r := by
                simp [e']
              _ = (LinearMap.snd R_mod_P V_mod_P R_mod_P) (qVR (v, r)) := by
                have hmk : algebraMap R R_mod_P r = Ideal.Quotient.mk P r := by
                  simp only [Ideal.Quotient.algebraMap_eq, R_mod_P]
                have hmk' :
                    Ideal.Quotient.mk P r =
                      (LinearMap.snd R_mod_P V_mod_P R_mod_P) (qVR (v, r)) := by
                  calc
                    Ideal.Quotient.mk P r =
                        (Submodule.mkQ (p := (P : Submodule R R)) r : R_mod_P) := by
                      rfl
                    _ = (LinearMap.snd R_mod_P V_mod_P R_mod_P) (qVR (v, r)) := by
                      simp [qVR]
                exact hmk.trans hmk'
      have h2 : πX (EvalMap τ.dualMap e' p) =
          EvalMap τ_mod_P.dualMap (LinearMap.snd R_mod_P V_mod_P R_mod_P) p_mod_P := by
        simpa [hπX_e'] using h1
      -- now πX y = 0
      calc
        πX y = πX (EvalMap τ.dualMap e' p) - πX x := by
          simp only [EvalMap_apply, map_sub, y]
        _ =
            (EvalMap τ_mod_P.dualMap (LinearMap.snd R_mod_P V_mod_P R_mod_P) p_mod_P) - πX x := by
          simpa [h2]
        _ = x_mod_P - πX x := by
          simp only [hp_mod_P]
        _ = x_mod_P - x_mod_P := by
          simp only [sub_self, x_mod_P]
        _ = 0 := by simp
    exact kernel_eval y this
  rcases hx with ⟨ p, hp ⟩
  set w := EvalMap τ.dualMap e' p with hw₀
  set d := w - x
  have hw : w ∈ W := by
    rw [LinearMap.mem_range]
    use p
  apply (Submodule.mem_sup (R := R) (p := W) (p' := P • Xmod)).mpr
  use w
  use hw
  use -d
  constructor
  · exact Submodule.neg_mem (P • Xmod) hp
  simp only [neg_sub, add_sub_cancel, d]


/-

We are given τ ∈ End(V × R).

1. We want to define τ_P ∈ End(V_P × R_P).  Here a subscripted P means "mod out" (rather than "localize").

  Well, we have a canoncial map End(V × R) → End((V × R)_P) that you've already defined, so I guess
  we just need to conjugate this last map by the isomorphism (V × R)_P ≅ V_P × R_P.

2. We want to know that its characteristic polynomials are obtained via reduction.

3. I guess we want to define it to be compatible with the reduction map πX : (V × R)' → (V_P × R_P)'.

4. We want evaluation to commute with reduction.

  This last assertion is critical, so let's spell out why it should be the case.

  Focus on what it would say if we were working with standard (rather than dual) actions.

  It would say that for each y ∈ V × R, with image y_P ∈ V_P × R_P, we have (f(τ) y)_P = f(τ_P) y_P
  for any polynomial f in R[X].  In the second case, I guess we work implicitly with the reduction
  of f modulo P.

  This should follow from expanding out the definition of τ_P.

5. We'll also need to compute the kernel of the reduction map.  Again, simple.

These are all general results about V₁ × V₂.  We can take endomorphisms of it, mod
everything out by an ideal, etc.  Maybe they're really about how tensor product behaves
with respect to direct sum?

I guess LinearAlgebra/TensorProduct/Prod.lean would be relevant if you could work with tensor products instead.

-/

example
  (R : Type) [CommRing R]
  (V : Type) [AddCommGroup V] [Module R V]
  (I : Ideal R)
  : V →ₗ[R] (V ⧸ (I • (⊤ : Submodule R V)))
  := Submodule.mkQ (I • ⊤)

-- The kernel of V → V/PV is PV.
example
  (R : Type) [CommRing R]
  (V : Type) [AddCommGroup V] [Module R V]
  (I : Ideal R)
  : LinearMap.ker (Submodule.mkQ (I • (⊤ : Submodule R V))) = I • ⊤
  := Submodule.ker_mkQ (I • ⊤)

example
  (R : Type) [CommRing R]
  (V : Type) [AddCommGroup V] [Module R V]
  (I : Ideal R)
  (v : V)
  :
  (V ⧸ (I • (⊤ : Submodule R V)))
  := Submodule.Quotient.mk v

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
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    : (V × R) ≃ₗ[R] (Dual R ((Dual R V) × R))
    := -- (V × R) → (V × R)'' → (V' × R')' → (V' × R)'
  evalEquiv R (V × R) 
  ≪≫ₗ (dualMap $ coprodEquiv R)
  ≪≫ₗ (dualMap $ (refl R $ Dual R V).prodCongr (LinearEquiv.symm $ ringLmapEquivSelf R R R))

open Module LinearMap in
theorem κ_e
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    : κ R V (0,1) = snd R (Dual R V) R
    := by
  unfold κ
  ext v
  simp only [LinearEquiv.trans_apply, evalEquiv_apply, coe_comp, coe_inl, Function.comp_apply,
    LinearEquiv.dualMap_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, map_zero,
    coprodEquiv_apply, Dual.eval_apply, coprod_apply, LinearMap.zero_apply, add_zero,
    snd_comp_inl]
  simp only [LinearEquiv.trans_apply, evalEquiv_apply, coe_comp, coe_inr, Function.comp_apply,
    LinearEquiv.dualMap_apply, LinearEquiv.prodCongr_apply, map_zero, ringLmapEquivSelf_symm_apply,
    coprodEquiv_apply, Dual.eval_apply, coprod_apply, coe_smulRight, smul_eq_mul,
    mul_one, zero_add, snd_comp_inr, id_coe, id_eq]
  rfl

/-

(V × R)' → V' × R

-/
open Module LinearMap LinearEquiv in
noncomputable def κ'
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    : (Dual R (V × R)) ≃ₗ[R] ((Dual R V) × R)
    -- (V × R)' → V' × R' → V' × R
    := (coprodEquiv R).symm ≪≫ₗ (refl R $ Dual R V).prodCongr (ringLmapEquivSelf R R R)

/-

V' × W' ≃ (V × W)'

-/
open Module LinearMap LinearEquiv in
theorem fst_κ'
    {R : Type} [CommRing R] [Nontrivial R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    : (fst R (Dual R V) R) ∘ₗ (κ' R V).toLinearMap
      = (fst R (Dual R V) (Dual R R))
        ∘ₗ ((coprodEquiv R).symm : Dual R (V × R) ≃ₗ[R] (Dual R V) × (Dual R R))
    := by
  unfold κ'
  rfl

open Module LinearMap in
theorem fst_κ'_apply
    {R : Type} [CommRing R] [Nontrivial R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (v : Dual R (V × R))
    : ((κ' R V) v).1 = (((coprodEquiv R).symm : Dual R (V × R) ≃ₗ[R] (Dual R V) × (Dual R R)) v).1
    := by
  unfold κ'
  rfl

open Module LinearMap LinearEquiv in
theorem κ'_symm
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    : (κ' R V).symm = ((refl R $ Dual R V).prodCongr (ringLmapEquivSelf R R R)).symm ≪≫ₗ (coprodEquiv R)
    := by rfl

open Module LinearMap LinearEquiv in
theorem κ'_symm_apply
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (v : (Dual R V) × R)
    : (κ' R V).symm v
      = (coprodEquiv R) (((refl R $ Dual R V).prodCongr (ringLmapEquivSelf R R R)).symm v)
    := by rfl

open Module LinearMap LinearEquiv in
theorem κ'_symm_inl_lem1
    {R : Type} [CommRing R] [Nontrivial R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (w : Dual R V)
    : ((refl R $ Dual R V).prodCongr (ringLmapEquivSelf R R R)).symm (w, 0) = (w,0)
    := (symm_apply_eq ((refl R (Dual R V)).prodCongr (ringLmapEquivSelf R R R))).mpr rfl

open Module LinearMap LinearEquiv in
theorem κ'_symm_inl_lem2
    {R : Type} [CommRing R] [Nontrivial R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (w : Dual R V)
    : (coprodEquiv R) ((w, 0) : (Dual R V) × (Dual R R)) = w ∘ₗ fst R V R
    := by
  simp only [coprodEquiv_apply]
  exact coprod_zero_right w

open Module LinearMap LinearEquiv in
theorem κ'_symm_inl
    {R : Type} [CommRing R] [Nontrivial R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (w : Dual R V)
    : (κ' R V).symm (w, 0) = w ∘ₗ fst R V R := by
  rw [κ'_symm_apply, κ'_symm_inl_lem1, κ'_symm_inl_lem2]


open Module LinearMap LinearEquiv in
theorem upper_left_conj_κ'
    {R : Type} [CommRing R] [Nontrivial R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (τ : End R (V × R))
    :
    let V' := Dual R V
    (upperLeftProj R V' R ((conj (κ' R V)) τ.dualMap)) = (upperLeftProj R V R τ).dualMap := by
  ext w v
  simp [upperLeftProj_apply, conj_apply, κ'_symm_inl, fst_κ'_apply, coprodEquiv_symm_apply,
    coe_comp, Function.comp_apply, LinearMap.dualMap_apply, coe_inl]

open Module LinearMap LinearEquiv in
theorem dual_dual
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (x : End R V)
    :
    x.dualMap.dualMap = (evalEquiv R V) ∘ₗ x ∘ₗ ((evalEquiv R V).symm : Dual R (Dual R V) ≃ₗ[R] V)
    := by
  calc
  _ = x.dualMap.dualMap ∘ₗ (refl R (Dual R (Dual R V))) := rfl
  _ = x.dualMap.dualMap ∘ₗ ((evalEquiv R V).symm ≪≫ₗ (evalEquiv R V)) := by rw [(symm_trans_self _)]
  _ = (x.dualMap.dualMap ∘ₗ (evalEquiv R V)
      : V →ₗ[R] Dual R (Dual R V)) ∘ₗ ((evalEquiv R V).symm : Dual R (Dual R V) ≃ₗ[R] V) := by rfl
  _ = ((evalEquiv R V) ∘ₗ x) ∘ₗ ((evalEquiv R V).symm : Dual R (Dual R V) ≃ₗ[R] V) := by rfl
  _ = (conj (evalEquiv R V)) x := by rfl

open Module in
theorem relate_κ_κ'
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
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
  _ = ((evalEquiv R (V × R)) ≪≫ₗ (κ' R V).symm.dualMap) ∘ₗ τ
      ∘ₗ ((κ' R V).dualMap ≪≫ₗ (evalEquiv R (V × R)).symm) := by rfl
  _ = (κ R V).toLinearMap ∘ₗ τ ∘ₗ (κ R V).symm.toLinearMap := by rfl

open Matrix in
theorem charpoly_transpose
    (R : Type) [CommRing R]
    (I : Type) [Fintype I] [DecidableEq I]
    (A : Matrix I I R)
    : A.charpoly = (Aᵀ).charpoly
    := by
  unfold Matrix.charpoly
  rw [Matrix.charmatrix_transpose, det_transpose]

open LinearMap Module in
theorem charpoly_dualmap_eq_charpoly
    {R : Type} [CommRing R] [Nontrivial R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (τ : End R V) 
    : τ.dualMap.charpoly = τ.charpoly
    := by
  let b := Module.Free.chooseBasis R V
  rw [← charpoly_toMatrix τ b]
  let b' := b.dualBasis
  rw [← charpoly_toMatrix τ.dualMap b']
  have hmat :
      LinearMap.toMatrix b' b' τ.dualMap = Matrix.transpose (LinearMap.toMatrix b b τ) := by
    simp [b', LinearMap.dualMap_def]
  rw [hmat]
  exact (charpoly_transpose (R := R) (I := Free.ChooseBasisIndex R V)
    (A := LinearMap.toMatrix b b τ)).symm

/-

The condition that a matrix and its upper-left block have coprime
characteristic polynomials is invariant under conjugation by κ.

-/
open Module LinearEquiv in
theorem upper_left_coprimality_dual
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
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
    _ = τ'.charpoly := (LinearEquiv.charpoly_conj (κ' R V) τ.dualMap).symm
  have h₂ : (upperLeftProj R V R τ).charpoly = (upperLeftProj R V' R τ').charpoly := by
    rw [upper_left_conj_κ']
    rw [← charpoly_dualmap_eq_charpoly]
  rw [h₁, h₂] at hτ
  exact hτ

open Module LinearEquiv in
theorem madness1
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (τ : End R (V × R)) 
    :
    (κ R V).toLinearMap ∘ₗ τ = ((κ R V).toLinearMap ∘ₗ τ ∘ₗ (κ R V).symm.toLinearMap) ∘ₗ (κ R V)
    := by
  calc
  (κ R V).toLinearMap ∘ₗ τ = (κ R V).toLinearMap ∘ₗ τ ∘ₗ (refl R (V × R)) := rfl
  _ = (κ R V).toLinearMap ∘ₗ τ ∘ₗ ((κ R V) ≪≫ₗ (κ R V).symm).toLinearMap := by
    rw [(self_trans_symm _)]
  _ = (κ R V).toLinearMap ∘ₗ τ ∘ₗ (κ R V).symm.toLinearMap ∘ₗ (κ R V) := by rfl
  _ = ((κ R V).toLinearMap ∘ₗ τ ∘ₗ (κ R V).symm.toLinearMap) ∘ₗ (κ R V) := by rfl

open Module in
theorem madness2
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (τ : End R (V × R)) 
    :
    let τ' := ((κ' R V).toLinearMap ∘ₗ τ.dualMap ∘ₗ (κ' R V).symm.toLinearMap)
    (κ R V) ∘ₗ τ = τ'.dualMap ∘ₗ (κ R V) := by
  intro τ'
  rw [madness1 R V τ]
  rw [← relate_κ_κ' R V τ]

open LinearMap LinearEquiv Module Polynomial in
theorem necessary_equivariance
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (τ : End R (V × R)) 
    :
    let τ' := ((κ' R V).toLinearMap ∘ₗ τ.dualMap ∘ₗ (κ' R V).symm.toLinearMap)
    ∀ p : R[X], (κ R V) ∘ₗ (aeval (R := R) τ p)
      = (aeval (R := R) τ'.dualMap p) ∘ₗ (κ R V).toLinearMap
    := by
  intro τ' p
  induction' p using Polynomial.induction_on' with p q hp hq n c
  · rw [aeval_add τ, aeval_add _, comp_add, add_comp _ _ _, hp, hq]
  induction' n with n hn
  · refine LinearMap.ext fun v => ?_
    simp [monomial_zero_left, aeval_C, coe_comp, Function.comp_apply, algebraMap_end_apply]
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
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
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
    simp only [EvalMap_apply, apply_symm_apply]
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
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
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
  simp only [symm_apply_apply, EvalMap_apply] at this 
  rw [this]
  exact ⟨p, rfl⟩
