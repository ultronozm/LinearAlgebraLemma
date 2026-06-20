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
    rw [← Dual.eval_comp_comp_evalEquiv_eq]
    simp only [evalEquiv_toLinearMap]
  _ = ((evalEquiv R (V × R)) ≪≫ₗ (κ' R V).symm.dualMap) ∘ₗ τ
      ∘ₗ ((κ' R V).dualMap ≪≫ₗ (evalEquiv R (V × R)).symm) := by rfl
  _ = (κ R V).toLinearMap ∘ₗ τ ∘ₗ (κ R V).symm.toLinearMap := by rfl

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
