import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Nakayama

/-!
# Small ring/module API candidates

Finiteness and Nakayama-style facts used by the project, stated without its
matrix or cyclic-vector vocabulary.
-/

theorem exists_maximal_smul_le_of_ne_bot_of_fg {R : Type} [CommRing R]
    {M : Type} [AddCommGroup M] [Module R M]
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

instance instModuleFiniteQuotientIdealSMulTop
    (R : Type) [CommRing R] [Nontrivial R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Finite R V]
    (I : Ideal R)
    : Module.Finite (R ⧸ I) (V ⧸ (I • (⊤ : Submodule R V) : Submodule R V)) := by
  haveI : Module.Finite R (V ⧸ (I • (⊤ : Submodule R V) : Submodule R V)) := by
    infer_instance
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I)
    (V ⧸ (I • (⊤ : Submodule R V) : Submodule R V))
