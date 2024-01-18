import Mathlib

/-!

# Main results:

* `coprime_of_disjoint_roots`

-/

theorem ideal_map_maximal_of_ideal_maximal
    {A : Type} [CommRing A]
    {B : Type} [CommRing B]
    (f : A ≃+* B)
    (I : Ideal A)
    (h : I.IsMaximal) 
    : (Ideal.map f I).IsMaximal
    := by
  refine Ideal.map.isMaximal f ?hf h
  exact RingEquiv.bijective f

theorem ideal_map_maximal_iff_ideal_maximal
    {A : Type} [CommRing A]
    {B : Type} [CommRing B]
    (f : A ≃+* B)
    (I : Ideal A)
    : I.IsMaximal ↔ (Ideal.map (f : A →+* B) I).IsMaximal
    := by
  constructor
  · exact ideal_map_maximal_of_ideal_maximal f I
  convert ideal_map_maximal_of_ideal_maximal f.symm (Ideal.map f I)
  show I = Ideal.map (f.symm : B →+* A) (Ideal.map (f : A →+* B) I)
  rw [Ideal.map_of_equiv]

open Polynomial in
theorem polynomial_eval_eq_mvpolynomial_punit_eval
    {R : Type} [Field R] [IsAlgClosed R] [DecidableEq R]
    (p : R[X])
    {c : Unit → R}
    :
    let f : R[X] ≃ₐ[R] (MvPolynomial Unit R) := AlgEquiv.symm (MvPolynomial.pUnitAlgEquiv R)
    (MvPolynomial.eval c) (f p) = (Polynomial.aeval (R := R) (c ())) p
    := by
  intro f
  induction' p using Polynomial.induction_on' with p q hp hq n a
  · rw [aeval_add, ← hp, ← hq]
    simp
  simp

open Polynomial in
theorem maximal_ideal_vanishes_at_point
    (R : Type) [Field R] [IsAlgClosed R] [DecidableEq R]
    (I : Ideal R[X])
    (hI : I.IsMaximal)
    : ∃ c : R, ∀ p ∈ I, Polynomial.aeval (R := R) c p = 0
    := by
  let f : R[X] ≃ₐ[R] (MvPolynomial Unit R) := AlgEquiv.symm (MvPolynomial.pUnitAlgEquiv R)
  let J := Ideal.map (f : R[X] →+* MvPolynomial Unit R) I
  have hJ : J.IsMaximal := (ideal_map_maximal_iff_ideal_maximal (f : R[X] ≃+* MvPolynomial Unit R) I).mp hI
  have := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton J).mp hJ
  rcases this with ⟨c, hc⟩
  use c ()
  have h : ∀ q ∈ J, MvPolynomial.eval (R := R) c q = 0 := by
    intro q hq
    rw [hc] at hq
    exact hq c rfl
  intro p hp
  have := h (f p) (Ideal.mem_map_of_mem f hp)
  rw [polynomial_eval_eq_mvpolynomial_punit_eval] at this
  exact this

open Polynomial in
theorem in_maximal_ideal_of_not_coprime
    (R : Type) [CommRing R]
    {p q : R[X]}
    (h : ¬ IsCoprime p q)
    : ∃ (m : Ideal R[X]), m.IsMaximal ∧ p ∈ m ∧ q ∈ m
    := by
  replace h := (Iff.not (Ideal.isCoprime_span_singleton_iff p q)).mpr h
  replace h := (Iff.not (Ideal.isCoprime_iff_sup_eq)).mp h
  set I := Ideal.span {p} ⊔ Ideal.span {q}
  push_neg at h
  have := Ideal.exists_le_maximal I h
  rcases this with ⟨m, hm, hI⟩
  use m
  constructor
  · exact hm
  constructor
  · exact hI (Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr (Eq.dvd rfl)))
  exact hI (Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr (Eq.dvd rfl)))

/-

If a pair of nonzero polynomials over an algebraically closed field
have no common roots, then they are coprime.

-/
open Polynomial in
theorem coprime_of_disjoint_roots
    (R : Type) [Field R] [IsAlgClosed R] [DecidableEq R]
    {p q : R[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : p.roots ⊓ q.roots = 0)
    : IsCoprime p q := by
  by_contra h'
  rcases in_maximal_ideal_of_not_coprime R h' with ⟨m, hm, hp', hq'⟩
  rcases maximal_ideal_vanishes_at_point R m hm with ⟨c, hc⟩
  have h'' : c ∈ p.roots ⊓ q.roots := by
    simp
    constructor
    · exact ⟨hp, hc p hp'⟩
    exact ⟨hq, hc q hq'⟩
  have := Multiset.eq_zero_iff_forall_not_mem.mp h
  exact this c h''
