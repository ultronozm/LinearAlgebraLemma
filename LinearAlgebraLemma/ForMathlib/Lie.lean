import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Small Lie API candidates

Compatibility of the commutator bracket with ring homomorphisms.
-/

/- Mathlib no longer registers the commutator-bracket Lie ring structure on
associative rings as a global instance; restore it locally for this file. -/
attribute [local instance 100] LieRing.ofAssociativeRing

theorem lie_map_of_ring_hom'
    (R : Type) [CommRing R]
    {A : Type} [Ring A] [Algebra R A]
    {B : Type} [Ring B] [Algebra R B]
    (f : A →+* B)
    (x y : A)
    : ⁅f x, f y⁆ = f ⁅x, y⁆ := by
  rw [Ring.lie_def, Ring.lie_def] at *
  rw [←f.map_mul, ←f.map_mul, ←f.map_sub]

theorem lie_map_of_ring_hom
    (R : Type) [CommRing R]
    {A : Type} [Ring A] [Algebra R A]
    {B : Type} [Ring B] [Algebra R B]
    (f : A →+* B)
    (x y : A)
    (h : ⁅x, y⁆ = 0)
    : ⁅f x, f y⁆ = 0 := by
  rw [lie_map_of_ring_hom' R f x y, h, map_zero]

