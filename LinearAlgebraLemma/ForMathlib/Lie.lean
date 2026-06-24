import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Small Lie API candidates

Compatibility of the commutator bracket with ring homomorphisms.
-/

/- Mathlib no longer registers the commutator-bracket Lie ring structure on
associative rings as a global instance; restore it locally for this file. -/
attribute [local instance 100] LieRing.ofAssociativeRing

namespace RingHom

theorem map_lie
    {A : Type} [Ring A]
    {B : Type} [Ring B]
    (f : A →+* B)
    (x y : A)
    : f ⁅x, y⁆ = ⁅f x, f y⁆ := by
  rw [Ring.lie_def, Ring.lie_def] at *
  rw [f.map_sub, f.map_mul, f.map_mul]

theorem map_lie_eq_zero
    {A : Type} [Ring A]
    {B : Type} [Ring B]
    (f : A →+* B)
    (x y : A)
    (h : ⁅x, y⁆ = 0)
    : ⁅f x, f y⁆ = 0 := by
  rw [← map_lie f x y, h, map_zero]

end RingHom
