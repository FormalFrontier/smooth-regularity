/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Ring

/-!
# Kernels of split ring homomorphisms

If a ring homomorphism admits a ring-homomorphism section and its kernel is
contained in `I²`, then the kernel equals its product with `I`.
-/

public section

namespace RingHom

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- If a ring homomorphism has a section and its kernel is contained in `I²`,
then its kernel is equal to `I` times the kernel. -/
theorem ker_eq_mul_of_rightInverse (f : A →+* B) (s : B →+* A)
    (hs : Function.RightInverse s f) (I : Ideal A) (h : RingHom.ker f ≤ I ^ 2) :
    RingHom.ker f = I * RingHom.ker f := by
  let p : A →+* A := s.comp f
  have hsub (a : A) : a - p a ∈ RingHom.ker f := by
    change f (a - s (f a)) = 0
    rw [map_sub, hs (f a), sub_self]
  have hI : RingHom.ker f ≤ I := h.trans (Ideal.pow_le_self two_ne_zero)
  have hpI (a : A) (ha : a ∈ I) : p a ∈ I := by
    convert I.sub_mem ha (hI (hsub a)) using 1
    ring
  have hdiff (a : A) (ha : a ∈ I ^ 2) : a - p a ∈ I * RingHom.ker f := by
    rw [pow_two] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      have hsum := (I * RingHom.ker f).add_mem
        (Ideal.mul_mem_mul hy (hsub x)) (Ideal.mul_mem_mul (hpI x hx) (hsub y))
      convert hsum using 1
      simp only [map_mul]
      ring
    · intro x y hx hy
      convert (I * RingHom.ker f).add_mem hx hy using 1
      simp only [map_add]
      ring
  refine le_antisymm ?_ Ideal.mul_le_right
  intro a ha
  have hpa : p a = 0 := by
    change s (f a) = 0
    rw [RingHom.mem_ker.mp ha, map_zero]
  simpa only [hpa, sub_zero] using hdiff a (h ha)

end RingHom
