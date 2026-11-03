/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Tactic.Ring

/-!
# Cotangent derivations of split algebra maps

A section `s` of an algebra map `q : A →ₐ[K] B` defines a derivation into
`I/I²`, where `I = ker q`, by sending `a` to the class of `a - s (q a)`.
The coefficient action is the natural `A`-action on the ideal quotient; the
`K`-action is induced by the given algebra structure on `A`. No algebra
structure on `A` over `B` is needed.

The derivation vanishes on the section and restricts on `I` to the quotient
map, so it is surjective. This does not assert a factorization property for
derivations into arbitrary coefficient modules.

## References

This generalizes the split-residue construction in `SmoothRegularity.Conormal`.
It uses Mathlib's derivations (Nicolò Cavalleri and Andrew Yang) and ideal
cotangent modules (Andrew Yang), together with their quotient maps and
scalar restriction.
-/

@[expose] public section

namespace AlgHom

universe u v w

variable {K : Type u} {A : Type v} {B : Type w}
  [CommSemiring K] [CommRing A] [Semiring B] [algebraKA : Algebra K A] [Algebra K B]

/-- An element differs from its section representative by an element of the kernel. -/
lemma sub_section_mem_ker (q : A →ₐ[K] B) (s : B →ₐ[K] A)
    (hs : Function.LeftInverse q s) (a : A) : a - s (q a) ∈ RingHom.ker (q : A →+* B) := by
  change q (a - s (q a)) = 0
  apply hs.injective
  change (s.comp q) (a - s (q a)) = s 0
  rw [map_sub]
  simp only [AlgHom.comp_apply, map_zero]
  rw [hs (q a), sub_self]

private def sectionDifference (q : A →ₐ[K] B) (s : B →ₐ[K] A)
    (hs : Function.LeftInverse q s) : A →ₗ[K] RingHom.ker (q : A →+* B) where
  toFun a := ⟨a - s (q a), sub_section_mem_ker q s hs a⟩
  map_add' x y := by
    apply Subtype.ext
    change x + y - s (q (x + y)) = (x - s (q x)) + (y - s (q y))
    simp only [map_add]
    ring
  map_smul' k x := by
    apply Subtype.ext
    change k • x - s (q (k • x)) = k • (x - s (q x))
    simp only [map_smul, smul_sub]

/-- The derivation associated to a section of an algebra map, sending `a` to
`[a - s (q a)]` in `(ker q)/(ker q)²`. The coefficient module uses its natural
`A`-action and the scalar action of the original `K`-algebra structure. These
two module arguments are fixed separately even when `K` and `A` coincide. -/
noncomputable def cotangentDerivationOfSection (q : A →ₐ[K] B) (s : B →ₐ[K] A)
    (hs : Function.LeftInverse q s) :
    @Derivation K A (RingHom.ker (q : A →+* B)).Cotangent _ _ _ algebraKA
      (inferInstance : Module A (RingHom.ker (q : A →+* B)).Cotangent)
      (inferInstance : Module K (RingHom.ker (q : A →+* B)).Cotangent) where
  toLinearMap := ((RingHom.ker (q : A →+* B)).toCotangent.restrictScalars K).comp
    ((private_decl% sectionDifference : (q : A →ₐ[K] B) → (s : B →ₐ[K] A) →
      Function.LeftInverse q s → A →ₗ[K] RingHom.ker (q : A →+* B)) q s hs)
  map_one_eq_zero' := by
    change (RingHom.ker (q : A →+* B)).toCotangent (sectionDifference q s hs 1) = 0
    rw [show sectionDifference q s hs 1 = 0 by
      apply Subtype.ext
      change (1 : A) - s (q 1) = 0
      simp only [map_one, sub_self], map_zero]
  leibniz' x y := by
    change (RingHom.ker (q : A →+* B)).toCotangent (sectionDifference q s hs (x * y)) =
      (RingHom.ker (q : A →+* B)).toCotangent (x • sectionDifference q s hs y) +
        (RingHom.ker (q : A →+* B)).toCotangent (y • sectionDifference q s hs x)
    rw [← map_add, ← sub_eq_zero, ← map_sub, Ideal.toCotangent_eq_zero]
    have hprod : -((sectionDifference q s hs x : A) * sectionDifference q s hs y) ∈
        RingHom.ker (q : A →+* B) ^ 2 := by
      apply (RingHom.ker (q : A →+* B) ^ 2).neg_mem
      rw [pow_two]
      exact Ideal.mul_mem_mul (sectionDifference q s hs x).2 (sectionDifference q s hs y).2
    convert hprod using 1
    change x * y - s (q (x * y)) -
        (x * (y - s (q y)) + y * (x - s (q x))) =
      -((x - s (q x)) * (y - s (q y)))
    simp only [map_mul]
    ring

/-- Evaluation of the cotangent derivation as the class of the difference
between an element and its image under the section. -/
theorem cotangentDerivationOfSection_apply (q : A →ₐ[K] B) (s : B →ₐ[K] A)
    (hs : Function.LeftInverse q s) (a : A) :
    q.cotangentDerivationOfSection s hs a =
      (RingHom.ker (q : A →+* B)).toCotangent
        ⟨a - s (q a), sub_section_mem_ker q s hs a⟩ := by
  rfl

/-- The cotangent derivation vanishes on the image of the section. -/
@[simp] theorem cotangentDerivationOfSection_apply_section (q : A →ₐ[K] B)
    (s : B →ₐ[K] A) (hs : Function.LeftInverse q s) (b : B) :
    q.cotangentDerivationOfSection s hs (s b) = 0 := by
  rw [cotangentDerivationOfSection_apply]
  have hzero : (⟨s b - s (q (s b)), sub_section_mem_ker q s hs (s b)⟩ :
      RingHom.ker (q : A →+* B)) = 0 := by
    apply Subtype.ext
    change s b - s (q (s b)) = 0
    rw [hs b, sub_self]
  rw [hzero, map_zero]

/-- On the kernel, the cotangent derivation is the quotient map. -/
@[simp] theorem cotangentDerivationOfSection_apply_coe (q : A →ₐ[K] B)
    (s : B →ₐ[K] A) (hs : Function.LeftInverse q s) (x : RingHom.ker (q : A →+* B)) :
    q.cotangentDerivationOfSection s hs x = (RingHom.ker (q : A →+* B)).toCotangent x := by
  rw [cotangentDerivationOfSection_apply]
  apply congrArg (RingHom.ker (q : A →+* B)).toCotangent
  apply Subtype.ext
  change (x : A) - s (q x) = x
  have hx : q (x : A) = 0 := x.2
  rw [hx, map_zero, sub_zero]

/-- Every cotangent class is the derivative of an element of the kernel. -/
theorem cotangentDerivationOfSection_surjective (q : A →ₐ[K] B) (s : B →ₐ[K] A)
    (hs : Function.LeftInverse q s) :
    Function.Surjective (q.cotangentDerivationOfSection s hs) := by
  intro x
  obtain ⟨a, rfl⟩ := (RingHom.ker (q : A →+* B)).toCotangent_surjective x
  exact ⟨a, cotangentDerivationOfSection_apply_coe q s hs a⟩

end AlgHom
