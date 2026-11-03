/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import SmoothRegularity.Algebra.FormallySmooth

/-!
# Smooth principal neighborhoods of nilpotent thickenings

A surjective algebra homomorphism whose kernel is annihilated by an element
induces a bijection on the corresponding principal localizations. This transports
smoothness to the localized source. Together with an annihilator supplied by
formal smoothness, it gives smooth principal neighborhoods of smooth quotients
by finitely generated nilpotent ideals contained in the square of an ideal.
-/

public section

universe u v w u₁ v₁

variable {K : Type u} {A : Type v} {B : Type w}
variable [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

namespace IsLocalization.Away

variable {Aₚ : Type u₁} [CommRing Aₚ] [Algebra A Aₚ] [Algebra K Aₚ]
variable [IsScalarTower K A Aₚ]
variable {Bₚ : Type v₁} [CommRing Bₚ] [Algebra B Bₚ] [Algebra K Bₚ]
variable [IsScalarTower K B Bₚ]

/-- A surjective algebra homomorphism whose kernel is annihilated by `r` induces
a bijection on localizations away from `r` and its image. The localizations may
be zero rings. -/
theorem mapₐ_bijective_of_surjective_of_mul_ker_eq_zero
    (f : A →ₐ[K] B) (hf : Function.Surjective f) (r : A)
    [IsLocalization.Away r Aₚ] [IsLocalization.Away (f r) Bₚ]
    (hr : ∀ a ∈ RingHom.ker f.toRingHom, r * a = 0) :
    Function.Bijective (mapₐ Aₚ Bₚ f r) := by
  constructor
  · change Function.Injective (map Aₚ Bₚ f.toRingHom r)
    apply (map_injective_iff (S := Aₚ) Bₚ f.toRingHom r).2
    intro a ha
    refine ⟨1, ?_⟩
    simpa only [pow_one] using hr a (RingHom.mem_ker.mpr ha)
  · exact mapₐ_surjective_of_surjective (Aₚ := Aₚ) (Bₚ := Bₚ) (f := f) r hf

end IsLocalization.Away

namespace Algebra.Smooth

/-- If a surjection onto a smooth algebra has kernel annihilated by `r`, then
its source localized away from `r` is smooth. -/
theorem localization_away_of_surjective_of_mul_ker_eq_zero
    [Smooth K B] (f : A →ₐ[K] B) (hf : Function.Surjective f) (r : A)
    (hr : ∀ a ∈ RingHom.ker f.toRingHom, r * a = 0) :
    Smooth K (Localization.Away r) := by
  let : Smooth B (Localization.Away (f r)) := of_isLocalization_Away (f r)
  let : Smooth K (Localization.Away (f r)) :=
    comp K B (Localization.Away (f r))
  exact of_equiv
    (AlgEquiv.ofBijective (Localization.awayMapₐ f r)
      (IsLocalization.Away.mapₐ_bijective_of_surjective_of_mul_ker_eq_zero
        (Aₚ := Localization.Away r) (Bₚ := Localization.Away (f r)) f hf r hr)).symm

/-- A smooth quotient by a finitely generated nilpotent ideal `N` contained in
`I²` has a smooth principal neighborhood in the original algebra, defined by an
element congruent to `1` modulo `I`. -/
theorem exists_sub_one_mem_and_smooth_away_of_quotient
    (N I : Ideal A) (hnil : IsNilpotent N) (hfg : N.FG)
    [Smooth K (A ⧸ N)] (h : N ≤ I ^ 2) :
    ∃ r : A, r - 1 ∈ I ∧ Smooth K (Localization.Away r) := by
  obtain ⟨r, hr, hzero⟩ :=
    FormallySmooth.exists_sub_one_mem_and_mul_eq_zero_of_quotient
      (K := K) N I hnil hfg h
  refine ⟨r, hr, ?_⟩
  apply localization_away_of_surjective_of_mul_ker_eq_zero
    (Ideal.Quotient.mkₐ K N) (Ideal.Quotient.mkₐ_surjective K N) r
  change ∀ a ∈ RingHom.ker (Ideal.Quotient.mk N), r * a = 0
  simpa only [Ideal.mk_ker] using hzero

end Algebra.Smooth
