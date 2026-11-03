/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Order.Hom.Set
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Cotangent spaces under surjective homomorphisms

A surjective ring homomorphism whose kernel lies in `I²` induces a bijection from
`I/I²` to the cotangent module of the image ideal. For local rings, this preserves
the dimension of the cotangent space over the canonical residue fields.

Consequently, a Noetherian local ring is regular if its quotient by the nilradical
is regular and the nilradical lies in the square of the maximal ideal.
-/

public section

universe u v

namespace Ideal

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- A surjective algebra map induces a bijection on cotangent modules when the
preimage of the target ideal is the source ideal plus the kernel, and that kernel
lies in the square of the source ideal. -/
theorem mapCotangent_bijective_of_comap_eq
    (surj : Function.Surjective (algebraMap A B)) {I : Ideal A} {J : Ideal B}
    {hIJ : I ≤ J.comap (algebraMap A B)}
    (hmap : J.comap (algebraMap A B) = RingHom.ker (algebraMap A B) ⊔ I)
    (hker : RingHom.ker (algebraMap A B) ≤ I ^ 2) :
    Function.Bijective (Ideal.mapCotangent I J (Algebra.ofId A B) hIJ) := by
  refine ⟨?_, Ideal.mapCotangent_surjective_of_comap_eq surj hmap⟩
  apply LinearMap.ker_eq_bot.mp
  rw [Ideal.mapCotangent_ker_of_surjective surj hmap]
  apply eq_bot_iff.mpr
  rintro x ⟨y, hy, rfl⟩
  change I.toCotangent y = 0
  exact (I.toCotangent_eq_zero y).mpr (hker (Ideal.mem_inf.mp hy).1)

/-- A surjective algebra map whose kernel is contained in `I²` induces a bijection
on the cotangent modules of `I` and its image ideal. -/
theorem mapCotangent_bijective_of_surjective
    (surj : Function.Surjective (algebraMap A B)) (I : Ideal A)
    (hker : RingHom.ker (algebraMap A B) ≤ I ^ 2) :
    Function.Bijective (Ideal.mapCotangent I (I.map (algebraMap A B))
      (Algebra.ofId A B) Ideal.le_comap_map) := by
  apply mapCotangent_bijective_of_comap_eq (hIJ := Ideal.le_comap_map) surj ?_ hker
  rw [Ideal.comap_map_of_surjective' _ surj, sup_comm]

end Ideal

namespace IsLocalRing

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [IsLocalRing A] [IsLocalRing B]

/-- A surjective map of local rings whose kernel lies in the square of the source
maximal ideal preserves the cotangent-space dimension over the residue fields. -/
theorem finrank_cotangentSpace_eq_of_surjective
    (surj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) ≤ maximalIdeal A ^ 2) :
    Module.finrank (ResidueField A) (CotangentSpace A) =
      Module.finrank (ResidueField B) (CotangentSpace B) := by
  let : IsLocalHom (algebraMap A B) := IsLocalHom.of_surjective _ surj
  have hcomap : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A :=
    maximalIdeal_comap _
  let g : CotangentSpace A →ₗ[A] CotangentSpace B :=
    Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
      (le_of_eq hcomap.symm)
  have hbij : Function.Bijective g :=
    Ideal.mapCotangent_bijective_of_comap_eq (hIJ := le_of_eq hcomap.symm) surj
      (hcomap.trans (sup_eq_right.mpr (hker.trans (Ideal.pow_le_self two_ne_zero))).symm)
      hker
  let : Module (ResidueField A) (CotangentSpace B) :=
    Module.compHom (CotangentSpace B)
      (algebraMap (ResidueField A) (ResidueField B))
  let : IsScalarTower (ResidueField A) (ResidueField B) (CotangentSpace B) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : IsScalarTower A (ResidueField A) (CotangentSpace B) := by
    apply IsScalarTower.of_algebraMap_smul
    intro a x
    calc
      (algebraMap A (ResidueField A) a) • x =
          (algebraMap (ResidueField A) (ResidueField B) (residue A a)) • x := rfl
      _ = (residue B (algebraMap A B a)) • x :=
        congrArg (fun b : ResidueField B ↦ b • x) (ResidueField.algebraMap_residue a)
      _ = (algebraMap B (ResidueField B) (algebraMap A B a)) • x := rfl
      _ = (algebraMap A B a) • x :=
        IsScalarTower.algebraMap_smul (A := ResidueField B) (algebraMap A B a) x
      _ = a • x := IsScalarTower.algebraMap_smul (A := B) a x
  let e : CotangentSpace A ≃ₗ[ResidueField A] CotangentSpace B :=
    (LinearEquiv.ofBijective g hbij).extendScalarsOfSurjective
      (residue_surjective (R := A))
  have hres : Function.Bijective (algebraMap (ResidueField A) (ResidueField B)) := by
    refine ⟨RingHom.injective _, ?_⟩
    intro x
    obtain ⟨b, rfl⟩ := residue_surjective x
    obtain ⟨a, rfl⟩ := surj b
    exact ⟨residue A a, ResidueField.algebraMap_residue a⟩
  calc
    Module.finrank (ResidueField A) (CotangentSpace A) =
        Module.finrank (ResidueField A) (CotangentSpace B) := e.finrank_eq
    _ = Module.finrank (ResidueField B) (CotangentSpace B) := by
      simpa only [Module.finrank_of_bijective_algebraMap hres, one_mul] using
        (Module.finrank_mul_finrank (ResidueField A) (ResidueField B)
          (CotangentSpace B)).symm

end IsLocalRing

/-- Passing to the quotient by the nilradical does not change Krull dimension. -/
theorem ringKrullDim_quotient_nilradical (R : Type u) [CommRing R] :
    ringKrullDim (R ⧸ nilradical R) = ringKrullDim R := by
  rw [ringKrullDim_quotient]
  change Order.krullDim (PrimeSpectrum.zeroLocus (nilradical R : Set R)) =
    Order.krullDim (PrimeSpectrum R)
  exact Order.krullDim_eq_of_orderIso
    ((Set.orderIsoOfEq _ _ (PrimeSpectrum.zeroLocus_nilradical (R := R))).trans
      OrderIso.Set.univ)

namespace IsRegularLocalRing

open IsLocalRing

/-- Regularity lifts from the nilradical quotient of a Noetherian local ring when
the nilradical is contained in the square of the maximal ideal. -/
theorem of_quotient_nilradical (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsRegularLocalRing (R ⧸ nilradical R)]
    (h : nilradical R ≤ maximalIdeal R ^ 2) : IsRegularLocalRing R := by
  have hsurj : Function.Surjective (algebraMap R (R ⧸ nilradical R)) :=
    Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (algebraMap R (R ⧸ nilradical R)) ≤ maximalIdeal R ^ 2 := by
    simpa only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] using h
  apply (iff_finrank_cotangentSpace R).mpr
  rw [finrank_cotangentSpace_eq_of_surjective hsurj hker]
  exact ((iff_finrank_cotangentSpace (R ⧸ nilradical R)).mp inferInstance).trans
    (ringKrullDim_quotient_nilradical R)

end IsRegularLocalRing
