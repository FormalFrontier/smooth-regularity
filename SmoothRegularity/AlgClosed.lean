/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import SmoothRegularity.Conormal

/-!
# Cotangent spaces over algebraically closed fields

This file identifies the residue field of a closed point of a finite-type
algebra over an algebraically closed field with the base field.  It then
compares the local cotangent space with the fibre of the module of Kähler
differentials.

The finrank comparison is the algebraically closed case of the rank formula
in Stacks Project tag 00TR.  It is a prerequisite for, but does not establish,
the smoothness criterion in tag 00TT.
-/

public section

open scoped TensorProduct

namespace Ideal

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {S : Type v} [CommRing S] [Algebra K S] [Algebra.FiniteType K S]

/-- The residue field of a maximal ideal of a finite-type algebra over an
algebraically closed field is isomorphic to the base field. -/
noncomputable def residueFieldAlgEquivOfIsAlgClosed
    (m : Ideal S) [m.IsMaximal] : m.ResidueField ≃ₐ[K] K := by
  letI : Algebra.FiniteType K m.ResidueField :=
    Algebra.FiniteType.trans (S := S) inferInstance inferInstance
  letI : Module.Finite K m.ResidueField :=
    finite_of_finite_type_of_isJacobsonRing K m.ResidueField
  exact (AlgEquiv.ofBijective (Algebra.ofId K m.ResidueField)
    IsAlgClosed.algebraMap_bijective_of_isIntegral).symm

/-- At a closed point of a finite-type algebra over an algebraically closed
field, the local cotangent space is the fibre of the module of Kähler
differentials of the original algebra. -/
noncomputable def cotangentSpaceEquivTensorKaehlerOfIsAlgClosed
    (m : Ideal S) [m.IsMaximal] :
    IsLocalRing.CotangentSpace (Localization.AtPrime m) ≃ₗ[m.ResidueField]
      (m.ResidueField ⊗[S] Ω[S⁄K]) := by
  let Rm := Localization.AtPrime m
  exact
    (IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv
      (m.residueFieldAlgEquivOfIsAlgClosed (K := K))).trans <|
      ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K S Rm).symm.baseChange
        Rm m.ResidueField _ _).trans <|
        TensorProduct.AlgebraTensorModule.cancelBaseChange
          S Rm m.ResidueField m.ResidueField Ω[S⁄K]

/-- The algebraically closed case of the differential-rank formula at a
closed point (Stacks Project tag 00TR). -/
theorem finrank_cotangentSpace_eq_finrank_tensorKaehlerOfIsAlgClosed
    (m : Ideal S) [m.IsMaximal] :
    Module.finrank m.ResidueField
        (IsLocalRing.CotangentSpace (Localization.AtPrime m)) =
      Module.finrank m.ResidueField (m.ResidueField ⊗[S] Ω[S⁄K]) :=
  (m.cotangentSpaceEquivTensorKaehlerOfIsAlgClosed (K := K)).finrank_eq

end Ideal
