/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SmoothRegularity.AlgClosed
public import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# Cotangent-kernel dimensions at algebraically closed points

This file computes the dimension of the kernel of the base-changed cotangent
map for a finite polynomial presentation at a closed point over an
algebraically closed field.  Rank-nullity and the standard polynomial
cotangent basis express the ambient dimension as the number of variables;
the closed-point comparison identifies the target with the local cotangent
space.

No regularity hypothesis is used.  In particular, this numerical identity
does not establish a regular-to-smooth criterion.
-/

public section

open scoped TensorProduct

namespace Algebra.Presentation

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {S : Type v} [CommRing S] [Algebra K S] [Algebra.FiniteType K S]

/-- For a finite polynomial presentation at a closed point over an
algebraically closed field, the dimension of the base-changed cotangent-map
kernel plus the local cotangent-space dimension is the number of polynomial
variables. -/
theorem finrank_cotangentKernel_add_finrank_cotangentSpace {n r : ℕ}
    (P : Algebra.Presentation K S (Fin n) (Fin r))
    (m : Ideal S) [m.IsMaximal] :
    Module.finrank m.ResidueField
          (LinearMap.ker (P.toExtension.toKaehler.baseChange m.ResidueField)) +
        Module.finrank m.ResidueField
          (IsLocalRing.CotangentSpace (Localization.AtPrime m)) = n := by
  let _ : Module.Finite m.ResidueField
      (m.ResidueField ⊗[S] P.toExtension.CotangentSpace) :=
    Module.Finite.of_basis (P.cotangentSpaceBasis.baseChange m.ResidueField)
  have hsurj : Function.Surjective
      (P.toExtension.toKaehler.baseChange m.ResidueField) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective m.ResidueField
      P.toExtension.toKaehler_surjective
  rw [m.finrank_cotangentSpace_eq_finrank_tensorKaehlerOfIsAlgClosed (K := K)]
  calc
    _ = Module.finrank m.ResidueField
          (LinearMap.ker (P.toExtension.toKaehler.baseChange m.ResidueField)) +
        Module.finrank m.ResidueField
          (LinearMap.range (P.toExtension.toKaehler.baseChange m.ResidueField)) := by
      rw [show LinearMap.range (P.toExtension.toKaehler.baseChange m.ResidueField) = ⊤
        from LinearMap.range_eq_top.mpr hsurj, finrank_top]
    _ = Module.finrank m.ResidueField
          (m.ResidueField ⊗[S] P.toExtension.CotangentSpace) := by
      rw [add_comm, LinearMap.finrank_range_add_finrank_ker]
    _ = n := by
      rw [Module.finrank_eq_card_basis
        (P.cotangentSpaceBasis.baseChange m.ResidueField), Fintype.card_fin]

end Algebra.Presentation
