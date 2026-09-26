/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import SmoothRegularity.SmoothAt

/-!
# Dedekind domains from smoothness and dimension

This file packages two source-independent consequences of regularity. A smooth
algebra over a field is a regular ring, and a regular domain of Krull dimension
at most one is a Dedekind domain.
-/

public section

universe u v

namespace Algebra

/-- A smooth algebra over a field is a regular ring. -/
theorem Smooth.isRegularRing
    {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
    [Algebra.Smooth K S] : IsRegularRing S := by
  let _ : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing K S
  rw [isRegularRing_iff]
  intro q hq
  apply Algebra.IsSmoothAt.isRegularLocalRing (K := K) (S := S) q
  infer_instance

end Algebra

namespace IsRegularRing

/-- A regular domain of Krull dimension at most one is a Dedekind domain. -/
theorem isDedekindDomain_of_dimensionLEOne
    {R : Type u} [CommRing R] [IsDomain R] [Ring.DimensionLEOne R]
    [IsRegularRing R] : IsDedekindDomain R := by
  rw [isDedekindDomain_iff_isDiscreteValuationRing_atPrime]
  refine ⟨inferInstance, ?_⟩
  intro P hP hPprime
  let _ : P.IsPrime := hPprime
  let Rₚ := Localization.AtPrime P
  let _ : Ring.DimensionLEOne Rₚ :=
    Ring.DimensionLEOne.localization Rₚ P.primeCompl_le_nonZeroDivisors
  have hmax : IsLocalRing.maximalIdeal Rₚ ≠ ⊥ := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P Rₚ]
    intro hmap
    exact hP ((Ideal.map_eq_bot_iff_of_injective
      (IsLocalization.injective Rₚ P.primeCompl_le_nonZeroDivisors)).mp hmap)
  have hnotfield : ¬ IsField Rₚ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr hmax
  apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
  have hreg := (IsRegularLocalRing.iff_finrank_cotangentSpace Rₚ).mp inferInstance
  have hdim : ringKrullDim Rₚ ≤ (1 : WithBot ℕ∞) :=
    Ring.krullDimLE_iff.mp inferInstance
  have hfinle : Module.finrank (IsLocalRing.ResidueField Rₚ)
      (IsLocalRing.CotangentSpace Rₚ) ≤ 1 := by
    exact_mod_cast hreg.trans_le hdim
  have hfinne : Module.finrank (IsLocalRing.ResidueField Rₚ)
      (IsLocalRing.CotangentSpace Rₚ) ≠ 0 := by
    intro hzero
    exact hnotfield (IsLocalRing.finrank_cotangentSpace_eq_zero_iff.mp hzero)
  exact (Nat.le_one_iff_eq_zero_or_eq_one.mp hfinle).resolve_left hfinne

end IsRegularRing

namespace Algebra

/-- A smooth domain of Krull dimension at most one over a field is a Dedekind
domain. -/
theorem Smooth.isDedekindDomain_of_dimensionLEOne
    {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
    [IsDomain S] [Ring.DimensionLEOne S] [Algebra.Smooth K S] :
    IsDedekindDomain S := by
  let _ : IsRegularRing S := Algebra.Smooth.isRegularRing (K := K) (S := S)
  exact IsRegularRing.isDedekindDomain_of_dimensionLEOne

end Algebra
