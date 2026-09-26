/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import SmoothRegularity.Dedekind

/-!
# Dedekind global sections of smooth affine schemes

This file packages the passage from a smooth integral affine scheme of
topological dimension at most one over a field to a Dedekind domain of global
sections.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The global sections of a smooth integral affine scheme of topological
dimension at most one over a field form a Dedekind domain. -/
theorem IsAffine.isDedekindDomain_globalSections_of_smooth
    {K : Type u} [Field K] (X : Scheme.{u}) [IsAffine X] [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [Smooth f]
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    IsDedekindDomain Γ(X, ⊤) := by
  let _ : Ring.KrullDimLE 1 Γ(X, ⊤) := by
    rw [Ring.krullDimLE_iff, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    change topologicalKrullDim (Spec Γ(X, ⊤)) ≤ (1 : WithBot ℕ∞)
    rw [← IsHomeomorph.topologicalKrullDim_eq _ X.isoSpec.hom.homeomorph.isHomeomorph]
    exact hdim
  let _ : Ring.DimensionLEOne Γ(X, ⊤) :=
    ⟨fun hP hPprime ↦ hPprime.isMaximal_of_ne_bot hP⟩
  let φ : K →+* Γ(X, ⊤) := f.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let _ : Algebra K Γ(X, ⊤) := φ.toAlgebra
  let htop : f.appTop.hom.Smooth :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp inferInstance
  have hφ : φ.Smooth := by
    exact (RingHom.Smooth.respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (.of K)).inv f.appTop).mpr htop
  have : Algebra.Smooth K Γ(X, ⊤) := by
    rw [← RingHom.smooth_algebraMap]
    change φ.Smooth
    exact hφ
  exact Algebra.Smooth.isDedekindDomain_of_dimensionLEOne (K := K)

end AlgebraicGeometry
