/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SmoothRegularity

/-!
# Public API examples

Representative algebra and scheme clients using only the root library import.
-/

open scoped TensorProduct

universe u v

private theorem regular_of_smooth
    {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
    [Algebra.Smooth K S] : IsRegularRing S :=
  Algebra.Smooth.isRegularRing (K := K) (S := S)

private theorem dedekind_of_smooth
    {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
    [IsDomain S] [Ring.DimensionLEOne S] [Algebra.Smooth K S] :
    IsDedekindDomain S :=
  Algebra.Smooth.isDedekindDomain_of_dimensionLEOne (K := K) (S := S)

private noncomputable def closedPointCotangentEquiv
    {K : Type u} {S : Type v} [Field K] [IsAlgClosed K]
    [CommRing S] [Algebra K S] [Algebra.FiniteType K S]
    (m : Ideal S) [m.IsMaximal] :
    IsLocalRing.CotangentSpace (Localization.AtPrime m) ≃ₗ[m.ResidueField]
      (m.ResidueField ⊗[S] Ω[S⁄K]) :=
  m.cotangentSpaceEquivTensorKaehlerOfIsAlgClosed (K := K)

private theorem splitResidueCotangent_apply
    {K : Type u} {R : Type v} [Field K] [CommRing R] [IsLocalRing R]
    [Algebra K R] [Algebra.FormallyUnramified K (IsLocalRing.ResidueField R)]
    (s : IsLocalRing.ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (IsLocalRing.ResidueField R)) s)
    (x : IsLocalRing.maximalIdeal R) :
    IsLocalRing.cotangentSpaceEquivTensorKaehlerOfSection s hs
        ((IsLocalRing.maximalIdeal R).toCotangent x) =
      1 ⊗ₜ[R] KaehlerDifferential.D K R x.1 := by
  exact IsLocalRing.cotangentSpaceEquivTensorKaehlerOfSection_apply_toCotangent s hs x

private theorem residueEquivCotangent_apply
    {K : Type u} {R : Type v} [Field K] [CommRing R] [IsLocalRing R]
    [Algebra K R] (e : IsLocalRing.ResidueField R ≃ₐ[K] K)
    (x : IsLocalRing.maximalIdeal R) :
    IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv e
        ((IsLocalRing.maximalIdeal R).toCotangent x) =
      1 ⊗ₜ[R] KaehlerDifferential.D K R x.1 := by
  rw [IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv_apply_toCotangent e x]

open AlgebraicGeometry

private theorem regular_stalk_of_smooth_locus
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {x : X}
    (hx : x ∈ f.smoothLocus) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  Scheme.Hom.isRegularLocalRing_of_mem_smoothLocus f hx
