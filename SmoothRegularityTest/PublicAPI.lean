/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SmoothRegularity
public import Mathlib.Algebra.DualNumber
import SmoothRegularityTest.Artinian

/-!
# Public API examples

Representative algebra and scheme clients using only the root library import.
-/

open scoped TensorProduct

universe u v

namespace MvPolynomial

/-- The polynomial ring in two variables over `ℚ` is regular, by smoothness over `ℚ`. -/
public theorem isRegularRing_fin_two_rat : IsRegularRing (MvPolynomial (Fin 2) ℚ) :=
  Algebra.Smooth.isRegularRing (K := ℚ) (S := MvPolynomial (Fin 2) ℚ)

end MvPolynomial

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
    {K : Type u} {R : Type v} [CommRing K] [CommRing R] [IsLocalRing R]
    [Algebra K R] [Algebra.FormallyUnramified K (IsLocalRing.ResidueField R)]
    (s : IsLocalRing.ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (IsLocalRing.ResidueField R)) s)
    (x : IsLocalRing.maximalIdeal R) :
    IsLocalRing.cotangentSpaceEquivTensorKaehlerOfSection s hs
        ((IsLocalRing.maximalIdeal R).toCotangent x) =
      1 ⊗ₜ[R] KaehlerDifferential.D K R x.1 := by
  exact IsLocalRing.cotangentSpaceEquivTensorKaehlerOfSection_apply_toCotangent s hs x

private theorem residueEquivCotangent_apply
    {K : Type u} {R : Type v} [CommRing K] [CommRing R] [IsLocalRing R]
    [Algebra K R] (e : IsLocalRing.ResidueField R ≃ₐ[K] K)
    (x : IsLocalRing.maximalIdeal R) :
    IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv e
        ((IsLocalRing.maximalIdeal R).toCotangent x) =
      1 ⊗ₜ[R] KaehlerDifferential.D K R x.1 := by
  rw [IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv_apply_toCotangent e x]

private noncomputable def polynomialAugmentation
    (K : Type u) [CommRing K] : Algebra.Extension K K :=
  Algebra.Extension.ofSurjective (Polynomial.aeval (0 : K)) (by
    intro x
    exact ⟨Polynomial.C x, by simp⟩)

private noncomputable def polynomialAugmentationX
    (K : Type u) [CommRing K] : (polynomialAugmentation K).ker :=
  ⟨Polynomial.X, by
    change Polynomial.aeval (0 : K) Polynomial.X = 0
    simp⟩

private theorem polynomialAugmentation_conormal_apply
    (K : Type u) [CommRing K] :
    (polynomialAugmentation K).cotangentEquivCotangentSpaceOfFormallyEtale
        (Algebra.Extension.Cotangent.mk (polynomialAugmentationX K)) =
      1 ⊗ₜ[(polynomialAugmentation K).Ring]
        KaehlerDifferential.D K (polynomialAugmentation K).Ring Polynomial.X := by
  exact Algebra.Extension.cotangentEquivCotangentSpaceOfFormallyEtale_apply_mk
    (polynomialAugmentation K) (polynomialAugmentationX K)

/-- The polynomial augmentation has a nonzero conormal class whose canonical
image is the base change of `dX`. -/
private theorem polynomialAugmentation_conormal
    (K : Type u) [CommRing K] [Nontrivial K] :
    let P := polynomialAugmentation K
    let x := Algebra.Extension.Cotangent.mk (polynomialAugmentationX K)
    P.cotangentEquivCotangentSpaceOfFormallyEtale x =
        1 ⊗ₜ[P.Ring] KaehlerDifferential.D K P.Ring Polynomial.X ∧
      P.cotangentEquivCotangentSpaceOfFormallyEtale x ≠ 0 := by
  dsimp only
  refine ⟨polynomialAugmentation_conormal_apply K, ?_⟩
  intro h
  have hx : Algebra.Extension.Cotangent.mk (polynomialAugmentationX K) = 0 := by
    apply (polynomialAugmentation K).cotangentEquivCotangentSpaceOfFormallyEtale.injective
    simpa only [map_zero] using h
  -- Use the concrete augmentation kernel so polynomial operations and their
  -- instances remain visible to rewriting inside the ideal-product induction.
  have hmem : (Polynomial.X : Polynomial K) ∈
      (RingHom.ker (Polynomial.aeval (0 : K)).toRingHom) ^ 2 :=
    (Algebra.Extension.Cotangent.mk_eq_zero_iff _).mp hx
  have hcoeff : ∀ p : Polynomial K,
      p ∈ (RingHom.ker (Polynomial.aeval (0 : K)).toRingHom) ^ 2 →
        Polynomial.coeff p 1 = 0 := by
    intro p hp
    rw [pow_two] at hp
    refine Submodule.mul_induction_on hp ?_ ?_
    · intro a ha b hb
      have ha0 : Polynomial.coeff a 0 = 0 := by
        rw [Polynomial.coeff_zero_eq_aeval_zero]
        exact RingHom.mem_ker.mp ha
      have hb0 : Polynomial.coeff b 0 = 0 := by
        rw [Polynomial.coeff_zero_eq_aeval_zero]
        exact RingHom.mem_ker.mp hb
      rw [Polynomial.mul_coeff_one, ha0, hb0, zero_mul, mul_zero, add_zero]
    · intro a b ha hb
      simp only [Polynomial.coeff_add, ha, hb, add_zero]
  have hzero : (1 : K) = 0 := by
    simpa only [Polynomial.coeff_X_one] using hcoeff Polynomial.X hmem
  exact one_ne_zero hzero

private noncomputable def dualNumberAugmentation
    (K : Type u) [CommRing K] : Algebra.Extension K K :=
  Algebra.Extension.ofSurjective (TrivSqZeroExt.fstHom K K K)
    TrivSqZeroExt.fst_surjective

private noncomputable def dualNumberAugmentationEps
    (K : Type u) [CommRing K] : (dualNumberAugmentation K).ker :=
  ⟨DualNumber.eps, by
    change TrivSqZeroExt.fst (DualNumber.eps : DualNumber K) = 0
    exact DualNumber.fst_eps⟩

private theorem dualNumberAugmentation_conormal_apply
    (K : Type u) [CommRing K] :
    (dualNumberAugmentation K).cotangentEquivCotangentSpaceOfFormallyEtale
        (Algebra.Extension.Cotangent.mk (dualNumberAugmentationEps K)) =
      1 ⊗ₜ[(dualNumberAugmentation K).Ring]
        KaehlerDifferential.D K (dualNumberAugmentation K).Ring DualNumber.eps := by
  exact Algebra.Extension.cotangentEquivCotangentSpaceOfFormallyEtale_apply_mk
    (dualNumberAugmentation K) (dualNumberAugmentationEps K)

/-- The dual-number augmentation has a nonzero conormal class even though
its kernel has square zero and its extension ring is not smooth. -/
private theorem dualNumberAugmentation_conormal
    (K : Type u) [CommRing K] [Nontrivial K] :
    let P := dualNumberAugmentation K
    let x := Algebra.Extension.Cotangent.mk (dualNumberAugmentationEps K)
    P.cotangentEquivCotangentSpaceOfFormallyEtale x =
        1 ⊗ₜ[P.Ring] KaehlerDifferential.D K P.Ring DualNumber.eps ∧
      P.cotangentEquivCotangentSpaceOfFormallyEtale x ≠ 0 := by
  dsimp only
  refine ⟨dualNumberAugmentation_conormal_apply K, ?_⟩
  intro h
  have hx : Algebra.Extension.Cotangent.mk (dualNumberAugmentationEps K) = 0 := by
    apply (dualNumberAugmentation K).cotangentEquivCotangentSpaceOfFormallyEtale.injective
    simpa only [map_zero] using h
  -- Keep the canonical coordinate ring explicit in the square-ideal induction.
  have hmem : (DualNumber.eps : DualNumber K) ∈
      (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom) ^ 2 :=
    (Algebra.Extension.Cotangent.mk_eq_zero_iff _).mp hx
  have hsnd : ∀ d ∈ (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom) ^ 2,
      TrivSqZeroExt.snd d = 0 := by
    intro d hd
    rw [pow_two] at hd
    refine Submodule.mul_induction_on hd ?_ ?_
    · intro a ha b hb
      have ha0 : TrivSqZeroExt.fst a = 0 := ha
      have hb0 : TrivSqZeroExt.fst b = 0 := hb
      rw [DualNumber.snd_mul, ha0, hb0, zero_mul, mul_zero, add_zero]
    · intro a b ha hb
      simp only [TrivSqZeroExt.snd_add, ha, hb, add_zero]
  have hzero : (1 : K) = 0 := by
    simpa only [DualNumber.snd_eps] using hsnd DualNumber.eps hmem
  exact one_ne_zero hzero

open AlgebraicGeometry

private theorem regular_stalk_of_smooth_locus
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {x : X}
    (hx : x ∈ f.smoothLocus) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  Scheme.Hom.isRegularLocalRing_of_mem_smoothLocus f hx
