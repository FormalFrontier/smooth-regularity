/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Extension.ExtendScalars
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Smooth.Kaehler
public import Mathlib.RingTheory.Unramified.Basic

/-!
# Conormal modules and formally étale quotients

For an extension `P → S` of algebras over a commutative ring `K`, with kernel
`I`, the canonical conormal map is `I/I² → S ⊗[P] Ω[P⁄K]`. A section
`S →ₐ[K] P/I²` makes this map injective. If `S` is formally étale over `K`,
the map is an isomorphism, without a section into `P` or smoothness of `P`.
The map is Mathlib's `Algebra.Extension.cotangentComplex` throughout.

For a local algebra `R`, this identifies its cotangent space with
`κ(R) ⊗[R] Ω[R⁄K]` when `κ(R)` is formally étale over `K`. The identification
agrees with the split-residue constructions under their shared hypotheses.
Those constructions also apply when the residue field is merely formally
unramified, provided a section into `R` is supplied.

## Examples and boundary

For any nontrivial commutative ring `K`, the augmentations `K[X] → K` and
`K[ε] → K`, where `ε² = 0`, have nonzero conormal classes `[X]` and `[ε]`.
Their images are `1 ⊗ dX` and `1 ⊗ dε`, respectively. The second example
illustrates that no smoothness hypothesis on the extension ring is required.

Let `R = ℚ[X]_(X² - 2)` and `f = X² - 2`. Its separable residue field has no
`ℚ`-algebra section into `R`: such a section would put a square root of `2`
in `ℚ(X)`. It does have a section into `R/(f²)`, sending the residue of `X`
to `X - f/(2X)`. Here `2X` is a unit and the square of this element minus `2`
is `f²/(4X²)`. The nonzero class `[f]` maps to `1 ⊗ 2X dX`.

The target hypothesis cannot be dropped in general. For
`K = 𝔽_p(s)` and `A = K[t]/(t^p - s)`, the ring `A` is a regular field with
zero maximal ideal, but `Ω[A⁄K]` is nonzero. Thus its zero cotangent space
cannot be identified with its differential module. The residue extension is
inseparable and not formally étale.

## References

The conormal map, its exact sequence, and the correspondence between
first-order sections and linear retractions are developed in Mathlib's
`RingTheory.Extension.Cotangent.Basic`, `RingTheory.Extension.ExtendScalars`,
and `RingTheory.Smooth.Kaehler`.
-/

public section

open scoped TensorProduct

namespace Algebra.Extension

universe u v w

variable {K : Type u} {S : Type v} [CommRing K] [CommRing S] [Algebra K S]

/-- The linear retraction induced by a section of the first-order quotient,
together with its left-inverse property. -/
private noncomputable def cotangentComplexRetractionOfInfinitesimalSection
    (P : Extension.{w} K S) (s : S →ₐ[K] P.infinitesimal.Ring)
    (hs : Function.LeftInverse (algebraMap P.infinitesimal.Ring S) s) :
    { r : P.CotangentSpace →ₗ[S] P.Cotangent //
      Function.LeftInverse r P.cotangentComplex } := by
  have hs' : (IsScalarTower.toAlgHom K P.Ring S).kerSquareLift.comp s =
      AlgHom.id K S := by
    ext x
    exact hs x
  let retraction :=
    (retractionKerCotangentToTensorEquivSection (R := K) (P := P.Ring) (S := S)
      P.algebraMap_surjective).symm ⟨s, hs'⟩
  let r : P.CotangentSpace →ₗ[S] P.Cotangent :=
    (P.cotangentEquivCotangentKer.symm.toLinearMap.comp retraction.1).extendScalarsOfSurjective
      P.algebraMap_surjective
  have hr : Function.LeftInverse r P.cotangentComplex := by
    intro x
    apply P.cotangentEquivCotangentKer.injective
    change retraction.1
        (KaehlerDifferential.kerCotangentToTensor K P.Ring S
          (P.cotangentEquivCotangentKer x)) = P.cotangentEquivCotangentKer x
    exact LinearMap.congr_fun retraction.2 (P.cotangentEquivCotangentKer x)
  exact ⟨r, hr⟩

/-- A section of the first-order quotient `P/I² → S` makes the canonical
conormal map injective. No section into `P` is required. -/
theorem cotangentComplex_injective_of_infinitesimalSection (P : Extension.{w} K S)
    (s : S →ₐ[K] P.infinitesimal.Ring)
    (hs : Function.LeftInverse (algebraMap P.infinitesimal.Ring S) s) :
    Function.Injective P.cotangentComplex := by
  exact (cotangentComplexRetractionOfInfinitesimalSection P s hs).2.injective

/-- The canonical conormal equivalence of an extension with formally étale
target over the base. Its forward map is `P.cotangentComplex`. -/
@[expose] noncomputable def cotangentEquivCotangentSpaceOfFormallyEtale
    (P : Extension.{w} K S) [Algebra.FormallyEtale K S] :
    P.Cotangent ≃ₗ[S] P.CotangentSpace := by
  let q : P.infinitesimal.Ring →ₐ[K] S :=
    (IsScalarTower.toAlgHom K P.Ring S).kerSquareLift
  have hq : Function.Surjective q := P.infinitesimal.algebraMap_surjective
  have hnil : IsNilpotent (RingHom.ker q.toRingHom) := by
    refine ⟨2, ?_⟩
    exact (congrArg (fun I : Ideal (P.Ring ⧸ P.ker ^ 2) ↦ I ^ 2)
      P.ker_infinitesimal).trans (Ideal.cotangentIdeal_square P.ker)
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id K S) q hq hnil
  have hs : q.comp s = AlgHom.id K S :=
    Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id K S) q hq hnil
  have hinj : Function.Injective P.cotangentComplex :=
    cotangentComplex_injective_of_infinitesimalSection P s
      (fun x ↦ DFunLike.congr_fun hs x)
  have hsurj : Function.Surjective P.cotangentComplex := by
    intro y
    exact (P.exact_cotangentComplex_toKaehler y).mp (Subsingleton.elim _ _)
  exact LinearEquiv.ofBijective P.cotangentComplex ⟨hinj, hsurj⟩

/-- If the target of an extension is formally étale over the base, its
canonical conormal map is bijective. The extension ring need not be smooth. -/
theorem cotangentComplex_bijective_of_formallyEtale (P : Extension.{w} K S)
    [Algebra.FormallyEtale K S] : Function.Bijective P.cotangentComplex := by
  exact (cotangentEquivCotangentSpaceOfFormallyEtale P).bijective

/-- The conormal equivalence has the existing cotangent-complex map as its
underlying linear map. -/
theorem cotangentEquivCotangentSpaceOfFormallyEtale_toLinearMap
    (P : Extension.{w} K S) [Algebra.FormallyEtale K S] :
    (cotangentEquivCotangentSpaceOfFormallyEtale P).toLinearMap =
      P.cotangentComplex := by
  rfl

/-- A kernel class is sent to its differential in the target base change. -/
@[simp] theorem cotangentEquivCotangentSpaceOfFormallyEtale_apply_mk
    (P : Extension.{w} K S) [Algebra.FormallyEtale K S] (x : P.ker) :
    cotangentEquivCotangentSpaceOfFormallyEtale P (Cotangent.mk x) =
      1 ⊗ₜ[P.Ring] KaehlerDifferential.D K P.Ring x.1 := by
  rfl

end Algebra.Extension

namespace IsLocalRing

universe u v

section

variable {K : Type u} {R : Type v} [CommRing K] [CommRing R] [IsLocalRing R]
  [Algebra K R]

private noncomputable def residueDifference
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s) (r : R) :
    maximalIdeal R :=
  ⟨r - s (residue R r), by
    rw [← residue_eq_zero_iff]
    simp only [map_sub, sub_eq_zero]
    rw [← ResidueField.algebraMap_eq]
    exact (hs _).symm⟩

private lemma residueDifference_add
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s) (x y : R) :
    residueDifference s hs (x + y) = residueDifference s hs x + residueDifference s hs y := by
  ext
  simp only [residueDifference, map_add, Submodule.coe_mk, Submodule.coe_add]
  ring

private lemma residueDifference_smul
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s) (k : K) (x : R) :
    residueDifference s hs (k • x) = k • residueDifference s hs x := by
  rw [← IsScalarTower.algebraMap_smul R k x,
    ← IsScalarTower.algebraMap_smul R k (residueDifference s hs x)]
  apply Subtype.ext
  dsimp only [residueDifference]
  change (algebraMap K R) k * x - s (residue R ((algebraMap K R) k * x)) =
    (algebraMap K R) k * (x - s (residue R x))
  have hk : residue R ((algebraMap K R) k) = algebraMap K (ResidueField R) k := by
    rw [← ResidueField.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K R (ResidueField R)]
  rw [map_mul, hk, map_mul, s.commutes]
  ring

private noncomputable def splitResidueDerivation
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s) :
    Derivation K R (CotangentSpace R) where
  toLinearMap :=
    { toFun := fun r ↦ (maximalIdeal R).toCotangent (residueDifference s hs r)
      map_add' := fun x y ↦ by rw [residueDifference_add, map_add]
      map_smul' := fun k x ↦ by
        rw [residueDifference_smul]
        exact (maximalIdeal R).toCotangent.map_smul_of_tower k _ }
  map_one_eq_zero' := by
    change (maximalIdeal R).toCotangent (residueDifference s hs 1) = 0
    rw [show residueDifference s hs 1 = 0 by ext; simp [residueDifference], map_zero]
  leibniz' := fun x y ↦ by
    change (maximalIdeal R).toCotangent (residueDifference s hs (x * y)) =
      (maximalIdeal R).toCotangent (x • residueDifference s hs y) +
        (maximalIdeal R).toCotangent (y • residueDifference s hs x)
    rw [← map_add, ← sub_eq_zero, ← map_sub, Ideal.toCotangent_eq_zero]
    have hprod : -((residueDifference s hs x : R) * residueDifference s hs y) ∈
        maximalIdeal R ^ 2 := by
      apply (maximalIdeal R ^ 2).neg_mem
      rw [pow_two]
      exact Ideal.mul_mem_mul (residueDifference s hs x).2 (residueDifference s hs y).2
    convert hprod using 1
    change x * y - s (residue R (x * y)) -
        (x * (y - s (residue R y)) + y * (x - s (residue R x))) =
      -((x - s (residue R x)) * (y - s (residue R y)))
    simp only [map_mul]
    ring

private noncomputable def splitResidueRetraction
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s) :
    LinearMap (RingHom.id (ResidueField R)) (ResidueField R ⊗[R] Ω[R⁄K])
      (CotangentSpace R) :=
  (TensorProduct.isBaseChange R Ω[R⁄K] (ResidueField R)).lift
    (splitResidueDerivation s hs).liftKaehlerDifferential

private lemma splitResidueRetraction_comp
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s)
    (hker : RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R) :
    (splitResidueRetraction s hs).restrictScalars R ∘ₗ
        KaehlerDifferential.kerCotangentToTensor K R (ResidueField R) =
      (Ideal.Cotangent.equivOfEq _ _ hker).toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
  rw [LinearMap.comp_apply, KaehlerDifferential.kerCotangentToTensor_toCotangent]
  change splitResidueRetraction s hs (1 ⊗ₜ[R] KaehlerDifferential.D K R x.1) = _
  rw [splitResidueRetraction, show (1 ⊗ₜ[R] KaehlerDifferential.D K R x.1) =
      (TensorProduct.mk R (ResidueField R) Ω[R⁄K] 1) (KaehlerDifferential.D K R x.1) by rfl,
    IsBaseChange.lift_eq, Derivation.liftKaehlerDifferential_comp_D]
  change (maximalIdeal R).toCotangent (residueDifference s hs x.1) =
    Ideal.Cotangent.equivOfEq _ _ hker
      ((RingHom.ker (algebraMap R (ResidueField R))).toCotangent x)
  rw [Ideal.Cotangent.equivOfEq_toCotangent]
  apply (maximalIdeal R).toCotangent.congr_arg
  ext
  simp only [residueDifference]
  have hx : residue R x.1 = 0 := by
    rw [← ResidueField.algebraMap_eq]
    exact RingHom.mem_ker.mp x.2
  rw [hx, map_zero, sub_zero]
  rfl

/--
If the residue map of a local `K`-algebra has a `K`-algebra section and the
residue field is formally unramified over `K`, its cotangent space is the base
change of its module of Kähler differentials to the residue field.
-/
noncomputable def cotangentSpaceEquivTensorKaehlerOfSection
    [Algebra.FormallyUnramified K (ResidueField R)]
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s) :
    LinearEquiv (RingHom.id (ResidueField R)) (CotangentSpace R)
      (ResidueField R ⊗[R] Ω[R⁄K]) := by
  let hker : RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := by
    rw [ResidueField.algebraMap_eq, ker_residue]
  let f := KaehlerDifferential.kerCotangentToTensor K R (ResidueField R)
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply (Ideal.Cotangent.equivOfEq _ _ hker).injective
    have hcomp := splitResidueRetraction_comp s hs hker
    exact (LinearMap.congr_fun hcomp x).symm.trans <|
      (congr_arg (splitResidueRetraction s hs) hxy).trans (LinearMap.congr_fun hcomp y)
  have hf_surjective : Function.Surjective f := by
    rw [← LinearMap.range_eq_top,
      KaehlerDifferential.range_kerCotangentToTensor K R (ResidueField R) residue_surjective]
    ext x
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker, Submodule.mem_top, iff_true]
    exact Subsingleton.elim _ _
  exact LinearEquiv.extendScalarsOfSurjective residue_surjective <|
    (Ideal.Cotangent.equivOfEq _ _ hker).symm.trans
      (LinearEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩)

/-- The split-residue cotangent equivalence sends a class in the maximal ideal to
the corresponding differential in the residue-field base change. -/
theorem cotangentSpaceEquivTensorKaehlerOfSection_apply_toCotangent
    [Algebra.FormallyUnramified K (ResidueField R)]
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s)
    (x : maximalIdeal R) :
    cotangentSpaceEquivTensorKaehlerOfSection s hs
        ((maximalIdeal R).toCotangent x) =
      1 ⊗ₜ[R] KaehlerDifferential.D K R x.1 := by
  rfl

private noncomputable def residueSection
    (e : ResidueField R ≃ₐ[K] K) : ResidueField R →ₐ[K] R :=
  (Algebra.ofId K R).comp e.toAlgHom

private lemma residueSection_isSection (e : ResidueField R ≃ₐ[K] K) :
    Function.LeftInverse (algebraMap R (ResidueField R)) (residueSection e) := by
  intro x
  change algebraMap R (ResidueField R) ((algebraMap K R) (e x)) = x
  rw [← IsScalarTower.algebraMap_apply K R (ResidueField R)]
  apply e.injective
  simp

/--
If a local `K`-algebra has residue field isomorphic to `K` as a `K`-algebra,
its cotangent space is the base change of its module of Kähler differentials to
the residue field.
-/
noncomputable def cotangentSpaceEquivTensorKaehlerOfResidueEquiv
    (e : ResidueField R ≃ₐ[K] K) :
    LinearEquiv (RingHom.id (ResidueField R)) (CotangentSpace R)
      (ResidueField R ⊗[R] Ω[R⁄K]) := by
  letI : Algebra.FormallyUnramified K (ResidueField R) :=
    Algebra.FormallyUnramified.of_equiv e.symm
  exact cotangentSpaceEquivTensorKaehlerOfSection (residueSection e)
    (residueSection_isSection e)

/-- The cotangent equivalence induced by a residue-field equivalence sends a
class in the maximal ideal to its differential in the base change. -/
theorem cotangentSpaceEquivTensorKaehlerOfResidueEquiv_apply_toCotangent
    (e : ResidueField R ≃ₐ[K] K) (x : maximalIdeal R) :
    cotangentSpaceEquivTensorKaehlerOfResidueEquiv e
        ((maximalIdeal R).toCotangent x) =
      1 ⊗ₜ[R] KaehlerDifferential.D K R x.1 := by
  rfl

/-- If the residue field of a local algebra is formally étale over the
commutative base, the canonical conormal map is a residue-field linear
equivalence. A residue section into the local ring is not required. -/
@[expose] noncomputable def cotangentSpaceEquivTensorKaehlerOfFormallyEtale
    [Algebra.FormallyEtale K (ResidueField R)] :
    CotangentSpace R ≃ₗ[ResidueField R] (ResidueField R ⊗[R] Ω[R⁄K]) := by
  let P : Algebra.Extension K (ResidueField R) :=
    { Ring := R
      σ x := (residue_surjective (R := R) x).choose
      algebraMap_σ x := (residue_surjective (R := R) x).choose_spec }
  let hker : RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := by
    rw [ResidueField.algebraMap_eq, ker_residue]
  exact LinearEquiv.extendScalarsOfSurjective residue_surjective <|
    (Ideal.Cotangent.equivOfEq _ _ hker).symm.trans <|
      P.cotangentEquivCotangentKer.symm.trans
        (P.cotangentEquivCotangentSpaceOfFormallyEtale.restrictScalars R)

/-- After identifying the kernel of the residue map with the maximal ideal,
the forward map is Mathlib's canonical conormal map. -/
theorem cotangentSpaceEquivTensorKaehlerOfFormallyEtale_restrictScalars
    [Algebra.FormallyEtale K (ResidueField R)] :
    (cotangentSpaceEquivTensorKaehlerOfFormallyEtale
      (K := K) (R := R)).toLinearMap.restrictScalars R =
      KaehlerDifferential.kerCotangentToTensor K R (ResidueField R) ∘ₗ
        (Ideal.Cotangent.equivOfEq
          (RingHom.ker (algebraMap R (ResidueField R))) (maximalIdeal R)
          (by rw [ResidueField.algebraMap_eq, ker_residue])).symm.toLinearMap := by
  rfl

/-- The residue-field equivalence sends a maximal-ideal class to its
differential in the residue-field base change. -/
@[simp] theorem cotangentSpaceEquivTensorKaehlerOfFormallyEtale_apply_toCotangent
    [Algebra.FormallyEtale K (ResidueField R)] (x : maximalIdeal R) :
    cotangentSpaceEquivTensorKaehlerOfFormallyEtale (K := K)
        ((maximalIdeal R).toCotangent x) =
      1 ⊗ₜ[R] KaehlerDifferential.D K R x.1 := by
  rfl

/-- When a residue section into the local ring is also supplied, the
formally étale and split-residue equivalences agree. -/
theorem cotangentSpaceEquivTensorKaehlerOfFormallyEtale_eq_ofSection
    [Algebra.FormallyEtale K (ResidueField R)]
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s) :
    cotangentSpaceEquivTensorKaehlerOfFormallyEtale (K := K) (R := R) =
      cotangentSpaceEquivTensorKaehlerOfSection s hs := by
  ext x
  obtain ⟨x, rfl⟩ := (maximalIdeal R).toCotangent_surjective x
  rw [cotangentSpaceEquivTensorKaehlerOfFormallyEtale_apply_toCotangent,
    cotangentSpaceEquivTensorKaehlerOfSection_apply_toCotangent]

/-- Under the shared formally étale hypothesis, the canonical residue-field
equivalence agrees with the one induced by a residue-field equivalence. -/
theorem cotangentSpaceEquivTensorKaehlerOfFormallyEtale_eq_ofResidueEquiv
    [Algebra.FormallyEtale K (ResidueField R)] (e : ResidueField R ≃ₐ[K] K) :
    cotangentSpaceEquivTensorKaehlerOfFormallyEtale (K := K) (R := R) =
      cotangentSpaceEquivTensorKaehlerOfResidueEquiv e := by
  ext x
  obtain ⟨x, rfl⟩ := (maximalIdeal R).toCotangent_surjective x
  rw [cotangentSpaceEquivTensorKaehlerOfFormallyEtale_apply_toCotangent,
    cotangentSpaceEquivTensorKaehlerOfResidueEquiv_apply_toCotangent]

end

end IsLocalRing
