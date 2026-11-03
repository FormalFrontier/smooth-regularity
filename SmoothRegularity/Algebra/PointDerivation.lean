/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SmoothRegularity.Algebra.CotangentDerivation
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.RingHom

/-!
# Augmentation cotangents and point derivations

For an augmentation `ε : A →ₐ[R] R`, linear maps from `(ker ε)/(ker ε)²`
represent derivations with coefficient action `a • m = ε a • m`. The
`R`-actions on the cotangent and coefficients are the original actions.
The point action is supplied separately to Mathlib's `Derivation` type.

The forward map evaluates a functional on the class of
`a - algebraMap R A (ε a)`. The inverse restricts a point derivation to
`ker ε` and uses the universal property of the ideal cotangent. Its lift
is taken over `A` with the identity self-algebra, so the base `R` need
only be a commutative semiring. The coefficient additive group needed
by that lift is canonically supplied by its point `A`-module, retaining
the given additive monoid.

## References

This uses the split-map construction in
`SmoothRegularity.Algebra.CotangentDerivation` (generalizing the
split-residue construction in `SmoothRegularity.Conormal`), Mathlib's derivations
(Nicolò Cavalleri and Andrew Yang), and Mathlib's ideal cotangent lift
(Andrew Yang).
-/

@[expose] public section

namespace AlgHom

universe u v w

variable {R : Type u} {A : Type v} {M : Type w}
  [r : CommSemiring R] [a : CommRing A] [m : AddCommMonoid M]
  [α : Algebra R A] [μ : Module R M]

/-- The difference between an element and the scalar selected by an
augmentation belongs to its kernel. -/
theorem sub_algebraMap_apply_mem_ker (ε : A →ₐ[R] R) (x : A) :
    x - algebraMap R A (ε x) ∈ RingHom.ker (ε : A →+* R) := by
  exact sub_section_mem_ker ε (Algebra.ofId R A) (fun t => ε.commutes t) x

/-- The natural action on the augmentation cotangent factors through the
augmentation, with the original scalar action on the right. -/
theorem cotangent_smul_eq (ε : A →ₐ[R] R) (x : A)
    (z : (RingHom.ker (ε : A →+* R)).Cotangent) : x • z = ε x • z := by
  have h := Ideal.Cotangent.smul_eq_zero_of_mem
    (sub_algebraMap_apply_mem_ker ε x) z
  rw [sub_smul, sub_eq_zero] at h
  exact h.trans (IsScalarTower.algebraMap_smul (R := R) (A := A) (ε x) z)

private theorem pointScalarTower (ε : A →ₐ[R] R) :
    @IsScalarTower R A M α.toSMul (Module.compHom M ε.toRingHom).toSMul μ.toSMul :=
  @IsScalarTower.of_algebraMap_smul R A M r a.toSemiring α
    (Module.compHom M ε.toRingHom).toMulAction μ.toSMul fun t z => by
      change ε (algebraMap R A t) • z = t • z
      exact congrArg (fun s : R => s • z) (ε.commutes t)

private def cotangentPointLinear (ε : A →ₐ[R] R)
    (f : (RingHom.ker (ε : A →+* R)).Cotangent →ₗ[R] M) :
    @LinearMap A A _ _ (RingHom.id A)
      (RingHom.ker (ε : A →+* R)).Cotangent M _ m _
      (Module.compHom M ε.toRingHom) :=
  @LinearMap.mk A A _ _ (RingHom.id A)
    (RingHom.ker (ε : A →+* R)).Cotangent M _ m _ (Module.compHom M ε.toRingHom)
    ⟨f, f.map_add⟩ fun x z => by
      change f (x • z) = ε x • f z
      rw [cotangent_smul_eq, f.map_smul]

private noncomputable def cotangentPointDerivation (ε : A →ₐ[R] R)
    (f : (RingHom.ker (ε : A →+* R)).Cotangent →ₗ[R] M) :
    @Derivation R A M r a.toCommSemiring m α (Module.compHom M ε.toRingHom) μ :=
  @LinearMap.compDer R A (RingHom.ker (ε : A →+* R)).Cotangent r a.toCommSemiring
    _ α _ _ M m (Module.compHom M ε.toRingHom) μ
    (inferInstance : IsScalarTower R A (RingHom.ker (ε : A →+* R)).Cotangent)
    (pointScalarTower ε) (cotangentPointLinear ε f)
    (ε.cotangentDerivationOfSection (Algebra.ofId R A) (fun t => ε.commutes t))

private theorem cotangentPointDerivation_apply (ε : A →ₐ[R] R)
    (f : (RingHom.ker (ε : A →+* R)).Cotangent →ₗ[R] M) (x : A) :
    cotangentPointDerivation ε f x =
      f (ε.cotangentDerivationOfSection (Algebra.ofId R A) (fun t => ε.commutes t) x) :=
  rfl

private theorem cotangentPointDerivation_apply_coe (ε : A →ₐ[R] R)
    (f : (RingHom.ker (ε : A →+* R)).Cotangent →ₗ[R] M)
    (x : RingHom.ker (ε : A →+* R)) :
    cotangentPointDerivation ε f x = f ((RingHom.ker (ε : A →+* R)).toCotangent x) := by
  exact (cotangentPointDerivation_apply ε f x).trans
    (congrArg f (cotangentDerivationOfSection_apply_coe ε (Algebra.ofId R A)
      (fun t => ε.commutes t) x))

private theorem cotangentPointDerivation_add (ε : A →ₐ[R] R)
    (f g : (RingHom.ker (ε : A →+* R)).Cotangent →ₗ[R] M) :
    cotangentPointDerivation ε (f + g) =
      cotangentPointDerivation ε f + cotangentPointDerivation ε g := by
  apply @Derivation.ext R A M r a.toCommSemiring m α
    (Module.compHom M ε.toRingHom) μ
  intro x
  rw [@Derivation.add_apply R A M r a.toCommSemiring m α
    (Module.compHom M ε.toRingHom) μ
    (cotangentPointDerivation ε f) (cotangentPointDerivation ε g) x]
  exact (cotangentPointDerivation_apply ε (f + g) x).trans
    (congrArg₂ (fun u v : M => u + v)
      (cotangentPointDerivation_apply ε f x).symm
      (cotangentPointDerivation_apply ε g x).symm)

private def pointRestriction (ε : A →ₐ[R] R)
    (δ : @Derivation R A M r a.toCommSemiring m α (Module.compHom M ε.toRingHom) μ) :
    @LinearMap A A _ _ (RingHom.id A) (RingHom.ker (ε : A →+* R)) M _ m _
      (Module.compHom M ε.toRingHom) :=
  @LinearMap.mk A A _ _ (RingHom.id A) (RingHom.ker (ε : A →+* R)) M _ m _
    (Module.compHom M ε.toRingHom)
    ⟨fun x => δ x, fun x y => map_add δ (x : A) (y : A)⟩ fun x y => by
      change δ (x * (y : A)) = ε x • δ y
      rw [@Derivation.leibniz R A M r a.toCommSemiring m α
        (Module.compHom M ε.toRingHom) μ δ x (y : A)]
      change ε x • δ y + ε (y : A) • δ x = ε x • δ y
      rw [show ε (y : A) = 0 from y.2, zero_smul, add_zero]

private theorem pointRestriction_apply (ε : A →ₐ[R] R)
    (δ : @Derivation R A M r a.toCommSemiring m α (Module.compHom M ε.toRingHom) μ)
    (x : RingHom.ker (ε : A →+* R)) : pointRestriction ε δ x = δ x :=
  rfl

private theorem pointRestriction_mul (ε : A →ₐ[R] R)
    (δ : @Derivation R A M r a.toCommSemiring m α (Module.compHom M ε.toRingHom) μ)
    (x y : RingHom.ker (ε : A →+* R)) : pointRestriction ε δ (x * y) = 0 := by
  rw [pointRestriction_apply, MulMemClass.coe_mul,
    @Derivation.leibniz R A M r a.toCommSemiring m α
    (Module.compHom M ε.toRingHom) μ δ (x : A) (y : A)]
  change ε (x : A) • δ y + ε (y : A) • δ x = 0
  rw [show ε (x : A) = 0 from x.2, show ε (y : A) = 0 from y.2,
    zero_smul, zero_smul, add_zero]

private noncomputable def pointDerivationCotangent (ε : A →ₐ[R] R)
    (δ : @Derivation R A M r a.toCommSemiring m α (Module.compHom M ε.toRingHom) μ) :
    (RingHom.ker (ε : A →+* R)).Cotangent →ₗ[R] M := by
  let point : Module A M := Module.compHom M ε.toRingHom
  let group : AddCommGroup M := @Module.addCommMonoidToAddCommGroup A M a.toRing m point
  let : @IsScalarTower R A M α.toSMul point.toSMul μ.toSMul := pointScalarTower ε
  exact (@Ideal.Cotangent.lift A a A a (Algebra.id A) (RingHom.ker (ε : A →+* R))
    M group point (pointRestriction ε δ) (pointRestriction_mul ε δ)).restrictScalars R

private theorem pointDerivationCotangent_apply (ε : A →ₐ[R] R)
    (δ : @Derivation R A M r a.toCommSemiring m α (Module.compHom M ε.toRingHom) μ)
    (x : RingHom.ker (ε : A →+* R)) :
    pointDerivationCotangent ε δ ((RingHom.ker (ε : A →+* R)).toCotangent x) = δ x := by
  change (@Ideal.Cotangent.lift A a A a (Algebra.id A) (RingHom.ker (ε : A →+* R))
    M (@Module.addCommMonoidToAddCommGroup A M a.toRing m (Module.compHom M ε.toRingHom))
    (Module.compHom M ε.toRingHom) (pointRestriction ε δ) (pointRestriction_mul ε δ))
      ((RingHom.ker (ε : A →+* R)).toCotangent x) = δ x
  exact (@Ideal.Cotangent.lift_toCotangent A a A a (Algebra.id A)
    (RingHom.ker (ε : A →+* R)) M
    (@Module.addCommMonoidToAddCommGroup A M a.toRing m (Module.compHom M ε.toRingHom))
    (Module.compHom M ε.toRingHom) (pointRestriction ε δ) (pointRestriction_mul ε δ) x).trans
      (pointRestriction_apply ε δ x)

private theorem pointDerivationCotangent_cotangentPointDerivation (ε : A →ₐ[R] R)
    (f : (RingHom.ker (ε : A →+* R)).Cotangent →ₗ[R] M) :
    pointDerivationCotangent ε (cotangentPointDerivation ε f) = f := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (RingHom.ker (ε : A →+* R)).toCotangent_surjective z
  rw [pointDerivationCotangent_apply, cotangentPointDerivation_apply_coe]

private theorem cotangentPointDerivation_pointDerivationCotangent (ε : A →ₐ[R] R)
    (δ : @Derivation R A M r a.toCommSemiring m α (Module.compHom M ε.toRingHom) μ) :
    cotangentPointDerivation ε (pointDerivationCotangent ε δ) = δ := by
  apply @Derivation.ext R A M r a.toCommSemiring m α
    (Module.compHom M ε.toRingHom) μ
  intro x
  calc
    cotangentPointDerivation ε (pointDerivationCotangent ε δ) x =
        pointDerivationCotangent ε δ ((RingHom.ker (ε : A →+* R)).toCotangent
          ⟨x - algebraMap R A (ε x), sub_algebraMap_apply_mem_ker ε x⟩) :=
      (cotangentPointDerivation_apply ε (pointDerivationCotangent ε δ) x).trans
        (congrArg (pointDerivationCotangent ε δ)
          (cotangentDerivationOfSection_apply ε (Algebra.ofId R A)
            (fun t => ε.commutes t) x))
    _ = δ (x - algebraMap R A (ε x)) := pointDerivationCotangent_apply ε δ _
    _ = δ x := by
      have h := map_add δ (x - algebraMap R A (ε x)) (algebraMap R A (ε x))
      rw [sub_add_cancel, @Derivation.map_algebraMap R A M r a.toCommSemiring m α
        (Module.compHom M ε.toRingHom) μ δ (ε x), add_zero] at h
      exact h.symm

private noncomputable def cotangentPointEquiv (ε : A →ₐ[R] R) :
    @LinearEquiv R R _ _ (RingHom.id R) (RingHom.id R) _ _
      ((RingHom.ker (ε : A →+* R)).Cotangent →ₗ[R] M)
      (@Derivation R A M r a.toCommSemiring m α (Module.compHom M ε.toRingHom) μ)
      _ _ _
      (@Derivation.instModule R A M r a.toCommSemiring m α
        (Module.compHom M ε.toRingHom) μ R r.toSemiring μ
        (smulCommClass_self R M)
        (SMul.comp.smulCommClass' (α := M) (β := R) (M := R) ε)) := by
  refine @LinearEquiv.mk R R _ _ (RingHom.id R) (RingHom.id R) _ _
    ((RingHom.ker (ε : A →+* R)).Cotangent →ₗ[R] M)
    (@Derivation R A M r a.toCommSemiring m α (Module.compHom M ε.toRingHom) μ)
    _ _ _
    (@Derivation.instModule R A M r a.toCommSemiring m α
      (Module.compHom M ε.toRingHom) μ R r.toSemiring μ
      (smulCommClass_self R M)
      (SMul.comp.smulCommClass' (α := M) (β := R) (M := R) ε)) ?_
    ((pointDerivationCotangent : (ε : A →ₐ[R] R) →
      @Derivation R A M r a.toCommSemiring m α (Module.compHom M ε.toRingHom) μ →
        (RingHom.ker (ε : A →+* R)).Cotangent →ₗ[R] M) ε) ?_ ?_
  · refine @LinearMap.mk R R _ _ (RingHom.id R)
      ((RingHom.ker (ε : A →+* R)).Cotangent →ₗ[R] M)
      (@Derivation R A M r a.toCommSemiring m α (Module.compHom M ε.toRingHom) μ)
      _ _ _
      (@Derivation.instModule R A M r a.toCommSemiring m α
        (Module.compHom M ε.toRingHom) μ R r.toSemiring μ
        (smulCommClass_self R M)
        (SMul.comp.smulCommClass' (α := M) (β := R) (M := R) ε))
      ⟨(cotangentPointDerivation : (ε : A →ₐ[R] R) →
        ((RingHom.ker (ε : A →+* R)).Cotangent →ₗ[R] M) →
          @Derivation R A M r a.toCommSemiring m α (Module.compHom M ε.toRingHom) μ) ε,
        ?_⟩ ?_
    · intro f g
      exact (cotangentPointDerivation_add) ε f g
    · intro t f
      apply @Derivation.ext R A M r a.toCommSemiring m α
        (Module.compHom M ε.toRingHom) μ
      intro x
      rfl
  · intro f
    exact (pointDerivationCotangent_cotangentPointDerivation) ε f
  · intro δ
    exact (cotangentPointDerivation_pointDerivationCotangent) ε δ

/-- Linear functionals on the augmentation cotangent represent derivations
with the canonical point coefficient action. The coefficient additive monoid
and its original `R`-module are unchanged, and the two module arguments of
`Derivation` remain separate. -/
noncomputable def cotangentEquivPointDerivation (ε : A →ₐ[R] R) :
    @LinearEquiv R R _ _ (RingHom.id R) (RingHom.id R) _ _
      ((RingHom.ker (ε : A →+* R)).Cotangent →ₗ[R] M)
      (@Derivation R A M r a.toCommSemiring m α (Module.compHom M ε.toRingHom) μ)
      _ _ _
      (@Derivation.instModule R A M r a.toCommSemiring m α
        (Module.compHom M ε.toRingHom) μ R r.toSemiring μ
        (smulCommClass_self R M)
        (SMul.comp.smulCommClass' (α := M) (β := R) (M := R) ε)) :=
  (private_decl% cotangentPointEquiv : (ε : A →ₐ[R] R) →
    @LinearEquiv R R _ _ (RingHom.id R) (RingHom.id R) _ _
      ((RingHom.ker (ε : A →+* R)).Cotangent →ₗ[R] M)
      (@Derivation R A M r a.toCommSemiring m α (Module.compHom M ε.toRingHom) μ)
      _ _ _
      (@Derivation.instModule R A M r a.toCommSemiring m α
        (Module.compHom M ε.toRingHom) μ R r.toSemiring μ
        (smulCommClass_self R M)
        (SMul.comp.smulCommClass' (α := M) (β := R) (M := R) ε))) ε

/-- Forward evaluation is the functional on the difference class. -/
theorem cotangentEquivPointDerivation_apply (ε : A →ₐ[R] R)
    (f : (RingHom.ker (ε : A →+* R)).Cotangent →ₗ[R] M) (x : A) :
    ε.cotangentEquivPointDerivation f x =
      f ((RingHom.ker (ε : A →+* R)).toCotangent
        ⟨x - algebraMap R A (ε x), sub_algebraMap_apply_mem_ker ε x⟩) := by
  exact (cotangentPointDerivation_apply ε f x).trans
    (congrArg f (cotangentDerivationOfSection_apply ε (Algebra.ofId R A)
      (fun t => ε.commutes t) x))

/-- On the augmentation kernel, forward evaluation is evaluation on its
cotangent class. -/
@[simp] theorem cotangentEquivPointDerivation_apply_coe (ε : A →ₐ[R] R)
    (f : (RingHom.ker (ε : A →+* R)).Cotangent →ₗ[R] M)
    (x : RingHom.ker (ε : A →+* R)) :
    ε.cotangentEquivPointDerivation f x = f ((RingHom.ker (ε : A →+* R)).toCotangent x) := by
  exact cotangentPointDerivation_apply_coe ε f x

/-- The inverse functional evaluates on a kernel class as the given point
derivation on its representative. -/
@[simp] theorem cotangentEquivPointDerivation_symm_apply_toCotangent (ε : A →ₐ[R] R)
    (δ : @Derivation R A M r a.toCommSemiring m α (Module.compHom M ε.toRingHom) μ)
    (x : RingHom.ker (ε : A →+* R)) :
    ε.cotangentEquivPointDerivation.symm δ ((RingHom.ker (ε : A →+* R)).toCotangent x) = δ x := by
  exact pointDerivationCotangent_apply ε δ x

/-- Point derivations are determined by their restriction to the augmentation
kernel. This follows from the cotangent representation. -/
theorem pointDerivation_ext (ε : A →ₐ[R] R)
    {δ₁ δ₂ : @Derivation R A M r a.toCommSemiring m α (Module.compHom M ε.toRingHom) μ}
    (h : ∀ x : RingHom.ker (ε : A →+* R), δ₁ x = δ₂ x) : δ₁ = δ₂ := by
  apply (ε.cotangentEquivPointDerivation (M := M)).symm.injective
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (RingHom.ker (ε : A →+* R)).toCotangent_surjective z
  simpa only [cotangentEquivPointDerivation_symm_apply_toCotangent] using h x

end AlgHom
