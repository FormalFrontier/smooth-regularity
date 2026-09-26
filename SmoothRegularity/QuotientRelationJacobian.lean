/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SmoothRegularity.KrullDimension
public import SmoothRegularity.RelationJacobian

/-!
# A quotient-dimension Jacobian criterion

This file derives generation of a presentation kernel from Krull-dimension
rigidity.  A finite family of relations spans an ideal contained in the
presentation kernel.  If the corresponding quotient is a finite-dimensional
domain whose dimension is at most that of the target, then the induced
surjection to the target is an isomorphism.  The relations therefore generate
the kernel, so the relation-basis Jacobian criterion applies.
-/

public section

open scoped TensorProduct

namespace Algebra.Extension

universe u v w t

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsLocalRing S] [Algebra R S]

/-- Let `P` be a formally smooth presentation of a local algebra `S`, with
finite free Kähler differentials.  Suppose a finite family of relations has
linearly independent images under the residue-field base change of the
cotangent-complex map.  If the quotient by the ideal spanned by those
relations is a finite-dimensional domain whose Krull dimension is at most
that of `S`, then `S` is formally smooth over the base. -/
theorem formallySmooth_of_quotient_span_dimension_of_linearIndependent
    (P : Algebra.Extension.{w} R S)
    [Algebra.FormallySmooth R P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄R]] [Module.Finite P.Ring Ω[P.Ring⁄R]]
    {ι : Type t} [Finite ι] (x : ι → P.ker)
    [IsDomain (P.Ring ⧸ Ideal.span (Set.range fun i ↦ (x i : P.Ring)))]
    [FiniteRingKrullDim
      (P.Ring ⧸ Ideal.span (Set.range fun i ↦ (x i : P.Ring)))]
    (hdim : ringKrullDim
        (P.Ring ⧸ Ideal.span (Set.range fun i ↦ (x i : P.Ring))) ≤
      ringKrullDim S)
    (hli : LinearIndependent (IsLocalRing.ResidueField S) (fun i ↦
      (P.cotangentComplex.baseChange (IsLocalRing.ResidueField S))
        (1 ⊗ₜ[S] Cotangent.mk (x i)))) :
    Algebra.FormallySmooth R S := by
  let J : Ideal P.Ring := Ideal.span (Set.range fun i ↦ (x i : P.Ring))
  have hJ : J ≤ P.ker := by
    change Ideal.span (Set.range fun i ↦ (x i : P.Ring)) ≤ P.ker
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (x i).property
  have hzero : ∀ r : P.Ring, r ∈ J → algebraMap P.Ring S r = 0 :=
    fun _ hr ↦ hJ hr
  let f : P.Ring ⧸ J →+* S :=
    Ideal.Quotient.lift J (algebraMap P.Ring S) hzero
  have hf_surjective : Function.Surjective f :=
    Ideal.Quotient.lift_surjective_of_surjective J hzero P.algebraMap_surjective
  have hf_bijective : Function.Bijective f :=
    RingHom.bijective_of_surjective_of_ringKrullDim_le f hf_surjective (by
      simpa [J] using hdim)
  have hker : P.ker ≤ J := by
    intro r hr
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply hf_bijective.1
    simpa [f] using hr
  apply P.formallySmooth_of_span_eq_ker_of_linearIndependent x
  · exact le_antisymm hJ hker
  · exact hli

end Algebra.Extension
