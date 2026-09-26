/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.Smooth.Local

/-!
# A relation-basis Jacobian criterion

This file packages a local Jacobian criterion for a finite family of
presentation relations. If the relations generate the presentation kernel
and their differentials remain linearly independent over the target residue
field, then the target is formally smooth.
-/

public section

open scoped TensorProduct

namespace Algebra.Extension

universe u v w t

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsLocalRing S] [Algebra R S]

/-- Let `P` be a formally smooth presentation of a local algebra `S`, with
finite free Kähler differentials. If a finite family of relations spans the
kernel of the presentation and its image under the residue-field base change
of the cotangent-complex map is linearly independent, then `S` is formally
smooth over the base.

This is the relation-basis form of the local Jacobian criterion. -/
theorem formallySmooth_of_span_eq_ker_of_linearIndependent
    (P : Algebra.Extension.{w} R S)
    [Algebra.FormallySmooth R P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄R]] [Module.Finite P.Ring Ω[P.Ring⁄R]]
    {ι : Type t} [Finite ι] (x : ι → P.ker)
    (hspan : Ideal.span (Set.range fun i ↦ (x i : P.Ring)) = P.ker)
    (hli : LinearIndependent (IsLocalRing.ResidueField S) (fun i ↦
      (P.cotangentComplex.baseChange (IsLocalRing.ResidueField S))
        (1 ⊗ₜ[S] Cotangent.mk (x i)))) :
    Algebra.FormallySmooth R S := by
  have hfg : P.ker.FG := hspan ▸ Submodule.fg_span (Set.finite_range _)
  rw [Algebra.FormallySmooth.iff_injective_lTensor_residueField P hfg]
  change Function.Injective
    (P.cotangentComplex.baseChange (IsLocalRing.ResidueField S))
  refine LinearMap.injective_of_linearIndependent
    (R := IsLocalRing.ResidueField S)
    (f := P.cotangentComplex.baseChange (IsLocalRing.ResidueField S))
    (v := fun i ↦
      (1 : IsLocalRing.ResidueField S) ⊗ₜ[S] Cotangent.mk (x i)) ?_ hli
  have hcotangent :
      Submodule.span S (Set.range fun i ↦ Cotangent.mk (x i)) = ⊤ := by
    exact Cotangent.span_eq_top_of_span_eq_ker (P := P)
      (fun i ↦ (x i : P.Ring)) hspan
  rw [show Set.range (fun i ↦
      (1 : IsLocalRing.ResidueField S) ⊗ₜ[S] Cotangent.mk (x i)) =
    TensorProduct.mk S (IsLocalRing.ResidueField S) P.Cotangent 1 ''
      Set.range (fun i ↦ Cotangent.mk (x i)) by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Cotangent.mk (x i), ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩]
  rw [← Submodule.baseChange_span, hcotangent, Submodule.baseChange_top]

end Algebra.Extension
