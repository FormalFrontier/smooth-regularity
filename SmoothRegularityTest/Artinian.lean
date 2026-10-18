/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SmoothRegularity
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.LocalRing.NonLocalRing

/-!
# Artinian regularity examples

Ordinary root-import clients for fields, finite products of fields, the
nonreduced Artinian ring `ZMod 4`, and the zero ring `PUnit`. Their Artinian and
reducedness hypotheses, and the field obstructions, use Mathlib. The regularity
conclusions use the Artinian equivalences.
-/

@[expose] public section

universe u v

private theorem regular_local_field (K : Type u) [Field K] :
    IsArtinianRing K ∧ IsRegularLocalRing K := by
  exact ⟨inferInstance,
    (IsArtinianRing.isRegularLocalRing_iff_isField K).mpr (Field.toIsField K)⟩

private theorem regular_field (K : Type u) [Field K] :
    IsArtinianRing K ∧ IsRegularRing K := by
  exact ⟨inferInstance,
    (IsArtinianRing.isRegularRing_iff_isReduced K).mpr inferInstance⟩

private theorem regular_local_reduced_artinian (R : Type u) [CommRing R]
    [IsArtinianRing R] [IsLocalRing R] [IsReduced R] : IsRegularLocalRing R :=
  (IsArtinianRing.isRegularLocalRing_iff_isField R).mpr
    (IsArtinianRing.isField_of_isReduced_of_isLocalRing R)

private theorem regular_finite_product_fields {ι : Type u} [Finite ι]
    (K : ι → Type v) [∀ i, Field (K i)] :
    IsArtinianRing (∀ i, K i) ∧ IsRegularRing (∀ i, K i) := by
  exact ⟨inferInstance,
    (IsArtinianRing.isRegularRing_iff_isReduced (∀ i, K i)).mpr inferInstance⟩

private theorem regular_two_rat_fields_not_field :
    IsArtinianRing (Fin 2 → ℚ) ∧ IsReduced (Fin 2 → ℚ) ∧
      IsRegularRing (Fin 2 → ℚ) ∧ ¬IsField (Fin 2 → ℚ) := by
  refine ⟨inferInstance, inferInstance,
    (IsArtinianRing.isRegularRing_iff_isReduced (Fin 2 → ℚ)).mpr inferInstance, ?_⟩
  intro h
  let : Field (Fin 2 → ℚ) := h.toField
  exact IsLocalRing.not_isLocalRing_of_nontrivial_pi (fun _ : Fin 2 ↦ ℚ) inferInstance

private theorem two_zmod_four_nilpotent :
    IsNilpotent (2 : ZMod 4) ∧ (2 : ZMod 4) ≠ 0 := by
  exact ⟨⟨2, by decide⟩, by decide⟩

private theorem zmod_four_not_reduced : ¬IsReduced (ZMod 4) := by
  intro h
  let : IsReduced (ZMod 4) := h
  exact two_zmod_four_nilpotent.2 two_zmod_four_nilpotent.1.eq_zero

private theorem artinian_zmod_four_not_regular :
    IsArtinianRing (ZMod 4) ∧ ¬IsRegularRing (ZMod 4) := by
  let : IsArtinianRing (ZMod 4) := isArtinian_of_finite
  refine ⟨inferInstance, ?_⟩
  intro h
  exact zmod_four_not_reduced
    ((IsArtinianRing.isRegularRing_iff_isReduced (ZMod 4)).mp h)

private theorem regular_zero_ring :
    IsArtinianRing PUnit.{u + 1} ∧ IsReduced PUnit.{u + 1} ∧
      IsRegularRing PUnit.{u + 1} ∧ ¬IsField PUnit.{u + 1} := by
  let : IsArtinianRing PUnit.{u + 1} := isArtinian_of_finite
  exact ⟨inferInstance, inferInstance,
    (IsArtinianRing.isRegularRing_iff_isReduced PUnit.{u + 1}).mpr inferInstance,
    not_isField_of_subsingleton PUnit.{u + 1}⟩

namespace PUnit

/-- The zero ring is regular but is not a field.
The regularity conclusion uses the Artinian reducedness criterion. -/
theorem isRegularRing_and_not_isField :
    IsRegularRing PUnit.{u + 1} ∧ ¬IsField PUnit.{u + 1} :=
  ⟨regular_zero_ring.{u}.2.2.1, regular_zero_ring.{u}.2.2.2⟩

end PUnit
