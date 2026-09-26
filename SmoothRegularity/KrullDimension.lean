/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.ENat.SuccOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Rigidity from Krull dimension

This file proves that a surjective homomorphism from a finite-dimensional
domain is bijective if the target has Krull dimension at least that of the
source.  A nonzero kernel element would be a non-zero-divisor, forcing the
target dimension to drop by at least one.
-/

public section

open scoped nonZeroDivisors

/-- A surjective homomorphism from a finite-dimensional domain is bijective if
the target has Krull dimension at least that of the source. -/
theorem RingHom.bijective_of_surjective_of_ringKrullDim_le
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R]
    [FiniteRingKrullDim R] (f : R →+* S) (hf : Function.Surjective f)
    (hdim : ringKrullDim R ≤ ringKrullDim S) : Function.Bijective f := by
  refine ⟨?_, hf⟩
  rw [RingHom.injective_iff_ker_eq_bot]
  apply bot_unique
  intro r hr
  by_contra hne
  have hsucc : ringKrullDim S + 1 ≤ ringKrullDim R :=
    ringKrullDim_succ_le_of_surjective f hf
      (mem_nonZeroDivisors_iff_ne_zero.mpr hne)
      (RingHom.mem_ker.mp hr)
  have hself : ringKrullDim R + 1 ≤ ringKrullDim R :=
    (add_le_add_left hdim 1).trans hsucc
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := R))
  have hdtop : d ≠ ⊤ := by
    intro hd'
    apply ringKrullDim_ne_top (R := R)
    rw [← hd, hd']
    rfl
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hdtop
  have hdimnat : ringKrullDim R = (n : WithBot ℕ∞) := by
    rw [← hd, ← hn]
    rfl
  rw [hdimnat] at hself
  exact (ENat.WithBot.add_one_le_natCast_iff.mp hself).false
