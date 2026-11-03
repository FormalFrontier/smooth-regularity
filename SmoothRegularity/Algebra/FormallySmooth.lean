/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Smooth.Basic
public import SmoothRegularity.Algebra.Ideal

/-!
# Annihilators of nilpotent ideals with formally smooth quotients

Formal smoothness of a quotient by a nilpotent ideal provides an algebra section.
If the ideal is finitely generated and contained in `I²`, there is an element
congruent to `1` modulo `I` that annihilates the ideal.
-/

public section

namespace Algebra.FormallySmooth

universe u v

variable {K : Type u} {A : Type v} [CommRing K] [CommRing A] [Algebra K A]

/-- If a finitely generated nilpotent ideal `N` has formally smooth quotient and
is contained in `I²`, then an element congruent to `1` modulo `I` annihilates `N`. -/
theorem exists_sub_one_mem_and_mul_eq_zero_of_quotient
    (N I : Ideal A) (hnil : IsNilpotent N) (hfg : N.FG)
    [FormallySmooth K (A ⧸ N)] (h : N ≤ I ^ 2) :
    ∃ r : A, r - 1 ∈ I ∧ ∀ n ∈ N, r * n = 0 := by
  let s : (A ⧸ N) →ₐ[K] A :=
    Algebra.FormallySmooth.lift N hnil (AlgHom.id K (A ⧸ N))
  have hs : Function.RightInverse s.toRingHom (Ideal.Quotient.mk N) := by
    intro a
    exact Algebra.FormallySmooth.mk_lift N hnil (AlgHom.id K (A ⧸ N)) a
  have hmul : N = I * N := by
    have hker : RingHom.ker (Ideal.Quotient.mk N) ≤ I ^ 2 := by
      simpa only [Ideal.mk_ker] using h
    simpa only [Ideal.mk_ker] using
      RingHom.ker_eq_mul_of_rightInverse (Ideal.Quotient.mk N) s.toRingHom hs I hker
  have hle : (N : Submodule A A) ≤ I • (N : Submodule A A) := by
    simpa only [Ideal.smul_eq_mul] using hmul.le
  obtain ⟨r, hr, hzero⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hfg hle
  refine ⟨r, hr, ?_⟩
  intro n hn
  simpa only [smul_eq_mul] using hzero n hn

end Algebra.FormallySmooth
