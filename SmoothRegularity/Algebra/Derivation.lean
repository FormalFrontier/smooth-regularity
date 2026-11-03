/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Torsion
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Derivations and nilpotent elements

A derivation of a commutative ring with torsion-free additive group sends
nilpotent elements to nilpotent elements.

The proof inducts on a vanishing power. The power rule and cancellation of a
positive natural multiple give a smaller vanishing power for `a * D a`.
Differentiating this product then expresses `(D a)^2` as a difference of
nilpotent elements.
-/

@[expose] public section

universe u v

namespace Derivation

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [CommRing A] [Algebra R A] [IsAddTorsionFree A]

/-- A derivation of a commutative ring with torsion-free additive group preserves
nilpotent elements. -/
theorem isNilpotent_apply (D : Derivation R A A) {a : A} (ha : IsNilpotent a) :
    IsNilpotent (D a) := by
  suffices h : ∀ (n : ℕ) (x : A), x ^ (n + 1) = 0 → IsNilpotent (D x) by
    obtain ⟨n, hn⟩ := ha
    exact h n a (by rw [pow_succ, hn, zero_mul])
  intro n
  induction n with
  | zero =>
      intro x hx
      have hx0 : x = 0 := by simpa only [Nat.zero_add, pow_one] using hx
      rw [hx0, D.map_zero]
      exact IsNilpotent.zero
  | succ n ih =>
      intro x hx
      have hmul : x ^ (n + 1) * D x = 0 := by
        apply (nsmul_eq_zero_iff_right (Nat.succ_ne_zero (n + 1))).mp
        simpa only [hx, D.map_zero, Nat.add_sub_cancel, smul_eq_mul] using
          (D.leibniz_pow x (n + 1 + 1)).symm
      have hprod : (x * D x) ^ (n + 1) = 0 := by
        rw [mul_pow, pow_succ' (D x) n, ← mul_assoc, hmul, zero_mul]
      have hdprod : IsNilpotent (D (x * D x)) := ih (x * D x) hprod
      have hterm : IsNilpotent (x * D (D x)) :=
        (Commute.all x (D (D x))).isNilpotent_mul_right ⟨n + 1 + 1, hx⟩
      have hsq : IsNilpotent ((D x) ^ 2) := by
        have hsub : IsNilpotent (D (x * D x) - x * D (D x)) :=
          (Commute.all _ _).isNilpotent_sub hdprod hterm
        simpa only [D.leibniz, smul_eq_mul, pow_two, add_sub_cancel_left] using hsub
      exact hsq.of_pow

end Derivation
