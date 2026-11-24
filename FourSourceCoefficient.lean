import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Finite coefficients from two prescribed ordered, synchronously joined
pairs. Each ordered pair of remaining tail lengths in {0,...,l-1}
has probability (1/2)^max(i,j) of agreeing on the necessary suffix. -/
namespace FourSourceCoefficient
open Finset

theorem weighted_shells (l : ℕ) (f : ℕ → ℚ) :
    (∑ i ∈ range l, ∑ j ∈ range l, f (max i j)) =
      ∑ j ∈ range l, (2 * (j : ℚ) + 1) * f j := by
  induction l with
  | zero => simp
  | succ l ih =>
    conv_lhs => rw [sum_range_succ]
    conv_rhs => rw [sum_range_succ]
    have A (i : ℕ) (hi : i ∈ range l) :
        (∑ j ∈ range (l+1), f (max i j)) =
        (∑ j ∈ range l, f (max i j)) + f l := by
      rw [sum_range_succ, max_eq_right (Nat.le_of_lt (mem_range.mp hi))]
    rw [sum_congr rfl A, sum_add_distrib, ih]
    have B (j : ℕ) (hj : j ∈ range (l+1)) :
        f (max l j) = f l := by
      rw [max_eq_left (Nat.le_of_lt_succ (mem_range.mp hj))]
    rw [sum_congr rfl B]
    simp
    ring

theorem coefficient (l : ℕ) :
    (∑ i ∈ range l, ∑ j ∈ range l, (1/2 : ℚ) ^ (max i j)) =
      6 - (4 * (l : ℚ) + 6) * (1/2 : ℚ) ^ l := by
  rw [weighted_shells]
  induction l with
  | zero => norm_num
  | succ l ih =>
    rw [sum_range_succ, ih, pow_succ]
    push_cast
    ring

end FourSourceCoefficient
