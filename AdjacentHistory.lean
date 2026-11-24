import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The finite same-marginal step in the terminal-label moment estimator.
The inputs to the bound are two real arrays with the same row sums.
No stochastic or asymptotic assumptions about a random automaton are made.
-/
namespace AdjacentHistory
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private theorem sum_div (s : Finset ι) (f : ι → ℝ) (c : ℝ) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i/c := by
  simp only [div_eq_mul_inv, sum_mul]

theorem norm_le_twice_offdiag (E : ι → ι → ℝ) (h : ∀ i, ∑ j, E i j = 0) :
    (∑ i, ∑ j, |E i j|) ≤ 2 * ∑ i, ∑ j ∈ univ.erase i, |E i j| := by
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  have hs := sum_erase_add univ (fun j => E i j) (mem_univ i)
  rw [h i] at hs
  have hneg : E i i = -(∑ j ∈ univ.erase i, E i j) := by linarith
  have habs : |E i i| ≤ ∑ j ∈ univ.erase i, |E i j| := by
    rw [hneg, abs_neg]
    exact abs_sum_le_sum_abs _ _
  have he := sum_erase_add univ (fun j => |E i j|) (mem_univ i)
  linarith

/-- Subtract, normalize, and restore the diagonal from the known marginal. -/
theorem adjacent_error (U V : ι → ι → ℝ) (π : ι → ℝ) (x : ℝ) (hx : x < 1)
    (hU : ∀ i, ∑ j, U i j = π i) (hV : ∀ i, ∑ j, V i j = π i) :
    (∑ i, ∑ j, |(V i j - x * U i j)/(1-x) - (if j=i then π i else 0)|) ≤
      2 * (∑ i, ∑ j ∈ univ.erase i, |V i j - x * U i j|)/(1-x) := by
  let E := fun i j => (V i j - x * U i j)/(1-x) - (if j=i then π i else 0)
  have hpos : 0 < 1-x := by linarith
  have hz : ∀ i, ∑ j, E i j = 0 := by
    intro i
    simp only [E, sum_sub_distrib, ← sum_div, ← mul_sum, hU, hV]
    simp
    field_simp
    ring
  have hh := norm_le_twice_offdiag E hz
  change (∑ i, ∑ j, |E i j|) ≤ _
  apply hh.trans
  apply le_of_eq
  rw [mul_div_assoc]
  congr 1
  rw [sum_div]
  apply sum_congr rfl
  intro i _
  rw [sum_div]
  apply sum_congr rfl
  intro j hj
  have hji : j ≠ i := (mem_erase.mp hj).1
  simp [E, hji, abs_div, abs_of_pos hpos]

/-- The sign-square calibration on a single fixed table uses off-diagonal mass alone. -/
theorem sign_calibration (S : ι → ι → ℝ) (z : ι → ℝ)
    (hs : (∑ i, ∑ j, S i j) = 1) (hz : ∀ i, z i * z i = 1) :
    1 - (∑ i, ∑ j, S i j * (z i * z j)) =
      ∑ i, ∑ j ∈ univ.erase i, S i j * (1-z i * z j) := by
  conv_lhs => lhs; rw [← hs]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sum_sub_distrib]
  have hdiag : S i i * (1-z i * z i) = 0 := by simp [hz i]
  have he := sum_erase_add univ (fun j => S i j * (1-z i*z j)) (mem_univ i)
  rw [hdiag, add_zero] at he
  rw [he]
  apply sum_congr rfl
  intro j _
  ring

end AdjacentHistory
