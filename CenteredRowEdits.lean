import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Deterministic components of the row-edit concentration argument.
The stochastic high-confidence theorem additionally uses heat, fibers and concentration. -/
namespace CenteredRowEdits
open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The two centered columns may use different means. -/
theorem column_identity (f g : ι → ℝ) (a b : ℝ)
    (hf : ∑ i, (f i - a) = 0) (hg : ∑ i, (g i - b) = 0) :
    (∑ i, (f i - a)^2) - (∑ i, (g i - b)^2)
      = ∑ i, ((f i - a) + (g i - b)) * (f i - g i) := by
  have hz : ∑ i, (((f i - a) + (g i - b)) * (a-b)) = 0 := by
    rw [← sum_mul, sum_add_distrib, hf, hg]
    ring
  rw [← sum_sub_distrib]
  calc
    _ = ∑ i, (((f i-a)+(g i-b))*(f i-g i) - ((f i-a)+(g i-b))*(a-b)) := by
      apply sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [sum_sub_distrib,hz,sub_zero]

/-- Point heat bounds the squared Frobenius difference by the entrywise absolute
difference before projection; the factor two applies to both centered kernels. -/
theorem array_sensitivity (F G : κ → ι → ℝ) (a b : κ → ℝ) (L : ℝ)
    (hf : ∀ j, ∑ i, (F j i - a j) = 0) (hg : ∀ j, ∑ i, (G j i - b j) = 0)
    (hF : ∀ j i, |F j i-a j| ≤ L) (hG : ∀ j i, |G j i-b j| ≤ L) :
    |(∑ j, ∑ i, (F j i-a j)^2) - (∑ j, ∑ i, (G j i-b j)^2)|
        ≤ (2*L) * ∑ j, ∑ i, |F j i-G j i| := by
  rw [← sum_sub_distrib]
  simp_rw [column_identity _ _ _ _ (hf _) (hg _)]
  calc
    _ ≤ ∑ j, |∑ i, ((F j i-a j)+(G j i-b j))*(F j i-G j i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ i, |((F j i-a j)+(G j i-b j))*(F j i-G j i)| := by
      apply sum_le_sum
      intro j _
      exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ i, (2*L) * |F j i-G j i| := by
      apply sum_le_sum
      intro j _
      apply sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      calc
        _ ≤ |F j i-a j| + |G j i-b j| := abs_add_le _ _
        _ ≤ _ := by linarith [hF j i,hG j i]
    _ = _ := by simp_rw [← mul_sum]

section Coupling
variable {State Letter : Type*}

def run (f : State → Letter → State) (s : State) : List Letter → State
  | [] => s
  | a::w => run f (f s a) w

def avoids (D : Set State) (f : State → Letter → State) (s : State) : List Letter → Prop
  | [] => True
  | a::w => s ∉ D ∧ avoids D f (f s a) w

/-- Run the same word, using only the first table to test whether a source
belongs to an edited row. No intermediate mixed table is required. -/
theorem run_eq_of_avoids (D : Set State) (f g : State → Letter → State)
    (agree : ∀ s ∉ D, ∀ a, f s a = g s a) (w : List Letter) (s : State)
    (safe : avoids D f s w) : run f s w = run g s w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    obtain ⟨h0,h1⟩ := safe
    simp only [run]
    rw [← agree s h0 a]
    exact ih (f s a) h1

end Coupling
end CenteredRowEdits
