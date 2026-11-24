import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Quantitative row separation from the explicit dual tests.
This is the deterministic margin step of the lifted-suffix proof. -/
namespace DualSeparation
open Finset
noncomputable section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Apply a dual test at a largest coefficient. The omitted-coordinate
error is explicitly bounded by the full number of rows times its tolerance. -/
theorem max_coeff_margin (v : ι → E) (c : ι → E →L[ℝ] ℝ)
    (a : ι → ℝ) (i : ι) (η M : ℝ)
    (ht : ∀ j, |a j| ≤ |a i|) (hη : 0 ≤ η)
    (hdiag : c i (v i) = 1)
    (hoff : ∀ j, j ≠ i → |c i (v j)| ≤ η)
    (hnorm : ‖c i‖ ≤ M)
    (hsmall : (Fintype.card ι : ℝ) * η ≤ 1/2) :
    |a i| / 2 ≤ M * ‖∑ j, a j • v j‖ := by
  classical
  let t := univ.erase i
  have hr : |∑ j ∈ t, a j * c i (v j)| ≤ (Fintype.card ι : ℝ) * η * |a i| := by
    calc
      _ ≤ ∑ j ∈ t, |a j * c i (v j)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ t, |a i| * η := by
        apply sum_le_sum
        intro j hj
        have hji := (mem_erase.mp hj).1
        rw [abs_mul]
        exact mul_le_mul (ht j) (hoff j hji) (abs_nonneg _) (abs_nonneg _)
      _ = (t.card : ℝ) * (|a i| * η) := by simp
      _ ≤ (Fintype.card ι : ℝ) * (|a i| * η) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ t)
          (mul_nonneg (abs_nonneg _) hη)
      _ = _ := by ring
  have hsum : c i (∑ j, a j • v j) = (∑ j ∈ t, a j * c i (v j)) + a i := by
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← sum_erase_add _ _ (mem_univ i)]
    simp [t,hdiag]
  have hbound : |c i (∑ j, a j • v j)| ≤ M * ‖∑ j, a j • v j‖ := by
    exact le_trans ((c i).le_opNorm _) (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
  have htri : |a i| ≤ |c i (∑ j, a j • v j)| + |∑ j ∈ t, a j * c i (v j)| := by
    rw [hsum]
    calc
      _ = |((∑ j ∈ t, a j * c i (v j)) + a i) - (∑ j ∈ t, a j * c i (v j))| := by ring_nf
      _ ≤ _ := abs_sub _ _
  have hsmall' := mul_le_mul_of_nonneg_right hsmall (abs_nonneg (a i))
  linarith

end
end DualSeparation
