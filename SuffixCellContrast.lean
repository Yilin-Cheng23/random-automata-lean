import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Finite observable contrasts for an exceptional closed action.
The field identity and telescoping are deterministic. The random-table
estimates that make each prefix regression learnable are separate inputs. -/
namespace SuffixCellContrast
open Finset
variable {ι : Type*}

/-- Each sum is an unnormalized weighted mass on its cell. -/
noncomputable def contrast (fine coarse fineMass coarseMass : ℝ) : ℝ :=
  fine - (fineMass / coarseMass) * coarse

theorem conditional_increment (fine coarse fineMass coarseMass : ℝ)
    (hf : fineMass ≠ 0) (hc : coarseMass ≠ 0) :
    contrast fine coarse fineMass coarseMass / fineMass =
      fine / fineMass - coarse / coarseMass := by
  unfold contrast
  field_simp

/-- If the terminal response has common mean z on the coarse cell,
the transformed observation has exactly zero conditional mean. -/
theorem vanishes_on_coarse_value (fineMass coarseMass z : ℝ)
    (hc : coarseMass ≠ 0) :
    contrast (fineMass*z) (coarseMass*z) fineMass coarseMass = 0 := by
  unfold contrast
  field_simp
  ring

theorem constant_cell_sum (u : Finset ι) (p h : ι → ℝ) (z : ℝ)
    (hz : ∀ i ∈ u, h i = z) :
    ∑ i ∈ u, p i * h i = (∑ i ∈ u, p i) * z := by
  rw [sum_mul]
  exact sum_congr rfl (fun i hi => by rw [hz i hi])

theorem reconstruct (M : ℕ → ℝ) (m : ℕ) :
    M 0 + ∑ j ∈ range m, (M (j+1)-M j) = M m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [sum_range_succ, ← add_assoc, ih]
      ring

end SuffixCellContrast
