import FourSourceCoefficient
import Mathlib.Analysis.SpecificLimits.Normed

/-! The two synchronously joined pairs in the binary variance calculation
contribute a finite sum with indices 0 through b, inclusive. -/
namespace CriticalWindowCoefficient
open Finset Filter Topology

def window (b : ℕ) : ℚ :=
  ∑ i ∈ range (b+1), ∑ j ∈ range (b+1), (1/2 : ℚ) ^ max i j

theorem finite_window (b : ℕ) :
    window b = 6 - (2*(b : ℚ)+5)*(1/2 : ℚ)^b := by
  rw [window, FourSourceCoefficient.coefficient, pow_succ]
  push_cast
  ring

theorem limit_six : Tendsto (fun b : ℕ => (window b : ℝ)) atTop (𝓝 6) := by
  have h₁ := tendsto_self_mul_const_pow_of_abs_lt_one (r := (1/2 : ℝ)) (by norm_num)
  have h₀ := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)
  have h : Tendsto (fun b : ℕ =>
      6 - (2 * ((b : ℝ)*(1/2 : ℝ)^b) + 5*(1/2 : ℝ)^b)) atTop (𝓝 6) := by
    simpa using ((tendsto_const_nhds (x := (6 : ℝ))).sub
      ((h₁.const_mul 2).add (h₀.const_mul 5)))
  convert h using 1
  funext b
  rw [finite_window]
  push_cast
  ring
end CriticalWindowCoefficient
