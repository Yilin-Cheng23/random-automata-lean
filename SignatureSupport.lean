import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Tests whether a prescribed finite signature occurs using the sign of a
weighted quadratic form. The probabilistic accuracy of the estimated moments
is a separate result. -/
namespace SignatureSupport
open Finset
noncomputable section
variable {ι τ E : Type*} [Fintype ι] [Fintype τ]
variable (V : ι → E → ℝ) (π : ι → ℝ) (off : τ → ι → ℝ)

def mismatch (i : ι) : ℝ := ∑ a, off a i

def mass (u : E) : ℝ := ∑ i, π i * (V i u)^2

def tested (a : τ) (u : E) : ℝ :=
  ∑ i, π i * (1 - 2 * off a i) * (V i u)^2

def statistic (u : E) : ℝ :=
  (∑ a, (mass V π u - tested V π off a u)/2) - mass V π u /2

theorem diagonal_form (u : E) :
    statistic V π off u = ∑ i, (mismatch off i - 1/2) * (π i * (V i u)^2) := by
  classical
  have hterm (a : τ) :
      (mass V π u - tested V π off a u)/2 = ∑ i, off a i * (π i * (V i u)^2) := by
    unfold mass tested
    rw [← sum_sub_distrib, div_eq_mul_inv, sum_mul]
    apply sum_congr rfl
    intro i _
    ring
  unfold statistic
  simp_rw [hterm]
  rw [sum_comm]
  unfold mass mismatch
  rw [div_eq_mul_inv, sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [sub_mul, sum_mul]
  ring

theorem absent_nonneg (hπ : ∀ i, 0 ≤ π i) (hn : ∀ i, 1 ≤ mismatch off i)
    (u : E) : 0 ≤ statistic V π off u := by
  rw [diagonal_form]
  apply sum_nonneg
  intro i _
  exact mul_nonneg (by linarith [hn i]) (mul_nonneg (hπ i) (sq_nonneg _))

theorem realized_witness (i : ι) (u : E) (hz : mismatch off i = 0)
    (hit : V i u = 1) (miss : ∀ j, j ≠ i → V j u = 0) :
    statistic V π off u = -π i / 2 := by
  classical
  rw [diagonal_form, sum_eq_single i]
  · rw [hz, hit]
    ring
  · intro j _ hji
    simp [miss j hji]
  · simp

/-- A uniform quadratic-form perturbation and a positive diagonal cushion
separate absence from a realized pattern, on any normalized test direction. -/
theorem cushion_absent {a ah η : ℝ} (ha : 0 ≤ a) (hη : 0 < η)
    (he : |ah-a| ≤ η/2) : 0 < ah+η := by
  have := (abs_le.mp he).1
  linarith

theorem cushion_realized {a ah η : ℝ} (ha : a ≤ -2*η) (hη : 0 < η)
    (he : |ah-a| ≤ η/2) : ah+η < 0 := by
  have := (abs_le.mp he).2
  linarith

end
end SignatureSupport
