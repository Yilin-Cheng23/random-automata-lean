import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

/-! The finite deterministic induction separating survival ratios from mixing estimates. -/
namespace SurvivalCone

/-- If all entries at each of the first B times are comparable and a B-step update
preserves this order, the same constant works forever. -/
theorem all_times {ι : Type*} (surv : ℕ → ι → ℝ) (κ : ℝ) (B : ℕ) (hB : 0 < B)
    (hbase : ∀ t < B, ∀ i j, κ * surv t j ≤ surv t i)
    (hstep : ∀ t, (∀ i j, κ * surv t j ≤ surv t i) →
                    ∀ i j, κ * surv (t+B) j ≤ surv (t+B) i) :
    ∀ t i j, κ * surv t j ≤ surv t i := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases hlt : t < B
    · exact hbase t hlt
    · have hle : B ≤ t := Nat.le_of_not_gt hlt
      have hsmall : t-B < t := Nat.sub_lt (lt_of_lt_of_le hB hle) hB
      have h := hstep (t-B) (ih (t-B) hsmall)
      simpa only [Nat.sub_add_cancel hle] using h

/-- One-block comparison. The discrepancy between two normalized rows acts
on f at most b*sup(f), and each normalized expectation is at least κ*sup(f). -/
theorem one_block (κ a b upper u v si sj : ℝ)
    (_hk : 0 < κ) (ha : 0 ≤ a) (hb : b ≤ κ / 2) (hup : 0 ≤ upper)
    (hv : κ * upper ≤ v) (hu : v - b*upper ≤ u)
    (hsi : a ≤ si) (hsj : sj ≤ 1) (hvk : 0 ≤ v) :
    (a / 2) * (sj*v) ≤ si*u := by
  have hbu : b * upper ≤ (κ/2)*upper := mul_le_mul_of_nonneg_right hb hup
  have huv : v/2 ≤ u := by linarith
  have hu0 : 0 ≤ u := by linarith
  calc
    _ ≤ (a/2)*v := mul_le_mul_of_nonneg_left (by simpa using mul_le_mul_of_nonneg_right hsj hvk) (by linarith)
    _ = a*(v/2) := by ring
    _ ≤ a*u := mul_le_mul_of_nonneg_left huv ha
    _ ≤ si*u := mul_le_mul_of_nonneg_right hsi hu0

end SurvivalCone
