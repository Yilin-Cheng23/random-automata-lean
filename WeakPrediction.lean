import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! Finite suffix-weight moments and squared prediction gains.
These calculations concern a fixed suffix and independent fair comparison bits. -/
namespace WeakPrediction

/-- Average over h independent equality indicators, starting with the last bit. -/
def avg : ℕ → (List Bool → ℚ) → ℚ
  | 0, f => f []
  | h + 1, f =>
      (avg h (fun w => f (false :: w)) + avg h (fun w => f (true :: w))) / 2

/-- The finite projected weight gives an extra unit on full suffix agreement. -/
def weight : List Bool → ℚ
  | [] => 2
  | false :: _ => 1
  | true :: w => 1 + weight w

theorem avg_const (h : ℕ) (q : ℚ) : avg h (fun _ => q) = q := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [avg, ih]; ring

theorem avg_add (h : ℕ) (f g : List Bool → ℚ) :
    avg h (fun w => f w + g w) = avg h f + avg h g := by
  induction h generalizing f g with
  | zero => rfl
  | succ h ih =>
    simp only [avg]
    rw [ih (fun w => f (false :: w)) (fun w => g (false :: w)),
      ih (fun w => f (true :: w)) (fun w => g (true :: w))]
    ring

theorem first_moment (h : ℕ) : avg h weight = 2 := by
  induction h with
  | zero => rfl
  | succ h ih =>
    change (avg h (fun _ => 1) + avg h (fun w => 1 + weight w)) / 2 = 2
    rw [avg_add h (fun _ => 1) weight, avg_const, ih]
    norm_num

theorem second_moment (h : ℕ) :
    avg h (fun w => (weight w)^2) = 6 - 2 * (1/2 : ℚ)^h := by
  induction h with
  | zero => norm_num [avg, weight]
  | succ h ih =>
    change (avg h (fun _ => (1:ℚ)^2) + avg h (fun w => (1 + weight w)^2)) / 2 = _
    have poly : (fun w => (1 + weight w)^2) =
        (fun w => (1 + weight w) + (weight w + (weight w)^2)) := by
      funext w
      ring
    rw [poly, avg_add, avg_add, avg_add, avg_const, avg_const, first_moment, ih, pow_succ]
    ring

/-- Conditional squared loss of predicting q for a sign of mean v. -/
theorem brier_decomposition (q v : ℚ) :
    ((1+v)/2)*(q-1)^2 + ((1-v)/2)*(q+1)^2 =
      (q-v)^2 + 1-v^2 := by ring

/-- The optimal amplitude on opposite unanimous panels completes the square. -/
theorem unanimous_gain (signal mass amplitude : ℚ) (h : mass ≠ 0) :
    2*amplitude*signal-amplitude^2*mass =
    signal^2/mass-mass*(amplitude-signal/mass)^2 := by
  field_simp
  ring

/-- Critical odds when the two unanimous sign strings share the rare mass. -/
theorem rare_unanimous_value (mass ratio : ℚ) :
    mass*(ratio*mass/(2+ratio*mass)) =
        ratio*mass^2/(2+ratio*mass) := by
  ring

end WeakPrediction
