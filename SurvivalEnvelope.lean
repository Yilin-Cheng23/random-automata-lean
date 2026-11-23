import Std

/-! Deterministic comparison steps in the shared-word meeting-time proof.
    Finite-time survival probabilities and comparison parameters here are rational.
    The random-table estimates supplying the recurrence hypotheses are separate. -/

namespace SurvivalEnvelope

/-- A two-step loss bound propagates a lower bound on successive block ratios.
    Multiplicative form also covers zero survival, without dividing by it. -/
theorem blockRatios (s : Nat → Rat) (theta lam loss : Rat)
    (nonnegative : ∀ j, 0 ≤ s j)
    (hparam : theta ≤ lam) (hlam : lam ≤ 1)
    (hbudget : loss ≤ (1 - lam) * theta)
    (hstart : theta * s 0 ≤ s 1)
    (hdelay : ∀ j, s (j+1) - loss * s j ≤ s (j+2)) :
    ∀ j, lam * s (j+1) ≤ s (j+2) := by
  have step (j : Nat) (prev : theta * s j ≤ s (j+1)) :
      lam * s (j+1) ≤ s (j+2) := by
    have h1 := Rat.mul_le_mul_of_nonneg_right hbudget (nonnegative j)
    have h2 := Rat.mul_le_mul_of_nonneg_left prev
      (show (0 : Rat) ≤ 1 - lam by grind)
    have h3 := hdelay j
    grind
  intro j
  induction j with
  | zero => exact step 0 hstart
  | succ j ih =>
    apply step (j+1)
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hparam (nonnegative (j+1))) ih

/-- An exponential upper barrier follows from any supersolution for the delayed
    upper recurrence. The two lag indices must be strictly earlier. -/
theorem upperBarrier (q g : Nat → Rat) (prev lag : Nat → Nat)
    (burn : Nat) (a b : Rat) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hinit : ∀ t, t < burn → q t ≤ g t)
    (hp : ∀ t, burn ≤ t → prev t < t)
    (hl : ∀ t, burn ≤ t → lag t < t)
    (hdelay : ∀ t, burn ≤ t → q t ≤ a * q (prev t) + b * q (lag t))
    (hbarrier : ∀ t, burn ≤ t → a * g (prev t) + b * g (lag t) ≤ g t) :
    ∀ t, q t ≤ g t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases early : t < burn
    · exact hinit t early
    · have late : burn ≤ t := by omega
      have h1 := Rat.mul_le_mul_of_nonneg_left (ih (prev t) (hp t late)) ha
      have h2 := Rat.mul_le_mul_of_nonneg_left (ih (lag t) (hl t late)) hb
      have h3 := hdelay t late
      have h4 := hbarrier t late
      grind

end SurvivalEnvelope
