import Mathlib.Data.List.Basic

/-! Deterministic state-folding with transition agreement after a fixed
number of letters. The two statements about random-table probabilities
and accepting-mask probabilities are separate mathematical estimates. -/
namespace PredictiveFolding

variable {S A : Type*}

def run (T : S → A → S) : S → List A → S
  | x, [] => x
  | x, a :: w => run T (T x a) w

@[simp] theorem run_append (T : S → A → S) (x : S) (v w : List A) :
    run T x (v ++ w) = run T (run T x v) w := by
  induction v generalizing x with
  | nil => rfl
  | cons a v ih => exact ih (T x a)

/-- Equality of physical endpoints after every word of this length. -/
def Folds (T : S → A → S) (h : ℕ) (x y : S) : Prop :=
  ∀ w : List A, w.length = h → run T x w = run T y w

theorem folds_zero (T : S → A → S) (x y : S) :
    Folds T 0 x y ↔ x = y := by
  constructor
  · intro h
    exact h [] rfl
  · rintro rfl w _
    rfl

theorem next (T : S → A → S) (h : ℕ) (x y : S) :
    Folds T (h+1) x y ↔ ∀ a, Folds T h (T x a) (T y a) := by
  constructor
  · intro H a w hw
    exact H (a :: w) (by simp [hw])
  · intro H w hw
    cases w with
    | nil => simp at hw
    | cons a v =>
      apply H a v
      simpa using hw

theorem monotone_step (T : S → A → S) (h : ℕ) (x y : S)
    (H : Folds T h x y) : Folds T (h+1) x y := by
  induction h generalizing x y with
  | zero =>
    have he := (folds_zero T x y).mp H
    subst y
    intro w _
    rfl
  | succ h ih =>
    apply (next T (h+1) x y).mpr
    intro a
    exact ih (T x a) (T y a) ((next T h x y).mp H a)

theorem right_congruence (T : S → A → S) (h : ℕ) (x y : S)
    (H : Folds T h x y) (a : A) : Folds T h (T x a) (T y a) :=
  (next T h x y).mp (monotone_step T h x y H) a

/-- A stationary partition at two successive depths is stationary thereafter. -/
theorem stabilization (T : S → A → S) (h : ℕ)
    (fixed : ∀ x y, Folds T (h+1) x y ↔ Folds T h x y) :
    ∀ k x y, Folds T (h+k) x y ↔ Folds T h x y := by
  intro k
  induction k with
  | zero => intro x y; rfl
  | succ k ih =>
    intro x y
    calc
      Folds T (h+(k+1)) x y ↔ ∀ a, Folds T (h+k) (T x a) (T y a) :=
        next T (h+k) x y
      _ ↔ ∀ a, Folds T h (T x a) (T y a) := forall_congr' (fun a => ih (T x a) (T y a))
      _ ↔ Folds T (h+1) x y := (next T h x y).symm
      _ ↔ Folds T h x y := fixed x y

theorem terminal_readout {O : Type*} (T : S → A → S) (b : S → O)
    (h : ℕ) (x y : S) (H : Folds T h x y) (v : List A) (hv : v.length = h) :
    b (run T x v) = b (run T y v) := congrArg b (H v hv)

end PredictiveFolding
