import PredictiveFolding

/-! Output indistinguishability of hidden closed actions, and the exact
last-entry discrepancy of the two clone orientations. -/
namespace HiddenAbsorber
open PredictiveFolding

variable {E I A O : Type*}

/-- Forget the internal name once the path has entered the closed set. -/
def collapse : Sum E I → Option E
  | .inl x => some x
  | .inr _ => none

def install (outside : E → A → Sum E I) (inside : I → A → I) :
    Sum E I → A → Sum E I
  | .inl x, a => outside x a
  | .inr y, a => .inr (inside y a)

def collapsedStep (outside : E → A → Sum E I) : Option E → A → Option E
  | some x, a => collapse (outside x a)
  | none, _ => none

theorem collapse_run (outside : E → A → Sum E I) (inside : I → A → I)
    (s : Sum E I) (w : List A) :
    collapse (run (install outside inside) s w) =
      run (collapsedStep outside) (collapse s) w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    simp only [run]
    rw [ih]
    cases s <;> rfl

theorem all_terminal_outputs_agree (outside : E → A → Sum E I)
    (first second : I → A → I) (readout : Option E → O)
    (s : Sum E I) (w : List A) :
    readout (collapse (run (install outside first) s w)) =
      readout (collapse (run (install outside second) s w)) := by
  rw [collapse_run, collapse_run]

/-- At a shared interior name the two clones point to opposite
absorbers on the following input bit. -/
def entersOn (outside : E → A → Sum E Bool) (last : A) : Option E → Prop
  | none => False
  | some x => collapse (outside x last) = none

private theorem clone_step (outside : E → A → Sum E Bool) (x y : Sum E Bool)
    (last : A) (hy : collapse y = collapse x) :
    (¬ (install outside (fun _ _ => false) x last = .inr false ↔
        install outside (fun _ _ => true) y last = .inr true)) ↔
    entersOn outside last (collapse x) := by
  cases x with
  | inr u =>
    cases y <;> simp_all [collapse, install, entersOn]
  | inl u =>
    cases y with
    | inr v => simp [collapse] at hy
    | inl v =>
      have h : v = u := by simpa [collapse] using hy
      subst v
      cases hz : outside u last with
      | inl v => simp [install, collapse, entersOn, hz]
      | inr b => cases b <;> simp [install, collapse, entersOn, hz]

theorem clone_last_entry (outside : E → A → Sum E Bool)
    (s : Sum E Bool) (front : List A) (last : A) :
    (¬ ((run (install outside (fun _ _ => false)) s (front ++ [last]) = .inr false) ↔
        (run (install outside (fun _ _ => true)) s (front ++ [last]) = .inr true))) ↔
    entersOn outside last (run (collapsedStep outside) (collapse s) front) := by
  simp only [run_append, run]
  rw [← collapse_run outside (fun _ _ => false) s front]
  apply clone_step
  rw [collapse_run, collapse_run]

end HiddenAbsorber
