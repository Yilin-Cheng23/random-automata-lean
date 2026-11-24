import AdjacentHistory
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
Algebra of common-history observations. The same deterministic transition is
applied to both coordinates; independence is used only for the draws from
the distribution at the start of a history.
-/
namespace CommonWordMoments
open Finset

variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι]

def mean (μ g : ι → ℝ) : ℝ := ∑ i, μ i * g i

def joint [Fintype κ] (p : κ → ℝ) (μ : κ → ι → ℝ) (i j : ι) : ℝ :=
  ∑ w, p w * (μ w i * μ w j)

omit [DecidableEq ι] in
theorem joint_marginal [Fintype κ] (p : κ → ℝ) (μ : κ → ι → ℝ)
    (hμ : ∀ w, ∑ j, μ w j = 1) (i : ι) :
    ∑ j, joint p μ i j = ∑ w, p w * μ w i := by
  unfold joint
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  simp only [← mul_assoc, ← mul_sum, hμ, mul_one]

omit [DecidableEq ι] in
theorem joint_tests [Fintype κ] (p : κ → ℝ) (μ : κ → ι → ℝ) (g h : ι → ℝ) :
    ∑ i, ∑ j, joint p μ i j * (g i * h j) =
      ∑ w, p w * (mean (μ w) g * mean (μ w) h) := by
  unfold joint mean
  simp_rw [sum_mul]
  conv_lhs =>
    arg 2; intro i; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  simp only [mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

/-- The transfer on a fiber of the actual deterministic transition table. -/
def push (f : ι → ι) (μ : ι → ℝ) (y : ι) : ℝ :=
  ∑ i, if f i=y then μ i else 0

theorem push_total (f : ι → ι) (μ : ι → ℝ) :
    ∑ y, push f μ y = ∑ i, μ i := by
  unfold push
  rw [sum_comm]
  simp

theorem push_mean (f : ι → ι) (μ g : ι → ℝ) :
    mean (push f μ) g = mean μ (fun i => g (f i)) := by
  unfold mean push
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp_rw [ite_mul, zero_mul]
  simp

/-- The two coordinates use the very same letter. -/
def pairPush (f : ι → ι) (S : ι → ι → ℝ) (i j : ι) : ℝ :=
  ∑ k, ∑ l, if f k=i ∧ f l=j then S k l else 0

def killed (S : ι → ι → ℝ) (i j : ι) : ℝ :=
  if i=j then 0 else S i j

theorem common_kill (f : ι → ι) (S : ι → ι → ℝ) (i j : ι) :
    killed (pairPush f S) i j = killed (pairPush f (killed S)) i j := by
  by_cases hij : i=j
  · simp [killed, hij]
  simp only [killed, hij, ite_false, pairPush]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro l _
  by_cases hkl : k=l
  · subst l
    have h : ¬ (f k=i ∧ f k=j) := fun ⟨a,b⟩ => hij (a.symm.trans b)
    simp [h]
  · simp [hkl]

/-- From two equal rows of marginals to the diagonal test estimator, for
arbitrary finite empirical-history ensembles. -/
theorem history_diagonal [Fintype κ] [Fintype α] (p : κ → ℝ) (p' : α → ℝ)
    (μ : κ → ι → ℝ) (μ' : α → ι → ℝ) (π : ι → ℝ) (x : ℝ) (hx : x < 1)
    (rows : ∀ w, ∑ i, μ w i = 1) (rows' : ∀ w, ∑ i, μ' w i = 1)
    (stat : ∀ i, ∑ w, p w * μ w i = π i) (stat' : ∀ i, ∑ w, p' w * μ' w i = π i) :
    (∑ i, ∑ j, |(joint p' μ' i j - x * joint p μ i j)/(1-x) -
      (if j=i then π i else 0)|) ≤
      2 * (∑ i, ∑ j ∈ univ.erase i, |joint p' μ' i j - x * joint p μ i j|)/(1-x) := by
  apply AdjacentHistory.adjacent_error _ _ π x hx
  · intro i
    rw [joint_marginal _ _ rows i, stat]
  · intro i
    rw [joint_marginal _ _ rows' i, stat']

end CommonWordMoments
