import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite estimates for the uniform deletion lemma. The table, the deleted
set and the common letter are fixed in the one-step identity. -/
namespace DeletionRootGap

/-- Count ordered starts that can both visit a forbidden name on a specified
coordinate and meet at the terminal step of a fixed word. For each of the
eligible first starts the second must belong to one terminal fiber. -/
theorem visitJoinCount {S : Type*} (eligible : Finset S)
    (partners : S → Finset S) (s M : ℕ) (he : eligible.card ≤ s * M)
    (hf : ∀ i ∈ eligible, (partners i).card ≤ M) :
    (∑ i ∈ eligible, (partners i).card) ≤ s * M ^ 2 := by
  calc
    _ ≤ ∑ _i ∈ eligible, M := Finset.sum_le_sum hf
    _ = eligible.card * M := by simp
    _ ≤ (s * M) * M := Nat.mul_le_mul_right M he
    _ = _ := by ring

/-- A pointwise approximation of survival controls the total deficit
of the right eigenfunction by the total chance of a visit and the row error. -/
theorem totalDeficit {S : Type*} (states : Finset S) (H survival : S → ℝ)
    (e : ℝ) (he : 0 ≤ e) (hs : ∀ y ∈ states, survival y ≤ 1)
    (hr : ∀ y ∈ states, survival y ≤ H y + e) :
    (∑ y ∈ states, max (1 - H y) 0) ≤
      (∑ y ∈ states, (1 - survival y)) + states.card * e := by
  calc
    _ ≤ ∑ y ∈ states, ((1 - survival y) + e) := by
      apply Finset.sum_le_sum
      intro y hy
      exact max_le (by linarith [hr y hy]) (by linarith [hs y hy])
    _ = _ := by simp [Finset.sum_add_distrib]

/-- Total lost endpoint weight when the meeting count per name is capped. -/
theorem endpointDeficit {S : Type*} (states : Finset S)
    (hits deficit : S → ℝ) (cap : ℝ)
    (hc : ∀ y ∈ states, hits y ≤ cap) (hd : ∀ y ∈ states, 0 ≤ deficit y) :
    (∑ y ∈ states, hits y * deficit y) ≤ cap * ∑ y ∈ states, deficit y := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_right (hc y hy) (hd y hy)

/-- Decomposing one common-letter step into a live distinct pair, a safe
meeting, or an entrance into the deleted set by just one coordinate. -/
theorem oneLetter {S : Type*} [DecidableEq S] (B : Set S)
    [DecidablePred (· ∈ B)] (H : S → ℝ) (hz : ∀ x ∈ B, H x = 0) (x y : S) :
    H x + H y =
      (if x ∉ B ∧ y ∉ B ∧ x ≠ y then H x + H y else 0) +
      2 * (if x ∉ B ∧ x = y then H x else 0) +
      (if x ∈ B then H y else 0) + (if y ∈ B then H x else 0) := by
  by_cases he : x = y
  · subst y
    by_cases hx : x ∈ B <;> simp [hx, hz, two_mul]
  · by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;> simp [he, hx, hy, hz]

/-- Averaging the exact balance under the left Perron probability leaves
a nonnegative one-sided entrance term. A positive flux forces a gap. -/
theorem rootGap (σ τ phi flux entrance lo hi : ℝ)
    (balance : (σ - τ) * phi = 2 * flux + entrance)
    (hphi : 0 ≤ phi) (hcap : phi ≤ 2 * hi) (hhi : 0 < hi)
    (hflux : lo ≤ flux) (hlo : 0 < lo) (he : 0 ≤ entrance) :
    lo / hi ≤ σ - τ := by
  have hprod : 0 < (σ - τ) * phi := by linarith
  have hgap : 0 ≤ σ - τ := by
    by_contra! hn
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hn.le hphi)) hprod
  have h := mul_le_mul_of_nonneg_left hcap hgap
  apply (div_le_iff₀ hhi).2
  nlinarith

open Filter Topology in
/-- Applied to any sequence of admissible deletions, the two scalar
limits and the finite flux inequality imply the unit asymptotic floor.
Here flux and gap have already been multiplied by the state count. -/
theorem scaledGapFloor (flux hi gap : ℕ → ℝ)
    (hf : Tendsto flux atTop (𝓝 1)) (hh : Tendsto hi atTop (𝓝 1))
    (hfinite : ∀ᶠ n in atTop, flux n / hi n ≤ gap n)
    (c : ℝ) (hc : c < 1) : ∀ᶠ n in atTop, c ≤ gap n := by
  have hr : Tendsto (fun n => flux n / hi n) atTop (𝓝 1) := by
    simpa [Pi.div_def] using hf.div hh (one_ne_zero : (1 : ℝ) ≠ 0)
  exact ((hr.eventually_const_le hc).and hfinite).mono fun _ h => h.1.trans h.2

/-- The scalar balance at empty deletion has unit single-walk root,
two units of coordinate mass, and zero one-sided entrance flux. -/
theorem emptyBalance (τ flux : ℝ) (balance : (1 - τ) * 2 = 2 * flux + 0) :
    1 - τ = flux := by linarith

open Filter Topology in
/-- A common asymptotic lower bound, specialized to the empty deletion,
cannot have a larger leading constant than its normalized gap limit. -/
theorem emptySharpness (scaledEmpty lower : ℕ → ℝ) (c : ℝ)
    (hempty : Tendsto scaledEmpty atTop (𝓝 1))
    (hlower : Tendsto lower atTop (𝓝 c))
    (huniform : ∀ᶠ n in atTop, lower n ≤ scaledEmpty n) : c ≤ 1 :=
  le_of_tendsto_of_tendsto hlower hempty huniform

end DeletionRootGap
