import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

/-! A sparse spanning family covers all fresh names on a nonzero first-letter
contrast. Together with the fork-rank inequality this gives the deterministic
three-returns-per-disjoint-pair bound. The probabilistic table exposure is
outside this module. -/
namespace MatchingContrast
open Finset
variable {X C : Type*} [DecidableEq X]

/-- Explicit finite linear combinations preserve the union of column
supports. The scalar type is rational because the endpoint contrasts are
integer vectors and their rank can be taken over the rationals. -/
theorem support_covered
    (basis : Finset C) (column : C → X → ℚ) (coeff : C → C → ℚ)
    (support : C → Finset X)
    (contains : ∀ b ∈ basis, ∀ x, column b x ≠ 0 → x ∈ support b)
    (spans : ∀ j x, column j x = ∑ b ∈ basis, coeff j b * column b x)
    {j : C} {x : X} (hx : column j x ≠ 0) :
    x ∈ basis.biUnion support := by
  classical
  by_contra hm
  have hzero : ∀ b ∈ basis, column b x = 0 := by
    intro b hb
    by_contra h
    exact hm (mem_biUnion.mpr ⟨b, hb, contains b hb x h⟩)
  apply hx
  rw [spans j x]
  exact sum_eq_zero (fun b hb => by rw [hzero b hb, mul_zero])

/-- First-round names belong either to cancelled raw comparisons or to
the union of supports of a contrast basis with two nonzero entries per
column. The input equalities count proposals at the two binary forks. -/
theorem three_returns
    (fresh cancelled : Finset X) (basis : Finset C) (support : C → Finset X)
    (k first later : ℕ)
    (cover : fresh ⊆ cancelled ∪ basis.biUnion support)
    (raw_equal : cancelled.card ≤ k)
    (sparse : ∀ b ∈ basis, (support b).card ≤ 2)
    (proposals : fresh.card + first = 4*k)
    (second_fork : 2*basis.card ≤ later) :
    3*k ≤ first+later := by
  classical
  have hu := card_union_le cancelled (basis.biUnion support)
  have hb := card_biUnion_le_card_mul basis support 2 sparse
  have hf := card_le_card cover
  omega

end MatchingContrast
