import AdjacentHistory

/-! Stable recovery of a scalar constant by commuting two unknown signed
filters. The proof is deterministic and finite. It covers repeated modes
and makes no assumption on the signs of the filter coefficients. -/
namespace BlindHistoryFilter
open Finset

private theorem signed_sum_error {ι : Type*} [Fintype ι]
    (a f : ι → ℝ) (c W ε : ℝ) (hε : 0 ≤ ε)
    (ha : ∑ i, a i = 1) (hW : ∑ i, |a i| ≤ W)
    (h : ∀ i, |f i - c| ≤ ε) :
    |(∑ i, a i * f i) - c| ≤ W * ε := by
  have eqn : (∑ i, a i * f i) - c = ∑ i, a i * (f i - c) := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, ha, one_mul]
  rw [eqn]
  calc
    _ ≤ ∑ i, |a i * (f i - c)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| * ε := by
      apply sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
    _ = (∑ i, |a i|) * ε := (sum_mul ..).symm
    _ ≤ W * ε := mul_le_mul_of_nonneg_right hW hε

/-- One matrix of moment observations, two mass-one filters and two
candidate constants. Input tolerances apply directly to the observed
matrix and so include both the sampling and truncation errors. -/
theorem certified_constants {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (w : κ → ℝ) (M : ι → κ → ℝ)
    (L θ A W τ δ : ℝ) (ht : 0 ≤ τ) (hd : 0 ≤ δ)
    (ha : ∑ i, a i = 1) (hw : ∑ j, w j = 1)
    (hA : ∑ i, |a i| ≤ A) (hW : ∑ j, |w j| ≤ W)
    (fit : ∀ i, |(∑ j, w j * M i j) - L| ≤ τ)
    (truth : ∀ j, |(∑ i, a i * M i j) - θ| ≤ δ) :
    |L - θ| ≤ A * τ + W * δ := by
  have h₁ := signed_sum_error a (fun i => ∑ j, w j * M i j)
    L A τ ht ha hA fit
  have h₂ := signed_sum_error w (fun j => ∑ i, a i * M i j)
    θ W δ hd hw hW truth
  have comm : (∑ i, a i * ∑ j, w j * M i j) =
      ∑ j, w j * ∑ i, a i * M i j := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro i _
    ring
  rw [← comm] at h₂
  rw [abs_sub_comm] at h₁
  exact (abs_sub_le L _ θ).trans (add_le_add h₁ h₂)

end BlindHistoryFilter
