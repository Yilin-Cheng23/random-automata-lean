import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring

/-! Exact signed collision identity, before averaging the transition table.
    X indexes state names, W words, and c contains arbitrary rational weights. -/
namespace SignedWalshCollision
open Finset

variable {X W I : Type*} [Fintype X] [DecidableEq X] [Fintype W] [Fintype I]

def dot (a b : X → ℚ) : ℚ := ∑ y, a y * b y

def row (T : W → X → X) (c : W → ℚ) (x y : X) : ℚ :=
  ∑ w, if y = T w x then c w else 0

def collisions (T : W → X → X) (c : W → ℚ) (x z : X) : ℚ :=
  ∑ u, ∑ v, if T u x = T v z then c u * c v else 0

omit [DecidableEq X] in
private theorem sum_left (a : I → X → ℚ) (b : X → ℚ) :
    dot (fun y => ∑ i, a i y) b = ∑ i, dot (a i) b := by
  simp only [dot, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq X] in
private theorem sum_right (a : X → ℚ) (b : I → X → ℚ) :
    dot a (fun y => ∑ i, b i y) = ∑ i, dot a (b i) := by
  simp only [dot, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem row_product (T : W → X → X) (c : W → ℚ) (x z : X) :
    dot (row T c x) (row T c z) = collisions T c x z := by
  unfold row collisions
  rw [sum_left]
  apply Finset.sum_congr rfl
  intro u _
  rw [sum_right]
  apply Finset.sum_congr rfl
  intro v _
  classical
  by_cases h : T u x = T v z
  · simp [dot, ite_mul, mul_ite, h]
  · simp [dot, ite_mul, mul_ite, h, Ne.symm h]

omit [DecidableEq X] in
private theorem sub_left (a b c : X → ℚ) :
    dot (fun y => a y - b y) c = dot a c - dot b c := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq X] in
private theorem sub_right (a b c : X → ℚ) :
    dot a (fun y => b y - c y) = dot a b - dot a c := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq X] in
private theorem scale_right (a b : X → ℚ) (k : ℚ) :
    dot a (fun y => k*b y) = k*dot a b := by
  simp only [dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

omit [DecidableEq X] in
private theorem scale_left (a b : X → ℚ) (k : ℚ) :
    dot (fun y => k*a y) b = k*dot a b := by
  simp only [dot, Finset.mul_sum, mul_assoc]

/-- The root diagonal and the independently sampled root pair use the
same family of terminal maps, and weights are not restricted in sign. -/
theorem centered_collision (T : W → X → X) (c : W → ℚ) (a : X → ℚ)
    (ha : ∀ y, (∑ x, row T c x y) = (Fintype.card X : ℚ) * a y) :
    (Fintype.card X : ℚ) *
        (∑ x, dot (fun y => row T c x y - a y) (fun y => row T c x y - a y)) =
      (Fintype.card X : ℚ) * (∑ x, collisions T c x x) -
        ∑ x, ∑ z, collisions T c x z := by
  have hf : (fun y => ∑ x, row T c x y) = fun y => (Fintype.card X : ℚ)*a y :=
    funext ha
  have h1 : (∑ x, dot (row T c x) a) = (Fintype.card X : ℚ)*dot a a := by
    rw [← sum_left, hf, scale_left]
  have h2 : (∑ x, dot a (row T c x)) = (Fintype.card X : ℚ)*dot a a := by
    rw [← sum_right, hf, scale_right]
  have h3 (x : X) : (∑ z, dot (row T c x) (row T c z)) =
      (Fintype.card X : ℚ)*dot (row T c x) a := by
    rw [← sum_right, hf, scale_right]
  simp only [← row_product, sub_left, sub_right, Finset.sum_sub_distrib, h3,
    ← Finset.mul_sum, h1, h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end SignedWalshCollision
