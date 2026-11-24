import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Finite likelihood and Hamming comparisons for terminal experiments.
These identities are conditional on a supplied test design. -/
namespace OriginExperiment

def loss (reported prediction : Bool) : ℤ := if reported = prediction then 0 else 1

theorem hamming_gap_antitone {ι : Type*} (tests : Finset ι)
    (truth other light heavy : ι → Bool)
    (nested : ∀ i ∈ tests, light i = true → heavy i = true) :
    (∑ i ∈ tests, (loss ((truth i).xor (heavy i)) (other i)
       - loss ((truth i).xor (heavy i)) (truth i))) ≤
     ∑ i ∈ tests, (loss ((truth i).xor (light i)) (other i)
       - loss ((truth i).xor (light i)) (truth i)) := by
  apply Finset.sum_le_sum
  intro i hi
  have hn := nested i hi
  cases ha : truth i <;> cases hb : other i <;>
    cases hc : light i <;> cases hd : heavy i <;>
    simp_all [loss, Bool.xor]

theorem mean_likelihood_ratio (a x v z : ℝ)
    (hp : 1 + a*z ≠ 0) (hm : 1 - a*z ≠ 0) :
    ((1+a*x)*(1+a*v))/(2*(1+a*z)) +
      ((1-a*x)*(1-a*v))/(2*(1-a*z)) =
    1 + a^2*(x-z)*(v-z)/(1-a^2*z^2) := by
  have hd : 1-a^2*z^2 = (1+a*z)*(1-a*z) := by ring
  rw [hd]
  field_simp
  ring

end OriginExperiment
