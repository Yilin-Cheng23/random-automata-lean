import Std

namespace OverlapWords

/-- The two length-d substrings in a block of length g+d start g positions apart. -/
def agrees {g d : Nat} (w : Fin (g+d) → Bool) : Prop :=
  ∀ j (hj : j < d), w ⟨j, by omega⟩ = w ⟨j+g, by omega⟩

def prefixBits {g d : Nat} (w : Fin (g+d) → Bool) (j : Fin g) : Bool :=
  w ⟨j.val, by omega⟩

def periodic {g d : Nat} (hg : 0 < g) (seed : Fin g → Bool) (j : Fin (g+d)) : Bool :=
  seed ⟨j.val % g, Nat.mod_lt _ hg⟩

theorem periodic_agrees {g d : Nat} (hg : 0 < g) (seed : Fin g → Bool) :
    agrees (periodic (d := d) hg seed) := by
  intro j hj
  simp [periodic]

theorem prefix_periodic {g d : Nat} (hg : 0 < g) (seed : Fin g → Bool) :
    prefixBits (periodic (d := d) hg seed) = seed := by
  funext j
  simp [prefixBits, periodic, Nat.mod_eq_of_lt j.isLt]

/-- Every agreeing block is uniquely reconstructed from its first g bits.
    Together with the previous two theorems this gives 2^g agreeing blocks out
    of 2^(g+d), including when the two substrings overlap. -/
theorem periodic_prefix {g d : Nat} (hg : 0 < g) (w : Fin (g+d) → Bool)
    (hw : agrees w) : periodic hg (prefixBits w) = w := by
  have h (j : Nat) : ∀ hj : j < g+d,
      w ⟨j % g, by have := Nat.mod_lt j hg; omega⟩ = w ⟨j,hj⟩ := by
    induction j using Nat.strongRecOn with
    | ind j ih =>
      intro hj
      by_cases top : j < g
      · simp [Nat.mod_eq_of_lt top]
      · let k := j-g
        have heq : j = k+g := by dsimp [k]; omega
        have hlt : k < j := by dsimp [k]; omega
        have hd : k < d := by omega
        have hyp := ih k hlt (by omega)
        have ties := hw k hd
        have hmod : j % g = k % g := by conv => lhs; rw [heq, Nat.add_mod_right]
        calc
          _ = w ⟨k % g, by have := Nat.mod_lt k hg; omega⟩ := by congr 1; exact Fin.ext hmod
          _ = w ⟨k, by omega⟩ := hyp
          _ = w ⟨k+g, by omega⟩ := ties
          _ = _ := by congr 1; exact Fin.ext heq.symm
  funext j
  exact h j j.isLt

end OverlapWords
