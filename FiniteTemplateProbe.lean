import Mathlib.Computability.DFA
import Mathlib.Data.Nat.Find

/-! Short words suffice to distinguish any two finite terminal templates.
The application with two states tests the empty word and all words of
length at most three. -/
namespace FiniteTemplateProbe
universe u v
variable {α : Type u} {σ τ : Type v}

theorem short_access [Fintype σ] (M : DFA α σ) (s : σ) (word : List α) :
    ∃ v : List α, v.length < Fintype.card σ ∧ M.evalFrom s v = M.evalFrom s word := by
  classical
  let goal := M.evalFrom s word
  let Good := fun l : ℕ => ∃ v : List α, v.length = l ∧ M.evalFrom s v = goal
  have h : ∃ l, Good l := ⟨word.length, word, rfl, rfl⟩
  obtain ⟨v, hv, he⟩ := Nat.find_spec h
  refine ⟨v, ?_, he⟩
  by_contra! hlong
  obtain ⟨q, a, b, c, habc, _, hb, haq, _, hqc⟩ := M.evalFrom_split hlong he
  have hshort : Good (a ++ c).length := by
    exact ⟨a ++ c, rfl, by rw [M.evalFrom_of_append, haq, hqc]⟩
  have hmin := Nat.find_min' h hshort
  rw [← hv, habc] at hmin
  have hpos : 0 < b.length := List.length_pos_iff.mpr hb
  simp only [List.length_append] at hmin
  omega

theorem pair_eval (M : DFA α σ) (N : DFA α τ) (s : σ) (t : τ) (word : List α) :
    (M.inter N).evalFrom (s,t) word = (M.evalFrom s word, N.evalFrom t word) := by
  induction word generalizing s t with
  | nil => rfl
  | cons a w ih =>
    simp only [DFA.evalFrom_cons, DFA.inter_step]
    exact ih _ _

theorem complete_probes [Fintype σ] [Fintype τ] (M : DFA α σ) (N : DFA α τ)
    (s : σ) (t : τ)
    (probes : ∀ w : List α, w.length < Fintype.card σ * Fintype.card τ →
      (M.evalFrom s w ∈ M.accept ↔ N.evalFrom t w ∈ N.accept)) :
    ∀ w : List α, (M.evalFrom s w ∈ M.accept ↔ N.evalFrom t w ∈ N.accept) := by
  intro w
  obtain ⟨v, hv, he⟩ := short_access (M.inter N) (s,t) w
  rw [Fintype.card_prod] at hv
  simp only [pair_eval, Prod.mk.injEq] at he
  simpa [he.1, he.2] using probes v hv

end FiniteTemplateProbe
