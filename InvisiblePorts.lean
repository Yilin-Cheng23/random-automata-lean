import PredictiveFolding

/-! Local deterministic facts about acceptance tests at lengths too short
to pass from the prescribed start through an edited cell to a marked name.
The random graph and its exposure filtration are outside this module. -/
namespace InvisiblePorts
open PredictiveFolding

variable {S A : Type*}

theorem short_tests_agree (T U : S → A → S) (s marker : S) (d l : ℕ)
    (access : ∀ (u : List A) (a : A),
      T (run T s u) a ≠ U (run T s u) a → d ≤ u.length)
    (absent : ∀ (x : S) (a : A), T x a ≠ U x a →
      ∀ v : List A, v.length ≤ l →
        run T (T x a) v ≠ marker ∧ run U (U x a) v ≠ marker)
    (w : List A) (hw : w.length ≤ d+l+1) :
    run T s w = marker ↔ run U s w = marker := by
  have aux (v : List A) : ∀ (u : List A),
      run T s u = run U s u → u.length+v.length ≤ d+l+1 →
      (run T (run T s u) v = marker ↔ run U (run U s u) v = marker) := by
    induction v with
    | nil => intro u hu _; simpa [run] using (congrArg (fun x => x = marker) hu).to_iff
    | cons a v ih =>
      intro u hu hlen
      by_cases hstep : T (run T s u) a = U (run T s u) a
      · have heq : run T s (u++[a]) = run U s (u++[a]) := by
          simpa [run_append, run, ← hu] using hstep
        have hlen' : (u++[a]).length+v.length ≤ d+l+1 := by
          simp only [List.length_cons, List.length_append, List.length_nil] at *
          omega
        simpa [run_append, run] using ih (u++[a]) heq hlen'
      · have hd := access u a hstep
        have hv : v.length ≤ l := by simp only [List.length_cons] at hlen; omega
        have hn := absent (run T s u) a hstep v hv
        simp [run, ← hu, hn.1, hn.2]
  simpa [run] using aux w [] rfl (by simpa using hw)

theorem eventual_heads_agree {O : Type*} (T U : S → A → S)
    (readout : S → O) (s y z : S) (p r : List A) (H : ℕ)
    (agree : ∀ w : List A, H ≤ w.length → readout (run T s w) = readout (run U s w))
    (py : run T s p = y) (pz : run U s p = z)
    (rz : run T s r = z) (rz' : run U s r = z)
    (w : List A) (hw : H ≤ w.length) :
    readout (run T y w) = readout (run T z w) := by
  have a := agree (p++w) (by simp only [List.length_append]; omega)
  have b := agree (r++w) (by simp only [List.length_append]; omega)
  rw [run_append, run_append, py, pz] at a
  rw [run_append, run_append, rz, rz'] at b
  exact a.trans b.symm

end InvisiblePorts
