import Mathlib.Data.List.Basic

/-! One identification during a fresh-cell exposure generates only its
right extensions. This module checks the deterministic word classification. -/
namespace SinglePrefixRelation

variable {A : Type*}

/-- The equivalence closure of replacing the initial prefix p by q, or back. -/
inductive Related (p q : List A) : List A → List A → Prop where
  | refl (x) : Related p q x x
  | move (w) : Related p q (p ++ w) (q ++ w)
  | symm {x y} : Related p q x y → Related p q y x
  | trans {x y z} : Related p q x y → Related p q y z → Related p q x z

def member (p q w x : List A) : Prop := x = p ++ w ∨ x = q ++ w

private theorem member_unique {p q u v x : List A}
    (sep : ∀ a b, p ++ a ≠ q ++ b)
    (hu : member p q u x) (hv : member p q v x) : u = v := by
  rcases hu with h | h <;> rcases hv with k | k
  · exact List.append_cancel_left (h.symm.trans k)
  · exact False.elim (sep u v (h.symm.trans k))
  · exact False.elim (sep v u (k.symm.trans h))
  · exact List.append_cancel_left (h.symm.trans k)

theorem incomparable {p q x y : List A} (sep : ∀ a b, p ++ a ≠ q ++ b)
    (h : Related p q x y) :
    x = y ∨ ∃ w, member p q w x ∧ member p q w y := by
  induction h with
  | refl => exact Or.inl rfl
  | move w => exact Or.inr ⟨w, Or.inl rfl, Or.inr rfl⟩
  | symm h ih =>
    rcases ih with k | ⟨w, u, v⟩
    · exact Or.inl k.symm
    · exact Or.inr ⟨w, v, u⟩
  | trans h k ih ik =>
    rcases ih with rfl | ⟨u, hx, hy⟩
    · exact ik
    rcases ik with rfl | ⟨v, hy', hz⟩
    · exact Or.inr ⟨u, hx, hy⟩
    obtain rfl := member_unique sep hy hy'
    exact Or.inr ⟨u, hx, hz⟩

def copies (t : List A) : ℕ → List A
  | 0 => []
  | j+1 => t ++ copies t j

private theorem copies_add (t : List A) (i j : ℕ) :
    copies t (i+j) = copies t i ++ copies t j := by
  induction i with
  | zero => simp [copies]
  | succ i ih => simp [Nat.succ_add, copies, ih, List.append_assoc]

private theorem length_copies (t : List A) (i : ℕ) :
    (copies t i).length = i * t.length := by
  induction i with
  | zero => simp [copies]
  | succ i ih => simp [copies, ih, Nat.succ_mul, Nat.add_comm]

private def aligned (t u v : List A) : Prop :=
  ∃ i j : ℕ, copies t i ++ u = copies t j ++ v

private theorem aligned_trans {t u v w : List A}
    (h : aligned t u v) (k : aligned t v w) : aligned t u w := by
  obtain ⟨a,b,h⟩ := h
  obtain ⟨c,d,k⟩ := k
  refine ⟨c+a, b+d, ?_⟩
  calc
    copies t (c+a) ++ u = copies t c ++ (copies t a ++ u) := by
      rw [copies_add, List.append_assoc]
    _ = copies t c ++ (copies t b ++ v) := by rw [h]
    _ = copies t (b+c) ++ v := by rw [Nat.add_comm b c, copies_add, List.append_assoc]
    _ = copies t b ++ (copies t c ++ v) := by rw [copies_add, List.append_assoc]
    _ = copies t b ++ (copies t d ++ w) := by rw [k]
    _ = copies t (b+d) ++ w := by rw [copies_add, List.append_assoc]

private theorem prefix_invariant {p t x y : List A} (h : Related p (p ++ t) x y) :
    x.take p.length = y.take p.length ∧ aligned t (x.drop p.length) (y.drop p.length) := by
  induction h with
  | refl x => exact ⟨rfl, 0, 0, rfl⟩
  | move w =>
    constructor
    · simp [List.append_assoc]
    · refine ⟨1,0,?_⟩
      simp [copies, List.append_assoc]
  | symm h ih =>
    obtain ⟨hp, i, j, he⟩ := ih
    exact ⟨hp.symm,j,i,he.symm⟩
  | trans h k ih ik => exact ⟨ih.1.trans ik.1, aligned_trans ih.2 ik.2⟩

theorem comparable_same_length {p t x y : List A} (ht : 0 < t.length)
    (h : Related p (p ++ t) x y) (hl : x.length = y.length) : x = y := by
  obtain ⟨hp,i,j,he⟩ := prefix_invariant h
  have hlen := congrArg List.length he
  simp only [List.length_append, length_copies, List.length_drop, hl] at hlen
  have hij : i = j := Nat.eq_of_mul_eq_mul_right ht (Nat.add_right_cancel hlen)
  subst j
  have hd := List.append_cancel_left he
  calc
    x = x.take p.length ++ x.drop p.length := (List.take_append_drop _ _).symm
    _ = y.take p.length ++ y.drop p.length := by rw [hp, hd]
    _ = y := List.take_append_drop _ _

end SinglePrefixRelation
