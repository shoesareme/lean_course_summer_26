import Std

import Mathlib.Tactic

section

variable {P Q : Prop}

theorem exercise1 : (¬(P ∧ Q) ↔ ¬ P ∨ ¬ Q) := by
  constructor
  -- for the first part of the proof I was not aware we were able to use tactics like by_contra, so the code is needlessly complicated.
  · intro h1
    by_cases h : ¬P ∨ ¬Q
    · exact h
    · left
      intro hp
      by_cases hq : Q
      · have hpq := h1 ⟨hp, hq⟩
        exact hpq
      · have hnpornq : ¬ P ∨ ¬ Q := by
          right
          exact hq
        have hf := h hnpornq
        exact hf
  · intro h1
    intro h2
    have hp := And.left h2
    have hq := And.right h2
    rcases h1 with hn1 | hn2
    · exact hn1 hp
    · exact hn2 hq

theorem exercise2 (h : P ∨ Q) (hp : ¬ P) : Q := by
  rcases h with hp1 | hq
  · apply hp at hp1
    cases hp1
  · exact hq

end

section -- Quantifiers

variable {T : Type} {P : T → Prop}

/-
Recall a proof of a universally quantified statement ∀ x, P x
is an object of the product type ∏ (x : T), P x. In other words, a proof of ∀ x, P x
is a function that takes an arbitrary element x of type T and returns a proof of P x.
Thus, we can apply h : ∀ x, P x to an arbitrary element x : T to obtain a proof of P x.
-/

theorem exercise3 (h : ∀ x, P x) (x : T) : P x := by
  exact h x


/-
Whenever we want to prove a universally quantified statement ∀ x, P x,
we can use the 'intro' tactic to introduce an element x of type T and change the goal to P x.
-/

theorem theorem_we_want_to_use (x : T) : P x := by
  sorry -- use this theorem to prove exercise4

theorem exercise4 : ∀ x, P x := by
  intro x
  exact theorem_we_want_to_use x


/-
Recall a proof of an existentially quantified statement ∃ x, P x
is an object of the sum type ∑ (x : T), P x. In other words, a proof of ∃ x, P x is a pair (x, h)
where x : T and h : P x.
We can use the 'use x' tactic to prove an existentially quantified statement by providing a witness
x : T and changing the goal to P x.
-/

theorem exercise5 (h : ∀ x, P x) (y : T) : ∃ y, P y := by
  have htemp := h y
  use y


/-
Finally, to use a hypothesis h : ∃ x, P x, we can use the 'rcases' tactic to obtain
a witness x : T and a proof h' : P x.
-/

theorem exercise6 (n : Nat) (h : ∃ k, n = 2 * k) : ∃ l, n*n = 4 * l := by
  rcases h with ⟨k, hk⟩
  use k*k
  rw [← mul_assoc]
  rw [hk]
  rw [← mul_assoc]
  nth_rewrite 2 [mul_comm]
  rw [← mul_assoc]
  have h224 : 2 * 2 = 4 := by decide
  rw [h224]
end
