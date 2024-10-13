import Mathlib.Tactic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime

-- variable {α : Type*}
-- variable (s t u : Set α)

-- variable (ssubt : s ⊆ t)

variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set


example (P Q :Prop): P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

example (P Q :Prop): P ∨ Q → Q ∨ P := by
  rintro (hp | hq)
  . exact Or.inr hp
  . exact Or.inl hq


--=============================

example (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  intro h nq
  have nhq := by
    exact not_or_of_imp h
  rcases nhq with hnp | hq
  . exact hnp
  . exfalso
    contradiction


example (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  intro h nq p
  exact nq (h p)

--=============================



example : (P → Q) ∧ (Q → R) → P → R := by
  intro h p
  rcases h with ⟨a,b⟩
  apply b
  apply a
  exact p

example : (P → Q) ∧ (Q → R) → P → R := by
  rintro (⟨hpq,hqr⟩) hp
  exact hqr (hpq hp)

--=============================

example (h : P → Q) (h1 : P ∧ R) : Q ∧ R := by
  rcases h1 with ⟨p,r⟩
  constructor
  exact h p
  exact r

example (h : P → Q) (h1 : P ∧ R) : Q ∧ R := by
  exact And.imp_left h h1

--=============================

example (h : ¬ (P ∧ Q)) : P → ¬ Q := by
  intro p opp
  have duh : P ∧ Q := by
    constructor
    exact p
    exact opp
  exact h duh

example (h : ¬ (P ∧ Q)) : P → ¬ Q := by
  intro hp hq
  apply h
  exact ⟨hp,hq⟩
