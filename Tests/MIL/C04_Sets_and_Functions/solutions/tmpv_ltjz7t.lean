import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Tests.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  . use xs; right; exact xu

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  constructor
  use xs
  · intro xt
    exact xntu (Or.inl xt)
  intro xu
  apply xntu (Or.inr xu)

example : s ∩ t = t ∩ s :=
    Subset.antisymm
    (fun x ⟨xs, xt⟩ ↦ ⟨xt, xs⟩) fun x ⟨xt, xs⟩ ↦ ⟨xs, xt⟩

example : s ∩ (s ∪ t) = s := by
  ext x; constructor
  · rintro ⟨xs, _⟩
    exact xs
  . intro xs
    use xs; left; exact xs

example : s ∪ s ∩ t = s := by
  ext x; constructor
  · rintro (xs | ⟨xs, xt⟩) <;> exact xs
  . intro xs; left; exact xs

example : s \ t ∪ t = s ∪ t := by
  ext x; constructor
  · rintro (⟨xs, nxt⟩ | xt)
    · left
      exact xs
    . right
      exact xt
  by_cases h : x ∈ t
  · intro
    right
    exact h
  rintro (xs | xt)
  · left
    use xs
  right; exact xt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t)  := by
  ext x; constructor
  have H1 : x ∈ (s ∪ t) := by
    rintro (⟨xs, _⟩ | ⟨xt, _⟩)
    . left; exact xs
    . right; exact xt
  have H2 : x ∉ (s ∩ t) := by
    rintro ⟨xs, xt⟩
    contradiction
  · rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    . constructor
      . exact H1
      . exact H2
    . constructor
      . exact H1
      . exact H2
  rintro ⟨xs | xt, nxst⟩
  · left
    use xs
    intro xt
    apply nxst
    constructor <;> assumption
  · right
    use xt
    intro xs
    apply nxst
    constructor <;> assumption
