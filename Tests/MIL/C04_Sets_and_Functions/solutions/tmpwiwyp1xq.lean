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

example : s ∩ (s ∪ t) = s  := by
  ext x; constructor
  have h₁ : x ∈ s ∩ (s ∪ t) → x ∈ s := by
    rintro ⟨xs, _⟩
    exact xs
  have h₂ : x ∈ s → x ∈ s ∩ (s ∪ t) := by
    intro xs
    use xs; left; exact xs
  exact ⟨h₁, h₂⟩
