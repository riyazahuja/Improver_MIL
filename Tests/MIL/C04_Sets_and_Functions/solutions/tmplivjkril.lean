import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Tests.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u)  := by
  rintro x hx
have h_s : x ∈ s := hx.elim (λ h, h.1) (λ h, h.1)
have h_tu : x ∈ t ∨ x ∈ u := hx.elim (λ h, Or.inl h.2) (λ h, Or.inr h.2)
use h_s
exact h_tu
