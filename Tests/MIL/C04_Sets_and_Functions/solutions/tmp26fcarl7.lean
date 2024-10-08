import Tests.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v   := by
  constructor
  · intro h x xs
    have fx_mem_image : f x ∈ f '' s := mem_image_of_mem _ xs
    exact h fx_mem_image
  · intro h y ymem
    have ⟨x, xs, fxeq⟩ := ymem
    have y_eq_fx : y = f x := fxeq.symm
    rw [y_eq_fx]
    exact h xs
