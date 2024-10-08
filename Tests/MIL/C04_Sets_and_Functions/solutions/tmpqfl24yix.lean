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

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    have : f x ∈ f '' s := mem_image_of_mem _ xs
    exact h this
  intro h y ymem
  rcases ymem with ⟨x, xs, fxeq⟩
  rw [← fxeq]
  apply h xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s    := by
  rintro x ⟨y, ys, fxeq⟩
  have hy_eq_fx : f y = f x := fxeq
  have hx_eq_y : x = y := by rw [← h hy_eq_fx]
  have hy_in_s : y ∈ s := ys
  have hx_in_s : x ∈ s := by rw [hx_eq_y]; exact hy_in_s
  exact hx_in_s
