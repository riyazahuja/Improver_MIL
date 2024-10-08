import Tests.Common
import Mathlib.Topology.Instances.Real

open Set Filter Topology

-- In the next example we could use `tauto` in each proof instead of knowing the lemmas
example {α : Type*} (s : Set α) : Filter α :=
  { sets := { t | s ⊆ t }
    univ_sets := subset_univ s
    sets_of_superset := fun hU hUV ↦ Subset.trans hU hUV
    inter_sets := fun hU hV ↦ subset_inter hU hV }

example : Filter ℕ :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := by
      use 42
      simp
    sets_of_superset := by
      rintro U V ⟨N, hN⟩ hUV
      use N
      tauto
    inter_sets := by
      rintro U V ⟨N, hN⟩ ⟨N', hN'⟩
      use max N N'
      intro b hb
      rw [max_le_iff] at hb
      constructor <;> tauto }

def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f ⁻¹' V ∈ F

example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}

example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H   := by
  intro V hV
  have preimage_g : g ⁻¹' V ∈ G := hg V hV
  have preimage_f_g : f ⁻¹' (g ⁻¹' V) ∈ F := hf (g ⁻¹' V) preimage_g
  exact preimage_f_g
