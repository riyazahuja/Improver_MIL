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

example : Filter ℕ  := by
  use 42
  simp
  sets_of_superset := by
    rintro U V ⟨N, hN⟩ hUV
    have hSub : U ⊆ V := hUV
    have hMem : ∀ b, N ≤ b → b ∈ U := hN
    use N
    intro b hb
    exact hSub (hMem b hb)
  inter_sets := by
    rintro U V ⟨N, hN⟩ ⟨N', hN'⟩
    have hMemU : ∀ b, N ≤ b → b ∈ U := hN
    have hMemV : ∀ b, N' ≤ b → b ∈ V := hN'
    have hMax : ∀ b, max N N' ≤ b → (N ≤ b ∧ N' ≤ b) := λ b hb => max_le_iff.1 hb
    use max N N'
    intro b hb
    have h := hMax b hb
    have hInU : b ∈ U := hMemU b h.1
    have hInV : b ∈ V := hMemV b h.2
    exact ⟨hInU, hInV⟩
