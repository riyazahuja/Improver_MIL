import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common




variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable {W : Type*} [AddCommGroup W] [Module K W]


open Polynomial Module LinearMap

theorem C09_S03_0(φ ψ : End K V) : φ * ψ = φ ∘ₗ ψ :=
  LinearMap.mul_eq_comp φ ψ -- `rfl` would also work

-- -- evaluating `P` on `φ`
-- theorem C09_S03_1(P : K[X]) (φ : End K V) : V →ₗ[K] V :=
--   aeval φ P

-- evaluating `X` on `φ` gives back `φ`
theorem C09_S03_2(φ : End K V) : aeval φ (X : K[X]) = φ :=
  aeval_X φ



#check Submodule.eq_bot_iff
#check Submodule.mem_inf
#check LinearMap.mem_ker

theorem C09_S03_3(P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) : ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro x hx
  rw [Submodule.mem_inf, mem_ker, mem_ker] at hx
  rcases h with ⟨U, V, hUV⟩
  have := congr((aeval φ) $hUV.symm x)
  simpa [hx]

#check Submodule.add_mem_sup
#check map_mul
#check LinearMap.mul_apply
#check LinearMap.ker_le_ker_comp

theorem C09_S03_4(P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by
  apply le_antisymm
  · apply sup_le
    · rw [mul_comm, map_mul]
      apply ker_le_ker_comp -- or alternative below:
      -- intro x hx
      -- rw [mul_comm, mem_ker] at *
      -- simp [hx]
    · rw [map_mul]
      apply ker_le_ker_comp -- or alternative as above
  · intro x hx
    rcases h with ⟨U, V, hUV⟩
    have key : x = aeval φ (U*P) x + aeval φ (V*Q) x := by simpa using congr((aeval φ) $hUV.symm x)
    rw [key, add_comm]
    apply Submodule.add_mem_sup <;> rw [mem_ker] at *
    · rw [← mul_apply, ← map_mul, show P*(V*Q) = V*(P*Q) by ring, map_mul, mul_apply, hx,
          map_zero]
    · rw [← mul_apply, ← map_mul, show Q*(U*P) = U*(P*Q) by ring, map_mul, mul_apply, hx,
          map_zero]
