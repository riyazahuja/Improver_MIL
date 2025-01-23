import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

theorem Problem1_1 {a b : ℤ} (h : a ∣ b) : a ∣ (a^2 - b^2) := by
  rcases h with ⟨k, akeqb⟩
  use (k + 1)*(a - b)
  rw [← mul_assoc, mul_add, ← akeqb]
  ring

theorem Problem1_5a : ¬ (∀ (a : ℝ), ∀ (x : ℝ), ∃! (y : ℝ), x^4*y+a*y+x=0) := by
  push_neg
  use 0, 0
  intro h
  rcases h with ⟨y, hy⟩
  have v1eqy: (0 : ℝ) = y := by
    apply hy.right 0
    simp
  have v2eqy: (1 : ℝ) = y := by
    apply hy.right 1
    simp
  rw [← v1eqy] at v2eqy
  symm at v2eqy
  exact (ne_of_lt (by norm_num)) v2eqy

theorem Problem2_1a : ¬ (∀ (A B C : Set Nat), (A ∩ B ∩ C) ⊂ (A ∪ B)) := by
  push_neg
  use {1}, {1}, {1}
  simp
  exact not_ssubset_of_subset fun ⦃a⦄ => congrArg fun ⦃a⦄ => a

theorem Problem2_1b : ∀ (A B : Set Nat), (A \ B) ∩ (B \ A) = ∅ := by
  intros A B
  ext x
  constructor
  · intro h
    refine (Set.mem_empty_iff_false x).mpr ?h.mp.a
    simp at h
    exact h.right.right h.left.left
  intro h
  simp at h

theorem Problem2_1c : ∀ (A B : Set Nat), (A ∩ B ≠ ∅) → ((A \ B) ⊂ A) := by
  intro A B h
  refine Set.ssubset_iff_subset_ne.mpr ?_
  constructor
  · exact Set.diff_subset
  refine Ne.intro ?right.h
  intro h'
  apply h
  rw [← h']
  exact Set.diff_inter_self

theorem Problem2_2 : {x : ℤ | 6 ∣ x} = {x : ℤ | 6 ∣ (7*x-12)} := by
  ext x
  constructor
  · intro h
    simp at *
    rcases h with ⟨k, hk⟩
    use (7*k - 2)
    linarith
  intro h
  simp at *
  rcases h with ⟨k, hk⟩
  use (k-x+2)
  linarith


def seq : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1 + 1) * seq n + (n + 1)

theorem Problem4_1 {n : ℕ} : seq n = Nat.factorial (n + 1) - 1 := by
  induction' n with n ih
  · simp [seq]
  rw [Nat.factorial_succ]
  have : (n + 1 + 1) * (n + 1).factorial - 1 = (n + 1 + 1) * ((n + 1).factorial - 1) + (n + 1) := by
    rw [Nat.mul_sub, Nat.mul_comm, Nat.mul_one]
    have : (n + 1).factorial * (n + 1 + 1) - (n + 1 + 1) + (n + 1) = (n + 1).factorial * (n + 1 + 1) - (n + 1) + (n + 1) - 1 := by
      have : 1 ≤ (n+1).factorial * (n + 1 + 1) - (n + 1):= by
        have : n + 1 + 1  ≤ (n+1).factorial * (n + 1 + 1) := by
          rw [mul_comm, ← Nat.factorial_succ]
          exact Nat.self_le_factorial (n+2)
        nth_rw 1 [add_comm (n+1)] at this
        exact Nat.le_sub_of_add_le this
      rw [← Nat.sub_sub]
      rw [← Nat.sub_add_comm this]
    rw [this]
    rw [Nat.sub_add_cancel]
    rw [mul_comm, ← Nat.factorial_succ]
    exact le_trans (by norm_num) (Nat.self_le_factorial (n+2))
  rw [this, ← ih, seq]

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

example {f g : ℝ → ℝ} (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb

example {f g : ℝ → ℝ} (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  rcases lbf with ⟨a, lbfa⟩
  rcases lbg with ⟨b, lbgb⟩
  use a + b
  have FnLb_add {a b : ℝ} (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
    intro x
    dsimp
    apply add_le_add
    apply hfa
    apply hgb
  apply FnLb_add lbfa lbgb

example {f g : ℝ → ℝ} (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  obtain ⟨a, lbfa⟩ := lbf
  obtain ⟨b, lbgb⟩ := lbg
  have FnLb_add {a b : ℝ} (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
    intro x
    dsimp
    apply add_le_add
    apply hfa
    apply hgb
  exact ⟨a+b, FnLb_add lbfa lbgb⟩

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h₀, h₁⟩
    constructor
    · exact h₀
    · intro h
      apply h₁
      exact le_of_eq (id (Eq.symm h))
  · rintro ⟨h₀, h₁⟩
    constructor
    · exact h₀
    · intro h
      apply h₁
      exact le_antisymm h₀ h

theorem helper {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · apply helper h
    · have h' : y ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
      apply pow_eq_zero h'
  · rintro ⟨rfl, rfl⟩
    linarith

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nge
  have ngeNs : Ns ≤ n := by apply le_of_max_le_left nge
  have ngeNt : Nt ≤ n := by apply le_of_max_le_right nge

  have hst : |s n - a| < ε / 2 ∧ |t n - b| < ε / 2 := by
    constructor
    · exact hs n ngeNs
    · exact ht n ngeNt
  have combined : |s n - a| + |t n - b| < ε := by
    linarith
  calc
    |s n + t n - (a + b)| = |s n - a + (t n - b)| := by
      congr
      ring
    _ ≤ |s n - a| + |t n - b| := (abs_add _ _)
    _ < ε := combined

-- theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
--     ConvergesTo (fun n ↦ c * s n) (c * a) := by
--   by_cases h : c = 0
--   · convert convergesTo_const 0
--     · rw [h]
--       ring
--     rw [h]
--     ring
--   have acpos : 0 < |c| := abs_pos.mpr h
--   intro ε εpos
--   rcases cs (ε / |c|) (div_pos εpos acpos) with ⟨N, h⟩
--   use N
--   intro n nge
--   have cneq0 : |c| ≠ 0 := by linarith
--   calc
--     |(fun n => c * s n) n - c * a| = |c * (s n - a)| := by
--       congr
--       ring
--     _ = |c| * |s n - a| := by
--       rw [abs_mul]
--     _ < |c| * (ε / |c|) := by
--       apply mul_lt_mul_of_pos_left
--       · exact h n nge
--       · exact acpos
--     _ = ε := by
--       rw [mul_div_cancel₀ ε cneq0]

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n ngeN
  calc
    |s n| = |s n - a + a| := by
      congr
      ring
    _ ≤ |s n - a| + |a| := by
      apply abs_add
    _ < 1 + |a| := by
      apply add_lt_add_right (h n ngeN) |a|
    _ = |a| + 1 := by
      ring


example {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  have h₁' : ∀ n, N₁ ≤ n → |t n| < ε / B := by
    intro n nge
    calc
      |t n| = |t n - 0| := by
        congr
        ring
      _ < ε / B := h₁ n nge
  use max N₀ N₁
  intro n nge
  calc
    |s n * t n - 0| = |s n * t n| := by
      congr
      ring
    _ = |s n| * |t n| := by
      rw [abs_mul]
    _ ≤ B * |t n| := by
      apply mul_le_mul_of_nonneg_right
      · exact le_of_lt (h₀ n (le_of_max_le_left nge))
      · exact abs_nonneg _
    _ < B * (ε / B) := by
      apply mul_lt_mul_of_pos_left
      · exact h₁' n (le_of_max_le_right nge)
      · exact Bpos
    _ = ε := by
      have Bneq0 : B ≠ 0 := by linarith
      rw [mul_div_cancel₀ ε Bneq0]

-- theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
--       (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
--     ConvergesTo (fun n ↦ s n * t n) (a * b) := by
--   have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
--     apply aux2 cs
--     convert convergesTo_add ct (convergesTo_const (-b))
--     ring
--   have := convergesTo_add h₁ (convergesTo_mul_const b cs)
--   convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
--   · ext; ring
--   ring
