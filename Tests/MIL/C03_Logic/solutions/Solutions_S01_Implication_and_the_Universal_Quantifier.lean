import Tests.Common
import Mathlib.Data.Real.Basic

namespace C03S01

theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := by apply abs_mul
    _ ≤ |x| * ε := by apply mul_le_mul; linarith; linarith; apply abs_nonneg; apply abs_nonneg;
    _ < 1 * ε := by rw [mul_lt_mul_right epos]; linarith
    _ = ε := by apply one_mul

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

section
variable (f g : ℝ → ℝ) (a b : ℝ)

theorem C03_S01_0(hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  apply add_le_add
  apply hfa
  apply hgb

theorem C03_S01_1(nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  apply mul_nonneg
  apply nnf
  apply nng

theorem C03_S01_2(hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  intro x
  apply mul_le_mul
  apply hfa
  apply hgb
  apply nng
  apply nna

end

section
variable (f g : ℝ → ℝ)

theorem C03_S01_3{c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b aleb
  apply mul_le_mul_of_nonneg_left _ nnc
  apply mf aleb

theorem C03_S01_4{c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  fun a b aleb ↦ mul_le_mul_of_nonneg_left (mf aleb) nnc

theorem C03_S01_5(mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro a b aleb
  apply mf
  apply mg
  apply aleb

theorem C03_S01_6(mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  fun a b aleb ↦ mf (mg aleb)

def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

theorem C03_S01_7(of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  calc
    (fun x ↦ f x * g x) x = f x * g x := rfl
    _ = f (-x) * g (-x) := by rw [of, og, neg_mul_neg]


theorem C03_S01_8(ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  dsimp
  rw [ef, og, neg_mul_eq_mul_neg]

theorem C03_S01_9(ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  dsimp
  rw [og, ← ef]

end

section

variable {α : Type*} (r s t : Set α)

theorem C03_S01_10: r ⊆ s → s ⊆ t → r ⊆ t := by
  intro rsubs ssubt x xr
  apply ssubt
  apply rsubs
  apply xr

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t :=
  fun rsubs ssubt x xr ↦ ssubt (rsubs xr)

end

section
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

theorem C03_S01_11(h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intro x xs
  apply le_trans (h x xs) h'

theorem C03_S01_12(h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  fun x xs ↦ le_trans (h x xs) h'

end

section

open Function

theorem C03_S01_13{c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  intro x₁ x₂ h'
  apply (mul_right_inj' h).mp h'

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

theorem C03_S01_14(injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro x₁ x₂ h
  apply injf
  apply injg
  apply h

end
