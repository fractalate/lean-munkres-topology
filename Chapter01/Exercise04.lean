import Mathlib.Tactic
import Mathlib.Data.Real.Basic


theorem MunkresCh1Ex4PartA (A B : Set ℝ) : ¬(∀ a ∈ A, a^2 ∈ B) ↔ (∃ a ∈ A, a^2 ∉ B) := by
  simp

theorem MunkresCh1Ex4PartB (A B : Set ℝ) : ¬(∃ a ∈ A, a^2 ∈ B) ↔ (∀ a ∈ A, a^2 ∉ B) := by
  simp

theorem MunkresCh1Ex4PartC (A B : Set ℝ) : ¬(∀ a ∈ A, a^2 ∉ B) ↔ (∃ a ∈ A, a^2 ∈ B) := by
  simp

theorem MunkresCh1Ex4PartD (A B : Set ℝ) : ¬(∃ a ∉ A, a^2 ∈ B) ↔ (∀ a ∉ A, a^2 ∉ B) := by
  simp
