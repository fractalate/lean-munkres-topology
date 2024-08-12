import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

open Finset

theorem MunkresCh1Ex7PartA {U} (A B C : Set U)
    : {x : U | x ∈ A ∧ (x ∈ B ∨ x ∈ C)} = A ∩ (B ∪ C) := by
  ext x
  apply Iff.intro

  intro h
  obtain ⟨xA, xBC⟩ := h
  constructor
  assumption
  obtain xB | xC := xBC
  exact Or.inl xB
  exact Or.inr xC

  intro h
  obtain ⟨xA, xBC⟩ := h
  simp
  obtain xB | xC := xBC
  exact Or.inl ⟨xA, xB⟩
  exact Or.inr ⟨xA, xC⟩

theorem MunkresCh1Ex7PartB {U} (A B C : Set U)
    : {x : U | (x ∈ A ∧ x ∈ B) ∨ x ∈ C} = (A ∩ B) ∪ C := by
  ext x
  simp

-- I'm unsure whether this is expressed correctly.
theorem MunkresCh1Ex7PartC {U} (A B C : Set U)
    : {x : U | x ∈ A ∧ (x ∈ B → x ∈ C)} = A ∩ (C \ B ∪ C) := by
  sorry
