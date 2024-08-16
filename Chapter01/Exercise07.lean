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

theorem MunkresCh1Ex7PartC {U} (A B C : Set U)
    : {x : U | x ∈ A ∧ (x ∈ B → x ∈ C)} = A ∩ (C ∪ (A \ B)) := by
  ext x
  apply Iff.intro
  simp
  intro h
  intro h2
  constructor
  assumption
  by_cases h3 : x ∈ B
  apply h2 at h3
  exact Or.inl h3
  exact Or.inr ⟨h, h3⟩

  intro h
  simp at h
  simp
  obtain ⟨a, bc⟩ := h
  constructor
  assumption
  intro h2
  obtain h3 | h3 := bc
  assumption
  obtain ⟨_, oops⟩ := h3
  apply oops at h2
  contradiction
