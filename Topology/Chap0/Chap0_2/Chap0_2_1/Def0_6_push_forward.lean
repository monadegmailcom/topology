import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.Data.Set.Function

import Topology.Chap0.Chap0_2.Chap0_2_1.Ex0_3_opposite

open CategoryTheory
open Set

def pushforward [Category C] {X : C} {Y : C} (f : X ⟶ Y) (Z : C) :
  (Z ⟶ X) -> (Z ⟶ Y) := fun g => g ≫ f

def pullback [Category C] {X : C} {Y : C} (f : X ⟶ Y) (Z : C) :
  (Y ⟶ Z) -> (X ⟶ Z) := fun g => f ≫ g

theorem pullback_eq_op_pushforward
  [Category C] {X : C} {Y : C} (f : X ⟶ Y) (Z : C) :
  pullback f Z = Opposite.unop
               ∘ pushforward f.op (Opposite.op Z)
               ∘ Opposite.op := rfl

theorem pushforward_eq_op_pullback
  [Category C] {X : C} {Y : C} (f : X ⟶ Y) (Z : C) :
  pushforward f Z = Opposite.unop
                  ∘ pullback f.op (Opposite.op Z)
                  ∘ Opposite.op := rfl

section theo06_01
theorem part1 [Category C] {X : C} {Y : C} (f : X ⟶ Y) :
  IsIso f ↔ ∀ Z, Function.Bijective (pullback f Z) := by
    apply Iff.intro
    . intro ⟨inv, ⟨p, q⟩⟩ Z
      let pb := pullback f Z
      have inj : Function.Injective pb := by
        intro yz1 yz2 h
        have r : ∀ h : Y ⟶ Z, inv ≫ (pb h) = h := fun h => calc
          inv ≫ (pb h) = inv ≫ (f ≫ h) := rfl
          _ = (inv ≫ f) ≫ h := by simp
          _ = 𝟙 Y ≫ h := by rw[q]
          _ = h := by simp
        rw[←r yz1, h, r yz2]
      have surj : Function.Surjective pb := fun h =>
        let g := inv ≫ h
        have : pb g = h := calc
          pb g = f ≫ g := rfl
          _ = (f ≫ inv) ≫ h := by simp
          _ = 𝟙 X ≫ h := by rw[p]
          _ = h := by simp
        ⟨g, this⟩
      exact ⟨inj, surj⟩
    . intro h
      have ⟨g, t⟩ := (h X).right (𝟙 X)
      have l_inv : f ≫ g = 𝟙 X := t
      have r_inv : g ≫ f = 𝟙 Y := by
        let pb := pullback f Y
        have z : pb (g ≫ f) = pb (𝟙 Y) := calc
          pb (g ≫ f) = f ≫ (g ≫ f) := rfl
          _ = (f ≫ g) ≫ f := by simp
          _ = 𝟙 X ≫ f := by rw[l_inv]
          _ = f := by simp
          _ = f ≫ 𝟙 Y := by simp
          _ = pb (𝟙 Y) := rfl
        apply (h Y).left z
      exact ⟨g, ⟨l_inv, r_inv⟩⟩

theorem part2 [Category C] {X : C} {Y : C} (f : X ⟶ Y) :
  IsIso f ↔ ∀ Z, Function.Bijective (pushforward f Z) := calc
    IsIso f ↔ IsIso f.op := (CategoryTheory.isIso_op_iff f).symm
    _ ↔ ∀ Z : Cᵒᵖ, Function.Bijective (pullback f.op Z) := part1 f.op
    _ ↔ ∀ Z : C, Function.Bijective (pullback f.op (Opposite.op Z)) := by
      apply Iff.intro
      . intro h Z
        exact h (Opposite.op Z)
      intro h Z
      exact h (Opposite.unop Z)
    _ ↔ ∀ Z, Function.Bijective (pushforward f Z) := by
      apply Iff.intro
      . intro h Z
        apply Function.Bijective.comp (unop_bijective _)
        apply Function.Bijective.comp (h Z)
        apply op_bijective
      intro h Z
      apply Function.Bijective.comp (op_bijective _)
      apply Function.Bijective.comp (h Z)
      apply unop_bijective

end theo06_01
