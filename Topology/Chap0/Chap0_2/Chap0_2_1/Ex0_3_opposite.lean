import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

structure Op (C : Type u) [Category C] where
  op : C

instance [Category C] : Category (Op C) where
  Hom X Y := Y.op ⟶ X.op
  id X := 𝟙 X.op
  comp f g := g ≫ f

def op [Category C] {X : C} {Y : C}
  : (X ⟶ Y) → (Op.mk Y ⟶ Op.mk X) := id

def unop [Category C] {X : Op C} {Y : Op C}
  : (X ⟶ Y) → (Y.op ⟶  X.op) := id

theorem op_is_surj [Category C] (p : Op C → Prop)
  : (∀ X : C, (p ∘ Op.mk) X) ↔ ∀ opX : Op C, p opX :=
    Iff.intro (fun q ⟨X⟩ => q X) (fun q X => q (Op.mk X))

/-
example (f : a → b) (p : b → Prop) (sur : f is_surjective)
  : (∀ x : a, p (f x)) ↔ (∀ y : b, p y) := by
  apply Iff.intro
  . intro q y
    have ⟨x, h⟩ := sur y
    rw [←h]
    exact q x
  . intro q x
    exact q (f x)
-/
