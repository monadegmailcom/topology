import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.Data.Set.Function
import Mathlib.CategoryTheory.Functor.Basic

import Topology.Chap0.Chap0_2.Chap0_2_1.Def0_6_push_forward

open CategoryTheory Set

variable [Category C] {X Y Z : C}

-- Type is automatically instanced as a category
def pushforward_functor : Functor C Type where
  obj Z := X ⟶ Z
  map {Y Z} (f : Y ⟶ Z) : (X ⟶ Y) → (X ⟶ Z) := pushforward f X
  map_id f := by
    dsimp
    ext Y
    rw [pushforward]
    simp
  map_comp f g := by
    dsimp
    ext h
    dsimp
    rw [pushforward, pushforward, pushforward]
    simp

def pullback_functor : Functor Cᵒᵖ Type where
  obj (Z : Cᵒᵖ) := Z.unop ⟶ X
  map {Y Z : Cᵒᵖ} (f : Y ⟶ Z) : (Y.unop ⟶ X) → (Z.unop ⟶ X) := pullback f.unop X
  map_id _ := by
    dsimp
    congr
    ext Y
    rw [pullback]
    simp
  map_comp _ _ := by
    dsimp
    congr
    ext h
    dsimp
    rw [pullback, pullback, pullback]
    simp
