import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Set.Prod

open CategoryTheory Set

def set_functor (X : Set u) : Functor Type Type where
  obj Y := X × Y
  map {Y Z} (f : Y ⟶ Z) : X × Y ⟶ X × Z := fun (x, y) => (x, f y)
