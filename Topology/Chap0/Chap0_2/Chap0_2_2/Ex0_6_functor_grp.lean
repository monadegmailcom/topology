import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Algebra.Category.GroupCat.Basic

open CategoryTheory Set

-- the forgetful functor
def grp_functor : Functor GroupCat Type where
  obj G := G
  map f := f
