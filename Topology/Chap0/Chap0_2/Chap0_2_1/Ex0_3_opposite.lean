import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Opposites

open CategoryTheory

theorem op_bijective u : Function.Bijective (Opposite.op (α := u)) := by
  apply And.intro
  . exact Opposite.op_injective
  exact Function.LeftInverse.surjective (congrFun rfl)

theorem unop_bijective u : Function.Bijective (Opposite.unop (α := u)) := by
  apply And.intro
  . exact Opposite.unop_injective
  exact Function.LeftInverse.surjective (congrFun rfl)
