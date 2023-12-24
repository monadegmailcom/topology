import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Set.Function

open CategoryTheory Set

variable {x y : Type}

def left_cancellative (f : x → y) : Prop
  := ∀ z : Type, ∀ g1 g2 : z → x, f ∘ g1 = f ∘ g2 → g1 = g2

example (f : x → y) : Function.Injective f ↔ left_cancellative f := by
  apply Iff.intro
  . intro h z g1 g2 h2
    ext t
    apply h
    apply congrFun h2 t
  intro h x1 x2 h2
  let g1 := fun (_ : Unit) => x1
  let g2 := fun (_ : Unit) => x2
  apply congrFun (f := g1) (g := g2) _ default
  apply h _ g1 g2
  ext
  dsimp
  exact h2
