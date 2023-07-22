import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap

open CategoryTheory

namespace rmod

structure Obj (R : Type u) [Semiring R] where
  M : Type v
  instMonoid : AddCommMonoid M
  instModule : Module R M

structure Mor [Semiring R] (s : Obj R) (d : Obj R) where
  sd : @LinearMap _ _ _ _ (RingHom.id _) _ _
          s.instMonoid d.instMonoid s.instModule d.instModule

instance [Semiring R] : Category (Obj R) where
  Hom := Mor
  id x :=
    have idLinearMap := @LinearMap.id _ _ _ x.instMonoid x.instModule
    Mor.mk idLinearMap
  comp := by
    intro x y z f g
    have xzLinearMap := @LinearMap.comp _ _ _ _ _ _
                          _ _ _
                          x.instMonoid y.instMonoid z.instMonoid _ _ _
                          _ _ _
                          _ g.sd f.sd

    apply Mor.mk xzLinearMap

namespace samples

def module1 : Module ℕ ℕ := AddCommMonoid.natModule
def obj1 : Obj ℕ := Obj.mk ℕ _ module1

def module2 : Module ℕ ℤ := AddCommMonoid.natModule
def obj2 : Obj ℕ := Obj.mk ℤ _ module2

def f : obj1 ⟶ obj1 := 𝟙 obj1

end samples
end rmod
