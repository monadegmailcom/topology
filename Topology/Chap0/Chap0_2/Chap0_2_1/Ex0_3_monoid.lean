import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Hom.Group
import Mathlib.Algebra.Group.Defs

open CategoryTheory

namespace monoid

structure Obj where
  carrier : Type
  instMul : MulOneClass carrier
  -- seems not to be necessary that carrier
  -- is actually a monoid
  --instMonoid : Monoid carrier

structure Mor (source : Obj) (dest : Obj) where
  hom : @MonoidHom
        source.carrier dest.carrier
        source.instMul dest.instMul

instance : Category Obj where
  Hom := Mor
  id x := Mor.mk (@MonoidHom.id x.carrier x.instMul)
  comp := by
    intro x y z f g
    apply Mor.mk (@MonoidHom.comp x.carrier y.carrier
      z.carrier x.instMul y.instMul z.instMul
      g.hom f.hom)

namespace samples

def obj : Obj := Obj.mk ℕ
  (MulOneClass.mk (by simp) (by simp))
def f : obj ⟶ obj := 𝟙 obj
def g : obj ⟶ obj := f ≫ f

end samples

end monoid
