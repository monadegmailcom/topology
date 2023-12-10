import Mathlib.CategoryTheory.Category.Basic
--import Mathlib.Algebra.Hom.Group
import Mathlib.Algebra.Group.Defs

open CategoryTheory

namespace one_object

-- object type with only one unique instance
structure Obj (a : Type u)

-- morphism are the instances of type a

instance [Monoid a] : CategoryStruct (Obj a) where
  Hom _ _ := a
  id _ := One.one
  comp := HMul.hMul
--  comp f g := f * g

instance [Monoid a] : Category (Obj a) where
  assoc := Semigroup.mul_assoc
  id_comp := Monoid.one_mul
  comp_id := Monoid.mul_one

end one_object
