import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Set.Function

import Topology.Chap0.Chap0_2.Chap0_2_1.Def0_5_inverse

open CategoryTheory
open Set

def is_surjective' (f : a -> b) := ∀ y : b, ∃ x : a, f x = y
postfix:50 "is_surjective" => is_surjective'

def is_injective' (f : a -> b) := ∀ x1 : a, ∀ x2 : a, f x1 = f x2 -> x1 = x2
postfix:50 "is_injective" => is_injective'

def is_bijective' (f : a -> b) := f is_injective ∧ f is_surjective
postfix:50 "is_bijective" => is_bijective'

-- my surjective is mathlib's surjective for (co)domain = univ
theorem is_surjective_iff_surj_on (f : a -> b) :
  f is_surjective ↔ SurjOn f univ univ := by
    apply Iff.intro
    . intro h y _
      have ⟨x, q⟩ := h y
      exact ⟨x, ⟨by simp, q⟩⟩
    . intro h y
      have i : y ∈ univ := by simp
      have ⟨x,v⟩ := h i
      exact ⟨x, v.right⟩

-- my injective is mathlib's injective for (co)domain = univ
theorem is_injective_iff_inj_on (f : a -> b) :
  f is_injective ↔ InjOn f univ := by
    apply Iff.intro
    . intro h x1 _ x2 _ p
      apply h x1 x2 p
    . intro h x1 x2 p
      apply h (by simp) (by simp) p

-- my bijective is mathlib's bijective for (co)domain = univ
theorem is_bijective_iff_bij_on (f : a -> b) :
  f is_bijective ↔ BijOn f univ univ := by
    apply Iff.intro
    . intro ⟨i, s⟩
      have inj := Iff.mp (is_injective_iff_inj_on f) i
      have surj := Iff.mp (is_surjective_iff_surj_on f) s
      apply BijOn.mk (by simp) inj surj
    . intro ⟨_, i, s⟩
      have inj := Iff.mpr (is_injective_iff_inj_on f) i
      have surj := Iff.mpr (is_surjective_iff_surj_on f) s
      exact ⟨inj, surj⟩

def pushforward [Category C] {X : C} {Y : C} (f : X ⟶ Y) (Z : C) :
  (Z ⟶ X) -> (Z ⟶ Y) := fun g => g ≫ f

def pullback [Category C] {X : C} {Y : C} (f : X ⟶ Y) (Z : C) :
  (Y ⟶ Z) -> (X ⟶ Z) := fun g => f ≫ g

theorem pullback_eq_op_pushforward [Category C] {X : C} {Y : C}
  (f : X ⟶ Y) (Z : C) : pullback f Z = pushforward (op f) (Op.mk Z) := rfl

theorem pushforward_eq_op_pullback [Category C] {X : C} {Y : C}
  (f : X ⟶ Y) (Z : C) : pushforward f Z = pullback (op f) (Op.mk Z) := rfl

theorem theo06_01 [Category C] {X : C} {Y : C} (f : X ⟶ Y) :
  f is_invertible ↔ ∀ Z, (pullback f Z) is_bijective := by
    apply Iff.intro
    . intro ⟨⟨l_inv, p⟩, ⟨r_inv, q⟩⟩ Z
      let pb := pullback f Z
      have inj : pb is_injective := by
        intro yz1 yz2 h
        have r : ∀ h : Y ⟶ Z, r_inv ≫ (pb h) = h := fun h => calc
          r_inv ≫ (pb h) = r_inv ≫ (f ≫ h) := rfl
          _ = (r_inv ≫ f) ≫ h := by simp
          _ = 𝟙 Y ≫ h := by rw[q]
          _ = h := by simp
        rw[←r yz1, h, r yz2]
      have surj : pb is_surjective := fun h =>
        let g := l_inv ≫ h
        have : pb g = h := calc
          pb g = f ≫ g := rfl
          _ = (f ≫ l_inv) ≫ h := by simp
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
        have ⟨r, _⟩ := h Y
        apply r (g ≫ f) (𝟙 Y) z
      exact ⟨⟨g, l_inv⟩, ⟨g, r_inv⟩⟩

theorem theo06_01' [Category C] {X : C} {Y : C} (f : X ⟶ Y) :
  f is_invertible ↔ ∀ Z, (pushforward f Z) is_bijective := calc
    f is_invertible ↔ op f is_invertible := is_inv_iff_op_is_inv f
    _ ↔ ∀ opZ, pullback (op f) opZ is_bijective := theo06_01 (op f)
    _ ↔ ∀ Z, pullback (op f) (Op.mk Z) is_bijective := by simp[←op_is_surj]
    _ ↔ ∀ Z, pushforward f Z is_bijective
      := by simp [← pushforward_eq_op_pullback f]
