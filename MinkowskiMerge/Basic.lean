import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic


set_option autoImplicit false

namespace MinkowskiMerge

abbrev Vec := ℝ × ℝ

abbrev Point := Vec

namespace Vec

def x (v : Vec) : ℝ := v.1

def t (v : Vec) : ℝ := v.2

@[ext]
theorem ext {v w : Vec} (hx : x v = x w) (ht : t v = t w) : v = w := by
  exact Prod.ext hx ht

@[simp] theorem x_mk (a b : ℝ) : x (a, b) = a := rfl
@[simp] theorem t_mk (a b : ℝ) : t (a, b) = b := rfl
@[simp] theorem x_zero : x (0 : Vec) = 0 := rfl
@[simp] theorem t_zero : t (0 : Vec) = 0 := rfl
@[simp] theorem x_add (v w : Vec) : x (v + w) = x v + x w := rfl
@[simp] theorem t_add (v w : Vec) : t (v + w) = t v + t w := rfl
@[simp] theorem x_sub (v w : Vec) : x (v - w) = x v - x w := rfl
@[simp] theorem t_sub (v w : Vec) : t (v - w) = t v - t w := rfl
@[simp] theorem x_neg (v : Vec) : x (-v) = -x v := rfl
@[simp] theorem t_neg (v : Vec) : t (-v) = -t v := rfl
@[simp] theorem x_smul (r : ℝ) (v : Vec) : x (r • v) = r * x v := rfl
@[simp] theorem t_smul (r : ℝ) (v : Vec) : t (r • v) = r * t v := rfl

end Vec

end MinkowskiMerge
