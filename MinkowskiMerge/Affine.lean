import MinkowskiMerge.Form
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic


set_option autoImplicit false

namespace MinkowskiMerge

abbrev Line := AffineSubspace ℝ Point

def lineThrough (P Q : Point) : Line := affineSpan ℝ {P, Q}

def intervalVec (P Q : Point) : Vec := Q -ᵥ P

def intervalSq (P Q : Point) : ℝ := q (intervalVec P Q)

def IsCollinear (P Q R : Point) : Prop := R ∈ lineThrough P Q

@[simp] theorem left_mem_line (P Q : Point) : P ∈ lineThrough P Q := by
  exact left_mem_affineSpan_pair ℝ P Q

@[simp] theorem right_mem_line (P Q : Point) : Q ∈ lineThrough P Q := by
  exact right_mem_affineSpan_pair ℝ P Q

theorem mem_line_iff {P Q R : Point} :
    R ∈ lineThrough P Q ↔ ∃ r : ℝ, AffineMap.lineMap P Q r = R := by
  exact mem_affineSpan_pair_iff_exists_lineMap_eq

@[simp] theorem intervalVec_self (P : Point) : intervalVec P P = 0 := by
  simp [intervalVec]

theorem intervalVec_rev (P Q : Point) : intervalVec Q P = -intervalVec P Q := by
  simp [intervalVec]

theorem intervalVec_add (P Q R : Point) :
    intervalVec P Q + intervalVec Q R = intervalVec P R := by
  simp only [intervalVec, vsub_eq_sub]
  module

theorem intervalVec_eq_sub_from (O P Q : Point) :
    intervalVec P Q = intervalVec O Q - intervalVec O P := by
  simp only [intervalVec, vsub_eq_sub]
  module

@[simp] theorem intervalSq_self (P : Point) : intervalSq P P = 0 := by
  simp [intervalSq]

theorem intervalSq_comm (P Q : Point) : intervalSq P Q = intervalSq Q P := by
  rw [intervalSq, intervalSq, intervalVec_rev, q_neg]

end MinkowskiMerge
