import MinkowskiMerge.Affine
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine


set_option autoImplicit false

open scoped LinearAlgebra.Projectivization OnePoint

namespace MinkowskiMerge

abbrev Direction := ℙ ℝ Vec

abbrev Slope := OnePoint ℝ

def directionOfVector (v : Vec) (hv : v ≠ 0) : Direction :=
  Projectivization.mk ℝ v hv

def directionThrough (P Q : Point) (hPQ : P ≠ Q) : Direction :=
  directionOfVector (intervalVec P Q) (by
    simpa [intervalVec] using sub_ne_zero.mpr hPQ.symm)

noncomputable def slopeOfVector (v : Vec) (hv : v ≠ 0) : Slope :=
  (OnePoint.equivProjectivization ℝ).symm
    (Projectivization.mk ℝ (v.t, v.x) (by
      intro h
      apply hv
      ext
      · exact (Prod.mk_eq_zero.mp h).2
      · exact (Prod.mk_eq_zero.mp h).1))

noncomputable def slopeThrough (P Q : Point) (hPQ : P ≠ Q) : Slope :=
  slopeOfVector (intervalVec P Q) (by
    simpa [intervalVec] using sub_ne_zero.mpr hPQ.symm)

theorem direction_smul (v : Vec) (hv : v ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    directionOfVector (r • v) (smul_ne_zero hr hv) = directionOfVector v hv := by
  rw [directionOfVector, directionOfVector, Projectivization.mk_eq_mk_iff']
  exact ⟨r, rfl⟩

theorem same_direction_iff (v w : Vec) (hv : v ≠ 0) (hw : w ≠ 0) :
    directionOfVector v hv = directionOfVector w hw ↔ ∃ r : ℝ, r • w = v := by
  exact Projectivization.mk_eq_mk_iff' ℝ v w hv hw

theorem slopeOfVector_formula (v : Vec) (hv : v ≠ 0) :
    slopeOfVector v hv = if v.x = 0 then ∞ else (↑(v.x⁻¹ * v.t) : Slope) := by
  simp [slopeOfVector, OnePoint.equivProjectivization_symm_apply_mk]

theorem slopeOfVector_eq_infinity_iff (v : Vec) (hv : v ≠ 0) :
    slopeOfVector v hv = ∞ ↔ v.x = 0 := by
  rw [slopeOfVector_formula]
  split_ifs with hx
  · simp [hx]
  · simp [hx]

theorem slopeOfVector_eq_coe (v : Vec) (hv : v ≠ 0) (hx : v.x ≠ 0) :
    slopeOfVector v hv = (↑(v.t / v.x) : Slope) := by
  rw [slopeOfVector_formula]
  simp [hx, div_eq_mul_inv, mul_comm]

theorem slopeThrough_eq_infinity_iff (P Q : Point) (hPQ : P ≠ Q) :
    slopeThrough P Q hPQ = ∞ ↔ Q.x = P.x := by
  rw [slopeThrough, slopeOfVector_eq_infinity_iff]
  change Q.x - P.x = 0 ↔ Q.x = P.x
  constructor <;> intro h <;> linarith

end MinkowskiMerge
