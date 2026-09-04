import MinkowskiMerge.Perpendicular
import MinkowskiMerge.Triangle.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

def sideVecA (T : Triangle) : Vec := intervalVec T.B T.C

def sideVecB (T : Triangle) : Vec := intervalVec T.C T.A

def sideVecC (T : Triangle) : Vec := intervalVec T.A T.B

def sideSqA (T : Triangle) : ℝ := intervalSq T.B T.C

def sideSqB (T : Triangle) : ℝ := intervalSq T.C T.A

def sideSqC (T : Triangle) : ℝ := intervalSq T.A T.B

noncomputable def sideTypeA (T : Triangle) : CausalType := causalType T.sideVecA

noncomputable def sideTypeB (T : Triangle) : CausalType := causalType T.sideVecB

noncomputable def sideTypeC (T : Triangle) : CausalType := causalType T.sideVecC

noncomputable def sideAbsLengthA (T : Triangle) : ℝ := absLength T.sideVecA

noncomputable def sideAbsLengthB (T : Triangle) : ℝ := absLength T.sideVecB

noncomputable def sideAbsLengthC (T : Triangle) : ℝ := absLength T.sideVecC

noncomputable def sideComplexLengthA (T : Triangle) : ℂ := complexLength T.sideVecA

noncomputable def sideComplexLengthB (T : Triangle) : ℂ := complexLength T.sideVecB

noncomputable def sideComplexLengthC (T : Triangle) : ℂ := complexLength T.sideVecC

noncomputable def perimeterAbs (T : Triangle) : ℝ :=
  T.sideAbsLengthA + T.sideAbsLengthB + T.sideAbsLengthC

noncomputable def semiperimeterAbs (T : Triangle) : ℝ := T.perimeterAbs / 2

noncomputable def perimeterComplex (T : Triangle) : ℂ :=
  T.sideComplexLengthA + T.sideComplexLengthB + T.sideComplexLengthC

noncomputable def semiperimeterComplex (T : Triangle) : ℂ := T.perimeterComplex / 2

def SidesNonNull (T : Triangle) : Prop :=
  IsNonNullLine T.B T.C ∧ IsNonNullLine T.C T.A ∧ IsNonNullLine T.A T.B

def IsSpacelike (T : Triangle) : Prop :=
  MinkowskiMerge.IsSpacelike T.sideVecA ∧
    MinkowskiMerge.IsSpacelike T.sideVecB ∧
    MinkowskiMerge.IsSpacelike T.sideVecC

def IsTimelike (T : Triangle) : Prop :=
  MinkowskiMerge.IsTimelike T.sideVecA ∧
    MinkowskiMerge.IsTimelike T.sideVecB ∧
    MinkowskiMerge.IsTimelike T.sideVecC

def signedDoubleArea (T : Triangle) : ℝ :=
  MinkowskiMerge.signedDoubleArea T.A T.B T.C

noncomputable def areaMagnitude (T : Triangle) : ℝ := |T.signedDoubleArea| / 2

@[simp] theorem sideSqA_eq_q (T : Triangle) : T.sideSqA = q T.sideVecA := rfl
@[simp] theorem sideSqB_eq_q (T : Triangle) : T.sideSqB = q T.sideVecB := rfl
@[simp] theorem sideSqC_eq_q (T : Triangle) : T.sideSqC = q T.sideVecC := rfl

@[simp] theorem sideComplexLengthA_sq (T : Triangle) :
    T.sideComplexLengthA ^ 2 = (T.sideSqA : ℂ) := by
  exact complexLength_sq T.sideVecA

@[simp] theorem sideComplexLengthB_sq (T : Triangle) :
    T.sideComplexLengthB ^ 2 = (T.sideSqB : ℂ) := by
  exact complexLength_sq T.sideVecB

@[simp] theorem sideComplexLengthC_sq (T : Triangle) :
    T.sideComplexLengthC ^ 2 = (T.sideSqC : ℂ) := by
  exact complexLength_sq T.sideVecC

theorem sideVec_cyclic_sum (T : Triangle) :
    T.sideVecA + T.sideVecB + T.sideVecC = 0 := by
  simp only [sideVecA, sideVecB, sideVecC, intervalVec, vsub_eq_sub]
  module

theorem signedDoubleArea_cyclic (T : Triangle) :
    MinkowskiMerge.signedDoubleArea T.B T.C T.A = T.signedDoubleArea := by
  simp only [Triangle.signedDoubleArea, MinkowskiMerge.signedDoubleArea,
    intervalVec, vsub_eq_sub, br_apply, Vec.x_sub, Vec.t_sub]
  ring

theorem signedDoubleArea_cyclic_two (T : Triangle) :
    MinkowskiMerge.signedDoubleArea T.C T.A T.B = T.signedDoubleArea := by
  simp only [Triangle.signedDoubleArea, MinkowskiMerge.signedDoubleArea,
    intervalVec, vsub_eq_sub, br_apply, Vec.x_sub, Vec.t_sub]
  ring

theorem signedDoubleArea_swap (T : Triangle) :
    MinkowskiMerge.signedDoubleArea T.A T.C T.B = -T.signedDoubleArea := by
  simp only [Triangle.signedDoubleArea, MinkowskiMerge.signedDoubleArea,
    intervalVec, vsub_eq_sub, br_apply, Vec.x_sub, Vec.t_sub]
  ring

theorem Nondegenerate.sideVecA_ne_zero {T : Triangle} (hT : T.Nondegenerate) :
    T.sideVecA ≠ 0 := by
  simpa [sideVecA, intervalVec] using sub_ne_zero.mpr hT.B_ne_C.symm

theorem Nondegenerate.sideVecB_ne_zero {T : Triangle} (hT : T.Nondegenerate) :
    T.sideVecB ≠ 0 := by
  simpa [sideVecB, intervalVec] using sub_ne_zero.mpr hT.C_ne_A.symm

theorem Nondegenerate.sideVecC_ne_zero {T : Triangle} (hT : T.Nondegenerate) :
    T.sideVecC ≠ 0 := by
  simpa [sideVecC, intervalVec] using sub_ne_zero.mpr hT.A_ne_B.symm

theorem nondegenerate_iff_signedDoubleArea_ne_zero (T : Triangle) :
    T.Nondegenerate ↔ T.signedDoubleArea ≠ 0 := by
  rw [Nondegenerate, vertices, affineIndependent_iff_not_collinear_set]
  constructor
  · intro hnotcol harea
    have hAB : T.A ≠ T.B := ne₁₂_of_not_collinear hnotcol
    have huv : intervalVec T.A T.B ≠ 0 := by
      simpa [intervalVec] using sub_ne_zero.mpr hAB.symm
    have hbr : br (intervalVec T.A T.B) (intervalVec T.A T.C) = 0 := by
      exact harea
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp
      ((mem_span_singleton_iff_br_eq_zero huv (intervalVec T.A T.C)).2 hbr)
    have hline : T.C ∈ lineThrough T.A T.B := by
      rw [mem_line_iff]
      refine ⟨r, ?_⟩
      calc
        AffineMap.lineMap T.A T.B r = r • (T.B - T.A) + T.A :=
          AffineMap.lineMap_apply_module' _ _ _
        _ = (T.C - T.A) + T.A := by
          rw [show r • (T.B - T.A) = T.C - T.A by
            simpa only [intervalVec, vsub_eq_sub] using hr]
        _ = T.C := sub_add_cancel _ _
    apply hnotcol
    have hcol := collinear_insert_of_mem_affineSpan_pair hline
    convert hcol using 1
    ext x
    simp [or_comm, or_left_comm]
  · intro harea hcol
    have hAB : T.A ≠ T.B := by
      intro hAB
      apply harea
      simp [Triangle.signedDoubleArea, MinkowskiMerge.signedDoubleArea, hAB,
        intervalVec]
    have hCline : T.C ∈ lineThrough T.A T.B :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAB
    rcases mem_line_iff.mp hCline with ⟨r, hr⟩
    apply harea
    unfold Triangle.signedDoubleArea
    rw [← hr]
    simp only [MinkowskiMerge.signedDoubleArea,
      intervalVec_lineMap, intervalVec_self, sub_zero, br_apply,
      Vec.x_smul, Vec.t_smul]
    ring

theorem Nondegenerate.signedDoubleArea_ne_zero {T : Triangle}
    (hT : T.Nondegenerate) : T.signedDoubleArea ≠ 0 :=
  (nondegenerate_iff_signedDoubleArea_ne_zero T).mp hT

end Triangle
end MinkowskiMerge
