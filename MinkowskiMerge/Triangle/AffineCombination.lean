import MinkowskiMerge.Triangle.Metric
import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.LinearAlgebra.AffineSpace.Midpoint


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

local instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

structure BarycentricWeights where
  a : ℝ
  b : ℝ
  c : ℝ
  sum_eq_one : a + b + c = 1

namespace BarycentricWeights

def toFun (w : BarycentricWeights) : Fin 3 → ℝ := ![w.a, w.b, w.c]

@[simp] theorem toFun_zero (w : BarycentricWeights) : w.toFun 0 = w.a := rfl
@[simp] theorem toFun_one (w : BarycentricWeights) : w.toFun 1 = w.b := rfl
@[simp] theorem toFun_two (w : BarycentricWeights) : w.toFun 2 = w.c := rfl

theorem sum_toFun (w : BarycentricWeights) : ∑ i : Fin 3, w.toFun i = 1 := by
  simpa [toFun, Fin.sum_univ_succ, add_assoc] using w.sum_eq_one

def ofTwo (a b : ℝ) : BarycentricWeights where
  a := a
  b := b
  c := 1 - a - b
  sum_eq_one := by ring

noncomputable def equal : BarycentricWeights where
  a := 1 / 3
  b := 1 / 3
  c := 1 / 3
  sum_eq_one := by norm_num

end BarycentricWeights

noncomputable def barycentricPoint (T : Triangle) (w : BarycentricWeights) : Point :=
  Finset.univ.affineCombination ℝ T.vertices w.toFun

theorem barycentricPoint_eq_linearCombination (T : Triangle) (w : BarycentricWeights) :
    T.barycentricPoint w = w.a • T.A + w.b • T.B + w.c • T.C := by
  rw [barycentricPoint,
    Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using w.sum_toFun)]
  simp [vertices, BarycentricWeights.toFun, Fin.sum_univ_succ, add_assoc]

@[simp] theorem barycentricPoint_ofTwo_apply (T : Triangle) (a b : ℝ) :
    T.barycentricPoint (BarycentricWeights.ofTwo a b) =
      a • T.A + b • T.B + (1 - a - b) • T.C := by
  rw [barycentricPoint_eq_linearCombination]
  rfl

theorem signedDoubleArea_barycentric_BC (T : Triangle) (w : BarycentricWeights) :
    MinkowskiMerge.signedDoubleArea (T.barycentricPoint w) T.B T.C =
      w.a * T.signedDoubleArea := by
  rw [barycentricPoint_eq_linearCombination]
  have hc : w.c = 1 - w.a - w.b := by linarith [w.sum_eq_one]
  rw [hc]
  simp only [MinkowskiMerge.signedDoubleArea, Triangle.signedDoubleArea,
    intervalVec, vsub_eq_sub, br_apply, Vec.x_sub, Vec.t_sub,
    Vec.x_add, Vec.t_add, Vec.x_smul, Vec.t_smul]
  ring

theorem signedDoubleArea_barycentric_CA (T : Triangle) (w : BarycentricWeights) :
    MinkowskiMerge.signedDoubleArea (T.barycentricPoint w) T.C T.A =
      w.b * T.signedDoubleArea := by
  rw [barycentricPoint_eq_linearCombination]
  have hc : w.c = 1 - w.a - w.b := by linarith [w.sum_eq_one]
  rw [hc]
  simp only [MinkowskiMerge.signedDoubleArea, Triangle.signedDoubleArea,
    intervalVec, vsub_eq_sub, br_apply, Vec.x_sub, Vec.t_sub,
    Vec.x_add, Vec.t_add, Vec.x_smul, Vec.t_smul]
  ring

theorem signedDoubleArea_barycentric_AB (T : Triangle) (w : BarycentricWeights) :
    MinkowskiMerge.signedDoubleArea (T.barycentricPoint w) T.A T.B =
      w.c * T.signedDoubleArea := by
  rw [barycentricPoint_eq_linearCombination]
  have hc : w.c = 1 - w.a - w.b := by linarith [w.sum_eq_one]
  rw [hc]
  simp only [MinkowskiMerge.signedDoubleArea, Triangle.signedDoubleArea,
    intervalVec, vsub_eq_sub, br_apply, Vec.x_sub, Vec.t_sub,
    Vec.x_add, Vec.t_add, Vec.x_smul, Vec.t_smul]
  ring

noncomputable def midpointA (T : Triangle) : Point := midpoint ℝ T.B T.C

noncomputable def midpointB (T : Triangle) : Point := midpoint ℝ T.C T.A

noncomputable def midpointC (T : Triangle) : Point := midpoint ℝ T.A T.B

@[simp] theorem midpointA_vsub_B (T : Triangle) :
    intervalVec T.B T.midpointA = (2 : ℝ)⁻¹ • T.sideVecA := by
  simp [midpointA, sideVecA, intervalVec, invOf_eq_inv]

@[simp] theorem midpointB_vsub_C (T : Triangle) :
    intervalVec T.C T.midpointB = (2 : ℝ)⁻¹ • T.sideVecB := by
  simp [midpointB, sideVecB, intervalVec, invOf_eq_inv]

@[simp] theorem midpointC_vsub_A (T : Triangle) :
    intervalVec T.A T.midpointC = (2 : ℝ)⁻¹ • T.sideVecC := by
  simp [midpointC, sideVecC, intervalVec, invOf_eq_inv]

noncomputable def centroid (T : Triangle) : Point :=
  Finset.univ.centroid ℝ T.vertices

theorem centroid_eq_linearCombination (T : Triangle) :
    T.centroid = (1 / 3 : ℝ) • T.A + (1 / 3 : ℝ) • T.B + (1 / 3 : ℝ) • T.C := by
  rw [centroid, Finset.centroid_def,
    Finset.affineCombination_eq_linear_combination]
  · simp [Finset.centroidWeights, vertices, Fin.sum_univ_succ, add_assoc]
  · norm_num [Finset.centroidWeights, Fin.sum_univ_succ]

theorem centroid_eq_barycentricPoint (T : Triangle) :
    T.centroid = T.barycentricPoint BarycentricWeights.equal := by
  rw [centroid_eq_linearCombination, barycentricPoint_eq_linearCombination]
  rfl

end

end Triangle
end MinkowskiMerge
