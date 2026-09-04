import MinkowskiMerge.Cycle.Matrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable section

namespace Cycle

def discriminant (C : Cycle) : ℝ :=
  q C.linearCoeff - C.quadCoeff * C.constantCoeff

def pairing (C D : Cycle) : ℝ :=
  dot C.linearCoeff D.linearCoeff -
    (C.quadCoeff * D.constantCoeff +
      D.quadCoeff * C.constantCoeff) / 2

theorem pairing_comm (C D : Cycle) : pairing C D = pairing D C := by
  simp only [pairing, dot_comm C.linearCoeff D.linearCoeff]
  ring

@[simp] theorem pairing_self (C : Cycle) :
    pairing C C = discriminant C := by
  simp only [pairing, discriminant, q_apply, dot_apply]
  ring

@[simp] theorem discriminant_scale (a : ℝ) (C : Cycle) :
    discriminant (C.scale a) = a ^ 2 * discriminant C := by
  simp only [discriminant, scale_linearCoeff, scale_quadCoeff,
    scale_constantCoeff, q_smul]
  ring

@[simp] theorem pairing_scale (a b : ℝ) (C D : Cycle) :
    pairing (C.scale a) (D.scale b) = a * b * pairing C D := by
  simp only [pairing, scale_linearCoeff, scale_quadCoeff,
    scale_constantCoeff, dot_smul_left, dot_smul_right]
  ring

@[simp] theorem discriminant_ofCircle (C : LorentzCircle) :
    discriminant (ofCircle C) = C.radiusSq := by
  simp only [discriminant, ofCircle_linearCoeff, ofCircle_quadCoeff,
    ofCircle_constantCoeff, q_neg, one_mul]
  ring

theorem pairing_ofCircle (C D : LorentzCircle) :
    pairing (ofCircle C) (ofCircle D) =
      (C.radiusSq + D.radiusSq - intervalSq C.center D.center) / 2 := by
  simp only [pairing, ofCircle_linearCoeff, ofCircle_quadCoeff,
    ofCircle_constantCoeff, one_mul, dot_apply, intervalSq, intervalVec,
    vsub_eq_sub, q_apply, Vec.x_neg, Vec.t_neg, Vec.x_sub, Vec.t_sub]
  ring

def matrixPairing (M N : MatrixRep) : ℝ :=
  (M 0 0 * N 1 1 + M 1 1 * N 0 0 -
    M 0 1 * N 1 0 - M 1 0 * N 0 1) / 2

theorem matrixPairing_comm (M N : MatrixRep) :
    matrixPairing M N = matrixPairing N M := by
  simp only [matrixPairing]
  ring

@[simp] theorem matrixPairing_self (M : MatrixRep) :
    matrixPairing M M = Matrix.det M := by
  rw [Matrix.det_fin_two]
  simp only [matrixPairing]
  ring

@[simp] theorem det_toMatrix (C : Cycle) :
    Matrix.det (toMatrix C) = discriminant C := by
  rw [Matrix.det_fin_two]
  simp [toMatrix, discriminant, q_apply]
  ring

@[simp] theorem matrixPairing_toMatrix (C D : Cycle) :
    matrixPairing (toMatrix C) (toMatrix D) = pairing C D := by
  simp [matrixPairing, toMatrix, pairing, dot_apply]
  ring

end Cycle

end

end MinkowskiMerge
