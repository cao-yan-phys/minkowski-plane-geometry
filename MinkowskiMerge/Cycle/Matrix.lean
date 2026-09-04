import MinkowskiMerge.Cycle.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable section

open scoped Matrix

namespace Cycle

def lightconeU (P : Point) : ℝ := P.t - P.x

def lightconeV (P : Point) : ℝ := P.t + P.x

abbrev MatrixRep := Matrix (Fin 2) (Fin 2) ℝ

def lightconeRow (P : Point) : Fin 2 → ℝ :=
  ![lightconeU P, 1]

def lightconeColumn (P : Point) : Fin 2 → ℝ :=
  ![lightconeV P, 1]

def matrixEval (M : MatrixRep) (P : Point) : ℝ :=
  lightconeRow P ⬝ᵥ (M *ᵥ lightconeColumn P)

def toMatrix (C : Cycle) : MatrixRep :=
  !![-C.quadCoeff, -(C.linearCoeff.x + C.linearCoeff.t);
      C.linearCoeff.x - C.linearCoeff.t, C.constantCoeff]

def ofMatrix (M : MatrixRep) : Cycle where
  quadCoeff := -M 0 0
  linearCoeff :=
    ((M 1 0 - M 0 1) / 2, -(M 0 1 + M 1 0) / 2)
  constantCoeff := M 1 1

@[simp] theorem ofMatrix_toMatrix (C : Cycle) :
    ofMatrix (toMatrix C) = C := by
  ext <;> simp [ofMatrix, toMatrix] <;> ring

@[simp] theorem toMatrix_ofMatrix (M : MatrixRep) :
    toMatrix (ofMatrix M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofMatrix, toMatrix] <;> ring

theorem toMatrix_injective : Function.Injective toMatrix := by
  intro C D h
  simpa using congrArg ofMatrix h

@[simp] theorem matrixEval_toMatrix (C : Cycle) (P : Point) :
    matrixEval (toMatrix C) P = C.eval P := by
  simp [matrixEval, lightconeRow, lightconeColumn, lightconeU, lightconeV,
    toMatrix, dotProduct, Matrix.mulVec, eval, q_apply, dot_apply]
  ring

@[simp] theorem matrixEval_toMatrix_ofCircle
    (C : LorentzCircle) (P : Point) :
    matrixEval (toMatrix (ofCircle C)) P =
      intervalSq C.center P - C.radiusSq := by
  rw [matrixEval_toMatrix, eval_ofCircle]

theorem mem_iff_matrixEval (C : Cycle) (P : Point) :
    P ∈ C ↔ matrixEval (toMatrix C) P = 0 := by
  rw [mem_iff, matrixEval_toMatrix]

@[simp] theorem toMatrix_scale (a : ℝ) (C : Cycle) :
    toMatrix (C.scale a) = a • toMatrix C := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, scale] <;> ring

@[simp] theorem matrixEval_smul (a : ℝ) (M : MatrixRep) (P : Point) :
    matrixEval (a • M) P = a * matrixEval M P := by
  simp [matrixEval, dotProduct, Matrix.mulVec]
  ring

theorem ScaleEquivalent.toMatrix {C D : Cycle}
    (h : ScaleEquivalent C D) :
    ∃ a : ℝ, a ≠ 0 ∧ toMatrix D = a • toMatrix C := by
  rcases h with ⟨a, ha, rfl⟩
  exact ⟨a, ha, toMatrix_scale a C⟩

end Cycle

end

end MinkowskiMerge
