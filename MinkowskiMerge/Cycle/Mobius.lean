import MinkowskiMerge.Cycle.Contact
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable section

open scoped Matrix

abbrev GL2 := GL (Fin 2) ℝ

abbrev LightconeMobius := GL2 × GL2

namespace LightconeMobius

def left (g : LightconeMobius) : GL2 := g.1

def right (g : LightconeMobius) : GL2 := g.2

def coordDenom (A : GL2) (z : ℝ) : ℝ :=
  A 1 0 * z + A 1 1

def coordMap (A : GL2) (z : ℝ) : ℝ :=
  (A 0 0 * z + A 0 1) / coordDenom A z

def coordVector (z : ℝ) : Fin 2 → ℝ :=
  ![z, 1]

theorem adjugate_mulVec_coordVector (A : GL2) (z : ℝ)
    (hdenom : coordDenom A z ≠ 0) :
    Matrix.adjugate (A : Cycle.MatrixRep) *ᵥ coordVector (coordMap A z) =
      (Matrix.det (A : Cycle.MatrixRep) / coordDenom A z) • coordVector z := by
  have hdenom' : A 1 0 * z + A 1 1 ≠ 0 := by
    simpa [coordDenom] using hdenom
  have denom_eq : A 1 0 * z + A 1 1 = A 1 1 + z * A 1 0 := by
    ring
  have hdenom'' : A 1 1 + z * A 1 0 ≠ 0 := by
    rw [← denom_eq]
    exact hdenom'
  ext i
  fin_cases i
  · simp only [coordVector, coordMap, coordDenom, Matrix.adjugate_fin_two,
      Matrix.mulVec, dotProduct, Matrix.det_fin_two, Fin.sum_univ_two,
      Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val',
      Matrix.of_apply, Matrix.cons_val', Pi.smul_apply, smul_eq_mul,
      mul_one]
    change
      A 1 1 * ((A 0 0 * z + A 0 1) / (A 1 0 * z + A 1 1)) - A 0 1 =
        ((A 0 0 * A 1 1 - A 0 1 * A 1 0) /
          (A 1 0 * z + A 1 1)) * z
    rw [denom_eq]
    field_simp [hdenom'']
    ring
  · simp only [coordVector, coordMap, coordDenom, Matrix.adjugate_fin_two,
      Matrix.mulVec, dotProduct, Matrix.det_fin_two, Fin.sum_univ_two,
      Fin.isValue, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val',
      Matrix.of_apply, Matrix.cons_val', Pi.smul_apply, smul_eq_mul,
      mul_one]
    change
      -A 1 0 * ((A 0 0 * z + A 0 1) / (A 1 0 * z + A 1 1)) + A 0 0 =
        (A 0 0 * A 1 1 - A 0 1 * A 1 0) /
          (A 1 0 * z + A 1 1)
    field_simp [hdenom']
    ring

def pointOfLightcone (u v : ℝ) : Point :=
  ((v - u) / 2, (u + v) / 2)

@[simp] theorem lightconeU_pointOfLightcone (u v : ℝ) :
    Cycle.lightconeU (pointOfLightcone u v) = u := by
  simp [Cycle.lightconeU, pointOfLightcone]
  ring

@[simp] theorem lightconeV_pointOfLightcone (u v : ℝ) :
    Cycle.lightconeV (pointOfLightcone u v) = v := by
  simp [Cycle.lightconeV, pointOfLightcone]
  ring

@[simp] theorem pointOfLightcone_lightcone (P : Point) :
    pointOfLightcone (Cycle.lightconeU P) (Cycle.lightconeV P) = P := by
  ext <;> simp [pointOfLightcone, Cycle.lightconeU, Cycle.lightconeV]

def mapCompactified (g : LightconeMobius)
    (Z : OnePoint ℝ × OnePoint ℝ) : OnePoint ℝ × OnePoint ℝ :=
  (g.left • Z.1, g.right • Z.2)

theorem mapCompactified_finite {g : LightconeMobius} {u v : ℝ}
    (hu : coordDenom g.left u ≠ 0)
    (hv : coordDenom g.right v ≠ 0) :
    g.mapCompactified ((u : OnePoint ℝ), (v : OnePoint ℝ)) =
      ((coordMap g.left u : OnePoint ℝ),
        (coordMap g.right v : OnePoint ℝ)) := by
  have hu' : g.left 1 0 * u + g.left 1 1 ≠ 0 := by
    simpa [coordDenom] using hu
  have hv' : g.right 1 0 * v + g.right 1 1 ≠ 0 := by
    simpa [coordDenom] using hv
  simp [mapCompactified, OnePoint.smul_some_eq_ite, coordMap, coordDenom,
    hu', hv']

def leftDenom (g : LightconeMobius) (P : Point) : ℝ :=
  coordDenom g.left (Cycle.lightconeU P)

def rightDenom (g : LightconeMobius) (P : Point) : ℝ :=
  coordDenom g.right (Cycle.lightconeV P)

def mapPoint (g : LightconeMobius) (P : Point) : Point :=
  pointOfLightcone
    (coordMap g.left (Cycle.lightconeU P))
    (coordMap g.right (Cycle.lightconeV P))

@[simp] theorem lightconeU_mapPoint (g : LightconeMobius) (P : Point) :
    Cycle.lightconeU (g.mapPoint P) =
      coordMap g.left (Cycle.lightconeU P) := by
  simp [mapPoint]

@[simp] theorem lightconeV_mapPoint (g : LightconeMobius) (P : Point) :
    Cycle.lightconeV (g.mapPoint P) =
      coordMap g.right (Cycle.lightconeV P) := by
  simp [mapPoint]

def scaleFactor (g : LightconeMobius) : ℝ :=
  Matrix.det (g.left : Cycle.MatrixRep) *
    Matrix.det (g.right : Cycle.MatrixRep)

theorem scaleFactor_ne_zero (g : LightconeMobius) :
    g.scaleFactor ≠ 0 := by
  exact mul_ne_zero
    (Matrix.GeneralLinearGroup.det_ne_zero g.left)
    (Matrix.GeneralLinearGroup.det_ne_zero g.right)

def mapMatrix (g : LightconeMobius) (M : Cycle.MatrixRep) :
    Cycle.MatrixRep :=
  (Matrix.adjugate (g.left : Cycle.MatrixRep))ᵀ * M *
    Matrix.adjugate (g.right : Cycle.MatrixRep)

def mapCycle (g : LightconeMobius) (C : Cycle) : Cycle :=
  Cycle.ofMatrix (g.mapMatrix C.toMatrix)

@[simp] theorem toMatrix_mapCycle (g : LightconeMobius) (C : Cycle) :
    (g.mapCycle C).toMatrix = g.mapMatrix C.toMatrix := by
  exact Cycle.toMatrix_ofMatrix _

theorem adjugate_left_mulVec_row (g : LightconeMobius) (P : Point)
    (hu : g.leftDenom P ≠ 0) :
    Matrix.adjugate (g.left : Cycle.MatrixRep) *ᵥ
        Cycle.lightconeRow (g.mapPoint P) =
      (Matrix.det (g.left : Cycle.MatrixRep) / g.leftDenom P) •
        Cycle.lightconeRow P := by
  simpa [Cycle.lightconeRow, coordVector, leftDenom] using
    adjugate_mulVec_coordVector g.left (Cycle.lightconeU P) hu

theorem adjugate_right_mulVec_column (g : LightconeMobius) (P : Point)
    (hv : g.rightDenom P ≠ 0) :
    Matrix.adjugate (g.right : Cycle.MatrixRep) *ᵥ
        Cycle.lightconeColumn (g.mapPoint P) =
      (Matrix.det (g.right : Cycle.MatrixRep) / g.rightDenom P) •
        Cycle.lightconeColumn P := by
  simpa [Cycle.lightconeColumn, coordVector, rightDenom] using
    adjugate_mulVec_coordVector g.right (Cycle.lightconeV P) hv

theorem matrixEval_mapMatrix_mapPoint
    (g : LightconeMobius) (M : Cycle.MatrixRep) (P : Point)
    (hu : g.leftDenom P ≠ 0) (hv : g.rightDenom P ≠ 0) :
    Cycle.matrixEval (g.mapMatrix M) (g.mapPoint P) =
      g.scaleFactor * Cycle.matrixEval M P /
        (g.leftDenom P * g.rightDenom P) := by
  unfold Cycle.matrixEval mapMatrix
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    adjugate_left_mulVec_row g P hu,
    adjugate_right_mulVec_column g P hv,
    Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  unfold scaleFactor
  field_simp [hu, hv]

@[simp] theorem det_mapMatrix (g : LightconeMobius) (M : Cycle.MatrixRep) :
    Matrix.det (g.mapMatrix M) = g.scaleFactor * Matrix.det M := by
  rw [mapMatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_adjugate, Matrix.det_adjugate]
  simp [scaleFactor]
  ring

theorem matrixPairing_eq_det_add (M N : Cycle.MatrixRep) :
    Cycle.matrixPairing M N =
      (Matrix.det (M + N) - Matrix.det M - Matrix.det N) / 2 := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.det_fin_two]
  simp [Cycle.matrixPairing]
  ring

@[simp] theorem mapMatrix_add (g : LightconeMobius)
    (M N : Cycle.MatrixRep) :
    g.mapMatrix (M + N) = g.mapMatrix M + g.mapMatrix N := by
  simp [mapMatrix, Matrix.mul_add, Matrix.add_mul]

@[simp] theorem matrixPairing_mapMatrix (g : LightconeMobius)
    (M N : Cycle.MatrixRep) :
    Cycle.matrixPairing (g.mapMatrix M) (g.mapMatrix N) =
      g.scaleFactor * Cycle.matrixPairing M N := by
  rw [matrixPairing_eq_det_add, ← mapMatrix_add, det_mapMatrix,
    det_mapMatrix, det_mapMatrix, matrixPairing_eq_det_add]
  ring

@[simp] theorem discriminant_mapCycle (g : LightconeMobius) (C : Cycle) :
    (g.mapCycle C).discriminant = g.scaleFactor * C.discriminant := by
  rw [← Cycle.det_toMatrix, toMatrix_mapCycle, det_mapMatrix,
    Cycle.det_toMatrix]

@[simp] theorem pairing_mapCycle (g : LightconeMobius) (C D : Cycle) :
    (g.mapCycle C).pairing (g.mapCycle D) =
      g.scaleFactor * C.pairing D := by
  rw [← Cycle.matrixPairing_toMatrix, toMatrix_mapCycle, toMatrix_mapCycle,
    matrixPairing_mapMatrix, Cycle.matrixPairing_toMatrix]

theorem mapPoint_mem_mapCycle {g : LightconeMobius} {C : Cycle} {P : Point}
    (hu : g.leftDenom P ≠ 0) (hv : g.rightDenom P ≠ 0)
    (hP : P ∈ C) : g.mapPoint P ∈ g.mapCycle C := by
  change (g.mapCycle C).eval (g.mapPoint P) = 0
  rw [← Cycle.matrixEval_toMatrix, toMatrix_mapCycle,
    matrixEval_mapMatrix_mapPoint g C.toMatrix P hu hv,
    Cycle.matrixEval_toMatrix]
  change C.eval P = 0 at hP
  rw [hP]
  ring

theorem map_firstOrderContactAt {g : LightconeMobius} {C D : Cycle}
    {P : Point} (hu : g.leftDenom P ≠ 0) (hv : g.rightDenom P ≠ 0)
    (h : Cycle.IsFirstOrderContactAt C D P) :
    Cycle.IsFirstOrderContactAt (g.mapCycle C) (g.mapCycle D)
      (g.mapPoint P) := by
  have hC : g.mapPoint P ∈ g.mapCycle C :=
    mapPoint_mem_mapCycle hu hv h.1
  have hD : g.mapPoint P ∈ g.mapCycle D :=
    mapPoint_mem_mapCycle hu hv h.2.1
  apply (Cycle.isFirstOrderContactAt_iff_pairing_sq_eq hC hD).2
  have hpair :=
    (Cycle.isFirstOrderContactAt_iff_pairing_sq_eq h.1 h.2.1).1 h
  rw [pairing_mapCycle, discriminant_mapCycle, discriminant_mapCycle]
  calc
    (g.scaleFactor * C.pairing D) ^ 2 =
        g.scaleFactor ^ 2 * C.pairing D ^ 2 := by ring
    _ = g.scaleFactor ^ 2 *
        (C.discriminant * D.discriminant) := by rw [hpair]
    _ = g.scaleFactor * C.discriminant *
        (g.scaleFactor * D.discriminant) := by ring

end LightconeMobius

end

end MinkowskiMerge
