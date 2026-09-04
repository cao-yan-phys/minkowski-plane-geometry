import MinkowskiMerge.Cycle.Pairing


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable section

namespace Cycle

def normal (C : Cycle) (P : Point) : Vec :=
  C.quadCoeff • P + C.linearCoeff

@[simp] theorem normal_scale (a : ℝ) (C : Cycle) (P : Point) :
    (C.scale a).normal P = a • C.normal P := by
  simp [normal, mul_smul, smul_add]

theorem eval_add (C : Cycle) (P : Point) (v : Vec) :
    C.eval (P + v) = C.eval P +
      2 * dot (C.normal P) v + C.quadCoeff * q v := by
  simp only [eval, normal, q_apply, dot_apply, Vec.x_add, Vec.t_add,
    Vec.x_smul, Vec.t_smul]
  ring

theorem q_normal (C : Cycle) (P : Point) :
    q (C.normal P) = C.quadCoeff * C.eval P + C.discriminant := by
  simp only [normal, eval, discriminant, q_apply, dot_apply,
    Vec.x_add, Vec.t_add, Vec.x_smul, Vec.t_smul]
  ring

theorem dot_normal (C D : Cycle) (P : Point) :
    dot (C.normal P) (D.normal P) = C.pairing D +
      (D.quadCoeff * C.eval P + C.quadCoeff * D.eval P) / 2 := by
  simp only [normal, eval, pairing, q_apply, dot_apply,
    Vec.x_add, Vec.t_add, Vec.x_smul, Vec.t_smul]
  ring

theorem q_normal_eq_discriminant_of_mem {C : Cycle} {P : Point}
    (hP : P ∈ C) : q (C.normal P) = C.discriminant := by
  change C.eval P = 0 at hP
  rw [q_normal, hP]
  ring

theorem dot_normal_eq_pairing_of_mem {C D : Cycle} {P : Point}
    (hC : P ∈ C) (hD : P ∈ D) :
    dot (C.normal P) (D.normal P) = C.pairing D := by
  change C.eval P = 0 at hC
  change D.eval P = 0 at hD
  rw [dot_normal, hC, hD]
  ring

def IsFirstOrderContactAt (C D : Cycle) (P : Point) : Prop :=
  P ∈ C ∧ P ∈ D ∧ br (C.normal P) (D.normal P) = 0

def IsRegularAt (C : Cycle) (P : Point) : Prop :=
  P ∈ C ∧ C.normal P ≠ 0

def IsProperTangentAt (C D : Cycle) (P : Point) : Prop :=
  IsFirstOrderContactAt C D P ∧
    IsRegularAt C P ∧ IsRegularAt D P ∧ ¬ScaleEquivalent C D

theorem IsFirstOrderContactAt.symm {C D : Cycle} {P : Point}
    (h : IsFirstOrderContactAt C D P) : IsFirstOrderContactAt D C P := by
  refine ⟨h.2.1, h.1, ?_⟩
  rw [br_swap, h.2.2, neg_zero]

def matrixPartialU (M : MatrixRep) (P : Point) : ℝ :=
  M 0 0 * lightconeV P + M 0 1

def matrixPartialV (M : MatrixRep) (P : Point) : ℝ :=
  M 0 0 * lightconeU P + M 1 0

def matrixGradientDet (M N : MatrixRep) (P : Point) : ℝ :=
  matrixPartialU M P * matrixPartialV N P -
    matrixPartialV M P * matrixPartialU N P

@[simp] theorem matrixPartialU_toMatrix (C : Cycle) (P : Point) :
    matrixPartialU (toMatrix C) P =
      -(C.normal P).x - (C.normal P).t := by
  simp [matrixPartialU, toMatrix, lightconeV, normal]
  ring

@[simp] theorem matrixPartialV_toMatrix (C : Cycle) (P : Point) :
    matrixPartialV (toMatrix C) P =
      (C.normal P).x - (C.normal P).t := by
  simp [matrixPartialV, toMatrix, lightconeU, normal]
  ring

@[simp] theorem matrixGradientDet_toMatrix
    (C D : Cycle) (P : Point) :
    matrixGradientDet (toMatrix C) (toMatrix D) P =
      2 * br (C.normal P) (D.normal P) := by
  simp only [matrixGradientDet, matrixPartialU_toMatrix,
    matrixPartialV_toMatrix, br_apply]
  ring

def HasMatrixFirstOrderContactAt (M N : MatrixRep) (P : Point) : Prop :=
  matrixEval M P = 0 ∧ matrixEval N P = 0 ∧
    matrixGradientDet M N P = 0

theorem isFirstOrderContactAt_iff_matrixGradient
    (C D : Cycle) (P : Point) :
    IsFirstOrderContactAt C D P ↔
      HasMatrixFirstOrderContactAt (toMatrix C) (toMatrix D) P := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [mem_iff] using h.1
    · simpa [mem_iff] using h.2.1
    · rw [matrixGradientDet_toMatrix, h.2.2, mul_zero]
  · intro h
    rcases h with ⟨hC, hD, hgradient⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [mem_iff] using hC
    · simpa [mem_iff] using hD
    · rw [matrixGradientDet_toMatrix] at hgradient
      linarith

theorem isFirstOrderContactAt_iff_pairing_sq_eq
    {C D : Cycle} {P : Point} (hC : P ∈ C) (hD : P ∈ D) :
    IsFirstOrderContactAt C D P ↔
      C.pairing D ^ 2 = C.discriminant * D.discriminant := by
  have hgram := gram_identity (C.normal P) (D.normal P)
  rw [dot_normal_eq_pairing_of_mem hC hD,
    q_normal_eq_discriminant_of_mem hC,
    q_normal_eq_discriminant_of_mem hD] at hgram
  constructor
  · intro h
    rw [h.2.2] at hgram
    norm_num at hgram
    linarith
  · intro hpair
    refine ⟨hC, hD, ?_⟩
    nlinarith [sq_nonneg (br (C.normal P) (D.normal P))]

theorem isFirstOrderContactAt_iff_matrixPairing_sq_eq
    {C D : Cycle} {P : Point} (hC : P ∈ C) (hD : P ∈ D) :
    IsFirstOrderContactAt C D P ↔
      matrixPairing (toMatrix C) (toMatrix D) ^ 2 =
        Matrix.det (toMatrix C) * Matrix.det (toMatrix D) := by
  simpa using isFirstOrderContactAt_iff_pairing_sq_eq hC hD

@[simp] theorem normal_ofCircle (C : LorentzCircle) (P : Point) :
    (ofCircle C).normal P = intervalVec C.center P := by
  ext <;> simp [normal, intervalVec, vsub_eq_sub, sub_eq_add_neg]

@[simp] theorem normal_ofPointNormalLine
    (O : Point) (lineNormal : Vec) (P : Point) :
    (ofPointNormalLine O lineNormal).normal P =
      (2 : ℝ)⁻¹ • lineNormal := by
  simp [normal, ofPointNormalLine]

theorem ofCircle_injective : Function.Injective ofCircle := by
  intro C D h
  have hcenterNeg : -C.center = -D.center := by
    simpa using congrArg Cycle.linearCoeff h
  have hcenter : C.center = D.center := neg_injective hcenterNeg
  have hconstant : q C.center - C.radiusSq =
      q D.center - D.radiusSq := by
    simpa using congrArg Cycle.constantCoeff h
  have hradius : C.radiusSq = D.radiusSq := by
    rw [hcenter] at hconstant
    linarith
  rcases C with ⟨centerC, radiusC⟩
  rcases D with ⟨centerD, radiusD⟩
  simp only at hcenter hradius
  subst centerD
  subst radiusD
  rfl

@[simp] theorem scaleEquivalent_ofCircle_iff
    (C D : LorentzCircle) :
    ScaleEquivalent (ofCircle C) (ofCircle D) ↔ C = D := by
  constructor
  · rintro ⟨a, ha, hEq⟩
    have hk := congrArg Cycle.quadCoeff hEq
    simp only [ofCircle_quadCoeff, scale_quadCoeff, mul_one] at hk
    have haOne : a = 1 := hk.symm
    subst a
    rw [scale_one] at hEq
    exact (ofCircle_injective hEq).symm
  · intro h
    subst D
    exact scaleEquivalent_refl (ofCircle C)

@[simp] theorem isFirstOrderContactAt_ofCircle_iff
    (C D : LorentzCircle) (P : Point) :
    IsFirstOrderContactAt (ofCircle C) (ofCircle D) P ↔
      LorentzCircle.IsFirstOrderContactAt C D P := by
  simp [IsFirstOrderContactAt, LorentzCircle.IsFirstOrderContactAt,
    sub_eq_zero]

@[simp] theorem isRegularAt_ofCircle_iff
    (C : LorentzCircle) (P : Point) :
    IsRegularAt (ofCircle C) P ↔ LorentzCircle.IsRegularAt C P := by
  simp [IsRegularAt, LorentzCircle.IsRegularAt, sub_eq_zero]

@[simp] theorem isProperTangentAt_ofCircle_iff
    (C D : LorentzCircle) (P : Point) :
    IsProperTangentAt (ofCircle C) (ofCircle D) P ↔
      LorentzCircle.IsProperTangentAt C D P := by
  simp [IsProperTangentAt, LorentzCircle.IsProperTangentAt,
    LorentzCircle.AreCoincident]

end Cycle

end

end MinkowskiMerge
