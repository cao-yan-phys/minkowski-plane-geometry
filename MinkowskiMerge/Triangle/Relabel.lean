import MinkowskiMerge.Triangle.NinePoint


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

def rotate (T : Triangle) : Triangle := ⟨T.B, T.C, T.A⟩

def rotateTwo (T : Triangle) : Triangle := T.rotate.rotate

@[simp] theorem rotate_A (T : Triangle) : T.rotate.A = T.B := rfl
@[simp] theorem rotate_B (T : Triangle) : T.rotate.B = T.C := rfl
@[simp] theorem rotate_C (T : Triangle) : T.rotate.C = T.A := rfl

@[simp] theorem rotateTwo_A (T : Triangle) : T.rotateTwo.A = T.C := rfl
@[simp] theorem rotateTwo_B (T : Triangle) : T.rotateTwo.B = T.A := rfl
@[simp] theorem rotateTwo_C (T : Triangle) : T.rotateTwo.C = T.B := rfl

@[simp] theorem rotate_rotate_rotate (T : Triangle) :
    T.rotate.rotate.rotate = T := by
  rfl

@[simp] theorem rotate_sideVecA (T : Triangle) :
    T.rotate.sideVecA = T.sideVecB := rfl

@[simp] theorem rotate_sideVecB (T : Triangle) :
    T.rotate.sideVecB = T.sideVecC := rfl

@[simp] theorem rotate_sideVecC (T : Triangle) :
    T.rotate.sideVecC = T.sideVecA := rfl

@[simp] theorem rotate_sideSqA (T : Triangle) :
    T.rotate.sideSqA = T.sideSqB := rfl

@[simp] theorem rotate_sideSqB (T : Triangle) :
    T.rotate.sideSqB = T.sideSqC := rfl

@[simp] theorem rotate_sideSqC (T : Triangle) :
    T.rotate.sideSqC = T.sideSqA := rfl

@[simp] theorem rotate_sideAbsLengthA (T : Triangle) :
    T.rotate.sideAbsLengthA = T.sideAbsLengthB := rfl

@[simp] theorem rotate_sideAbsLengthB (T : Triangle) :
    T.rotate.sideAbsLengthB = T.sideAbsLengthC := rfl

@[simp] theorem rotate_sideAbsLengthC (T : Triangle) :
    T.rotate.sideAbsLengthC = T.sideAbsLengthA := rfl

@[simp] theorem rotate_sideComplexLengthA (T : Triangle) :
    T.rotate.sideComplexLengthA = T.sideComplexLengthB := rfl

@[simp] theorem rotate_sideComplexLengthB (T : Triangle) :
    T.rotate.sideComplexLengthB = T.sideComplexLengthC := rfl

@[simp] theorem rotate_sideComplexLengthC (T : Triangle) :
    T.rotate.sideComplexLengthC = T.sideComplexLengthA := rfl

@[simp] theorem rotate_signedDoubleArea (T : Triangle) :
    T.rotate.signedDoubleArea = T.signedDoubleArea := by
  change MinkowskiMerge.signedDoubleArea T.B T.C T.A = T.signedDoubleArea
  exact T.signedDoubleArea_cyclic

@[simp] theorem rotate_areaMagnitude (T : Triangle) :
    T.rotate.areaMagnitude = T.areaMagnitude := by
  simp [areaMagnitude]

@[simp] theorem rotate_perimeterAbs (T : Triangle) :
    T.rotate.perimeterAbs = T.perimeterAbs := by
  unfold perimeterAbs
  rw [rotate_sideAbsLengthA, rotate_sideAbsLengthB, rotate_sideAbsLengthC]
  ring

@[simp] theorem rotate_perimeterComplex (T : Triangle) :
    T.rotate.perimeterComplex = T.perimeterComplex := by
  unfold perimeterComplex
  rw [rotate_sideComplexLengthA, rotate_sideComplexLengthB, rotate_sideComplexLengthC]
  ring

@[simp] theorem rotate_semiperimeterComplex (T : Triangle) :
    T.rotate.semiperimeterComplex = T.semiperimeterComplex := by
  unfold semiperimeterComplex
  rw [rotate_perimeterComplex]

theorem rotate_isSpacelike_iff (T : Triangle) :
    T.rotate.IsSpacelike ↔ T.IsSpacelike := by
  unfold IsSpacelike
  constructor
  · rintro ⟨hB, hC, hA⟩
    exact ⟨hA, hB, hC⟩
  · rintro ⟨hA, hB, hC⟩
    exact ⟨hB, hC, hA⟩

theorem rotate_isTimelike_iff (T : Triangle) :
    T.rotate.IsTimelike ↔ T.IsTimelike := by
  unfold IsTimelike
  constructor
  · rintro ⟨hB, hC, hA⟩
    exact ⟨hA, hB, hC⟩
  · rintro ⟨hA, hB, hC⟩
    exact ⟨hB, hC, hA⟩

theorem rotate_isNonMixed_iff (T : Triangle) :
    T.rotate.IsNonMixed ↔ T.IsNonMixed := by
  unfold IsNonMixed
  rw [rotate_isSpacelike_iff, rotate_isTimelike_iff]

theorem rotate_nondegenerate_iff (T : Triangle) :
    T.rotate.Nondegenerate ↔ T.Nondegenerate := by
  rw [nondegenerate_iff_signedDoubleArea_ne_zero,
    nondegenerate_iff_signedDoubleArea_ne_zero, rotate_signedDoubleArea]

def rotateNondegenerate (T : Triangle) (hT : T.Nondegenerate) :
    T.rotate.Nondegenerate :=
  (rotate_nondegenerate_iff T).mpr hT

def rotateIsNonMixed (T : Triangle) (hT : T.IsNonMixed) : T.rotate.IsNonMixed :=
  (rotate_isNonMixed_iff T).mpr hT

private theorem circumcenter_isCircumcenter_rotate (T : Triangle)
    (hT : T.Nondegenerate) :
    T.rotate.IsCircumcenter (T.circumcenter hT) := by
  have hO := circumcenter_isCircumcenter T hT
  change intervalSq (T.circumcenter hT) T.B =
      intervalSq (T.circumcenter hT) T.C ∧
    intervalSq (T.circumcenter hT) T.C =
      intervalSq (T.circumcenter hT) T.A
  exact ⟨hO.2, hO.intervalSq_A_eq_C.symm⟩

theorem rotate_circumcenter (T : Triangle) (hT : T.Nondegenerate) :
    (T.rotate).circumcenter (rotateNondegenerate T hT) = T.circumcenter hT := by
  exact (IsCircumcenter.eq_circumcenter (rotateNondegenerate T hT)
    (circumcenter_isCircumcenter_rotate T hT)).symm

theorem rotate_circumradiusSqAt (T : Triangle) (hT : T.Nondegenerate) :
    (T.rotate).circumradiusSqAt
      ((T.rotate).circumcenter (rotateNondegenerate T hT)) =
      T.circumradiusSqAt (T.circumcenter hT) := by
  rw [rotate_circumcenter]
  change intervalSq (T.circumcenter hT) T.B =
    intervalSq (T.circumcenter hT) T.A
  exact (circumcenter_isCircumcenter T hT).1.symm

@[simp] theorem rotate_excenterDenomC (T : Triangle) :
    T.rotate.excenterDenomC = T.excenterDenomA := by
  unfold excenterDenomC excenterDenomA signedPerimeter
  simp only [one_mul, neg_one_mul]
  rw [rotate_sideAbsLengthA, rotate_sideAbsLengthB, rotate_sideAbsLengthC]
  ring

@[simp] theorem rotate_excenterDenomA (T : Triangle) :
    T.rotate.excenterDenomA = T.excenterDenomB := by
  unfold excenterDenomA excenterDenomB signedPerimeter
  simp only [one_mul, neg_one_mul]
  rw [rotate_sideAbsLengthA, rotate_sideAbsLengthB, rotate_sideAbsLengthC]
  ring

@[simp] theorem rotate_excenterDenomB (T : Triangle) :
    T.rotate.excenterDenomB = T.excenterDenomC := by
  unfold excenterDenomB excenterDenomC signedPerimeter
  simp only [one_mul, neg_one_mul]
  rw [rotate_sideAbsLengthA, rotate_sideAbsLengthB, rotate_sideAbsLengthC]
  ring

@[simp] theorem rotate_lambdaC (T : Triangle) :
    T.rotate.lambdaC = T.lambdaA := by
  unfold lambdaC lambdaA
  change branchSign (T.sideAbsLengthB + T.sideAbsLengthC - T.sideAbsLengthA) =
    branchSign (T.sideAbsLengthB + T.sideAbsLengthC - T.sideAbsLengthA)
  rfl

@[simp] theorem rotate_lambdaA (T : Triangle) :
    T.rotate.lambdaA = T.lambdaB := by
  unfold lambdaA lambdaB
  change branchSign (T.sideAbsLengthC + T.sideAbsLengthA - T.sideAbsLengthB) =
    branchSign (T.sideAbsLengthC + T.sideAbsLengthA - T.sideAbsLengthB)
  rfl

@[simp] theorem rotate_lambdaB (T : Triangle) :
    T.rotate.lambdaB = T.lambdaC := by
  change branchSign (T.rotate.sideAbsLengthC + T.rotate.sideAbsLengthA -
      T.rotate.sideAbsLengthB) =
    branchSign (T.sideAbsLengthA + T.sideAbsLengthB - T.sideAbsLengthC)
  rw [rotate_sideAbsLengthA, rotate_sideAbsLengthB, rotate_sideAbsLengthC]

theorem rotate_excenterC_eq_excenterA (T : Triangle) (hA : T.excenterDenomA ≠ 0) :
    T.rotate.excenterC (by simpa only [rotate_excenterDenomC] using hA) =
      T.excenterA hA := by
  rw [excenterC_eq_sideCombination, excenterA_eq_sideCombination]
  simp only [rotate_A, rotate_B, rotate_C, rotate_sideAbsLengthA,
    rotate_sideAbsLengthB, rotate_sideAbsLengthC, rotate_excenterDenomC]
  module

theorem rotate_excenterA_eq_excenterB (T : Triangle) (hB : T.excenterDenomB ≠ 0) :
    T.rotate.excenterA (by simpa only [rotate_excenterDenomA] using hB) =
      T.excenterB hB := by
  rw [excenterA_eq_sideCombination, excenterB_eq_sideCombination]
  simp only [rotate_A, rotate_B, rotate_C, rotate_sideAbsLengthA,
    rotate_sideAbsLengthB, rotate_sideAbsLengthC, rotate_excenterDenomA]
  module

@[simp] theorem rotateTwo_excenterDenomC (T : Triangle) :
    T.rotateTwo.excenterDenomC = T.excenterDenomB := by
  unfold rotateTwo
  rw [rotate_excenterDenomC, rotate_excenterDenomA]

theorem rotateTwo_excenterC_eq_excenterB (T : Triangle)
    (hB : T.excenterDenomB ≠ 0) :
    T.rotateTwo.excenterC (by simpa only [rotateTwo_excenterDenomC] using hB) =
      T.excenterB hB := by
  let hA : T.rotate.excenterDenomA ≠ 0 := by
    simpa only [rotate_excenterDenomA] using hB
  calc
    T.rotateTwo.excenterC (by simpa only [rotateTwo_excenterDenomC] using hB) =
        T.rotate.excenterA hA := by
          simpa only [rotateTwo] using rotate_excenterC_eq_excenterA T.rotate hA
    _ = T.excenterB hB := rotate_excenterA_eq_excenterB T hB

end

end Triangle
end MinkowskiMerge
