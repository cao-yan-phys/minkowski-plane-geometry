import MinkowskiMerge.Triangle.Feuerbach

set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

private theorem circumradius_eq_I_mul_abs_formula (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsSpacelike) :
    T.circumradius hN = Complex.I *
      ((T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
        (2 * |T.signedDoubleArea|) : ℝ) : ℂ) := by
  have hD : T.signedDoubleArea ≠ 0 := hN.signedDoubleArea_ne_zero
  have habsD : |T.signedDoubleArea| ≠ 0 := abs_ne_zero.mpr hD
  have hA : T.sideAbsLengthA ^ 2 = T.sideSqA :=
    absLength_sq_of_spacelike hT.1
  have hB : T.sideAbsLengthB ^ 2 = T.sideSqB :=
    absLength_sq_of_spacelike hT.2.1
  have hC : T.sideAbsLengthC ^ 2 = T.sideSqC :=
    absLength_sq_of_spacelike hT.2.2
  have hr : 0 ≤ T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
      (2 * |T.signedDoubleArea|) := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (absLength_nonneg _) (absLength_nonneg _))
        (absLength_nonneg _))
      (mul_nonneg (by norm_num) (abs_nonneg _))
  have hR : T.circumradiusSqAt (T.circumcenter hN) =
      -(T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
        (2 * |T.signedDoubleArea|)) ^ 2 := by
    rw [circumradiusSq_eq_sideSq_product_div_areaSq T hN, ← hA, ← hB, ← hC]
    field_simp [hD, habsD]
    rw [sq_abs]
    ring
  unfold circumradius circumcircle LorentzCircle.complexRadius
  exact positiveComplexSqrt_eq_I_mul_real_of_eq_neg_sq hr hR

private theorem circumradius_eq_real_abs_formula (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsTimelike) :
    T.circumradius hN =
      ((T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
        (2 * |T.signedDoubleArea|) : ℝ) : ℂ) := by
  have hD : T.signedDoubleArea ≠ 0 := hN.signedDoubleArea_ne_zero
  have habsD : |T.signedDoubleArea| ≠ 0 := abs_ne_zero.mpr hD
  have hA : T.sideSqA = -T.sideAbsLengthA ^ 2 := by
    have h := absLength_sq_of_timelike hT.1
    have h' : T.sideAbsLengthA ^ 2 = -q T.sideVecA := by
      simpa [sideAbsLengthA] using h
    change q T.sideVecA = -T.sideAbsLengthA ^ 2
    linarith [h']
  have hB : T.sideSqB = -T.sideAbsLengthB ^ 2 := by
    have h := absLength_sq_of_timelike hT.2.1
    have h' : T.sideAbsLengthB ^ 2 = -q T.sideVecB := by
      simpa [sideAbsLengthB] using h
    change q T.sideVecB = -T.sideAbsLengthB ^ 2
    linarith [h']
  have hC : T.sideSqC = -T.sideAbsLengthC ^ 2 := by
    have h := absLength_sq_of_timelike hT.2.2
    have h' : T.sideAbsLengthC ^ 2 = -q T.sideVecC := by
      simpa [sideAbsLengthC] using h
    change q T.sideVecC = -T.sideAbsLengthC ^ 2
    linarith [h']
  have hr : 0 ≤ T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
      (2 * |T.signedDoubleArea|) := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (absLength_nonneg _) (absLength_nonneg _))
        (absLength_nonneg _))
      (mul_nonneg (by norm_num) (abs_nonneg _))
  have hR : T.circumradiusSqAt (T.circumcenter hN) =
      (T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
        (2 * |T.signedDoubleArea|)) ^ 2 := by
    rw [circumradiusSq_eq_sideSq_product_div_areaSq T hN, hA, hB, hC]
    field_simp [hD, habsD]
    rw [sq_abs]
    ring
  unfold circumradius circumcircle LorentzCircle.complexRadius
  exact positiveComplexSqrt_eq_real_of_eq_sq hr hR

theorem circumradius_eq_neg_sideProduct_div_four_complexArea (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) :
    T.circumradius hN =
      -(T.sideComplexLengthA * T.sideComplexLengthB * T.sideComplexLengthC) /
        (4 * T.complexArea) := by
  rcases hT with hS | hT
  · have hD : T.signedDoubleArea ≠ 0 := hN.signedDoubleArea_ne_zero
    have habsD : |T.signedDoubleArea| ≠ 0 := abs_ne_zero.mpr hD
    rw [circumradius_eq_I_mul_abs_formula T hN hS]
    simp only [sideAbsLengthA, sideAbsLengthB, sideAbsLengthC]
    unfold sideComplexLengthA sideComplexLengthB sideComplexLengthC complexArea areaMagnitude
    rw [complexLength_eq_absLength_of_spacelike hS.1,
      complexLength_eq_absLength_of_spacelike hS.2.1,
      complexLength_eq_absLength_of_spacelike hS.2.2]
    push_cast
    field_simp [habsD, Complex.I_ne_zero]
    rw [pow_two Complex.I, Complex.I_mul_I]
    ring
  · have hD : T.signedDoubleArea ≠ 0 := hN.signedDoubleArea_ne_zero
    have habsD : |T.signedDoubleArea| ≠ 0 := abs_ne_zero.mpr hD
    rw [circumradius_eq_real_abs_formula T hN hT]
    simp only [sideAbsLengthA, sideAbsLengthB, sideAbsLengthC]
    unfold sideComplexLengthA sideComplexLengthB sideComplexLengthC complexArea areaMagnitude
    rw [complexLength_eq_I_mul_absLength_of_timelike hT.1,
      complexLength_eq_I_mul_absLength_of_timelike hT.2.1,
      complexLength_eq_I_mul_absLength_of_timelike hT.2.2]
    push_cast
    field_simp [habsD, Complex.I_ne_zero]
    rw [pow_two Complex.I, Complex.I_mul_I]
    ring

end

end Triangle
end MinkowskiMerge
