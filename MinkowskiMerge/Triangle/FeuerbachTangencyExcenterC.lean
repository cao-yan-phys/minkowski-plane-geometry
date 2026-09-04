import MinkowskiMerge.Triangle.FeuerbachTangencyIncenter


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

noncomputable def exradiusCMagnitude (T : Triangle) : ℝ :=
  |T.signedDoubleArea| / |T.excenterDenomC|

theorem exradiusCMagnitude_pos (T : Triangle) (hN : T.Nondegenerate)
    (hC : T.excenterDenomC ≠ 0) : 0 < T.exradiusCMagnitude := by
  dsimp [exradiusCMagnitude]
  exact div_pos (abs_pos.mpr hN.signedDoubleArea_ne_zero) (abs_pos.mpr hC)

private theorem semiperimeterComplex_sub_sideC_eq_spacelike
    {T : Triangle} (hS : T.IsSpacelike) :
    T.semiperimeterComplex - T.sideComplexLengthC =
      (T.excenterDenomC / 2 : ℂ) := by
  unfold semiperimeterComplex perimeterComplex sideComplexLengthA
    sideComplexLengthB sideComplexLengthC
  rw [complexLength_eq_absLength_of_spacelike hS.1,
    complexLength_eq_absLength_of_spacelike hS.2.1,
    complexLength_eq_absLength_of_spacelike hS.2.2]
  simp [sideAbsLengthA, sideAbsLengthB, sideAbsLengthC,
    excenterDenomC, signedPerimeter]
  ring

private theorem semiperimeterComplex_sub_sideC_eq_timelike
    {T : Triangle} (hT : T.IsTimelike) :
    T.semiperimeterComplex - T.sideComplexLengthC =
      Complex.I * (T.excenterDenomC / 2 : ℂ) := by
  unfold semiperimeterComplex perimeterComplex sideComplexLengthA
    sideComplexLengthB sideComplexLengthC
  rw [complexLength_eq_I_mul_absLength_of_timelike hT.1,
    complexLength_eq_I_mul_absLength_of_timelike hT.2.1,
    complexLength_eq_I_mul_absLength_of_timelike hT.2.2]
  simp [sideAbsLengthA, sideAbsLengthB, sideAbsLengthC,
    excenterDenomC, signedPerimeter]
  ring

theorem exradiusC_eq_I_mul_magnitude_of_spacelike (T : Triangle)
    (hN : T.Nondegenerate) (hS : T.IsSpacelike)
    (hC : T.excenterDenomC ≠ 0) :
    T.exradiusC (Or.inl hS) hC = Complex.I * (T.exradiusCMagnitude : ℂ) := by
  have hD : |T.excenterDenomC| ≠ 0 := abs_ne_zero.mpr hC
  have hA : |T.signedDoubleArea| ≠ 0 :=
    abs_ne_zero.mpr hN.signedDoubleArea_ne_zero
  have hLambda := lambdaC_mul_abs_denominator T
  have hLambda' : T.lambdaC * |T.excenterDenomC| = T.excenterDenomC := by
    simpa [excenterDenomC, signedPerimeter] using hLambda
  rw [exradiusC_eq_lambdaC_mul_complexArea_div_semiperimeter_sub_side
    T (Or.inl hS) hC, semiperimeterComplex_sub_sideC_eq_spacelike hS]
  unfold complexArea areaMagnitude exradiusCMagnitude
  push_cast
  field_simp [hC, hD, hA]
  exact_mod_cast hLambda'

theorem exradiusC_eq_magnitude_of_timelike (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsTimelike)
    (hC : T.excenterDenomC ≠ 0) :
    T.exradiusC (Or.inr hT) hC = (T.exradiusCMagnitude : ℂ) := by
  have hD : |T.excenterDenomC| ≠ 0 := abs_ne_zero.mpr hC
  have hA : |T.signedDoubleArea| ≠ 0 :=
    abs_ne_zero.mpr hN.signedDoubleArea_ne_zero
  have hLambda := lambdaC_mul_abs_denominator T
  have hLambda' : T.lambdaC * |T.excenterDenomC| = T.excenterDenomC := by
    simpa [excenterDenomC, signedPerimeter] using hLambda
  rw [exradiusC_eq_lambdaC_mul_complexArea_div_semiperimeter_sub_side
    T (Or.inr hT) hC, semiperimeterComplex_sub_sideC_eq_timelike hT]
  unfold complexArea areaMagnitude exradiusCMagnitude
  field_simp [hC, hD, hA, Complex.I_ne_zero]
  push_cast
  field_simp [hA, hD]
  exact_mod_cast hLambda'

theorem excircleC_radiusSq_eq_neg_magnitude_sq_spacelike (T : Triangle)
    (hN : T.Nondegenerate) (hS : T.IsSpacelike)
    (hC : T.excenterDenomC ≠ 0) :
    (T.excircleC (Or.inl hS) hC).radiusSq = -T.exradiusCMagnitude ^ 2 := by
  have hE := exradiusC_eq_I_mul_magnitude_of_spacelike T hN hS hC
  have hSq := exradiusC_sq_eq_sideDistanceSq T (Or.inl hS) hC
  rw [hE] at hSq
  have hComplex : (Complex.I * (T.exradiusCMagnitude : ℂ)) ^ 2 =
      ((-T.exradiusCMagnitude ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, pow_two Complex.I, Complex.I_mul_I]
    push_cast
    ring
  rw [hComplex] at hSq
  have hReal : -T.exradiusCMagnitude ^ 2 = T.exradiusSqC (Or.inl hS) hC := by
    exact_mod_cast hSq
  rw [excircleC_radiusSq]
  exact hReal.symm

theorem excircleC_radiusSq_eq_magnitude_sq_timelike (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsTimelike)
    (hC : T.excenterDenomC ≠ 0) :
    (T.excircleC (Or.inr hT) hC).radiusSq = T.exradiusCMagnitude ^ 2 := by
  have hE := exradiusC_eq_magnitude_of_timelike T hN hT hC
  have hSq := exradiusC_sq_eq_sideDistanceSq T (Or.inr hT) hC
  rw [hE] at hSq
  have hComplex : (T.exradiusCMagnitude : ℂ) ^ 2 =
      ((T.exradiusCMagnitude ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hComplex] at hSq
  have hReal : T.exradiusCMagnitude ^ 2 = T.exradiusSqC (Or.inr hT) hC := by
    exact_mod_cast hSq
  rw [excircleC_radiusSq]
  exact hReal.symm

theorem ninePointCenter_excenterC_intervalSq_eq_neg_signedDifference_sq_spacelike
    (T : Triangle) (hN : T.Nondegenerate) (hS : T.IsSpacelike)
    (hC : T.excenterDenomC ≠ 0) :
    intervalSq (T.ninePointCenter hN) (T.excenterC hC) =
      -(T.ninePointRadiusMagnitude - T.lambdaC * T.exradiusCMagnitude) ^ 2 := by
  have hEq := hasFeuerbachExcircleCEquation T hN (Or.inl hS) hC
  rw [hasFeuerbachExcircleCEquation_iff] at hEq
  rw [circumradius_eq_I_mul_sideAbsProduct_div_two_absDoubleArea_of_spacelike
      T hN hS,
    exradiusC_eq_I_mul_magnitude_of_spacelike T hN hS hC] at hEq
  let u : ℝ := T.ninePointRadiusMagnitude - T.lambdaC * T.exradiusCMagnitude
  have hSq : (T.ninePointCircle hN).centerDistance
      (T.excircleC (Or.inl hS) hC) ^ 2 = (Complex.I * (u : ℂ)) ^ 2 := by
    calc
      (T.ninePointCircle hN).centerDistance (T.excircleC (Or.inl hS) hC) ^ 2 =
          (Complex.I *
            ((T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
              (2 * |T.signedDoubleArea|) : ℝ) : ℂ) / 2 -
            (T.lambdaC : ℂ) * (Complex.I * (T.exradiusCMagnitude : ℂ))) ^ 2 := hEq
      _ = (Complex.I * (u : ℂ)) ^ 2 := by
        dsimp [u, ninePointRadiusMagnitude]
        push_cast
        ring
  rw [LorentzCircle.centerDistance_sq] at hSq
  have hComplex : (Complex.I * (u : ℂ)) ^ 2 = ((-u ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, pow_two Complex.I, Complex.I_mul_I]
    push_cast
    ring
  rw [hComplex] at hSq
  have hReal : intervalSq (T.ninePointCenter hN) (T.excenterC hC) = -u ^ 2 := by
    exact_mod_cast hSq
  simpa [u] using hReal

theorem ninePointCenter_excenterC_intervalSq_eq_signedDifference_sq_timelike
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsTimelike)
    (hC : T.excenterDenomC ≠ 0) :
    intervalSq (T.ninePointCenter hN) (T.excenterC hC) =
      (T.ninePointRadiusMagnitude - T.lambdaC * T.exradiusCMagnitude) ^ 2 := by
  have hEq := hasFeuerbachExcircleCEquation T hN (Or.inr hT) hC
  rw [hasFeuerbachExcircleCEquation_iff] at hEq
  rw [circumradius_eq_sideAbsProduct_div_two_absDoubleArea_of_timelike
      T hN hT,
    exradiusC_eq_magnitude_of_timelike T hN hT hC] at hEq
  let u : ℝ := T.ninePointRadiusMagnitude - T.lambdaC * T.exradiusCMagnitude
  have hSq : (T.ninePointCircle hN).centerDistance
      (T.excircleC (Or.inr hT) hC) ^ 2 = (u : ℂ) ^ 2 := by
    calc
      (T.ninePointCircle hN).centerDistance (T.excircleC (Or.inr hT) hC) ^ 2 =
          (((T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
              (2 * |T.signedDoubleArea|) : ℝ) : ℂ) / 2 -
            (T.lambdaC : ℂ) * (T.exradiusCMagnitude : ℂ)) ^ 2 := hEq
      _ = (u : ℂ) ^ 2 := by
        dsimp [u, ninePointRadiusMagnitude]
        push_cast
        ring
  rw [LorentzCircle.centerDistance_sq] at hSq
  have hComplex : (u : ℂ) ^ 2 = ((u ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hComplex] at hSq
  have hReal : intervalSq (T.ninePointCenter hN) (T.excenterC hC) = u ^ 2 := by
    exact_mod_cast hSq
  simpa [u] using hReal

noncomputable def excircleCFeuerbachContactPointSpacelike (T : Triangle)
    (hN : T.Nondegenerate) (hS : T.IsSpacelike)
    (hC : T.excenterDenomC ≠ 0) : Point :=
  LorentzCircle.tangentPointOfRadiusDifference (T.ninePointCircle hN)
    (T.excircleC (Or.inl hS) hC) T.ninePointRadiusMagnitude
    (T.lambdaC * T.exradiusCMagnitude)

noncomputable def excircleCFeuerbachContactPointTimelike (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsTimelike)
    (hC : T.excenterDenomC ≠ 0) : Point :=
  LorentzCircle.tangentPointOfRadiusDifference (T.ninePointCircle hN)
    (T.excircleC (Or.inr hT) hC) T.ninePointRadiusMagnitude
    (T.lambdaC * T.exradiusCMagnitude)

theorem isTangentAt_excircleC_spacelike (T : Triangle) (hN : T.Nondegenerate)
    (hS : T.IsSpacelike) (hC : T.excenterDenomC ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaC * T.exradiusCMagnitude ≠ 0) :
    LorentzCircle.IsTangentAt (T.ninePointCircle hN) (T.excircleC (Or.inl hS) hC)
      (T.excircleCFeuerbachContactPointSpacelike hN hS hC) := by
  have hD := ninePointCenter_excenterC_intervalSq_eq_neg_signedDifference_sq_spacelike
    T hN hS hC
  have h1 := ninePointCircle_radiusSq_eq_neg_magnitude_sq_spacelike T hN hS
  have h2 := excircleC_radiusSq_eq_neg_magnitude_sq_spacelike T hN hS hC
  have hLambda := lambdaC_sq T
  have hD' : intervalSq (T.ninePointCircle hN).center
      (T.excircleC (Or.inl hS) hC).center =
      (-1 : ℝ) *
        (T.ninePointRadiusMagnitude - T.lambdaC * T.exradiusCMagnitude) ^ 2 := by
    simpa using hD
  have h1' : (T.ninePointCircle hN).radiusSq =
      (-1 : ℝ) * T.ninePointRadiusMagnitude ^ 2 := by
    simpa using h1
  have h2' : (T.excircleC (Or.inl hS) hC).radiusSq =
      (-1 : ℝ) * (T.lambdaC * T.exradiusCMagnitude) ^ 2 := by
    rw [h2, mul_pow, hLambda]
    ring
  simpa [excircleCFeuerbachContactPointSpacelike] using
    (LorentzCircle.isTangentAt_of_radiusDifferenceData
      (T.ninePointCircle hN) (T.excircleC (Or.inl hS) hC) (-1)
      T.ninePointRadiusMagnitude (T.lambdaC * T.exradiusCMagnitude)
      hGap hD' h1' h2')

theorem isTangentAt_excircleC_timelike (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsTimelike) (hC : T.excenterDenomC ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaC * T.exradiusCMagnitude ≠ 0) :
    LorentzCircle.IsTangentAt (T.ninePointCircle hN) (T.excircleC (Or.inr hT) hC)
      (T.excircleCFeuerbachContactPointTimelike hN hT hC) := by
  have hD := ninePointCenter_excenterC_intervalSq_eq_signedDifference_sq_timelike
    T hN hT hC
  have h1 := ninePointCircle_radiusSq_eq_magnitude_sq_timelike T hN hT
  have h2 := excircleC_radiusSq_eq_magnitude_sq_timelike T hN hT hC
  have hLambda := lambdaC_sq T
  have hD' : intervalSq (T.ninePointCircle hN).center
      (T.excircleC (Or.inr hT) hC).center =
      (1 : ℝ) *
        (T.ninePointRadiusMagnitude - T.lambdaC * T.exradiusCMagnitude) ^ 2 := by
    simpa using hD
  have h1' : (T.ninePointCircle hN).radiusSq =
      (1 : ℝ) * T.ninePointRadiusMagnitude ^ 2 := by
    simpa using h1
  have h2' : (T.excircleC (Or.inr hT) hC).radiusSq =
      (1 : ℝ) * (T.lambdaC * T.exradiusCMagnitude) ^ 2 := by
    rw [h2, mul_pow, hLambda]
    ring
  simpa [excircleCFeuerbachContactPointTimelike] using
    (LorentzCircle.isTangentAt_of_radiusDifferenceData
      (T.ninePointCircle hN) (T.excircleC (Or.inr hT) hC) 1
      T.ninePointRadiusMagnitude (T.lambdaC * T.exradiusCMagnitude)
      hGap hD' h1' h2')

theorem isProperTangentAt_excircleC_spacelike
    (T : Triangle) (hN : T.Nondegenerate) (hS : T.IsSpacelike)
    (hC : T.excenterDenomC ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaC * T.exradiusCMagnitude ≠ 0) :
    LorentzCircle.IsProperTangentAt
      (T.ninePointCircle hN) (T.excircleC (Or.inl hS) hC)
      (T.excircleCFeuerbachContactPointSpacelike hN hS hC) := by
  have hNM : T.IsNonMixed := Or.inl hS
  have hD := ninePointCenter_excenterC_intervalSq_eq_neg_signedDifference_sq_spacelike
    T hN hS hC
  have h1 := ninePointCircle_radiusSq_eq_neg_magnitude_sq_spacelike T hN hS
  have h2 := excircleC_radiusSq_eq_neg_magnitude_sq_spacelike T hN hS hC
  have hLambda := lambdaC_sq T
  have hD' : intervalSq (T.ninePointCircle hN).center
      (T.excircleC (Or.inl hS) hC).center =
      (-1 : ℝ) *
        (T.ninePointRadiusMagnitude - T.lambdaC * T.exradiusCMagnitude) ^ 2 := by
    simpa using hD
  have h1' : (T.ninePointCircle hN).radiusSq =
      (-1 : ℝ) * T.ninePointRadiusMagnitude ^ 2 := by
    simpa using h1
  have h2' : (T.excircleC (Or.inl hS) hC).radiusSq =
      (-1 : ℝ) * (T.lambdaC * T.exradiusCMagnitude) ^ 2 := by
    rw [h2, mul_pow, hLambda]
    ring
  simpa [excircleCFeuerbachContactPointSpacelike] using
    (LorentzCircle.isProperTangentAt_of_radiusDifferenceData
      (T.ninePointCircle hN) (T.excircleC (Or.inl hS) hC) (-1)
      T.ninePointRadiusMagnitude (T.lambdaC * T.exradiusCMagnitude)
      (by norm_num) (ne_of_gt (ninePointRadiusMagnitude_pos T hN hNM))
      (mul_ne_zero (lambdaC_ne_zero T)
        (ne_of_gt (exradiusCMagnitude_pos T hN hC)))
      hGap hD' h1' h2')

theorem isProperTangentAt_excircleC_timelike
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsTimelike)
    (hC : T.excenterDenomC ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaC * T.exradiusCMagnitude ≠ 0) :
    LorentzCircle.IsProperTangentAt
      (T.ninePointCircle hN) (T.excircleC (Or.inr hT) hC)
      (T.excircleCFeuerbachContactPointTimelike hN hT hC) := by
  have hNM : T.IsNonMixed := Or.inr hT
  have hD := ninePointCenter_excenterC_intervalSq_eq_signedDifference_sq_timelike
    T hN hT hC
  have h1 := ninePointCircle_radiusSq_eq_magnitude_sq_timelike T hN hT
  have h2 := excircleC_radiusSq_eq_magnitude_sq_timelike T hN hT hC
  have hLambda := lambdaC_sq T
  have hD' : intervalSq (T.ninePointCircle hN).center
      (T.excircleC (Or.inr hT) hC).center =
      (1 : ℝ) *
        (T.ninePointRadiusMagnitude - T.lambdaC * T.exradiusCMagnitude) ^ 2 := by
    simpa using hD
  have h1' : (T.ninePointCircle hN).radiusSq =
      (1 : ℝ) * T.ninePointRadiusMagnitude ^ 2 := by
    simpa using h1
  have h2' : (T.excircleC (Or.inr hT) hC).radiusSq =
      (1 : ℝ) * (T.lambdaC * T.exradiusCMagnitude) ^ 2 := by
    rw [h2, mul_pow, hLambda]
    ring
  simpa [excircleCFeuerbachContactPointTimelike] using
    (LorentzCircle.isProperTangentAt_of_radiusDifferenceData
      (T.ninePointCircle hN) (T.excircleC (Or.inr hT) hC) 1
      T.ninePointRadiusMagnitude (T.lambdaC * T.exradiusCMagnitude)
      (by norm_num) (ne_of_gt (ninePointRadiusMagnitude_pos T hN hNM))
      (mul_ne_zero (lambdaC_ne_zero T)
        (ne_of_gt (exradiusCMagnitude_pos T hN hC)))
      hGap hD' h1' h2')

end
end Triangle
end MinkowskiMerge
