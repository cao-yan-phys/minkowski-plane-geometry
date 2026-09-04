import MinkowskiMerge.Triangle.FeuerbachContact


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

private theorem complexArea_ne_zero (T : Triangle) (hN : T.Nondegenerate) :
    T.complexArea ≠ 0 := by
  unfold complexArea areaMagnitude
  apply mul_ne_zero Complex.I_ne_zero
  exact_mod_cast div_ne_zero (abs_ne_zero.mpr hN.signedDoubleArea_ne_zero) (by norm_num)

private theorem semiperimeterComplex_sub_sideC_eq_spacelike
    {T : Triangle} (hT : T.IsSpacelike) :
    T.semiperimeterComplex - T.sideComplexLengthC =
      (T.excenterDenomC / 2 : ℂ) := by
  unfold semiperimeterComplex perimeterComplex sideComplexLengthA
    sideComplexLengthB sideComplexLengthC
  rw [complexLength_eq_absLength_of_spacelike hT.1,
    complexLength_eq_absLength_of_spacelike hT.2.1,
    complexLength_eq_absLength_of_spacelike hT.2.2]
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

private theorem neg_lambdaC_mul_circumradius_mul_exradiusC_eq_spacelike
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsSpacelike)
    (hC : T.excenterDenomC ≠ 0) :
    -(T.lambdaC : ℂ) * T.circumradius hN * T.exradiusC (Or.inl hT) hC =
      (T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
        (2 * T.excenterDenomC) : ℝ) := by
  have hArea : T.complexArea ≠ 0 := complexArea_ne_zero T hN
  have hLambda : (T.lambdaC : ℂ) ^ 2 = 1 := by
    exact_mod_cast lambdaC_sq T
  rw [circumradius_eq_neg_sideProduct_div_four_complexArea T hN (Or.inl hT),
    exradiusC_eq_lambdaC_mul_complexArea_div_semiperimeter_sub_side T
      (Or.inl hT) hC,
    semiperimeterComplex_sub_sideC_eq_spacelike hT]
  unfold sideComplexLengthA sideComplexLengthB sideComplexLengthC
  rw [complexLength_eq_absLength_of_spacelike hT.1,
    complexLength_eq_absLength_of_spacelike hT.2.1,
    complexLength_eq_absLength_of_spacelike hT.2.2]
  push_cast
  field_simp [hArea, hC]
  rw [hLambda]
  simp only [sideAbsLengthA, sideAbsLengthB, sideAbsLengthC]
  ring

private theorem neg_lambdaC_mul_circumradius_mul_exradiusC_eq_timelike
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsTimelike)
    (hC : T.excenterDenomC ≠ 0) :
    -(T.lambdaC : ℂ) * T.circumradius hN * T.exradiusC (Or.inr hT) hC =
      -(T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
        (2 * T.excenterDenomC) : ℝ) := by
  have hArea : T.complexArea ≠ 0 := complexArea_ne_zero T hN
  have hLambda : (T.lambdaC : ℂ) ^ 2 = 1 := by
    exact_mod_cast lambdaC_sq T
  rw [circumradius_eq_neg_sideProduct_div_four_complexArea T hN (Or.inr hT),
    exradiusC_eq_lambdaC_mul_complexArea_div_semiperimeter_sub_side T
      (Or.inr hT) hC,
    semiperimeterComplex_sub_sideC_eq_timelike hT]
  unfold sideComplexLengthA sideComplexLengthB sideComplexLengthC
  rw [complexLength_eq_I_mul_absLength_of_timelike hT.1,
    complexLength_eq_I_mul_absLength_of_timelike hT.2.1,
    complexLength_eq_I_mul_absLength_of_timelike hT.2.2]
  push_cast
  field_simp [hArea, hC, Complex.I_ne_zero]
  rw [hLambda]
  simp only [sideAbsLengthA, sideAbsLengthB, sideAbsLengthC]
  rw [pow_two Complex.I, Complex.I_mul_I]
  ring

private theorem radius_difference_sq (R r l : ℂ) (hl : l ^ 2 = 1) :
    R ^ 2 / 4 + r ^ 2 - l * R * r = (R / 2 - l * r) ^ 2 := by
  rw [sub_sq, mul_pow, hl]
  ring

theorem hasFeuerbachExcircleCEquation (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (hC : T.excenterDenomC ≠ 0) :
    T.HasFeuerbachExcircleCEquation hN hT hC := by
  rw [hasFeuerbachExcircleCEquation_iff]
  rcases hT with hS | hT
  · rw [LorentzCircle.centerDistance_sq]
    change (intervalSq (T.ninePointCenter hN) (T.excenterC hC) : ℂ) = _
    have hCross := intervalSq_ninePointCenter_excenterC_crossTerm_eq_spacelike
      T hN hS hC
    have hInterval : intervalSq (T.ninePointCenter hN) (T.excenterC hC) =
        T.circumradiusSqAt (T.circumcenter hN) / 4 +
          T.exradiusSqC (Or.inl hS) hC +
          T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
            (2 * T.excenterDenomC) := by
      linarith
    have hProduct := neg_lambdaC_mul_circumradius_mul_exradiusC_eq_spacelike
      T hN hS hC
    have hProduct' : (T.lambdaC : ℂ) * T.circumradius hN *
        T.exradiusC (Or.inl hS) hC =
        -((T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
          (2 * T.excenterDenomC) : ℝ) : ℂ) := by
      calc
        (T.lambdaC : ℂ) * T.circumradius hN * T.exradiusC (Or.inl hS) hC =
            - (-(T.lambdaC : ℂ) * T.circumradius hN * T.exradiusC (Or.inl hS) hC) := by
              ring
        _ = -((T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
          (2 * T.excenterDenomC) : ℝ) : ℂ) := by rw [hProduct]
    have hLambda : (T.lambdaC : ℂ) ^ 2 = 1 := by
      exact_mod_cast lambdaC_sq T
    calc
      (intervalSq (T.ninePointCenter hN) (T.excenterC hC) : ℂ) =
          (T.circumradiusSqAt (T.circumcenter hN) : ℂ) / 4 +
            (T.exradiusSqC (Or.inl hS) hC : ℂ) +
            (T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
              (2 * T.excenterDenomC) : ℝ) := by
          exact_mod_cast hInterval
      _ = T.circumradius hN ^ 2 / 4 + T.exradiusC (Or.inl hS) hC ^ 2 -
            (T.lambdaC : ℂ) * T.circumradius hN * T.exradiusC (Or.inl hS) hC := by
          rw [← circumradius_sq T hN,
            ← exradiusC_sq_eq_sideDistanceSq T (Or.inl hS) hC,
            hProduct']
          ring
      _ = _ := radius_difference_sq _ _ _ hLambda
  · rw [LorentzCircle.centerDistance_sq]
    change (intervalSq (T.ninePointCenter hN) (T.excenterC hC) : ℂ) = _
    have hCross := intervalSq_ninePointCenter_excenterC_crossTerm_eq_timelike
      T hN hT hC
    have hInterval : intervalSq (T.ninePointCenter hN) (T.excenterC hC) =
        T.circumradiusSqAt (T.circumcenter hN) / 4 +
          T.exradiusSqC (Or.inr hT) hC -
          T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
            (2 * T.excenterDenomC) := by
      linarith
    have hProduct := neg_lambdaC_mul_circumradius_mul_exradiusC_eq_timelike
      T hN hT hC
    have hProduct' : (T.lambdaC : ℂ) * T.circumradius hN *
        T.exradiusC (Or.inr hT) hC =
        (T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
          (2 * T.excenterDenomC) : ℝ) := by
      calc
        (T.lambdaC : ℂ) * T.circumradius hN * T.exradiusC (Or.inr hT) hC =
            - (-(T.lambdaC : ℂ) * T.circumradius hN * T.exradiusC (Or.inr hT) hC) := by
              ring
        _ = -(-((T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
          (2 * T.excenterDenomC) : ℝ) : ℂ)) := by rw [hProduct]
        _ = (T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
          (2 * T.excenterDenomC) : ℝ) := by ring
    have hLambda : (T.lambdaC : ℂ) ^ 2 = 1 := by
      exact_mod_cast lambdaC_sq T
    calc
      (intervalSq (T.ninePointCenter hN) (T.excenterC hC) : ℂ) =
          (T.circumradiusSqAt (T.circumcenter hN) : ℂ) / 4 +
            (T.exradiusSqC (Or.inr hT) hC : ℂ) -
            (T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
              (2 * T.excenterDenomC) : ℝ) := by
          exact_mod_cast hInterval
      _ = T.circumradius hN ^ 2 / 4 + T.exradiusC (Or.inr hT) hC ^ 2 -
            (T.lambdaC : ℂ) * T.circumradius hN * T.exradiusC (Or.inr hT) hC := by
          rw [← circumradius_sq T hN,
            ← exradiusC_sq_eq_sideDistanceSq T (Or.inr hT) hC,
            hProduct']
      _ = _ := radius_difference_sq _ _ _ hLambda

end

end Triangle
end MinkowskiMerge
