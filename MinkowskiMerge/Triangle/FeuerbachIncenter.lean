import MinkowskiMerge.Triangle.FeuerbachContactEquation


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

theorem circumradius_eq_I_mul_sideAbsProduct_div_two_absDoubleArea_of_spacelike
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsSpacelike) :
    T.circumradius hN = Complex.I *
      ((T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
        (2 * |T.signedDoubleArea|) : ℝ) : ℂ) := by
  have hD : T.signedDoubleArea ≠ 0 := hN.signedDoubleArea_ne_zero
  have hAbsD : |T.signedDoubleArea| ≠ 0 := abs_ne_zero.mpr hD
  rw [circumradius_eq_neg_sideProduct_div_four_complexArea T hN (Or.inl hT)]
  unfold sideComplexLengthA sideComplexLengthB sideComplexLengthC complexArea areaMagnitude
  rw [complexLength_eq_absLength_of_spacelike hT.1,
    complexLength_eq_absLength_of_spacelike hT.2.1,
    complexLength_eq_absLength_of_spacelike hT.2.2]
  push_cast
  field_simp [hAbsD, Complex.I_ne_zero]
  rw [pow_two Complex.I, Complex.I_mul_I]
  simp only [sideAbsLengthA, sideAbsLengthB, sideAbsLengthC]
  ring

theorem circumradius_eq_sideAbsProduct_div_two_absDoubleArea_of_timelike
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsTimelike) :
    T.circumradius hN =
      ((T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
        (2 * |T.signedDoubleArea|) : ℝ) : ℂ) := by
  have hD : T.signedDoubleArea ≠ 0 := hN.signedDoubleArea_ne_zero
  have hAbsD : |T.signedDoubleArea| ≠ 0 := abs_ne_zero.mpr hD
  rw [circumradius_eq_neg_sideProduct_div_four_complexArea T hN (Or.inr hT)]
  unfold sideComplexLengthA sideComplexLengthB sideComplexLengthC complexArea areaMagnitude
  rw [complexLength_eq_I_mul_absLength_of_timelike hT.1,
    complexLength_eq_I_mul_absLength_of_timelike hT.2.1,
    complexLength_eq_I_mul_absLength_of_timelike hT.2.2]
  push_cast
  field_simp [hAbsD, Complex.I_ne_zero]
  rw [pow_two Complex.I, Complex.I_mul_I]
  simp only [sideAbsLengthA, sideAbsLengthB, sideAbsLengthC]
  ring

private theorem semiperimeterComplex_eq_spacelike
    {T : Triangle} (hT : T.IsSpacelike) :
    T.semiperimeterComplex = (T.perimeterAbs / 2 : ℂ) := by
  unfold semiperimeterComplex perimeterComplex sideComplexLengthA
    sideComplexLengthB sideComplexLengthC
  rw [complexLength_eq_absLength_of_spacelike hT.1,
    complexLength_eq_absLength_of_spacelike hT.2.1,
    complexLength_eq_absLength_of_spacelike hT.2.2]
  simp [sideAbsLengthA, sideAbsLengthB, sideAbsLengthC, perimeterAbs]

private theorem semiperimeterComplex_eq_timelike
    {T : Triangle} (hT : T.IsTimelike) :
    T.semiperimeterComplex = Complex.I * (T.perimeterAbs / 2 : ℂ) := by
  unfold semiperimeterComplex perimeterComplex sideComplexLengthA
    sideComplexLengthB sideComplexLengthC
  rw [complexLength_eq_I_mul_absLength_of_timelike hT.1,
    complexLength_eq_I_mul_absLength_of_timelike hT.2.1,
    complexLength_eq_I_mul_absLength_of_timelike hT.2.2]
  simp [sideAbsLengthA, sideAbsLengthB, sideAbsLengthC, perimeterAbs]
  ring

theorem inradius_eq_I_mul_absDoubleArea_div_perimeterAbs_of_spacelike
    (T : Triangle) (hT : T.IsSpacelike) :
    T.inradius (Or.inl hT) = Complex.I *
      ((|T.signedDoubleArea| / T.perimeterAbs : ℝ) : ℂ) := by
  have hP : 0 < T.perimeterAbs := IsNonMixed.perimeterAbs_pos (Or.inl hT)
  have hPC : (T.perimeterAbs : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hP
  rw [inradius_eq_complexArea_div_semiperimeter T (Or.inl hT),
    semiperimeterComplex_eq_spacelike hT]
  unfold complexArea areaMagnitude
  field_simp [hPC]
  push_cast
  field_simp [hPC]

theorem inradius_eq_absDoubleArea_div_perimeterAbs_of_timelike
    (T : Triangle) (hT : T.IsTimelike) :
    T.inradius (Or.inr hT) =
      ((|T.signedDoubleArea| / T.perimeterAbs : ℝ) : ℂ) := by
  have hP : 0 < T.perimeterAbs := IsNonMixed.perimeterAbs_pos (Or.inr hT)
  have hPC : (T.perimeterAbs : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hP
  rw [inradius_eq_complexArea_div_semiperimeter T (Or.inr hT),
    semiperimeterComplex_eq_timelike hT]
  unfold complexArea areaMagnitude
  field_simp [hPC, Complex.I_ne_zero]
  push_cast
  field_simp [hPC, Complex.I_ne_zero]

private theorem circumradius_mul_inradius_eq_spacelike
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsSpacelike) :
    T.circumradius hN * T.inradius (Or.inl hT) =
      -((T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
        (2 * T.perimeterAbs) : ℝ) : ℂ) := by
  have hAbsD : |T.signedDoubleArea| ≠ 0 :=
    abs_ne_zero.mpr hN.signedDoubleArea_ne_zero
  have hP : 0 < T.perimeterAbs := IsNonMixed.perimeterAbs_pos (Or.inl hT)
  rw [circumradius_eq_I_mul_sideAbsProduct_div_two_absDoubleArea_of_spacelike
      T hN hT,
    inradius_eq_I_mul_absDoubleArea_div_perimeterAbs_of_spacelike T hT]
  push_cast
  field_simp [hAbsD, ne_of_gt hP]
  rw [pow_two Complex.I, Complex.I_mul_I]
  simp only [sideAbsLengthA, sideAbsLengthB, sideAbsLengthC]
  ring

private theorem circumradius_mul_inradius_eq_timelike
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsTimelike) :
    T.circumradius hN * T.inradius (Or.inr hT) =
      (T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
        (2 * T.perimeterAbs) : ℝ) := by
  have hAbsD : |T.signedDoubleArea| ≠ 0 :=
    abs_ne_zero.mpr hN.signedDoubleArea_ne_zero
  have hP : 0 < T.perimeterAbs := IsNonMixed.perimeterAbs_pos (Or.inr hT)
  rw [circumradius_eq_sideAbsProduct_div_two_absDoubleArea_of_timelike T hN hT,
    inradius_eq_absDoubleArea_div_perimeterAbs_of_timelike T hT]
  push_cast
  field_simp [hAbsD, ne_of_gt hP]

private theorem incenter_intervalSq_eq_radiusSum_sq_spacelike
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsSpacelike) :
    (intervalSq (T.ninePointCenter hN) (T.incenter (Or.inl hT)) : ℂ) =
      (T.circumradius hN / 2 + T.inradius (Or.inl hT)) ^ 2 := by
  have hCross := intervalSq_ninePointCenter_incenter_crossTerm_eq_spacelike
    T hN hT
  have hInterval : intervalSq (T.ninePointCenter hN) (T.incenter (Or.inl hT)) =
      T.circumradiusSqAt (T.circumcenter hN) / 4 + T.inradiusSq (Or.inl hT) -
        T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
          (2 * T.perimeterAbs) := by
    linarith
  have hProduct := circumradius_mul_inradius_eq_spacelike T hN hT
  calc
    (intervalSq (T.ninePointCenter hN) (T.incenter (Or.inl hT)) : ℂ) =
        (T.circumradiusSqAt (T.circumcenter hN) : ℂ) / 4 +
          (T.inradiusSq (Or.inl hT) : ℂ) -
          (T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
            (2 * T.perimeterAbs) : ℝ) := by
        exact_mod_cast hInterval
    _ = T.circumradius hN ^ 2 / 4 + T.inradius (Or.inl hT) ^ 2 -
          (T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
            (2 * T.perimeterAbs) : ℝ) := by
        rw [← circumradius_sq T hN,
          ← inradius_sq_eq_sideDistanceSq T (Or.inl hT)]
    _ = T.circumradius hN ^ 2 / 4 + T.inradius (Or.inl hT) ^ 2 +
          T.circumradius hN * T.inradius (Or.inl hT) := by
        rw [hProduct]
        ring
    _ = _ := by ring

private theorem incenter_intervalSq_eq_radiusSum_sq_timelike
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsTimelike) :
    (intervalSq (T.ninePointCenter hN) (T.incenter (Or.inr hT)) : ℂ) =
      (T.circumradius hN / 2 + T.inradius (Or.inr hT)) ^ 2 := by
  have hCross := intervalSq_ninePointCenter_incenter_crossTerm_eq_timelike
    T hN hT
  have hInterval : intervalSq (T.ninePointCenter hN) (T.incenter (Or.inr hT)) =
      T.circumradiusSqAt (T.circumcenter hN) / 4 + T.inradiusSq (Or.inr hT) +
        T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
          (2 * T.perimeterAbs) := by
    linarith
  have hProduct := circumradius_mul_inradius_eq_timelike T hN hT
  calc
    (intervalSq (T.ninePointCenter hN) (T.incenter (Or.inr hT)) : ℂ) =
        (T.circumradiusSqAt (T.circumcenter hN) : ℂ) / 4 +
          (T.inradiusSq (Or.inr hT) : ℂ) +
          (T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
            (2 * T.perimeterAbs) : ℝ) := by
        exact_mod_cast hInterval
    _ = T.circumradius hN ^ 2 / 4 + T.inradius (Or.inr hT) ^ 2 +
          (T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
            (2 * T.perimeterAbs) : ℝ) := by
        rw [← circumradius_sq T hN,
          ← inradius_sq_eq_sideDistanceSq T (Or.inr hT)]
    _ = T.circumradius hN ^ 2 / 4 + T.inradius (Or.inr hT) ^ 2 +
          T.circumradius hN * T.inradius (Or.inr hT) := by
        rw [hProduct]
    _ = _ := by ring

private theorem ninePointCircle_centerDistance_eq_radiusSum_spacelike
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsSpacelike) :
    (T.ninePointCircle hN).centerDistance (T.incircle (Or.inl hT)) =
      T.circumradius hN / 2 + T.inradius (Or.inl hT) := by
  have hAbsDPos : 0 < |T.signedDoubleArea| :=
    abs_pos.mpr hN.signedDoubleArea_ne_zero
  have hP : 0 < T.perimeterAbs := IsNonMixed.perimeterAbs_pos (Or.inl hT)
  let u : ℝ :=
    T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
        (4 * |T.signedDoubleArea|) + |T.signedDoubleArea| / T.perimeterAbs
  have hu : 0 ≤ u := by
    dsimp [u]
    exact add_nonneg
      (div_nonneg
        (mul_nonneg (mul_nonneg (absLength_nonneg _) (absLength_nonneg _))
          (absLength_nonneg _))
        (mul_nonneg (by norm_num) hAbsDPos.le))
      (div_nonneg hAbsDPos.le hP.le)
  have hSquare := incenter_intervalSq_eq_radiusSum_sq_spacelike T hN hT
  have hIntervalSq : intervalSq (T.ninePointCenter hN) (T.incenter (Or.inl hT)) =
      -u ^ 2 := by
    have hSum : T.circumradius hN / 2 + T.inradius (Or.inl hT) =
        Complex.I * (u : ℂ) := by
      rw [circumradius_eq_I_mul_sideAbsProduct_div_two_absDoubleArea_of_spacelike
          T hN hT,
        inradius_eq_I_mul_absDoubleArea_div_perimeterAbs_of_spacelike T hT]
      dsimp [u]
      push_cast
      ring
    have hComplex :
        (intervalSq (T.ninePointCenter hN) (T.incenter (Or.inl hT)) : ℂ) =
          ((-u ^ 2 : ℝ) : ℂ) := by
      calc
        (intervalSq (T.ninePointCenter hN) (T.incenter (Or.inl hT)) : ℂ) =
            (T.circumradius hN / 2 + T.inradius (Or.inl hT)) ^ 2 := hSquare
        _ = (Complex.I * (u : ℂ)) ^ 2 := by rw [hSum]
        _ = ((-u ^ 2 : ℝ) : ℂ) := by
          rw [mul_pow, pow_two Complex.I, Complex.I_mul_I]
          push_cast
          ring
    exact_mod_cast hComplex
  rw [LorentzCircle.centerDistance_eq_positiveComplexSqrt_intervalSq]
  change positiveComplexSqrt
      (intervalSq (T.ninePointCenter hN) (T.incenter (Or.inl hT))) = _
  rw [positiveComplexSqrt_eq_I_mul_real_of_eq_neg_sq hu hIntervalSq,
    circumradius_eq_I_mul_sideAbsProduct_div_two_absDoubleArea_of_spacelike T hN hT,
    inradius_eq_I_mul_absDoubleArea_div_perimeterAbs_of_spacelike T hT]
  dsimp [u]
  push_cast
  ring

private theorem ninePointCircle_centerDistance_eq_radiusSum_timelike
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsTimelike) :
    (T.ninePointCircle hN).centerDistance (T.incircle (Or.inr hT)) =
      T.circumradius hN / 2 + T.inradius (Or.inr hT) := by
  have hAbsDPos : 0 < |T.signedDoubleArea| :=
    abs_pos.mpr hN.signedDoubleArea_ne_zero
  have hP : 0 < T.perimeterAbs := IsNonMixed.perimeterAbs_pos (Or.inr hT)
  let u : ℝ :=
    T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
        (4 * |T.signedDoubleArea|) + |T.signedDoubleArea| / T.perimeterAbs
  have hu : 0 ≤ u := by
    dsimp [u]
    exact add_nonneg
      (div_nonneg
        (mul_nonneg (mul_nonneg (absLength_nonneg _) (absLength_nonneg _))
          (absLength_nonneg _))
        (mul_nonneg (by norm_num) hAbsDPos.le))
      (div_nonneg hAbsDPos.le hP.le)
  have hSquare := incenter_intervalSq_eq_radiusSum_sq_timelike T hN hT
  have hIntervalSq : intervalSq (T.ninePointCenter hN) (T.incenter (Or.inr hT)) =
      u ^ 2 := by
    have hSum : T.circumradius hN / 2 + T.inradius (Or.inr hT) = (u : ℂ) := by
      rw [circumradius_eq_sideAbsProduct_div_two_absDoubleArea_of_timelike
          T hN hT,
        inradius_eq_absDoubleArea_div_perimeterAbs_of_timelike T hT]
      dsimp [u]
      push_cast
      ring
    have hComplex :
        (intervalSq (T.ninePointCenter hN) (T.incenter (Or.inr hT)) : ℂ) =
          ((u ^ 2 : ℝ) : ℂ) := by
      calc
        (intervalSq (T.ninePointCenter hN) (T.incenter (Or.inr hT)) : ℂ) =
            (T.circumradius hN / 2 + T.inradius (Or.inr hT)) ^ 2 := hSquare
        _ = (u : ℂ) ^ 2 := by rw [hSum]
        _ = ((u ^ 2 : ℝ) : ℂ) := by
          push_cast
          rfl
    exact_mod_cast hComplex
  rw [LorentzCircle.centerDistance_eq_positiveComplexSqrt_intervalSq]
  change positiveComplexSqrt
      (intervalSq (T.ninePointCenter hN) (T.incenter (Or.inr hT))) = _
  rw [positiveComplexSqrt_eq_real_of_eq_sq hu hIntervalSq,
    circumradius_eq_sideAbsProduct_div_two_absDoubleArea_of_timelike T hN hT,
    inradius_eq_absDoubleArea_div_perimeterAbs_of_timelike T hT]
  dsimp [u]
  push_cast
  ring

theorem hasFeuerbachIncenterEquation (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) : T.HasFeuerbachIncenterEquation hN hT := by
  rw [hasFeuerbachIncenterEquation_iff]
  rcases hT with hS | hT
  · exact ninePointCircle_centerDistance_eq_radiusSum_spacelike T hN hS
  · exact ninePointCircle_centerDistance_eq_radiusSum_timelike T hN hT

end

end Triangle
end MinkowskiMerge
