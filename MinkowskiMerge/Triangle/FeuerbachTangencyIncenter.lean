import MinkowskiMerge.Triangle.FeuerbachIncenter
import MinkowskiMerge.CircleTangencyRadii

set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

theorem ninePointCircle_radiusSq_eq_neg_magnitude_sq_spacelike
    (T : Triangle) (hN : T.Nondegenerate)
    (hS : T.IsSpacelike) :
    (T.ninePointCircle hN).radiusSq =
      -((T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
        (4 * |T.signedDoubleArea|)) ^ 2) := by
  have hR := circumradius_eq_I_mul_sideAbsProduct_div_two_absDoubleArea_of_spacelike
    T hN hS
  let u : ℝ := T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
    (2 * |T.signedDoubleArea|)
  have hR' : T.circumradius hN = Complex.I * (u : ℂ) := by
    simpa [u] using hR
  have hSq := circumradius_sq T hN
  rw [hR'] at hSq
  have hComplex : (Complex.I * (u : ℂ)) ^ 2 = ((-u ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, pow_two Complex.I, Complex.I_mul_I]
    push_cast
    ring
  rw [hComplex] at hSq
  have hReal : -u ^ 2 = T.circumradiusSqAt (T.circumcenter hN) := by
    exact_mod_cast hSq
  rw [ninePointCircle_radiusSq, ninePointRadiusSq_eq_quarter_circumradiusSq]
  rw [← hReal]
  dsimp [u]
  ring

theorem ninePointCircle_radiusSq_eq_magnitude_sq_timelike
    (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsTimelike) :
    (T.ninePointCircle hN).radiusSq =
      ((T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
        (4 * |T.signedDoubleArea|)) ^ 2) := by
  have hR := circumradius_eq_sideAbsProduct_div_two_absDoubleArea_of_timelike
    T hN hT
  let u : ℝ := T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
    (2 * |T.signedDoubleArea|)
  have hR' : T.circumradius hN = (u : ℂ) := by
    simpa [u] using hR
  have hSq := circumradius_sq T hN
  rw [hR'] at hSq
  have hComplex : (u : ℂ) ^ 2 = ((u ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hComplex] at hSq
  have hReal : u ^ 2 = T.circumradiusSqAt (T.circumcenter hN) := by
    exact_mod_cast hSq
  rw [ninePointCircle_radiusSq, ninePointRadiusSq_eq_quarter_circumradiusSq]
  rw [← hReal]
  dsimp [u]
  ring

private theorem incircle_radiusSq_eq_neg_magnitude_sq_spacelike (T : Triangle)
    (hS : T.IsSpacelike) :
    (T.incircle (Or.inl hS)).radiusSq =
      -((|T.signedDoubleArea| / T.perimeterAbs) ^ 2) := by
  rw [incircle_radiusSq, inradiusSq_eq_spacelike_formula hS, div_pow, sq_abs]
  ring

private theorem incircle_radiusSq_eq_magnitude_sq_timelike (T : Triangle)
    (hT : T.IsTimelike) :
    (T.incircle (Or.inr hT)).radiusSq =
      ((|T.signedDoubleArea| / T.perimeterAbs) ^ 2) := by
  rw [incircle_radiusSq, inradiusSq_eq_timelike_formula hT, div_pow, sq_abs]

private theorem incenter_intervalSq_eq_neg_magnitude_sum_sq_spacelike (T : Triangle)
    (hN : T.Nondegenerate) (hS : T.IsSpacelike) :
    intervalSq (T.ninePointCenter hN) (T.incenter (Or.inl hS)) =
      -((T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
        (4 * |T.signedDoubleArea|) +
        |T.signedDoubleArea| / T.perimeterAbs) ^ 2) := by
  have hEq := hasFeuerbachIncenterEquation T hN (Or.inl hS)
  rw [hasFeuerbachIncenterEquation_iff] at hEq
  rw [circumradius_eq_I_mul_sideAbsProduct_div_two_absDoubleArea_of_spacelike
      T hN hS,
    inradius_eq_I_mul_absDoubleArea_div_perimeterAbs_of_spacelike T hS] at hEq
  let u : ℝ := T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
    (4 * |T.signedDoubleArea|) + |T.signedDoubleArea| / T.perimeterAbs
  have hEq' : (T.ninePointCircle hN).centerDistance
      (T.incircle (Or.inl hS)) = Complex.I * (u : ℂ) := by
    rw [hEq]
    dsimp [u]
    push_cast
    ring
  have hSq := congrArg (fun z : ℂ => z ^ 2) hEq'
  change (T.ninePointCircle hN).centerDistance
      (T.incircle (Or.inl hS)) ^ 2 = (Complex.I * (u : ℂ)) ^ 2 at hSq
  rw [LorentzCircle.centerDistance_sq] at hSq
  have hComplex : (Complex.I * (u : ℂ)) ^ 2 = ((-u ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, pow_two Complex.I, Complex.I_mul_I]
    push_cast
    ring
  rw [hComplex] at hSq
  have hReal : intervalSq (T.ninePointCenter hN) (T.incenter (Or.inl hS)) =
      -u ^ 2 := by
    exact_mod_cast hSq
  simpa [u] using hReal

private theorem incenter_intervalSq_eq_magnitude_sum_sq_timelike (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsTimelike) :
    intervalSq (T.ninePointCenter hN) (T.incenter (Or.inr hT)) =
      ((T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
        (4 * |T.signedDoubleArea|) +
        |T.signedDoubleArea| / T.perimeterAbs) ^ 2) := by
  have hEq := hasFeuerbachIncenterEquation T hN (Or.inr hT)
  rw [hasFeuerbachIncenterEquation_iff] at hEq
  rw [circumradius_eq_sideAbsProduct_div_two_absDoubleArea_of_timelike
      T hN hT,
    inradius_eq_absDoubleArea_div_perimeterAbs_of_timelike T hT] at hEq
  let u : ℝ := T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
    (4 * |T.signedDoubleArea|) + |T.signedDoubleArea| / T.perimeterAbs
  have hEq' : (T.ninePointCircle hN).centerDistance
      (T.incircle (Or.inr hT)) = (u : ℂ) := by
    rw [hEq]
    dsimp [u]
    push_cast
    ring
  have hSq := congrArg (fun z : ℂ => z ^ 2) hEq'
  change (T.ninePointCircle hN).centerDistance
      (T.incircle (Or.inr hT)) ^ 2 = (u : ℂ) ^ 2 at hSq
  rw [LorentzCircle.centerDistance_sq] at hSq
  have hComplex : (u : ℂ) ^ 2 = ((u ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hComplex] at hSq
  have hReal : intervalSq (T.ninePointCenter hN) (T.incenter (Or.inr hT)) =
      u ^ 2 := by
    exact_mod_cast hSq
  simpa [u] using hReal

noncomputable def ninePointRadiusMagnitude (T : Triangle) : ℝ :=
  T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC /
    (4 * |T.signedDoubleArea|)

noncomputable def inradiusMagnitude (T : Triangle) : ℝ :=
  |T.signedDoubleArea| / T.perimeterAbs

theorem ninePointRadiusMagnitude_pos (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) : 0 < T.ninePointRadiusMagnitude := by
  have hD : 0 < |T.signedDoubleArea| :=
    abs_pos.mpr hN.signedDoubleArea_ne_zero
  dsimp [ninePointRadiusMagnitude]
  exact div_pos
    (mul_pos (mul_pos hT.sideAbsLengthA_pos hT.sideAbsLengthB_pos)
      hT.sideAbsLengthC_pos)
    (mul_pos (by norm_num) hD)

theorem inradiusMagnitude_pos (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) : 0 < T.inradiusMagnitude := by
  dsimp [inradiusMagnitude]
  exact div_pos (abs_pos.mpr hN.signedDoubleArea_ne_zero) hT.perimeterAbs_pos

noncomputable def incenterFeuerbachContactPointSpacelike (T : Triangle)
    (hN : T.Nondegenerate) (hS : T.IsSpacelike) : Point :=
  LorentzCircle.tangentPointOfRadiusSum (T.ninePointCircle hN)
    (T.incircle (Or.inl hS)) T.ninePointRadiusMagnitude T.inradiusMagnitude

noncomputable def incenterFeuerbachContactPointTimelike (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsTimelike) : Point :=
  LorentzCircle.tangentPointOfRadiusSum (T.ninePointCircle hN)
    (T.incircle (Or.inr hT)) T.ninePointRadiusMagnitude T.inradiusMagnitude

private theorem radiusMagnitude_sum_ne_zero_spacelike (T : Triangle)
    (hN : T.Nondegenerate) (hS : T.IsSpacelike) :
    T.ninePointRadiusMagnitude + T.inradiusMagnitude ≠ 0 := by
  have hnm : T.IsNonMixed := Or.inl hS
  have hD : 0 < |T.signedDoubleArea| := abs_pos.mpr hN.signedDoubleArea_ne_zero
  have hP : 0 < T.perimeterAbs := hnm.perimeterAbs_pos
  have hR : 0 < T.ninePointRadiusMagnitude := by
    dsimp [ninePointRadiusMagnitude]
    exact div_pos
      (mul_pos (mul_pos hnm.sideAbsLengthA_pos hnm.sideAbsLengthB_pos)
        hnm.sideAbsLengthC_pos)
      (mul_pos (by norm_num) hD)
  have hr : 0 < T.inradiusMagnitude := by
    dsimp [inradiusMagnitude]
    exact div_pos hD hP
  linarith

private theorem radiusMagnitude_sum_ne_zero_timelike (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsTimelike) :
    T.ninePointRadiusMagnitude + T.inradiusMagnitude ≠ 0 := by
  have hnm : T.IsNonMixed := Or.inr hT
  have hD : 0 < |T.signedDoubleArea| := abs_pos.mpr hN.signedDoubleArea_ne_zero
  have hP : 0 < T.perimeterAbs := hnm.perimeterAbs_pos
  have hR : 0 < T.ninePointRadiusMagnitude := by
    dsimp [ninePointRadiusMagnitude]
    exact div_pos
      (mul_pos (mul_pos hnm.sideAbsLengthA_pos hnm.sideAbsLengthB_pos)
        hnm.sideAbsLengthC_pos)
      (mul_pos (by norm_num) hD)
  have hr : 0 < T.inradiusMagnitude := by
    dsimp [inradiusMagnitude]
    exact div_pos hD hP
  linarith

theorem isTangentAt_incenter_spacelike (T : Triangle) (hN : T.Nondegenerate)
    (hS : T.IsSpacelike) :
    LorentzCircle.IsTangentAt (T.ninePointCircle hN) (T.incircle (Or.inl hS))
      (T.incenterFeuerbachContactPointSpacelike hN hS) := by
  have hs := radiusMagnitude_sum_ne_zero_spacelike T hN hS
  have hD := incenter_intervalSq_eq_neg_magnitude_sum_sq_spacelike T hN hS
  have h₁ := ninePointCircle_radiusSq_eq_neg_magnitude_sq_spacelike T hN hS
  have h₂ := incircle_radiusSq_eq_neg_magnitude_sq_spacelike T hS
  have hD' : intervalSq (T.ninePointCircle hN).center
      (T.incircle (Or.inl hS)).center =
      (-1 : ℝ) * (T.ninePointRadiusMagnitude + T.inradiusMagnitude) ^ 2 := by
    simpa [ninePointRadiusMagnitude, inradiusMagnitude] using hD
  have h₁' : (T.ninePointCircle hN).radiusSq =
      (-1 : ℝ) * T.ninePointRadiusMagnitude ^ 2 := by
    simpa [ninePointRadiusMagnitude] using h₁
  have h₂' : (T.incircle (Or.inl hS)).radiusSq =
      (-1 : ℝ) * T.inradiusMagnitude ^ 2 := by
    simpa [inradiusMagnitude] using h₂
  simpa [incenterFeuerbachContactPointSpacelike] using
    (LorentzCircle.isTangentAt_of_radiusSumData
      (T.ninePointCircle hN) (T.incircle (Or.inl hS)) (-1)
      T.ninePointRadiusMagnitude T.inradiusMagnitude hs hD' h₁' h₂')

theorem isTangentAt_incenter_timelike (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsTimelike) :
    LorentzCircle.IsTangentAt (T.ninePointCircle hN) (T.incircle (Or.inr hT))
      (T.incenterFeuerbachContactPointTimelike hN hT) := by
  have hs := radiusMagnitude_sum_ne_zero_timelike T hN hT
  have hD := incenter_intervalSq_eq_magnitude_sum_sq_timelike T hN hT
  have h₁ := ninePointCircle_radiusSq_eq_magnitude_sq_timelike T hN hT
  have h₂ := incircle_radiusSq_eq_magnitude_sq_timelike T hT
  have hD' : intervalSq (T.ninePointCircle hN).center
      (T.incircle (Or.inr hT)).center =
      (1 : ℝ) * (T.ninePointRadiusMagnitude + T.inradiusMagnitude) ^ 2 := by
    simpa [ninePointRadiusMagnitude, inradiusMagnitude] using hD
  have h₁' : (T.ninePointCircle hN).radiusSq =
      (1 : ℝ) * T.ninePointRadiusMagnitude ^ 2 := by
    simpa [ninePointRadiusMagnitude] using h₁
  have h₂' : (T.incircle (Or.inr hT)).radiusSq =
      (1 : ℝ) * T.inradiusMagnitude ^ 2 := by
    simpa [inradiusMagnitude] using h₂
  simpa [incenterFeuerbachContactPointTimelike] using
    (LorentzCircle.isTangentAt_of_radiusSumData
      (T.ninePointCircle hN) (T.incircle (Or.inr hT)) 1
      T.ninePointRadiusMagnitude T.inradiusMagnitude hs hD' h₁' h₂')

theorem isProperTangentAt_incenter_spacelike
    (T : Triangle) (hN : T.Nondegenerate) (hS : T.IsSpacelike) :
    LorentzCircle.IsProperTangentAt
      (T.ninePointCircle hN) (T.incircle (Or.inl hS))
      (T.incenterFeuerbachContactPointSpacelike hN hS) := by
  have hNM : T.IsNonMixed := Or.inl hS
  have hs := radiusMagnitude_sum_ne_zero_spacelike T hN hS
  have hD := incenter_intervalSq_eq_neg_magnitude_sum_sq_spacelike T hN hS
  have h₁ := ninePointCircle_radiusSq_eq_neg_magnitude_sq_spacelike T hN hS
  have h₂ := incircle_radiusSq_eq_neg_magnitude_sq_spacelike T hS
  have hD' : intervalSq (T.ninePointCircle hN).center
      (T.incircle (Or.inl hS)).center =
      (-1 : ℝ) * (T.ninePointRadiusMagnitude + T.inradiusMagnitude) ^ 2 := by
    simpa [ninePointRadiusMagnitude, inradiusMagnitude] using hD
  have h₁' : (T.ninePointCircle hN).radiusSq =
      (-1 : ℝ) * T.ninePointRadiusMagnitude ^ 2 := by
    simpa [ninePointRadiusMagnitude] using h₁
  have h₂' : (T.incircle (Or.inl hS)).radiusSq =
      (-1 : ℝ) * T.inradiusMagnitude ^ 2 := by
    simpa [inradiusMagnitude] using h₂
  simpa [incenterFeuerbachContactPointSpacelike] using
    (LorentzCircle.isProperTangentAt_of_radiusSumData
      (T.ninePointCircle hN) (T.incircle (Or.inl hS)) (-1)
      T.ninePointRadiusMagnitude T.inradiusMagnitude (by norm_num)
      (ne_of_gt (ninePointRadiusMagnitude_pos T hN hNM))
      (ne_of_gt (inradiusMagnitude_pos T hN hNM)) hs hD' h₁' h₂')

theorem isProperTangentAt_incenter_timelike
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsTimelike) :
    LorentzCircle.IsProperTangentAt
      (T.ninePointCircle hN) (T.incircle (Or.inr hT))
      (T.incenterFeuerbachContactPointTimelike hN hT) := by
  have hNM : T.IsNonMixed := Or.inr hT
  have hs := radiusMagnitude_sum_ne_zero_timelike T hN hT
  have hD := incenter_intervalSq_eq_magnitude_sum_sq_timelike T hN hT
  have h₁ := ninePointCircle_radiusSq_eq_magnitude_sq_timelike T hN hT
  have h₂ := incircle_radiusSq_eq_magnitude_sq_timelike T hT
  have hD' : intervalSq (T.ninePointCircle hN).center
      (T.incircle (Or.inr hT)).center =
      (1 : ℝ) * (T.ninePointRadiusMagnitude + T.inradiusMagnitude) ^ 2 := by
    simpa [ninePointRadiusMagnitude, inradiusMagnitude] using hD
  have h₁' : (T.ninePointCircle hN).radiusSq =
      (1 : ℝ) * T.ninePointRadiusMagnitude ^ 2 := by
    simpa [ninePointRadiusMagnitude] using h₁
  have h₂' : (T.incircle (Or.inr hT)).radiusSq =
      (1 : ℝ) * T.inradiusMagnitude ^ 2 := by
    simpa [inradiusMagnitude] using h₂
  simpa [incenterFeuerbachContactPointTimelike] using
    (LorentzCircle.isProperTangentAt_of_radiusSumData
      (T.ninePointCircle hN) (T.incircle (Or.inr hT)) 1
      T.ninePointRadiusMagnitude T.inradiusMagnitude (by norm_num)
      (ne_of_gt (ninePointRadiusMagnitude_pos T hN hNM))
      (ne_of_gt (inradiusMagnitude_pos T hN hNM)) hs hD' h₁' h₂')

end
end Triangle
end MinkowskiMerge
