import MinkowskiMerge.Triangle.Incenters


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

def complexArea (T : Triangle) : ℂ :=
  Complex.I * (T.areaMagnitude : ℂ)

theorem complexArea_sq (T : Triangle) :
    T.complexArea ^ 2 = -(T.signedDoubleArea ^ 2 : ℂ) / 4 := by
  rw [complexArea, areaMagnitude, mul_pow, pow_two Complex.I, Complex.I_mul_I]
  push_cast
  rw [div_pow, ← Complex.ofReal_pow, sq_abs]
  rw [Complex.ofReal_pow]
  ring

theorem Nondegenerate.complexArea_ne_zero {T : Triangle}
    (hN : T.Nondegenerate) : T.complexArea ≠ 0 := by
  unfold complexArea areaMagnitude
  apply mul_ne_zero Complex.I_ne_zero
  exact_mod_cast div_ne_zero
    (abs_ne_zero.mpr hN.signedDoubleArea_ne_zero) (by norm_num)

theorem sideSq_heron_polynomial (T : Triangle) :
    4 * T.sideSqB * T.sideSqC -
        (T.sideSqB + T.sideSqC - T.sideSqA) ^ 2 =
      -4 * T.signedDoubleArea ^ 2 := by
  simp only [sideSqA, sideSqB, sideSqC, signedDoubleArea,
    intervalSq, MinkowskiMerge.signedDoubleArea, intervalVec,
    q_apply, br_apply, vsub_eq_sub, Vec.x_sub, Vec.t_sub]
  ring

theorem heron_polynomial (a b c : ℂ) :
    4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 =
      (a + b + c) * (-a + b + c) * (a - b + c) *
        (a + b - c) := by
  ring

theorem complex_heron (T : Triangle) :
    16 * T.complexArea ^ 2 =
      (T.sideComplexLengthA + T.sideComplexLengthB + T.sideComplexLengthC) *
      (-T.sideComplexLengthA + T.sideComplexLengthB + T.sideComplexLengthC) *
      (T.sideComplexLengthA - T.sideComplexLengthB + T.sideComplexLengthC) *
      (T.sideComplexLengthA + T.sideComplexLengthB - T.sideComplexLengthC) := by
  rw [← heron_polynomial]
  rw [sideComplexLengthA_sq, sideComplexLengthB_sq, sideComplexLengthC_sq]
  rw [show
    (4 : ℂ) * T.sideSqB * T.sideSqC -
        ((T.sideSqB : ℂ) + T.sideSqC - T.sideSqA) ^ 2 =
      ((4 * T.sideSqB * T.sideSqC -
        (T.sideSqB + T.sideSqC - T.sideSqA) ^ 2 : ℝ) : ℂ) by
      push_cast
      ring]
  rw [sideSq_heron_polynomial, complexArea_sq]
  push_cast
  ring

theorem Nondegenerate.excenterDenomA_ne_zero {T : Triangle}
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) :
    T.excenterDenomA ≠ 0 := by
  intro hA
  obtain ⟨phase, hp⟩ := T.exists_commonLengthPhase hT
  have hA' : T.signedPerimeter (-1) 1 1 = 0 := by
    simpa [excenterDenomA] using hA
  have hdenComplex : T.signedPerimeterComplex (-1) 1 1 = 0 := by
    rw [signedPerimeterComplex_eq_phase_mul T hp, hA']
    norm_num
  have hfactor :
      -T.sideComplexLengthA + T.sideComplexLengthB + T.sideComplexLengthC = 0 := by
    simpa [signedPerimeterComplex] using hdenComplex
  have hHeron := complex_heron T
  rw [hfactor] at hHeron
  have hAreaSq : T.complexArea ^ 2 = 0 := by
    simpa using hHeron
  exact hN.complexArea_ne_zero (sq_eq_zero_iff.mp hAreaSq)

theorem Nondegenerate.excenterDenomB_ne_zero {T : Triangle}
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) :
    T.excenterDenomB ≠ 0 := by
  intro hB
  obtain ⟨phase, hp⟩ := T.exists_commonLengthPhase hT
  have hB' : T.signedPerimeter 1 (-1) 1 = 0 := by
    simpa [excenterDenomB] using hB
  have hdenComplex : T.signedPerimeterComplex 1 (-1) 1 = 0 := by
    rw [signedPerimeterComplex_eq_phase_mul T hp, hB']
    norm_num
  have hfactor :
      T.sideComplexLengthA - T.sideComplexLengthB + T.sideComplexLengthC = 0 := by
    simpa [signedPerimeterComplex] using hdenComplex
  have hHeron := complex_heron T
  rw [hfactor] at hHeron
  have hAreaSq : T.complexArea ^ 2 = 0 := by
    simpa using hHeron
  exact hN.complexArea_ne_zero (sq_eq_zero_iff.mp hAreaSq)

theorem Nondegenerate.excenterDenomC_ne_zero {T : Triangle}
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) :
    T.excenterDenomC ≠ 0 := by
  intro hC
  obtain ⟨phase, hp⟩ := T.exists_commonLengthPhase hT
  have hC' : T.signedPerimeter 1 1 (-1) = 0 := by
    simpa [excenterDenomC] using hC
  have hdenComplex : T.signedPerimeterComplex 1 1 (-1) = 0 := by
    rw [signedPerimeterComplex_eq_phase_mul T hp, hC']
    norm_num
  have hfactor :
      T.sideComplexLengthA + T.sideComplexLengthB - T.sideComplexLengthC = 0 := by
    simpa [signedPerimeterComplex] using hdenComplex
  have hHeron := complex_heron T
  rw [hfactor] at hHeron
  have hAreaSq : T.complexArea ^ 2 = 0 := by
    simpa using hHeron
  exact hN.complexArea_ne_zero (sq_eq_zero_iff.mp hAreaSq)

theorem complex_heron_semiperimeter (T : Triangle) :
    T.complexArea ^ 2 =
      T.semiperimeterComplex *
      (T.semiperimeterComplex - T.sideComplexLengthA) *
      (T.semiperimeterComplex - T.sideComplexLengthB) *
      (T.semiperimeterComplex - T.sideComplexLengthC) := by
  rw [show T.semiperimeterComplex =
      (T.sideComplexLengthA + T.sideComplexLengthB + T.sideComplexLengthC) / 2 by
    rfl]
  have h := complex_heron T
  calc
    T.complexArea ^ 2 = (16 * T.complexArea ^ 2) / 16 := by ring
    _ = ((T.sideComplexLengthA + T.sideComplexLengthB + T.sideComplexLengthC) *
        (-T.sideComplexLengthA + T.sideComplexLengthB + T.sideComplexLengthC) *
        (T.sideComplexLengthA - T.sideComplexLengthB + T.sideComplexLengthC) *
        (T.sideComplexLengthA + T.sideComplexLengthB - T.sideComplexLengthC)) / 16 := by
      rw [h]
    _ = _ := by ring

noncomputable def inradius (T : Triangle) (hT : T.IsNonMixed) : ℂ :=
  pointLineDistance (T.incenter hT) T.B T.C hT.sidesNonNull.1

noncomputable def inradiusSq (T : Triangle) (hT : T.IsNonMixed) : ℝ :=
  T.sideDistanceSqA (T.incenter hT) hT.sidesNonNull.1

theorem inradius_sq_eq_sideDistanceSq (T : Triangle) (hT : T.IsNonMixed) :
    T.inradius hT ^ 2 = (T.inradiusSq hT : ℂ) := by
  rw [inradius, pointLineDistance_sq]
  unfold inradiusSq sideDistanceSqA
  rw [heightSq_eq_neg_area_sq_div_intervalSq]

private theorem signedMagnitude_ratio_value
    (a side s d epsilon : ℝ)
    (hs : s ^ 2 = 1) (ha : a ^ 2 = epsilon * side)
    (hside : side ≠ 0) (hd : d ≠ 0) :
    (s * a / d) ^ 2 / side = epsilon / d ^ 2 := by
  calc
    (s * a / d) ^ 2 / side =
        (s ^ 2 * a ^ 2) / (d ^ 2 * side) := by ring
    _ = (epsilon * side) / (d ^ 2 * side) := by rw [hs, ha]; ring
    _ = epsilon / d ^ 2 := by field_simp [hside, hd]

private theorem sideDistanceSqA_sideMagnitude_value
    (T : Triangle) (sa epsilon : ℝ)
    (hsa : sa ^ 2 = 1) (hden : T.signedPerimeter sa 1 1 ≠ 0)
    (hA : T.sideAbsLengthA ^ 2 = epsilon * T.sideSqA)
    (hside : T.sideSqA ≠ 0) :
    T.sideDistanceSqA
        (T.barycentricPoint (T.sideMagnitudeWeights sa 1 1 hden)) hside =
      -epsilon * T.signedDoubleArea ^ 2 /
        T.signedPerimeter sa 1 1 ^ 2 := by
  rw [sideDistanceSqA_barycentric]
  change
    -((sa * T.sideAbsLengthA / T.signedPerimeter sa 1 1) *
        T.signedDoubleArea) ^ 2 / T.sideSqA = _
  calc
    -((sa * T.sideAbsLengthA / T.signedPerimeter sa 1 1) *
        T.signedDoubleArea) ^ 2 / T.sideSqA =
        -T.signedDoubleArea ^ 2 *
          ((sa * T.sideAbsLengthA / T.signedPerimeter sa 1 1) ^ 2 /
            T.sideSqA) := by ring
    _ = -T.signedDoubleArea ^ 2 *
          (epsilon / T.signedPerimeter sa 1 1 ^ 2) := by
      rw [signedMagnitude_ratio_value _ _ _ _ _ hsa hA hside hden]
    _ = -epsilon * T.signedDoubleArea ^ 2 /
        T.signedPerimeter sa 1 1 ^ 2 := by ring

private theorem sideDistanceSqC_sideMagnitude_value
    (T : Triangle) (sc epsilon : ℝ)
    (hsc : sc ^ 2 = 1) (hden : T.signedPerimeter 1 1 sc ≠ 0)
    (hC : T.sideAbsLengthC ^ 2 = epsilon * T.sideSqC)
    (hside : T.sideSqC ≠ 0) :
    T.sideDistanceSqC
        (T.barycentricPoint (T.sideMagnitudeWeights 1 1 sc hden)) hside =
      -epsilon * T.signedDoubleArea ^ 2 /
        T.signedPerimeter 1 1 sc ^ 2 := by
  rw [sideDistanceSqC_barycentric]
  change
    -((sc * T.sideAbsLengthC / T.signedPerimeter 1 1 sc) *
        T.signedDoubleArea) ^ 2 / T.sideSqC = _
  calc
    -((sc * T.sideAbsLengthC / T.signedPerimeter 1 1 sc) *
        T.signedDoubleArea) ^ 2 / T.sideSqC =
        -T.signedDoubleArea ^ 2 *
          ((sc * T.sideAbsLengthC / T.signedPerimeter 1 1 sc) ^ 2 /
            T.sideSqC) := by ring
    _ = -T.signedDoubleArea ^ 2 *
          (epsilon / T.signedPerimeter 1 1 sc ^ 2) := by
      rw [signedMagnitude_ratio_value _ _ _ _ _ hsc hC hside hden]
    _ = -epsilon * T.signedDoubleArea ^ 2 /
        T.signedPerimeter 1 1 sc ^ 2 := by ring

theorem inradiusSq_eq_spacelike_formula {T : Triangle}
    (hT : T.IsSpacelike) :
    T.inradiusSq (Or.inl hT) =
      -T.signedDoubleArea ^ 2 / T.perimeterAbs ^ 2 := by
  unfold inradiusSq incenter incenterWeights
  have hnm : T.IsNonMixed := Or.inl hT
  have hden : T.signedPerimeter 1 1 1 ≠ 0 := by
    simpa [signedPerimeter, perimeterAbs] using
      ne_of_gt hnm.perimeterAbs_pos
  have h := sideDistanceSqA_sideMagnitude_value T 1 1 (by norm_num)
    hden
    (by
      change absLength T.sideVecA ^ 2 = 1 * q T.sideVecA
      simpa only [one_mul] using absLength_sq_of_spacelike hT.1)
    (ne_of_gt hT.1)
  simpa [signedPerimeter, perimeterAbs] using h

theorem inradiusSq_eq_timelike_formula {T : Triangle}
    (hT : T.IsTimelike) :
    T.inradiusSq (Or.inr hT) =
      T.signedDoubleArea ^ 2 / T.perimeterAbs ^ 2 := by
  unfold inradiusSq incenter incenterWeights
  have hnm : T.IsNonMixed := Or.inr hT
  have hden : T.signedPerimeter 1 1 1 ≠ 0 := by
    simpa [signedPerimeter, perimeterAbs] using
      ne_of_gt hnm.perimeterAbs_pos
  have h := sideDistanceSqA_sideMagnitude_value T 1 (-1) (by norm_num)
    hden
    (by
      change absLength T.sideVecA ^ 2 = (-1) * q T.sideVecA
      simpa only [neg_one_mul] using absLength_sq_of_timelike hT.1)
    (ne_of_lt hT.1)
  simpa [signedPerimeter, perimeterAbs] using h

private theorem semiperimeterComplex_eq_spacelike_formula
    {T : Triangle} (hT : T.IsSpacelike) :
    T.semiperimeterComplex = (T.perimeterAbs / 2 : ℂ) := by
  unfold semiperimeterComplex perimeterComplex sideComplexLengthA
    sideComplexLengthB sideComplexLengthC
  rw [complexLength_eq_absLength_of_spacelike hT.1,
    complexLength_eq_absLength_of_spacelike hT.2.1,
    complexLength_eq_absLength_of_spacelike hT.2.2]
  simp [sideAbsLengthA, sideAbsLengthB, sideAbsLengthC, perimeterAbs]

private theorem semiperimeterComplex_eq_timelike_formula
    {T : Triangle} (hT : T.IsTimelike) :
    T.semiperimeterComplex = Complex.I * (T.perimeterAbs / 2 : ℂ) := by
  unfold semiperimeterComplex perimeterComplex sideComplexLengthA
    sideComplexLengthB sideComplexLengthC
  rw [complexLength_eq_I_mul_absLength_of_timelike hT.1,
    complexLength_eq_I_mul_absLength_of_timelike hT.2.1,
    complexLength_eq_I_mul_absLength_of_timelike hT.2.2]
  simp [sideAbsLengthA, sideAbsLengthB, sideAbsLengthC, perimeterAbs]
  ring

noncomputable def exradiusC (T : Triangle) (hT : T.IsNonMixed)
    (hC : T.excenterDenomC ≠ 0) : ℂ :=
  pointLineDistance (T.excenterC hC) T.A T.B hT.sidesNonNull.2.2

noncomputable def exradiusSqC (T : Triangle) (hT : T.IsNonMixed)
    (hC : T.excenterDenomC ≠ 0) : ℝ :=
  T.sideDistanceSqC (T.excenterC hC) hT.sidesNonNull.2.2

theorem exradiusC_sq_eq_sideDistanceSq (T : Triangle) (hT : T.IsNonMixed)
    (hC : T.excenterDenomC ≠ 0) :
    T.exradiusC hT hC ^ 2 = (T.exradiusSqC hT hC : ℂ) := by
  rw [exradiusC, pointLineDistance_sq]
  unfold exradiusSqC sideDistanceSqC
  rw [heightSq_eq_neg_area_sq_div_intervalSq]

private theorem semiperimeterComplex_sub_sideC_eq_spacelike_formula
    {T : Triangle} (hT : T.IsSpacelike) :
    T.semiperimeterComplex - T.sideComplexLengthC =
      (T.excenterDenomC / 2 : ℂ) := by
  rw [semiperimeterComplex_eq_spacelike_formula hT]
  unfold sideComplexLengthC
  rw [complexLength_eq_absLength_of_spacelike hT.2.2]
  simp [sideAbsLengthC, excenterDenomC, signedPerimeter, perimeterAbs]
  ring

private theorem semiperimeterComplex_sub_sideC_eq_timelike_formula
    {T : Triangle} (hT : T.IsTimelike) :
    T.semiperimeterComplex - T.sideComplexLengthC =
      Complex.I * (T.excenterDenomC / 2 : ℂ) := by
  rw [semiperimeterComplex_eq_timelike_formula hT]
  unfold sideComplexLengthC
  rw [complexLength_eq_I_mul_absLength_of_timelike hT.2.2]
  simp [sideAbsLengthC, excenterDenomC, signedPerimeter, perimeterAbs]
  ring

theorem exradiusSqC_eq_spacelike_formula {T : Triangle}
    (hT : T.IsSpacelike) (hC : T.excenterDenomC ≠ 0) :
    T.exradiusSqC (Or.inl hT) hC =
      -T.signedDoubleArea ^ 2 / T.excenterDenomC ^ 2 := by
  unfold exradiusSqC excenterC excenterWeightsC
  have h := sideDistanceSqC_sideMagnitude_value T (-1) 1 (by norm_num)
    (by simpa [excenterDenomC] using hC)
    (by
      change absLength T.sideVecC ^ 2 = 1 * q T.sideVecC
      simpa only [one_mul] using absLength_sq_of_spacelike hT.2.2)
    (ne_of_gt hT.2.2)
  simpa [excenterDenomC] using h

theorem exradiusSqC_eq_timelike_formula {T : Triangle}
    (hT : T.IsTimelike) (hC : T.excenterDenomC ≠ 0) :
    T.exradiusSqC (Or.inr hT) hC =
      T.signedDoubleArea ^ 2 / T.excenterDenomC ^ 2 := by
  unfold exradiusSqC excenterC excenterWeightsC
  have h := sideDistanceSqC_sideMagnitude_value T (-1) (-1) (by norm_num)
    (by simpa [excenterDenomC] using hC)
    (by
      change absLength T.sideVecC ^ 2 = (-1) * q T.sideVecC
      simpa only [neg_one_mul] using absLength_sq_of_timelike hT.2.2)
    (ne_of_lt hT.2.2)
  simpa [excenterDenomC] using h

theorem exradiusC_sq_eq_complexArea_div_semiperimeter_sub_side_sq
    (T : Triangle) (hT : T.IsNonMixed) (hC : T.excenterDenomC ≠ 0) :
    T.exradiusC hT hC ^ 2 =
      T.complexArea ^ 2 /
        (T.semiperimeterComplex - T.sideComplexLengthC) ^ 2 := by
  rcases hT with hS | hT
  · rw [exradiusC_sq_eq_sideDistanceSq T (Or.inl hS) hC,
      exradiusSqC_eq_spacelike_formula hS hC, complexArea_sq,
      semiperimeterComplex_sub_sideC_eq_spacelike_formula hS]
    push_cast
    ring
  · rw [exradiusC_sq_eq_sideDistanceSq T (Or.inr hT) hC,
      exradiusSqC_eq_timelike_formula hT hC, complexArea_sq,
      semiperimeterComplex_sub_sideC_eq_timelike_formula hT]
    rw [mul_pow, pow_two Complex.I, Complex.I_mul_I]
    push_cast
    ring

theorem inradius_sq_eq_complexArea_div_semiperimeter_sq
    (T : Triangle) (hT : T.IsNonMixed) :
    T.inradius hT ^ 2 =
      T.complexArea ^ 2 / T.semiperimeterComplex ^ 2 := by
  rcases hT with hS | hT
  · rw [inradius_sq_eq_sideDistanceSq T (Or.inl hS),
      inradiusSq_eq_spacelike_formula hS, complexArea_sq,
      semiperimeterComplex_eq_spacelike_formula hS]
    push_cast
    ring
  · rw [inradius_sq_eq_sideDistanceSq T (Or.inr hT),
      inradiusSq_eq_timelike_formula hT, complexArea_sq,
      semiperimeterComplex_eq_timelike_formula hT]
    rw [mul_pow, pow_two Complex.I, Complex.I_mul_I]
    push_cast
    ring

end

end Triangle
end MinkowskiMerge
