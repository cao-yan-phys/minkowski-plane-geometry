import MinkowskiMerge.Triangle.CircleAlgebra
import MinkowskiMerge.Triangle.Radii


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

private theorem incenter_quartic_algebra (a b c D e : ℝ)
    (hp : a + b + c ≠ 0) (hD : D ≠ 0) (he : e ^ 2 = 1)
    (hheron : 4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 = -4 * D ^ 2) :
    let p := a + b + c
    let R2 := -e * (a ^ 2 * b ^ 2 * c ^ 2) / (4 * D ^ 2)
    let r2 := -e * D ^ 2 / p ^ 2
    let S := R2 / 4 - e * (
      (b / p - 1 / 2) * (c / p - 1 / 2) * a ^ 2 +
      (c / p - 1 / 2) * (a / p - 1 / 2) * b ^ 2 +
      (a / p - 1 / 2) * (b / p - 1 / 2) * c ^ 2)
    (S - R2 / 4 - r2) ^ 2 = R2 * r2 := by
  dsimp
  have hfactor : (e - 1) * (e + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · have heq : e = 1 := by linarith
    subst e
    have hD2 : D ^ 2 =
        -(4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2) / 4 := by
      linarith
    have hD4 : D ^ 4 =
        (-(4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2) / 4) ^ 2 := by
      rw [show D ^ 4 = (D ^ 2) ^ 2 by ring, hD2]
    field_simp [hp, hD]
    rw [hD4, hD2]
    ring
  · have heq : e = -1 := by linarith
    subst e
    have hD2 : D ^ 2 =
        -(4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2) / 4 := by
      linarith
    have hD4 : D ^ 4 =
        (-(4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2) / 4) ^ 2 := by
      rw [show D ^ 4 = (D ^ 2) ^ 2 by ring, hD2]
    field_simp [hp, hD]
    rw [hD4, hD2]
    ring

private theorem excenterC_quartic_algebra (a b c D e : ℝ)
    (hd : a + b - c ≠ 0) (hD : D ≠ 0) (he : e ^ 2 = 1)
    (hheron : 4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 = -4 * D ^ 2) :
    let d := a + b - c
    let R2 := -e * (a ^ 2 * b ^ 2 * c ^ 2) / (4 * D ^ 2)
    let r2 := -e * D ^ 2 / d ^ 2
    let S := R2 / 4 - e * (
      (b / d - 1 / 2) * (-c / d - 1 / 2) * a ^ 2 +
      (-c / d - 1 / 2) * (a / d - 1 / 2) * b ^ 2 +
      (a / d - 1 / 2) * (b / d - 1 / 2) * c ^ 2)
    (S - R2 / 4 - r2) ^ 2 = R2 * r2 := by
  dsimp
  have hfactor : (e - 1) * (e + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · have heq : e = 1 := by linarith
    subst e
    have hD2 : D ^ 2 =
        -(4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2) / 4 := by
      linarith
    have hD4 : D ^ 4 =
        (-(4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2) / 4) ^ 2 := by
      rw [show D ^ 4 = (D ^ 2) ^ 2 by ring, hD2]
    field_simp [hd, hD]
    rw [hD4, hD2]
    ring
  · have heq : e = -1 := by linarith
    subst e
    have hD2 : D ^ 2 =
        -(4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2) / 4 := by
      linarith
    have hD4 : D ^ 4 =
        (-(4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2) / 4) ^ 2 := by
      rw [show D ^ 4 = (D ^ 2) ^ 2 by ring, hD2]
    field_simp [hd, hD]
    rw [hD4, hD2]
    ring

theorem intervalSq_ninePointCenter_incenter_euler_quartic (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) :
    (intervalSq (T.ninePointCenter hN) (T.incenter hT) -
        T.circumradiusSqAt (T.circumcenter hN) / 4 - T.inradiusSq hT) ^ 2 =
      T.circumradiusSqAt (T.circumcenter hN) * T.inradiusSq hT := by
  rcases hT with hS | hT
  · have hp : T.sideAbsLengthA + T.sideAbsLengthB + T.sideAbsLengthC ≠ 0 := by
      simpa [perimeterAbs] using ne_of_gt (IsNonMixed.perimeterAbs_pos (Or.inl hS))
    have hD := hN.signedDoubleArea_ne_zero
    have hA : T.sideAbsLengthA ^ 2 = T.sideSqA := by
      exact absLength_sq_of_spacelike hS.1
    have hB : T.sideAbsLengthB ^ 2 = T.sideSqB := by
      exact absLength_sq_of_spacelike hS.2.1
    have hC : T.sideAbsLengthC ^ 2 = T.sideSqC := by
      exact absLength_sq_of_spacelike hS.2.2
    have hheron : 4 * T.sideAbsLengthB ^ 2 * T.sideAbsLengthC ^ 2 -
        (T.sideAbsLengthB ^ 2 + T.sideAbsLengthC ^ 2 - T.sideAbsLengthA ^ 2) ^ 2 =
          -4 * T.signedDoubleArea ^ 2 := by
      calc
        4 * T.sideAbsLengthB ^ 2 * T.sideAbsLengthC ^ 2 -
            (T.sideAbsLengthB ^ 2 + T.sideAbsLengthC ^ 2 -
              T.sideAbsLengthA ^ 2) ^ 2 =
            4 * T.sideSqB * T.sideSqC -
              (T.sideSqB + T.sideSqC - T.sideSqA) ^ 2 := by rw [hA, hB, hC]
        _ = -4 * T.signedDoubleArea ^ 2 := T.sideSq_heron_polynomial
    rw [intervalSq_ninePointCenter_incenter T hN (Or.inl hS),
      circumradiusSq_eq_sideSq_product_div_areaSq T hN,
      inradiusSq_eq_spacelike_formula hS, ← hA, ← hB, ← hC]
    simp only [incenterWeights, sideMagnitudeWeights, normalizedWeights,
      perimeterAbs, one_mul]
    convert incenter_quartic_algebra T.sideAbsLengthA T.sideAbsLengthB T.sideAbsLengthC
      T.signedDoubleArea 1 hp hD (by norm_num) hheron using 1 <;> ring
  · have hp : T.sideAbsLengthA + T.sideAbsLengthB + T.sideAbsLengthC ≠ 0 := by
      simpa [perimeterAbs] using ne_of_gt (IsNonMixed.perimeterAbs_pos (Or.inr hT))
    have hD := hN.signedDoubleArea_ne_zero
    have hA : T.sideAbsLengthA ^ 2 = -T.sideSqA := by
      exact absLength_sq_of_timelike hT.1
    have hB : T.sideAbsLengthB ^ 2 = -T.sideSqB := by
      exact absLength_sq_of_timelike hT.2.1
    have hC : T.sideAbsLengthC ^ 2 = -T.sideSqC := by
      exact absLength_sq_of_timelike hT.2.2
    have hA' : T.sideSqA = -T.sideAbsLengthA ^ 2 := by linarith
    have hB' : T.sideSqB = -T.sideAbsLengthB ^ 2 := by linarith
    have hC' : T.sideSqC = -T.sideAbsLengthC ^ 2 := by linarith
    have hheron : 4 * T.sideAbsLengthB ^ 2 * T.sideAbsLengthC ^ 2 -
        (T.sideAbsLengthB ^ 2 + T.sideAbsLengthC ^ 2 - T.sideAbsLengthA ^ 2) ^ 2 =
          -4 * T.signedDoubleArea ^ 2 := by
      calc
        4 * T.sideAbsLengthB ^ 2 * T.sideAbsLengthC ^ 2 -
            (T.sideAbsLengthB ^ 2 + T.sideAbsLengthC ^ 2 -
              T.sideAbsLengthA ^ 2) ^ 2 =
            4 * T.sideSqB * T.sideSqC -
              (T.sideSqB + T.sideSqC - T.sideSqA) ^ 2 := by
                rw [hA, hB, hC]
                ring
        _ = -4 * T.signedDoubleArea ^ 2 := T.sideSq_heron_polynomial
    rw [intervalSq_ninePointCenter_incenter T hN (Or.inr hT),
      circumradiusSq_eq_sideSq_product_div_areaSq T hN,
      inradiusSq_eq_timelike_formula hT, hA', hB', hC']
    simp only [incenterWeights, sideMagnitudeWeights, normalizedWeights,
      perimeterAbs, one_mul]
    convert incenter_quartic_algebra T.sideAbsLengthA T.sideAbsLengthB T.sideAbsLengthC
      T.signedDoubleArea (-1) hp hD (by norm_num) hheron using 1 <;> ring

theorem intervalSq_ninePointCenter_excenterC_euler_quartic (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) (hC : T.excenterDenomC ≠ 0) :
    (intervalSq (T.ninePointCenter hN) (T.excenterC hC) -
        T.circumradiusSqAt (T.circumcenter hN) / 4 - T.exradiusSqC hT hC) ^ 2 =
      T.circumradiusSqAt (T.circumcenter hN) * T.exradiusSqC hT hC := by
  rcases hT with hS | hT
  · have hd : T.sideAbsLengthA + T.sideAbsLengthB - T.sideAbsLengthC ≠ 0 := by
      simpa [excenterDenomC, signedPerimeter] using hC
    have hD := hN.signedDoubleArea_ne_zero
    have hA : T.sideAbsLengthA ^ 2 = T.sideSqA := by
      exact absLength_sq_of_spacelike hS.1
    have hB : T.sideAbsLengthB ^ 2 = T.sideSqB := by
      exact absLength_sq_of_spacelike hS.2.1
    have hCside : T.sideAbsLengthC ^ 2 = T.sideSqC := by
      exact absLength_sq_of_spacelike hS.2.2
    have hheron : 4 * T.sideAbsLengthB ^ 2 * T.sideAbsLengthC ^ 2 -
        (T.sideAbsLengthB ^ 2 + T.sideAbsLengthC ^ 2 - T.sideAbsLengthA ^ 2) ^ 2 =
          -4 * T.signedDoubleArea ^ 2 := by
      calc
        4 * T.sideAbsLengthB ^ 2 * T.sideAbsLengthC ^ 2 -
            (T.sideAbsLengthB ^ 2 + T.sideAbsLengthC ^ 2 -
              T.sideAbsLengthA ^ 2) ^ 2 =
            4 * T.sideSqB * T.sideSqC -
              (T.sideSqB + T.sideSqC - T.sideSqA) ^ 2 := by rw [hA, hB, hCside]
        _ = -4 * T.signedDoubleArea ^ 2 := T.sideSq_heron_polynomial
    rw [intervalSq_ninePointCenter_excenterC T hN hC,
      circumradiusSq_eq_sideSq_product_div_areaSq T hN,
      exradiusSqC_eq_spacelike_formula hS hC, ← hA, ← hB, ← hCside]
    simp only [excenterWeightsC, sideMagnitudeWeights, normalizedWeights,
      excenterDenomC, signedPerimeter, one_mul, neg_one_mul]
    convert excenterC_quartic_algebra T.sideAbsLengthA T.sideAbsLengthB T.sideAbsLengthC
      T.signedDoubleArea 1 hd hD (by norm_num) hheron using 1 <;> ring
  · have hd : T.sideAbsLengthA + T.sideAbsLengthB - T.sideAbsLengthC ≠ 0 := by
      simpa [excenterDenomC, signedPerimeter] using hC
    have hD := hN.signedDoubleArea_ne_zero
    have hA : T.sideAbsLengthA ^ 2 = -T.sideSqA := by
      exact absLength_sq_of_timelike hT.1
    have hB : T.sideAbsLengthB ^ 2 = -T.sideSqB := by
      exact absLength_sq_of_timelike hT.2.1
    have hCside : T.sideAbsLengthC ^ 2 = -T.sideSqC := by
      exact absLength_sq_of_timelike hT.2.2
    have hA' : T.sideSqA = -T.sideAbsLengthA ^ 2 := by linarith
    have hB' : T.sideSqB = -T.sideAbsLengthB ^ 2 := by linarith
    have hC' : T.sideSqC = -T.sideAbsLengthC ^ 2 := by linarith
    have hheron : 4 * T.sideAbsLengthB ^ 2 * T.sideAbsLengthC ^ 2 -
        (T.sideAbsLengthB ^ 2 + T.sideAbsLengthC ^ 2 - T.sideAbsLengthA ^ 2) ^ 2 =
          -4 * T.signedDoubleArea ^ 2 := by
      calc
        4 * T.sideAbsLengthB ^ 2 * T.sideAbsLengthC ^ 2 -
            (T.sideAbsLengthB ^ 2 + T.sideAbsLengthC ^ 2 -
              T.sideAbsLengthA ^ 2) ^ 2 =
            4 * T.sideSqB * T.sideSqC -
              (T.sideSqB + T.sideSqC - T.sideSqA) ^ 2 := by
                rw [hA, hB, hCside]
                ring
        _ = -4 * T.signedDoubleArea ^ 2 := T.sideSq_heron_polynomial
    rw [intervalSq_ninePointCenter_excenterC T hN hC,
      circumradiusSq_eq_sideSq_product_div_areaSq T hN,
      exradiusSqC_eq_timelike_formula hT hC, hA', hB', hC']
    simp only [excenterWeightsC, sideMagnitudeWeights, normalizedWeights,
      excenterDenomC, signedPerimeter, one_mul, neg_one_mul]
    convert excenterC_quartic_algebra T.sideAbsLengthA T.sideAbsLengthB T.sideAbsLengthC
      T.signedDoubleArea (-1) hd hD (by norm_num) hheron using 1 <;> ring

end

end Triangle
end MinkowskiMerge
