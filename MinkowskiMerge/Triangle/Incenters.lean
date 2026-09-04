import MinkowskiMerge.Length
import MinkowskiMerge.Triangle.AffineCombination
import MinkowskiMerge.Triangle.Lines


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

def IsNonMixed (T : Triangle) : Prop := T.IsSpacelike ∨ T.IsTimelike

theorem IsNonMixed.sidesNonNull {T : Triangle} (hT : T.IsNonMixed) :
    T.SidesNonNull := by
  rcases hT with hT | hT
  · exact ⟨ne_of_gt hT.1, ne_of_gt hT.2.1, ne_of_gt hT.2.2⟩
  · exact ⟨ne_of_lt hT.1, ne_of_lt hT.2.1, ne_of_lt hT.2.2⟩

theorem IsNonMixed.sideAbsLengthA_pos {T : Triangle} (hT : T.IsNonMixed) :
    0 < T.sideAbsLengthA := by
  apply absLength_pos_iff.mpr
  exact hT.sidesNonNull.1

theorem IsNonMixed.sideAbsLengthB_pos {T : Triangle} (hT : T.IsNonMixed) :
    0 < T.sideAbsLengthB := by
  apply absLength_pos_iff.mpr
  exact hT.sidesNonNull.2.1

theorem IsNonMixed.sideAbsLengthC_pos {T : Triangle} (hT : T.IsNonMixed) :
    0 < T.sideAbsLengthC := by
  apply absLength_pos_iff.mpr
  exact hT.sidesNonNull.2.2

theorem IsNonMixed.perimeterAbs_pos {T : Triangle} (hT : T.IsNonMixed) :
    0 < T.perimeterAbs := by
  unfold perimeterAbs
  linarith [hT.sideAbsLengthA_pos, hT.sideAbsLengthB_pos,
    hT.sideAbsLengthC_pos]

def normalizedWeights (a b c : ℝ) (h : a + b + c ≠ 0) : BarycentricWeights where
  a := a / (a + b + c)
  b := b / (a + b + c)
  c := c / (a + b + c)
  sum_eq_one := by
    field_simp [h]

def signedPerimeter (T : Triangle) (sa sb sc : ℝ) : ℝ :=
  sa * T.sideAbsLengthA + sb * T.sideAbsLengthB + sc * T.sideAbsLengthC

def sideMagnitudeWeights (T : Triangle) (sa sb sc : ℝ)
    (h : T.signedPerimeter sa sb sc ≠ 0) : BarycentricWeights :=
  normalizedWeights
    (sa * T.sideAbsLengthA)
    (sb * T.sideAbsLengthB)
    (sc * T.sideAbsLengthC) h

def signedPerimeterComplex (T : Triangle) (sa sb sc : ℝ) : ℂ :=
  (sa : ℂ) * T.sideComplexLengthA +
    (sb : ℂ) * T.sideComplexLengthB +
    (sc : ℂ) * T.sideComplexLengthC

def HasCommonLengthPhase (T : Triangle) (phase : ℂ) : Prop :=
  phase ≠ 0 ∧
    T.sideComplexLengthA = phase * (T.sideAbsLengthA : ℂ) ∧
    T.sideComplexLengthB = phase * (T.sideAbsLengthB : ℂ) ∧
    T.sideComplexLengthC = phase * (T.sideAbsLengthC : ℂ)

theorem exists_commonLengthPhase (T : Triangle) (hT : T.IsNonMixed) :
    ∃ phase : ℂ, T.HasCommonLengthPhase phase := by
  rcases hT with hS | hT
  · refine ⟨1, one_ne_zero, ?_, ?_, ?_⟩
    · change complexLength T.sideVecA = 1 * (absLength T.sideVecA : ℂ)
      simpa only [one_mul] using complexLength_eq_absLength_of_spacelike hS.1
    · change complexLength T.sideVecB = 1 * (absLength T.sideVecB : ℂ)
      simpa only [one_mul] using complexLength_eq_absLength_of_spacelike hS.2.1
    · change complexLength T.sideVecC = 1 * (absLength T.sideVecC : ℂ)
      simpa only [one_mul] using complexLength_eq_absLength_of_spacelike hS.2.2
  · refine ⟨Complex.I, Complex.I_ne_zero, ?_, ?_, ?_⟩
    · change complexLength T.sideVecA = Complex.I * (absLength T.sideVecA : ℂ)
      exact complexLength_eq_I_mul_absLength_of_timelike hT.1
    · change complexLength T.sideVecB = Complex.I * (absLength T.sideVecB : ℂ)
      exact complexLength_eq_I_mul_absLength_of_timelike hT.2.1
    · change complexLength T.sideVecC = Complex.I * (absLength T.sideVecC : ℂ)
      exact complexLength_eq_I_mul_absLength_of_timelike hT.2.2

theorem signedPerimeterComplex_eq_phase_mul (T : Triangle) {phase : ℂ}
    (hp : T.HasCommonLengthPhase phase) (sa sb sc : ℝ) :
    T.signedPerimeterComplex sa sb sc =
      phase * (T.signedPerimeter sa sb sc : ℂ) := by
  rw [signedPerimeterComplex, hp.2.1, hp.2.2.1, hp.2.2.2]
  simp only [signedPerimeter]
  push_cast
  ring

private theorem sideMagnitudeWeight_eq_complexCoefficient
    (T : Triangle) {phase : ℂ} (hp : T.HasCommonLengthPhase phase)
    (s a : ℝ) (L : ℂ) (hL : L = phase * (a : ℂ))
    (sa sb sc : ℝ) (hden : T.signedPerimeter sa sb sc ≠ 0) :
    (((s * a / T.signedPerimeter sa sb sc : ℝ)) : ℂ) =
      (s : ℂ) * L / T.signedPerimeterComplex sa sb sc := by
  rw [hL, signedPerimeterComplex_eq_phase_mul T hp]
  have hd : (T.signedPerimeter sa sb sc : ℂ) ≠ 0 := by exact_mod_cast hden
  field_simp [hp.1, hd]
  exact_mod_cast div_mul_cancel₀ (s * a) hden

theorem sideMagnitudeWeightA_eq_complexCoefficient
    (T : Triangle) (hT : T.IsNonMixed) (sa sb sc : ℝ)
    (hden : T.signedPerimeter sa sb sc ≠ 0) :
    ((T.sideMagnitudeWeights sa sb sc hden).a : ℂ) =
      (sa : ℂ) * T.sideComplexLengthA / T.signedPerimeterComplex sa sb sc := by
  obtain ⟨phase, hp⟩ := T.exists_commonLengthPhase hT
  apply sideMagnitudeWeight_eq_complexCoefficient T hp sa T.sideAbsLengthA
    T.sideComplexLengthA hp.2.1 sa sb sc hden

theorem sideMagnitudeWeightB_eq_complexCoefficient
    (T : Triangle) (hT : T.IsNonMixed) (sa sb sc : ℝ)
    (hden : T.signedPerimeter sa sb sc ≠ 0) :
    ((T.sideMagnitudeWeights sa sb sc hden).b : ℂ) =
      (sb : ℂ) * T.sideComplexLengthB / T.signedPerimeterComplex sa sb sc := by
  obtain ⟨phase, hp⟩ := T.exists_commonLengthPhase hT
  apply sideMagnitudeWeight_eq_complexCoefficient T hp sb T.sideAbsLengthB
    T.sideComplexLengthB hp.2.2.1 sa sb sc hden

theorem sideMagnitudeWeightC_eq_complexCoefficient
    (T : Triangle) (hT : T.IsNonMixed) (sa sb sc : ℝ)
    (hden : T.signedPerimeter sa sb sc ≠ 0) :
    ((T.sideMagnitudeWeights sa sb sc hden).c : ℂ) =
      (sc : ℂ) * T.sideComplexLengthC / T.signedPerimeterComplex sa sb sc := by
  obtain ⟨phase, hp⟩ := T.exists_commonLengthPhase hT
  apply sideMagnitudeWeight_eq_complexCoefficient T hp sc T.sideAbsLengthC
    T.sideComplexLengthC hp.2.2.2 sa sb sc hden

def excenterDenomA (T : Triangle) : ℝ := T.signedPerimeter (-1) 1 1

def excenterDenomB (T : Triangle) : ℝ := T.signedPerimeter 1 (-1) 1

def excenterDenomC (T : Triangle) : ℝ := T.signedPerimeter 1 1 (-1)

def incenterWeights (T : Triangle) (hT : T.IsNonMixed) : BarycentricWeights :=
  T.sideMagnitudeWeights 1 1 1 (by
    simpa [signedPerimeter, perimeterAbs] using ne_of_gt hT.perimeterAbs_pos)

def excenterWeightsA (T : Triangle) (hA : T.excenterDenomA ≠ 0) :
    BarycentricWeights :=
  T.sideMagnitudeWeights (-1) 1 1 hA

def excenterWeightsB (T : Triangle) (hB : T.excenterDenomB ≠ 0) :
    BarycentricWeights :=
  T.sideMagnitudeWeights 1 (-1) 1 hB

def excenterWeightsC (T : Triangle) (hC : T.excenterDenomC ≠ 0) :
    BarycentricWeights :=
  T.sideMagnitudeWeights 1 1 (-1) hC

def incenter (T : Triangle) (hT : T.IsNonMixed) : Point :=
  T.barycentricPoint (T.incenterWeights hT)

def excenterA (T : Triangle) (hA : T.excenterDenomA ≠ 0) : Point :=
  T.barycentricPoint (T.excenterWeightsA hA)

def excenterB (T : Triangle) (hB : T.excenterDenomB ≠ 0) : Point :=
  T.barycentricPoint (T.excenterWeightsB hB)

def excenterC (T : Triangle) (hC : T.excenterDenomC ≠ 0) : Point :=
  T.barycentricPoint (T.excenterWeightsC hC)

theorem two_mul_semiperimeterAbs_sub_sideAbsLengthA (T : Triangle) :
    2 * (T.semiperimeterAbs - T.sideAbsLengthA) = T.excenterDenomA := by
  simp only [semiperimeterAbs, perimeterAbs, excenterDenomA, signedPerimeter]
  ring

theorem two_mul_semiperimeterAbs_sub_sideAbsLengthB (T : Triangle) :
    2 * (T.semiperimeterAbs - T.sideAbsLengthB) = T.excenterDenomB := by
  simp only [semiperimeterAbs, perimeterAbs, excenterDenomB, signedPerimeter]
  ring

theorem two_mul_semiperimeterAbs_sub_sideAbsLengthC (T : Triangle) :
    2 * (T.semiperimeterAbs - T.sideAbsLengthC) = T.excenterDenomC := by
  simp only [semiperimeterAbs, perimeterAbs, excenterDenomC, signedPerimeter]
  ring

theorem incenter_eq_sideCombination (T : Triangle) (hT : T.IsNonMixed) :
    T.incenter hT =
      (T.sideAbsLengthA / T.perimeterAbs) • T.A +
      (T.sideAbsLengthB / T.perimeterAbs) • T.B +
      (T.sideAbsLengthC / T.perimeterAbs) • T.C := by
  rw [incenter, barycentricPoint_eq_linearCombination]
  simp only [incenterWeights, sideMagnitudeWeights, normalizedWeights,
    perimeterAbs, one_mul]

theorem excenterA_eq_sideCombination (T : Triangle) (hA : T.excenterDenomA ≠ 0) :
    T.excenterA hA =
      (-T.sideAbsLengthA / T.excenterDenomA) • T.A +
      (T.sideAbsLengthB / T.excenterDenomA) • T.B +
      (T.sideAbsLengthC / T.excenterDenomA) • T.C := by
  rw [excenterA, barycentricPoint_eq_linearCombination]
  simp only [excenterWeightsA, sideMagnitudeWeights, normalizedWeights,
    excenterDenomA, signedPerimeter, one_mul, neg_one_mul]

theorem excenterB_eq_sideCombination (T : Triangle) (hB : T.excenterDenomB ≠ 0) :
    T.excenterB hB =
      (T.sideAbsLengthA / T.excenterDenomB) • T.A +
      (-T.sideAbsLengthB / T.excenterDenomB) • T.B +
      (T.sideAbsLengthC / T.excenterDenomB) • T.C := by
  rw [excenterB, barycentricPoint_eq_linearCombination]
  simp only [excenterWeightsB, sideMagnitudeWeights, normalizedWeights,
    excenterDenomB, signedPerimeter, one_mul, neg_one_mul]

theorem excenterC_eq_sideCombination (T : Triangle) (hC : T.excenterDenomC ≠ 0) :
    T.excenterC hC =
      (T.sideAbsLengthA / T.excenterDenomC) • T.A +
      (T.sideAbsLengthB / T.excenterDenomC) • T.B +
      (-T.sideAbsLengthC / T.excenterDenomC) • T.C := by
  rw [excenterC, barycentricPoint_eq_linearCombination]
  simp only [excenterWeightsC, sideMagnitudeWeights, normalizedWeights,
    excenterDenomC, signedPerimeter, one_mul, neg_one_mul]

def sideDistanceSqA (T : Triangle) (P : Point) (hA : T.sideSqA ≠ 0) : ℝ :=
  heightSq P T.B T.C hA

def sideDistanceSqB (T : Triangle) (P : Point) (hB : T.sideSqB ≠ 0) : ℝ :=
  heightSq P T.C T.A hB

def sideDistanceSqC (T : Triangle) (P : Point) (hC : T.sideSqC ≠ 0) : ℝ :=
  heightSq P T.A T.B hC

theorem sideDistanceSqA_barycentric (T : Triangle) (w : BarycentricWeights)
    (hA : T.sideSqA ≠ 0) :
    T.sideDistanceSqA (T.barycentricPoint w) hA =
      -(w.a * T.signedDoubleArea) ^ 2 / T.sideSqA := by
  rw [sideDistanceSqA, heightSq_eq_neg_area_sq_div_intervalSq,
    signedDoubleArea_barycentric_BC]
  rfl

theorem sideDistanceSqB_barycentric (T : Triangle) (w : BarycentricWeights)
    (hB : T.sideSqB ≠ 0) :
    T.sideDistanceSqB (T.barycentricPoint w) hB =
      -(w.b * T.signedDoubleArea) ^ 2 / T.sideSqB := by
  rw [sideDistanceSqB, heightSq_eq_neg_area_sq_div_intervalSq,
    signedDoubleArea_barycentric_CA]
  rfl

theorem sideDistanceSqC_barycentric (T : Triangle) (w : BarycentricWeights)
    (hC : T.sideSqC ≠ 0) :
    T.sideDistanceSqC (T.barycentricPoint w) hC =
      -(w.c * T.signedDoubleArea) ^ 2 / T.sideSqC := by
  rw [sideDistanceSqC, heightSq_eq_neg_area_sq_div_intervalSq,
    signedDoubleArea_barycentric_AB]
  rfl

def WeightsMatchSideSquares (T : Triangle) (w : BarycentricWeights) : Prop :=
  w.a ^ 2 / T.sideSqA = w.b ^ 2 / T.sideSqB ∧
    w.b ^ 2 / T.sideSqB = w.c ^ 2 / T.sideSqC

def HasEqualSideDistanceSq (T : Triangle) (P : Point) (hS : T.SidesNonNull) : Prop :=
  T.sideDistanceSqA P hS.1 = T.sideDistanceSqB P hS.2.1 ∧
    T.sideDistanceSqB P hS.2.1 = T.sideDistanceSqC P hS.2.2

theorem barycentricPoint_hasEqualSideDistanceSq (T : Triangle)
    (w : BarycentricWeights) (hS : T.SidesNonNull)
    (hw : T.WeightsMatchSideSquares w) :
    T.HasEqualSideDistanceSq (T.barycentricPoint w) hS := by
  rw [HasEqualSideDistanceSq,
    sideDistanceSqA_barycentric, sideDistanceSqB_barycentric,
    sideDistanceSqC_barycentric]
  constructor
  · calc
      -(w.a * T.signedDoubleArea) ^ 2 / T.sideSqA =
          -T.signedDoubleArea ^ 2 * (w.a ^ 2 / T.sideSqA) := by ring
      _ = -T.signedDoubleArea ^ 2 * (w.b ^ 2 / T.sideSqB) := by rw [hw.1]
      _ = -(w.b * T.signedDoubleArea) ^ 2 / T.sideSqB := by ring
  · calc
      -(w.b * T.signedDoubleArea) ^ 2 / T.sideSqB =
          -T.signedDoubleArea ^ 2 * (w.b ^ 2 / T.sideSqB) := by ring
      _ = -T.signedDoubleArea ^ 2 * (w.c ^ 2 / T.sideSqC) := by rw [hw.2]
      _ = -(w.c * T.signedDoubleArea) ^ 2 / T.sideSqC := by ring

private theorem signedMagnitude_ratio
    (a side s d epsilon : ℝ)
    (hs : s ^ 2 = 1) (ha : a ^ 2 = epsilon * side)
    (hside : side ≠ 0) (hd : d ≠ 0) :
    (s * a / d) ^ 2 / side = epsilon / d ^ 2 := by
  calc
    (s * a / d) ^ 2 / side =
        (s ^ 2 * a ^ 2) / (d ^ 2 * side) := by ring
    _ = (epsilon * side) / (d ^ 2 * side) := by rw [hs, ha]; ring
    _ = epsilon / d ^ 2 := by field_simp [hside, hd]

private theorem sideMagnitudeWeights_match_of_sideAbsLength_sq
    (T : Triangle) (sa sb sc epsilon : ℝ)
    (hsa : sa ^ 2 = 1) (hsb : sb ^ 2 = 1) (hsc : sc ^ 2 = 1)
    (hden : T.signedPerimeter sa sb sc ≠ 0)
    (hA : T.sideAbsLengthA ^ 2 = epsilon * T.sideSqA)
    (hB : T.sideAbsLengthB ^ 2 = epsilon * T.sideSqB)
    (hC : T.sideAbsLengthC ^ 2 = epsilon * T.sideSqC)
    (hnA : T.sideSqA ≠ 0) (hnB : T.sideSqB ≠ 0) (hnC : T.sideSqC ≠ 0) :
    T.WeightsMatchSideSquares (T.sideMagnitudeWeights sa sb sc hden) := by
  unfold WeightsMatchSideSquares
  change
    (sa * T.sideAbsLengthA / T.signedPerimeter sa sb sc) ^ 2 / T.sideSqA =
        (sb * T.sideAbsLengthB / T.signedPerimeter sa sb sc) ^ 2 / T.sideSqB ∧
      (sb * T.sideAbsLengthB / T.signedPerimeter sa sb sc) ^ 2 / T.sideSqB =
        (sc * T.sideAbsLengthC / T.signedPerimeter sa sb sc) ^ 2 / T.sideSqC
  constructor
  · rw [signedMagnitude_ratio _ _ _ _ _ hsa hA hnA hden,
      signedMagnitude_ratio _ _ _ _ _ hsb hB hnB hden]
  · rw [signedMagnitude_ratio _ _ _ _ _ hsb hB hnB hden,
      signedMagnitude_ratio _ _ _ _ _ hsc hC hnC hden]

theorem sideMagnitudeWeights_matchSideSquares (T : Triangle) (hT : T.IsNonMixed)
    (sa sb sc : ℝ) (hsa : sa ^ 2 = 1) (hsb : sb ^ 2 = 1) (hsc : sc ^ 2 = 1)
    (hden : T.signedPerimeter sa sb sc ≠ 0) :
    T.WeightsMatchSideSquares (T.sideMagnitudeWeights sa sb sc hden) := by
  have hS := hT.sidesNonNull
  rcases hT with hT | hT
  · apply sideMagnitudeWeights_match_of_sideAbsLength_sq T sa sb sc 1
      hsa hsb hsc hden
    · change absLength T.sideVecA ^ 2 = 1 * q T.sideVecA
      simpa only [one_mul] using absLength_sq_of_spacelike hT.1
    · change absLength T.sideVecB ^ 2 = 1 * q T.sideVecB
      simpa only [one_mul] using absLength_sq_of_spacelike hT.2.1
    · change absLength T.sideVecC ^ 2 = 1 * q T.sideVecC
      simpa only [one_mul] using absLength_sq_of_spacelike hT.2.2
    · exact hS.1
    · exact hS.2.1
    · exact hS.2.2
  · apply sideMagnitudeWeights_match_of_sideAbsLength_sq T sa sb sc (-1)
      hsa hsb hsc hden
    · change absLength T.sideVecA ^ 2 = (-1) * q T.sideVecA
      simpa only [neg_one_mul] using absLength_sq_of_timelike hT.1
    · change absLength T.sideVecB ^ 2 = (-1) * q T.sideVecB
      simpa only [neg_one_mul] using absLength_sq_of_timelike hT.2.1
    · change absLength T.sideVecC ^ 2 = (-1) * q T.sideVecC
      simpa only [neg_one_mul] using absLength_sq_of_timelike hT.2.2
    · exact hS.1
    · exact hS.2.1
    · exact hS.2.2

theorem incenter_hasEqualSideDistanceSq (T : Triangle) (hT : T.IsNonMixed) :
    T.HasEqualSideDistanceSq (T.incenter hT) hT.sidesNonNull := by
  apply barycentricPoint_hasEqualSideDistanceSq
  exact sideMagnitudeWeights_matchSideSquares T hT 1 1 1 (by norm_num)
    (by norm_num) (by norm_num) _

theorem excenterA_hasEqualSideDistanceSq (T : Triangle) (hT : T.IsNonMixed)
    (hA : T.excenterDenomA ≠ 0) :
    T.HasEqualSideDistanceSq (T.excenterA hA) hT.sidesNonNull := by
  apply barycentricPoint_hasEqualSideDistanceSq
  exact sideMagnitudeWeights_matchSideSquares T hT (-1) 1 1 (by norm_num)
    (by norm_num) (by norm_num) hA

theorem excenterB_hasEqualSideDistanceSq (T : Triangle) (hT : T.IsNonMixed)
    (hB : T.excenterDenomB ≠ 0) :
    T.HasEqualSideDistanceSq (T.excenterB hB) hT.sidesNonNull := by
  apply barycentricPoint_hasEqualSideDistanceSq
  exact sideMagnitudeWeights_matchSideSquares T hT 1 (-1) 1 (by norm_num)
    (by norm_num) (by norm_num) hB

theorem excenterC_hasEqualSideDistanceSq (T : Triangle) (hT : T.IsNonMixed)
    (hC : T.excenterDenomC ≠ 0) :
    T.HasEqualSideDistanceSq (T.excenterC hC) hT.sidesNonNull := by
  apply barycentricPoint_hasEqualSideDistanceSq
  exact sideMagnitudeWeights_matchSideSquares T hT 1 1 (-1) (by norm_num)
    (by norm_num) (by norm_num) hC

end

end Triangle
end MinkowskiMerge
