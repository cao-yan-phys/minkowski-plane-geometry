import MinkowskiMerge.Triangle.FeuerbachTangencyExcenterC
import MinkowskiMerge.Triangle.FeuerbachRelabel


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

noncomputable def exradiusAMagnitude (T : Triangle) : ℝ :=
  |T.signedDoubleArea| / |T.excenterDenomA|

noncomputable def exradiusBMagnitude (T : Triangle) : ℝ :=
  |T.signedDoubleArea| / |T.excenterDenomB|

@[simp] theorem rotate_ninePointRadiusMagnitude (T : Triangle) :
    T.rotate.ninePointRadiusMagnitude = T.ninePointRadiusMagnitude := by
  unfold ninePointRadiusMagnitude
  rw [rotate_sideAbsLengthA, rotate_sideAbsLengthB, rotate_sideAbsLengthC,
    rotate_signedDoubleArea]
  ring

@[simp] theorem rotate_exradiusCMagnitude (T : Triangle) :
    T.rotate.exradiusCMagnitude = T.exradiusAMagnitude := by
  unfold exradiusCMagnitude exradiusAMagnitude
  rw [rotate_signedDoubleArea, rotate_excenterDenomC]

@[simp] theorem rotateTwo_ninePointRadiusMagnitude (T : Triangle) :
    T.rotateTwo.ninePointRadiusMagnitude = T.ninePointRadiusMagnitude := by
  rw [show T.rotateTwo = T.rotate.rotate by rfl,
    rotate_ninePointRadiusMagnitude, rotate_ninePointRadiusMagnitude]

@[simp] theorem rotateTwo_exradiusCMagnitude (T : Triangle) :
    T.rotateTwo.exradiusCMagnitude = T.exradiusBMagnitude := by
  unfold exradiusCMagnitude exradiusBMagnitude
  unfold rotateTwo
  rw [rotate_signedDoubleArea, rotate_signedDoubleArea,
    rotate_excenterDenomC, rotate_excenterDenomA]

private theorem rotateSpacelike (T : Triangle) (hS : T.IsSpacelike) :
    T.rotate.IsSpacelike :=
  (rotate_isSpacelike_iff T).mpr hS

private theorem rotateTimelike (T : Triangle) (hT : T.IsTimelike) :
    T.rotate.IsTimelike :=
  (rotate_isTimelike_iff T).mpr hT

private theorem rotateTwoSpacelike (T : Triangle) (hS : T.IsSpacelike) :
    T.rotateTwo.IsSpacelike :=
  (rotate_isSpacelike_iff T.rotate).mpr (rotateSpacelike T hS)

private theorem rotateTwoTimelike (T : Triangle) (hT : T.IsTimelike) :
    T.rotateTwo.IsTimelike :=
  (rotate_isTimelike_iff T.rotate).mpr (rotateTimelike T hT)

noncomputable def excircleAFeuerbachContactPointSpacelike (T : Triangle)
    (hN : T.Nondegenerate) (hS : T.IsSpacelike)
    (hA : T.excenterDenomA ≠ 0) : Point :=
  LorentzCircle.tangentPointOfRadiusDifference (T.ninePointCircle hN)
    (T.excircleA (Or.inl hS) hA) T.ninePointRadiusMagnitude
    (T.lambdaA * T.exradiusAMagnitude)

noncomputable def excircleAFeuerbachContactPointTimelike (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsTimelike)
    (hA : T.excenterDenomA ≠ 0) : Point :=
  LorentzCircle.tangentPointOfRadiusDifference (T.ninePointCircle hN)
    (T.excircleA (Or.inr hT) hA) T.ninePointRadiusMagnitude
    (T.lambdaA * T.exradiusAMagnitude)

noncomputable def excircleBFeuerbachContactPointSpacelike (T : Triangle)
    (hN : T.Nondegenerate) (hS : T.IsSpacelike)
    (hB : T.excenterDenomB ≠ 0) : Point :=
  LorentzCircle.tangentPointOfRadiusDifference (T.ninePointCircle hN)
    (T.excircleB (Or.inl hS) hB) T.ninePointRadiusMagnitude
    (T.lambdaB * T.exradiusBMagnitude)

noncomputable def excircleBFeuerbachContactPointTimelike (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsTimelike)
    (hB : T.excenterDenomB ≠ 0) : Point :=
  LorentzCircle.tangentPointOfRadiusDifference (T.ninePointCircle hN)
    (T.excircleB (Or.inr hT) hB) T.ninePointRadiusMagnitude
    (T.lambdaB * T.exradiusBMagnitude)

theorem isTangentAt_excircleA_spacelike (T : Triangle) (hN : T.Nondegenerate)
    (hS : T.IsSpacelike) (hA : T.excenterDenomA ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaA * T.exradiusAMagnitude ≠ 0) :
    LorentzCircle.IsTangentAt (T.ninePointCircle hN) (T.excircleA (Or.inl hS) hA)
      (T.excircleAFeuerbachContactPointSpacelike hN hS hA) := by
  have hR : T.rotate.Nondegenerate := rotateNondegenerate T hN
  have hS' := rotateSpacelike T hS
  have hC : T.rotate.excenterDenomC ≠ 0 := by
    simpa only [rotate_excenterDenomC] using hA
  have hGap' : T.rotate.ninePointRadiusMagnitude - T.rotate.lambdaC *
      T.rotate.exradiusCMagnitude ≠ 0 := by
    simpa using hGap
  have hTan := isTangentAt_excircleC_spacelike T.rotate hR hS' hC hGap'
  simp only [excircleCFeuerbachContactPointSpacelike] at hTan
  rw [rotate_ninePointCircle T hN hR] at hTan
  simpa [excircleAFeuerbachContactPointSpacelike, excircleA] using hTan

theorem isTangentAt_excircleA_timelike (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsTimelike) (hA : T.excenterDenomA ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaA * T.exradiusAMagnitude ≠ 0) :
    LorentzCircle.IsTangentAt (T.ninePointCircle hN) (T.excircleA (Or.inr hT) hA)
      (T.excircleAFeuerbachContactPointTimelike hN hT hA) := by
  have hR : T.rotate.Nondegenerate := rotateNondegenerate T hN
  have hT' := rotateTimelike T hT
  have hC : T.rotate.excenterDenomC ≠ 0 := by
    simpa only [rotate_excenterDenomC] using hA
  have hGap' : T.rotate.ninePointRadiusMagnitude - T.rotate.lambdaC *
      T.rotate.exradiusCMagnitude ≠ 0 := by
    simpa using hGap
  have hTan := isTangentAt_excircleC_timelike T.rotate hR hT' hC hGap'
  simp only [excircleCFeuerbachContactPointTimelike] at hTan
  rw [rotate_ninePointCircle T hN hR] at hTan
  simpa [excircleAFeuerbachContactPointTimelike, excircleA] using hTan

theorem isTangentAt_excircleB_spacelike (T : Triangle) (hN : T.Nondegenerate)
    (hS : T.IsSpacelike) (hB : T.excenterDenomB ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaB * T.exradiusBMagnitude ≠ 0) :
    LorentzCircle.IsTangentAt (T.ninePointCircle hN) (T.excircleB (Or.inl hS) hB)
      (T.excircleBFeuerbachContactPointSpacelike hN hS hB) := by
  have hR : T.rotate.Nondegenerate := rotateNondegenerate T hN
  have hRR : T.rotateTwo.Nondegenerate := rotateTwoNondegenerate T hN
  have hS' := rotateTwoSpacelike T hS
  have hC : T.rotateTwo.excenterDenomC ≠ 0 := by
    simpa only [rotateTwo_excenterDenomC] using hB
  have hGap' : T.rotateTwo.ninePointRadiusMagnitude - T.rotateTwo.lambdaC *
      T.rotateTwo.exradiusCMagnitude ≠ 0 := by
    simpa using hGap
  have hTan := isTangentAt_excircleC_spacelike T.rotateTwo hRR hS' hC hGap'
  simp only [excircleCFeuerbachContactPointSpacelike] at hTan
  rw [rotateTwo_ninePointCircle T hN hR hRR] at hTan
  simpa [excircleBFeuerbachContactPointSpacelike, excircleB] using hTan

theorem isTangentAt_excircleB_timelike (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsTimelike) (hB : T.excenterDenomB ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaB * T.exradiusBMagnitude ≠ 0) :
    LorentzCircle.IsTangentAt (T.ninePointCircle hN) (T.excircleB (Or.inr hT) hB)
      (T.excircleBFeuerbachContactPointTimelike hN hT hB) := by
  have hR : T.rotate.Nondegenerate := rotateNondegenerate T hN
  have hRR : T.rotateTwo.Nondegenerate := rotateTwoNondegenerate T hN
  have hT' := rotateTwoTimelike T hT
  have hC : T.rotateTwo.excenterDenomC ≠ 0 := by
    simpa only [rotateTwo_excenterDenomC] using hB
  have hGap' : T.rotateTwo.ninePointRadiusMagnitude - T.rotateTwo.lambdaC *
      T.rotateTwo.exradiusCMagnitude ≠ 0 := by
    simpa using hGap
  have hTan := isTangentAt_excircleC_timelike T.rotateTwo hRR hT' hC hGap'
  simp only [excircleCFeuerbachContactPointTimelike] at hTan
  rw [rotateTwo_ninePointCircle T hN hR hRR] at hTan
  simpa [excircleBFeuerbachContactPointTimelike, excircleB] using hTan

theorem isProperTangentAt_excircleA_spacelike
    (T : Triangle) (hN : T.Nondegenerate) (hS : T.IsSpacelike)
    (hA : T.excenterDenomA ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaA * T.exradiusAMagnitude ≠ 0) :
    LorentzCircle.IsProperTangentAt
      (T.ninePointCircle hN) (T.excircleA (Or.inl hS) hA)
      (T.excircleAFeuerbachContactPointSpacelike hN hS hA) := by
  have hR : T.rotate.Nondegenerate := rotateNondegenerate T hN
  have hS' := rotateSpacelike T hS
  have hC : T.rotate.excenterDenomC ≠ 0 := by
    simpa only [rotate_excenterDenomC] using hA
  have hGap' : T.rotate.ninePointRadiusMagnitude - T.rotate.lambdaC *
      T.rotate.exradiusCMagnitude ≠ 0 := by
    simpa using hGap
  have hTan := isProperTangentAt_excircleC_spacelike T.rotate hR hS' hC hGap'
  simp only [excircleCFeuerbachContactPointSpacelike] at hTan
  rw [rotate_ninePointCircle T hN hR] at hTan
  simpa [excircleAFeuerbachContactPointSpacelike, excircleA] using hTan

theorem isProperTangentAt_excircleA_timelike
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsTimelike)
    (hA : T.excenterDenomA ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaA * T.exradiusAMagnitude ≠ 0) :
    LorentzCircle.IsProperTangentAt
      (T.ninePointCircle hN) (T.excircleA (Or.inr hT) hA)
      (T.excircleAFeuerbachContactPointTimelike hN hT hA) := by
  have hR : T.rotate.Nondegenerate := rotateNondegenerate T hN
  have hT' := rotateTimelike T hT
  have hC : T.rotate.excenterDenomC ≠ 0 := by
    simpa only [rotate_excenterDenomC] using hA
  have hGap' : T.rotate.ninePointRadiusMagnitude - T.rotate.lambdaC *
      T.rotate.exradiusCMagnitude ≠ 0 := by
    simpa using hGap
  have hTan := isProperTangentAt_excircleC_timelike T.rotate hR hT' hC hGap'
  simp only [excircleCFeuerbachContactPointTimelike] at hTan
  rw [rotate_ninePointCircle T hN hR] at hTan
  simpa [excircleAFeuerbachContactPointTimelike, excircleA] using hTan

theorem isProperTangentAt_excircleB_spacelike
    (T : Triangle) (hN : T.Nondegenerate) (hS : T.IsSpacelike)
    (hB : T.excenterDenomB ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaB * T.exradiusBMagnitude ≠ 0) :
    LorentzCircle.IsProperTangentAt
      (T.ninePointCircle hN) (T.excircleB (Or.inl hS) hB)
      (T.excircleBFeuerbachContactPointSpacelike hN hS hB) := by
  have hR : T.rotate.Nondegenerate := rotateNondegenerate T hN
  have hRR : T.rotateTwo.Nondegenerate := rotateTwoNondegenerate T hN
  have hS' := rotateTwoSpacelike T hS
  have hC : T.rotateTwo.excenterDenomC ≠ 0 := by
    simpa only [rotateTwo_excenterDenomC] using hB
  have hGap' : T.rotateTwo.ninePointRadiusMagnitude - T.rotateTwo.lambdaC *
      T.rotateTwo.exradiusCMagnitude ≠ 0 := by
    simpa using hGap
  have hTan := isProperTangentAt_excircleC_spacelike T.rotateTwo hRR hS' hC hGap'
  simp only [excircleCFeuerbachContactPointSpacelike] at hTan
  rw [rotateTwo_ninePointCircle T hN hR hRR] at hTan
  simpa [excircleBFeuerbachContactPointSpacelike, excircleB] using hTan

theorem isProperTangentAt_excircleB_timelike
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsTimelike)
    (hB : T.excenterDenomB ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaB * T.exradiusBMagnitude ≠ 0) :
    LorentzCircle.IsProperTangentAt
      (T.ninePointCircle hN) (T.excircleB (Or.inr hT) hB)
      (T.excircleBFeuerbachContactPointTimelike hN hT hB) := by
  have hR : T.rotate.Nondegenerate := rotateNondegenerate T hN
  have hRR : T.rotateTwo.Nondegenerate := rotateTwoNondegenerate T hN
  have hT' := rotateTwoTimelike T hT
  have hC : T.rotateTwo.excenterDenomC ≠ 0 := by
    simpa only [rotateTwo_excenterDenomC] using hB
  have hGap' : T.rotateTwo.ninePointRadiusMagnitude - T.rotateTwo.lambdaC *
      T.rotateTwo.exradiusCMagnitude ≠ 0 := by
    simpa using hGap
  have hTan := isProperTangentAt_excircleC_timelike T.rotateTwo hRR hT' hC hGap'
  simp only [excircleCFeuerbachContactPointTimelike] at hTan
  rw [rotateTwo_ninePointCircle T hN hR hRR] at hTan
  simpa [excircleBFeuerbachContactPointTimelike, excircleB] using hTan

end
end Triangle
end MinkowskiMerge
