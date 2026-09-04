import MinkowskiMerge.Triangle.FeuerbachContactEquation
import MinkowskiMerge.Triangle.RelabelCircles


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

def rotateTwoNondegenerate (T : Triangle) (hT : T.Nondegenerate) :
    T.rotateTwo.Nondegenerate :=
  rotateNondegenerate T.rotate (rotateNondegenerate T hT)

theorem rotateTwo_ninePointCircle (T : Triangle) (hT : T.Nondegenerate)
    (hR : T.rotate.Nondegenerate) (hRR : T.rotateTwo.Nondegenerate) :
    T.rotateTwo.ninePointCircle hRR = T.ninePointCircle hT := by
  calc
    T.rotateTwo.ninePointCircle hRR = T.rotate.ninePointCircle hR := by
      exact rotate_ninePointCircle T.rotate hR hRR
    _ = T.ninePointCircle hT := rotate_ninePointCircle T hT hR

@[simp] theorem rotateTwo_lambdaC (T : Triangle) :
    T.rotateTwo.lambdaC = T.lambdaB := by
  unfold rotateTwo
  rw [rotate_lambdaC, rotate_lambdaA]

def HasFeuerbachExcircleAEquation (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (hA : T.excenterDenomA ≠ 0) : Prop :=
  LorentzCircle.HasSignedRadiusDifferenceSqEquation
    (T.ninePointCircle hN) (T.excircleA hT hA) T.lambdaA

def HasFeuerbachExcircleBEquation (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (hB : T.excenterDenomB ≠ 0) : Prop :=
  LorentzCircle.HasSignedRadiusDifferenceSqEquation
    (T.ninePointCircle hN) (T.excircleB hT hB) T.lambdaB

theorem hasFeuerbachExcircleAEquation (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (hA : T.excenterDenomA ≠ 0) :
    T.HasFeuerbachExcircleAEquation hN hT hA := by
  have hR : T.rotate.Nondegenerate := rotateNondegenerate T hN
  have hC : T.rotate.excenterDenomC ≠ 0 := by
    simpa only [rotate_excenterDenomC] using hA
  have hEq := hasFeuerbachExcircleCEquation T.rotate hR
    (rotateIsNonMixed T hT) hC
  change LorentzCircle.HasSignedRadiusDifferenceSqEquation
    (T.rotate.ninePointCircle hR)
    (T.rotate.excircleC (rotateIsNonMixed T hT) hC) T.rotate.lambdaC at hEq
  change LorentzCircle.HasSignedRadiusDifferenceSqEquation
    (T.ninePointCircle hN) (T.excircleA hT hA) T.lambdaA
  rw [rotate_ninePointCircle T hN hR, rotate_lambdaC T] at hEq
  exact hEq

theorem hasFeuerbachExcircleBEquation (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (hB : T.excenterDenomB ≠ 0) :
    T.HasFeuerbachExcircleBEquation hN hT hB := by
  have hR : T.rotate.Nondegenerate := rotateNondegenerate T hN
  have hRR : T.rotateTwo.Nondegenerate := rotateTwoNondegenerate T hN
  have hC : T.rotateTwo.excenterDenomC ≠ 0 := by
    simpa only [rotateTwo_excenterDenomC] using hB
  have hEq := hasFeuerbachExcircleCEquation T.rotateTwo hRR
    (rotateTwoIsNonMixed T hT) hC
  change LorentzCircle.HasSignedRadiusDifferenceSqEquation
    (T.rotateTwo.ninePointCircle hRR)
    (T.rotateTwo.excircleC (rotateTwoIsNonMixed T hT) hC) T.rotateTwo.lambdaC at hEq
  change LorentzCircle.HasSignedRadiusDifferenceSqEquation
    (T.ninePointCircle hN) (T.excircleB hT hB) T.lambdaB
  rw [rotateTwo_ninePointCircle T hN hR hRR, rotateTwo_lambdaC T] at hEq
  exact hEq

theorem hasFeuerbachExcircleAEquation_iff (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) (hA : T.excenterDenomA ≠ 0) :
    T.HasFeuerbachExcircleAEquation hN hT hA ↔
      (T.ninePointCircle hN).centerDistance (T.excircleA hT hA) ^ 2 =
        (T.circumradius hN / 2 - (T.lambdaA : ℂ) *
          (T.excircleA hT hA).complexRadius) ^ 2 := by
  unfold HasFeuerbachExcircleAEquation
    LorentzCircle.HasSignedRadiusDifferenceSqEquation
  change (T.ninePointCircle hN).centerDistance (T.excircleA hT hA) ^ 2 =
      (T.ninePointRadius hN - (T.lambdaA : ℂ) *
        (T.excircleA hT hA).complexRadius) ^ 2 ↔ _
  rw [ninePointRadius_eq_half_circumradius]

theorem hasFeuerbachExcircleBEquation_iff (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) (hB : T.excenterDenomB ≠ 0) :
    T.HasFeuerbachExcircleBEquation hN hT hB ↔
      (T.ninePointCircle hN).centerDistance (T.excircleB hT hB) ^ 2 =
        (T.circumradius hN / 2 - (T.lambdaB : ℂ) *
          (T.excircleB hT hB).complexRadius) ^ 2 := by
  unfold HasFeuerbachExcircleBEquation
    LorentzCircle.HasSignedRadiusDifferenceSqEquation
  change (T.ninePointCircle hN).centerDistance (T.excircleB hT hB) ^ 2 =
      (T.ninePointRadius hN - (T.lambdaB : ℂ) *
        (T.excircleB hT hB).complexRadius) ^ 2 ↔ _
  rw [ninePointRadius_eq_half_circumradius]

end

end Triangle
end MinkowskiMerge
