import MinkowskiMerge.CircleContact
import MinkowskiMerge.Triangle.Circles
import MinkowskiMerge.Triangle.CircleAlgebra
import MinkowskiMerge.Triangle.FeuerbachAlgebra


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

noncomputable def circumradius (T : Triangle) (hT : T.Nondegenerate) : ℂ :=
  (T.circumcircle hT).complexRadius

noncomputable def ninePointRadius (T : Triangle) (hT : T.Nondegenerate) : ℂ :=
  (T.ninePointCircle hT).complexRadius

@[simp] theorem circumradius_sq (T : Triangle) (hT : T.Nondegenerate) :
    T.circumradius hT ^ 2 =
      (T.circumradiusSqAt (T.circumcenter hT) : ℂ) := by
  unfold circumradius circumcircle LorentzCircle.complexRadius
  exact positiveComplexSqrt_sq _

@[simp] theorem ninePointRadius_sq (T : Triangle) (hT : T.Nondegenerate) :
    T.ninePointRadius hT ^ 2 = (T.ninePointRadiusSq hT : ℂ) := by
  unfold ninePointRadius ninePointCircle LorentzCircle.complexRadius
  exact positiveComplexSqrt_sq _

theorem ninePointRadius_eq_half_circumradius
    (T : Triangle) (hT : T.Nondegenerate) :
    T.ninePointRadius hT = T.circumradius hT / 2 := by
  unfold ninePointRadius circumradius ninePointCircle circumcircle
  change positiveComplexSqrt (T.ninePointRadiusSq hT) =
    positiveComplexSqrt (T.circumradiusSqAt (T.circumcenter hT)) / 2
  rw [ninePointRadiusSq_eq_quarter_circumradiusSq,
    positiveComplexSqrt_div_four]

theorem incircle_complexRadius_eq_inradius (T : Triangle) (hT : T.IsNonMixed) :
    (T.incircle hT).complexRadius = T.inradius hT := by
  change positiveComplexSqrt
      (q (heightVec (T.incenter hT) T.B T.C hT.sidesNonNull.1)) =
    complexLength (heightVec (T.incenter hT) T.B T.C hT.sidesNonNull.1)
  exact (complexLength_eq_positiveComplexSqrt _).symm

theorem excircleC_complexRadius_eq_exradiusC (T : Triangle)
    (hT : T.IsNonMixed) (hC : T.excenterDenomC ≠ 0) :
    (T.excircleC hT hC).complexRadius = T.exradiusC hT hC := by
  change positiveComplexSqrt
      (q (heightVec (T.excenterC hC) T.A T.B hT.sidesNonNull.2.2)) =
    complexLength (heightVec (T.excenterC hC) T.A T.B hT.sidesNonNull.2.2)
  exact (complexLength_eq_positiveComplexSqrt _).symm

def HasFeuerbachIncenterEquation (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) : Prop :=
  LorentzCircle.HasRadiusSumEquation (T.ninePointCircle hN) (T.incircle hT)

def HasFeuerbachExcircleCEquation (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (hC : T.excenterDenomC ≠ 0) : Prop :=
  LorentzCircle.HasSignedRadiusDifferenceSqEquation
    (T.ninePointCircle hN) (T.excircleC hT hC) T.lambdaC

theorem hasFeuerbachIncenterEquation_iff (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) :
    T.HasFeuerbachIncenterEquation hN hT ↔
      (T.ninePointCircle hN).centerDistance (T.incircle hT) =
        T.circumradius hN / 2 + T.inradius hT := by
  unfold HasFeuerbachIncenterEquation LorentzCircle.HasRadiusSumEquation
  change (T.ninePointCircle hN).centerDistance (T.incircle hT) =
      T.ninePointRadius hN + (T.incircle hT).complexRadius ↔ _
  rw [ninePointRadius_eq_half_circumradius,
    incircle_complexRadius_eq_inradius]

theorem hasFeuerbachExcircleCEquation_iff (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) (hC : T.excenterDenomC ≠ 0) :
    T.HasFeuerbachExcircleCEquation hN hT hC ↔
      (T.ninePointCircle hN).centerDistance (T.excircleC hT hC) ^ 2 =
        (T.circumradius hN / 2 -
          (T.lambdaC : ℂ) * T.exradiusC hT hC) ^ 2 := by
  unfold HasFeuerbachExcircleCEquation
    LorentzCircle.HasSignedRadiusDifferenceSqEquation
  change (T.ninePointCircle hN).centerDistance (T.excircleC hT hC) ^ 2 =
      (T.ninePointRadius hN -
        (T.lambdaC : ℂ) * (T.excircleC hT hC).complexRadius) ^ 2 ↔ _
  rw [ninePointRadius_eq_half_circumradius,
    excircleC_complexRadius_eq_exradiusC]

end

end Triangle
end MinkowskiMerge
