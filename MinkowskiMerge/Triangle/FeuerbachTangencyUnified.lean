import MinkowskiMerge.Triangle.FeuerbachTangencyExcenterAB


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

noncomputable def incenterFeuerbachContactPoint (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) : Point :=
  LorentzCircle.tangentPointOfRadiusSum (T.ninePointCircle hN)
    (T.incircle hT) T.ninePointRadiusMagnitude T.inradiusMagnitude

theorem isTangentAt_incenter (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) :
    LorentzCircle.IsTangentAt (T.ninePointCircle hN) (T.incircle hT)
      (T.incenterFeuerbachContactPoint hN hT) := by
  rcases hT with hS | hT
  · simpa [incenterFeuerbachContactPoint] using
      isTangentAt_incenter_spacelike T hN hS
  · simpa [incenterFeuerbachContactPoint] using
      isTangentAt_incenter_timelike T hN hT

theorem isProperTangentAt_incenter (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) :
    LorentzCircle.IsProperTangentAt
      (T.ninePointCircle hN) (T.incircle hT)
      (T.incenterFeuerbachContactPoint hN hT) := by
  rcases hT with hS | hT
  · simpa [incenterFeuerbachContactPoint] using
      isProperTangentAt_incenter_spacelike T hN hS
  · simpa [incenterFeuerbachContactPoint] using
      isProperTangentAt_incenter_timelike T hN hT

noncomputable def excircleCFeuerbachContactPoint (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed)
    (hC : T.excenterDenomC ≠ 0) : Point :=
  LorentzCircle.tangentPointOfRadiusDifference (T.ninePointCircle hN)
    (T.excircleC hT hC) T.ninePointRadiusMagnitude
    (T.lambdaC * T.exradiusCMagnitude)

theorem isTangentAt_excircleC (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (hC : T.excenterDenomC ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaC * T.exradiusCMagnitude ≠ 0) :
    LorentzCircle.IsTangentAt (T.ninePointCircle hN) (T.excircleC hT hC)
      (T.excircleCFeuerbachContactPoint hN hT hC) := by
  rcases hT with hS | hT
  · simpa [excircleCFeuerbachContactPoint] using
      isTangentAt_excircleC_spacelike T hN hS hC hGap
  · simpa [excircleCFeuerbachContactPoint] using
      isTangentAt_excircleC_timelike T hN hT hC hGap

theorem isProperTangentAt_excircleC (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (hC : T.excenterDenomC ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaC * T.exradiusCMagnitude ≠ 0) :
    LorentzCircle.IsProperTangentAt
      (T.ninePointCircle hN) (T.excircleC hT hC)
      (T.excircleCFeuerbachContactPoint hN hT hC) := by
  rcases hT with hS | hT
  · simpa [excircleCFeuerbachContactPoint] using
      isProperTangentAt_excircleC_spacelike T hN hS hC hGap
  · simpa [excircleCFeuerbachContactPoint] using
      isProperTangentAt_excircleC_timelike T hN hT hC hGap

end
end Triangle
end MinkowskiMerge
