import MinkowskiMerge.Triangle.FeuerbachTangencyExcenterIndex


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

def IsExcircleFeuerbachAdmissible (T : Triangle) (i : ExcenterIndex) : Prop :=
  T.excircleFeuerbachGap i ≠ 0

def HasGeneralizedFeuerbachTangency (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) : Prop :=
  LorentzCircle.IsTangentAt (T.ninePointCircle hN) (T.incircle hT)
    (T.incenterFeuerbachContactPoint hN hT) ∧
  ∀ (i : ExcenterIndex) (_hi : T.IsExcircleFeuerbachAdmissible i),
    LorentzCircle.IsTangentAt (T.ninePointCircle hN)
      (T.excircleAt hT i (hN.excenterDenomAt_ne_zero hT i))
      (T.excircleFeuerbachContactPoint hN hT i
        (hN.excenterDenomAt_ne_zero hT i))

def HasGeneralizedFeuerbachProperTangency
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsNonMixed) : Prop :=
  LorentzCircle.IsProperTangentAt (T.ninePointCircle hN) (T.incircle hT)
    (T.incenterFeuerbachContactPoint hN hT) ∧
  ∀ (i : ExcenterIndex) (_hi : T.IsExcircleFeuerbachAdmissible i),
    LorentzCircle.IsProperTangentAt (T.ninePointCircle hN)
      (T.excircleAt hT i (hN.excenterDenomAt_ne_zero hT i))
      (T.excircleFeuerbachContactPoint hN hT i
        (hN.excenterDenomAt_ne_zero hT i))

theorem generalizedFeuerbachProperFinite
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsNonMixed) :
    T.HasGeneralizedFeuerbachProperTangency hN hT := by
  refine ⟨isProperTangentAt_incenter T hN hT, ?_⟩
  intro i hi
  exact isProperTangentAt_excircle T hN hT i
    (hN.excenterDenomAt_ne_zero hT i) hi

theorem generalizedFeuerbach (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) : T.HasGeneralizedFeuerbachTangency hN hT := by
  have hProper := generalizedFeuerbachProperFinite T hN hT
  refine ⟨hProper.1.firstOrderContact, ?_⟩
  intro i hi
  exact (hProper.2 i hi).firstOrderContact

theorem generalizedFeuerbach_incenter (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) :
    LorentzCircle.IsTangentAt (T.ninePointCircle hN) (T.incircle hT)
      (T.incenterFeuerbachContactPoint hN hT) :=
  (generalizedFeuerbach T hN hT).1

theorem generalizedFeuerbach_excircle (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (i : ExcenterIndex)
    (hi : T.IsExcircleFeuerbachAdmissible i) :
    LorentzCircle.IsTangentAt (T.ninePointCircle hN)
      (T.excircleAt hT i (hN.excenterDenomAt_ne_zero hT i))
      (T.excircleFeuerbachContactPoint hN hT i
        (hN.excenterDenomAt_ne_zero hT i)) :=
  (generalizedFeuerbach T hN hT).2 i hi

theorem generalizedFeuerbachProperFinite_incenter
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsNonMixed) :
    LorentzCircle.IsProperTangentAt
      (T.ninePointCircle hN) (T.incircle hT)
      (T.incenterFeuerbachContactPoint hN hT) :=
  (generalizedFeuerbachProperFinite T hN hT).1

theorem generalizedFeuerbachProperFinite_excircle
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsNonMixed)
    (i : ExcenterIndex) (hi : T.IsExcircleFeuerbachAdmissible i) :
    LorentzCircle.IsProperTangentAt (T.ninePointCircle hN)
      (T.excircleAt hT i (hN.excenterDenomAt_ne_zero hT i))
      (T.excircleFeuerbachContactPoint hN hT i
        (hN.excenterDenomAt_ne_zero hT i)) :=
  (generalizedFeuerbachProperFinite T hN hT).2 i hi

end
end Triangle
end MinkowskiMerge
