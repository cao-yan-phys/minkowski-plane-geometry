import MinkowskiMerge.Triangle.FeuerbachNullInfinity


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

def HasFeuerbachExcircleEquationAt
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsNonMixed)
    (i : ExcenterIndex) : Prop :=
  LorentzCircle.HasSignedRadiusDifferenceSqEquation
    (T.ninePointCircle hN)
    (T.excircleAt hT i (hN.excenterDenomAt_ne_zero hT i))
    (T.lambdaAt i)

def HasFeuerbachIdentities
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsNonMixed) : Prop :=
  T.HasFeuerbachIncenterEquation hN hT ∧
  ∀ i : ExcenterIndex, T.HasFeuerbachExcircleEquationAt hN hT i

theorem hasFeuerbachExcircleEquationAt
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsNonMixed)
    (i : ExcenterIndex) :
    T.HasFeuerbachExcircleEquationAt hN hT i := by
  cases i with
  | A =>
      simpa [HasFeuerbachExcircleEquationAt, excircleAt, lambdaAt,
        HasFeuerbachExcircleAEquation] using
        hasFeuerbachExcircleAEquation T hN hT
          (hN.excenterDenomAt_ne_zero hT .A)
  | B =>
      simpa [HasFeuerbachExcircleEquationAt, excircleAt, lambdaAt,
        HasFeuerbachExcircleBEquation] using
        hasFeuerbachExcircleBEquation T hN hT
          (hN.excenterDenomAt_ne_zero hT .B)
  | C =>
      simpa [HasFeuerbachExcircleEquationAt, excircleAt, lambdaAt] using
        hasFeuerbachExcircleCEquation T hN hT
          (hN.excenterDenomAt_ne_zero hT .C)

theorem hasFeuerbachIdentities
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsNonMixed) :
    T.HasFeuerbachIdentities hN hT := by
  exact ⟨hasFeuerbachIncenterEquation T hN hT,
    hasFeuerbachExcircleEquationAt T hN hT⟩

def HasUnifiedFeuerbachTheorem
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsNonMixed) : Prop :=
  T.HasFeuerbachIdentities hN hT ∧
  LorentzCircle.IsProperTangentAt
    (T.ninePointCircle hN) (T.incircle hT)
    (T.incenterFeuerbachContactPoint hN hT) ∧
  ∀ i : ExcenterIndex, T.HasExcircleFeuerbachContact hN hT i

theorem unifiedFeuerbachTheorem
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsNonMixed) :
    T.HasUnifiedFeuerbachTheorem hN hT := by
  exact ⟨hasFeuerbachIdentities T hN hT,
    generalizedFeuerbachProperFinite_incenter T hN hT,
    excircleFeuerbachContact T hN hT⟩

theorem unifiedFeuerbachTheorem_identities
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsNonMixed) :
    T.HasFeuerbachIdentities hN hT :=
  (unifiedFeuerbachTheorem T hN hT).1

theorem unifiedFeuerbachTheorem_incenter
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsNonMixed) :
    LorentzCircle.IsProperTangentAt
      (T.ninePointCircle hN) (T.incircle hT)
      (T.incenterFeuerbachContactPoint hN hT) :=
  (unifiedFeuerbachTheorem T hN hT).2.1

theorem unifiedFeuerbachTheorem_excircle
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsNonMixed)
    (i : ExcenterIndex) : T.HasExcircleFeuerbachContact hN hT i :=
  (unifiedFeuerbachTheorem T hN hT).2.2 i

end

end Triangle
end MinkowskiMerge
