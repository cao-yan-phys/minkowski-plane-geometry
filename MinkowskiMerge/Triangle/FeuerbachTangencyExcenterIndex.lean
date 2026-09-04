import MinkowskiMerge.Triangle.FeuerbachTangencyUnified


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

inductive ExcenterIndex
  | A
  | B
  | C
  deriving DecidableEq, Repr

def excenterDenomAt (T : Triangle) : ExcenterIndex -> ℝ
  | .A => T.excenterDenomA
  | .B => T.excenterDenomB
  | .C => T.excenterDenomC

def lambdaAt (T : Triangle) : ExcenterIndex -> ℝ
  | .A => T.lambdaA
  | .B => T.lambdaB
  | .C => T.lambdaC

noncomputable def exradiusMagnitudeAt (T : Triangle) : ExcenterIndex -> ℝ
  | .A => T.exradiusAMagnitude
  | .B => T.exradiusBMagnitude
  | .C => T.exradiusCMagnitude

noncomputable def excenterAt (T : Triangle) (i : ExcenterIndex)
    (hD : T.excenterDenomAt i ≠ 0) : Point :=
  match i with
  | .A => T.excenterA hD
  | .B => T.excenterB hD
  | .C => T.excenterC hD

noncomputable def excircleAt (T : Triangle) (hT : T.IsNonMixed)
    (i : ExcenterIndex) (hD : T.excenterDenomAt i ≠ 0) : LorentzCircle :=
  match i with
  | .A => T.excircleA hT hD
  | .B => T.excircleB hT hD
  | .C => T.excircleC hT hD

@[simp] theorem excenterDenomAt_A (T : Triangle) :
    T.excenterDenomAt .A = T.excenterDenomA := rfl

@[simp] theorem excenterDenomAt_B (T : Triangle) :
    T.excenterDenomAt .B = T.excenterDenomB := rfl

@[simp] theorem excenterDenomAt_C (T : Triangle) :
    T.excenterDenomAt .C = T.excenterDenomC := rfl

theorem Nondegenerate.excenterDenomAt_ne_zero {T : Triangle}
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) (i : ExcenterIndex) :
    T.excenterDenomAt i ≠ 0 := by
  cases i with
  | A => exact hN.excenterDenomA_ne_zero hT
  | B => exact hN.excenterDenomB_ne_zero hT
  | C => exact hN.excenterDenomC_ne_zero hT

@[simp] theorem lambdaAt_A (T : Triangle) : T.lambdaAt .A = T.lambdaA := rfl

@[simp] theorem lambdaAt_B (T : Triangle) : T.lambdaAt .B = T.lambdaB := rfl

@[simp] theorem lambdaAt_C (T : Triangle) : T.lambdaAt .C = T.lambdaC := rfl

@[simp] theorem exradiusMagnitudeAt_A (T : Triangle) :
    T.exradiusMagnitudeAt .A = T.exradiusAMagnitude := rfl

@[simp] theorem exradiusMagnitudeAt_B (T : Triangle) :
    T.exradiusMagnitudeAt .B = T.exradiusBMagnitude := rfl

@[simp] theorem exradiusMagnitudeAt_C (T : Triangle) :
    T.exradiusMagnitudeAt .C = T.exradiusCMagnitude := rfl

@[simp] theorem excenterAt_A (T : Triangle) (hA : T.excenterDenomA ≠ 0) :
    T.excenterAt .A hA = T.excenterA hA := rfl

@[simp] theorem excenterAt_B (T : Triangle) (hB : T.excenterDenomB ≠ 0) :
    T.excenterAt .B hB = T.excenterB hB := rfl

@[simp] theorem excenterAt_C (T : Triangle) (hC : T.excenterDenomC ≠ 0) :
    T.excenterAt .C hC = T.excenterC hC := rfl

@[simp] theorem excircleAt_A (T : Triangle) (hT : T.IsNonMixed)
    (hA : T.excenterDenomA ≠ 0) :
    T.excircleAt hT .A hA = T.excircleA hT hA := rfl

@[simp] theorem excircleAt_B (T : Triangle) (hT : T.IsNonMixed)
    (hB : T.excenterDenomB ≠ 0) :
    T.excircleAt hT .B hB = T.excircleB hT hB := rfl

@[simp] theorem excircleAt_C (T : Triangle) (hT : T.IsNonMixed)
    (hC : T.excenterDenomC ≠ 0) :
    T.excircleAt hT .C hC = T.excircleC hT hC := rfl

theorem excircleAt_center (T : Triangle) (hT : T.IsNonMixed)
    (i : ExcenterIndex) (hD : T.excenterDenomAt i ≠ 0) :
    (T.excircleAt hT i hD).center = T.excenterAt i hD := by
  cases i with
  | A => exact excircleA_center T hT hD
  | B => exact excircleB_center T hT hD
  | C => rfl

noncomputable def excircleAFeuerbachContactPoint (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed)
    (hA : T.excenterDenomA ≠ 0) : Point :=
  LorentzCircle.tangentPointOfRadiusDifference (T.ninePointCircle hN)
    (T.excircleA hT hA) T.ninePointRadiusMagnitude
    (T.lambdaA * T.exradiusAMagnitude)

noncomputable def excircleBFeuerbachContactPoint (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed)
    (hB : T.excenterDenomB ≠ 0) : Point :=
  LorentzCircle.tangentPointOfRadiusDifference (T.ninePointCircle hN)
    (T.excircleB hT hB) T.ninePointRadiusMagnitude
    (T.lambdaB * T.exradiusBMagnitude)

theorem isTangentAt_excircleA (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (hA : T.excenterDenomA ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaA * T.exradiusAMagnitude ≠ 0) :
    LorentzCircle.IsTangentAt (T.ninePointCircle hN) (T.excircleA hT hA)
      (T.excircleAFeuerbachContactPoint hN hT hA) := by
  rcases hT with hS | hT
  · simpa [excircleAFeuerbachContactPoint] using
      isTangentAt_excircleA_spacelike T hN hS hA hGap
  · simpa [excircleAFeuerbachContactPoint] using
      isTangentAt_excircleA_timelike T hN hT hA hGap

theorem isTangentAt_excircleB (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (hB : T.excenterDenomB ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaB * T.exradiusBMagnitude ≠ 0) :
    LorentzCircle.IsTangentAt (T.ninePointCircle hN) (T.excircleB hT hB)
      (T.excircleBFeuerbachContactPoint hN hT hB) := by
  rcases hT with hS | hT
  · simpa [excircleBFeuerbachContactPoint] using
      isTangentAt_excircleB_spacelike T hN hS hB hGap
  · simpa [excircleBFeuerbachContactPoint] using
      isTangentAt_excircleB_timelike T hN hT hB hGap

theorem isProperTangentAt_excircleA (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (hA : T.excenterDenomA ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaA * T.exradiusAMagnitude ≠ 0) :
    LorentzCircle.IsProperTangentAt
      (T.ninePointCircle hN) (T.excircleA hT hA)
      (T.excircleAFeuerbachContactPoint hN hT hA) := by
  rcases hT with hS | hT
  · simpa [excircleAFeuerbachContactPoint] using
      isProperTangentAt_excircleA_spacelike T hN hS hA hGap
  · simpa [excircleAFeuerbachContactPoint] using
      isProperTangentAt_excircleA_timelike T hN hT hA hGap

theorem isProperTangentAt_excircleB (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (hB : T.excenterDenomB ≠ 0)
    (hGap : T.ninePointRadiusMagnitude - T.lambdaB * T.exradiusBMagnitude ≠ 0) :
    LorentzCircle.IsProperTangentAt
      (T.ninePointCircle hN) (T.excircleB hT hB)
      (T.excircleBFeuerbachContactPoint hN hT hB) := by
  rcases hT with hS | hT
  · simpa [excircleBFeuerbachContactPoint] using
      isProperTangentAt_excircleB_spacelike T hN hS hB hGap
  · simpa [excircleBFeuerbachContactPoint] using
      isProperTangentAt_excircleB_timelike T hN hT hB hGap

def excircleFeuerbachGap (T : Triangle) (i : ExcenterIndex) : ℝ :=
  T.ninePointRadiusMagnitude - T.lambdaAt i * T.exradiusMagnitudeAt i

noncomputable def excircleFeuerbachContactPoint (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed)
    (i : ExcenterIndex) (hD : T.excenterDenomAt i ≠ 0) : Point :=
  LorentzCircle.tangentPointOfRadiusDifference (T.ninePointCircle hN)
    (T.excircleAt hT i hD) T.ninePointRadiusMagnitude
    (T.lambdaAt i * T.exradiusMagnitudeAt i)

theorem isTangentAt_excircle (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (i : ExcenterIndex)
    (hD : T.excenterDenomAt i ≠ 0)
    (hGap : T.excircleFeuerbachGap i ≠ 0) :
    LorentzCircle.IsTangentAt (T.ninePointCircle hN) (T.excircleAt hT i hD)
      (T.excircleFeuerbachContactPoint hN hT i hD) := by
  cases i with
  | A =>
      simpa [excircleFeuerbachContactPoint, excircleFeuerbachGap, excircleAt,
        lambdaAt, exradiusMagnitudeAt, excircleAFeuerbachContactPoint] using
        isTangentAt_excircleA T hN hT hD hGap
  | B =>
      simpa [excircleFeuerbachContactPoint, excircleFeuerbachGap, excircleAt,
        lambdaAt, exradiusMagnitudeAt, excircleBFeuerbachContactPoint] using
        isTangentAt_excircleB T hN hT hD hGap
  | C =>
      simpa [excircleFeuerbachContactPoint, excircleFeuerbachGap, excircleAt,
        lambdaAt, exradiusMagnitudeAt, excircleCFeuerbachContactPoint] using
        isTangentAt_excircleC T hN hT hD hGap

theorem isProperTangentAt_excircle (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (i : ExcenterIndex)
    (hD : T.excenterDenomAt i ≠ 0)
    (hGap : T.excircleFeuerbachGap i ≠ 0) :
    LorentzCircle.IsProperTangentAt
      (T.ninePointCircle hN) (T.excircleAt hT i hD)
      (T.excircleFeuerbachContactPoint hN hT i hD) := by
  cases i with
  | A =>
      simpa [excircleFeuerbachContactPoint, excircleFeuerbachGap, excircleAt,
        lambdaAt, exradiusMagnitudeAt, excircleAFeuerbachContactPoint] using
        isProperTangentAt_excircleA T hN hT hD hGap
  | B =>
      simpa [excircleFeuerbachContactPoint, excircleFeuerbachGap, excircleAt,
        lambdaAt, exradiusMagnitudeAt, excircleBFeuerbachContactPoint] using
        isProperTangentAt_excircleB T hN hT hD hGap
  | C =>
      simpa [excircleFeuerbachContactPoint, excircleFeuerbachGap, excircleAt,
        lambdaAt, exradiusMagnitudeAt, excircleCFeuerbachContactPoint] using
        isProperTangentAt_excircleC T hN hT hD hGap

end
end Triangle
end MinkowskiMerge
