import MinkowskiMerge.Triangle.RelabelCenters
import MinkowskiMerge.Triangle.Circles


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

private theorem lorentzCircle_eq_of_center_eq_radiusSq_eq
    {C D : LorentzCircle} (hc : C.center = D.center)
    (hr : C.radiusSq = D.radiusSq) : C = D := by
  cases C with
  | mk c r =>
    cases D with
    | mk d s =>
      simp_all

theorem rotate_ninePointCircle (T : Triangle) (hT : T.Nondegenerate)
    (hR : T.rotate.Nondegenerate) :
    T.rotate.ninePointCircle hR = T.ninePointCircle hT := by
  apply lorentzCircle_eq_of_center_eq_radiusSq_eq
  · exact rotate_ninePointCenter T hT hR
  · exact rotate_ninePointRadiusSq T hT hR

def rotateTwoIsNonMixed (T : Triangle) (hT : T.IsNonMixed) :
    T.rotateTwo.IsNonMixed :=
  (rotate_isNonMixed_iff T.rotate).mpr (rotateIsNonMixed T hT)

noncomputable def excircleA (T : Triangle) (hT : T.IsNonMixed)
    (hA : T.excenterDenomA ≠ 0) : LorentzCircle :=
  T.rotate.excircleC (rotateIsNonMixed T hT)
    (by simpa only [rotate_excenterDenomC] using hA)

noncomputable def excircleB (T : Triangle) (hT : T.IsNonMixed)
    (hB : T.excenterDenomB ≠ 0) : LorentzCircle :=
  T.rotateTwo.excircleC (rotateTwoIsNonMixed T hT)
    (by simpa only [rotateTwo_excenterDenomC] using hB)

@[simp] theorem excircleA_center (T : Triangle) (hT : T.IsNonMixed)
    (hA : T.excenterDenomA ≠ 0) :
    (T.excircleA hT hA).center = T.excenterA hA := by
  change T.rotate.excenterC _ = T.excenterA hA
  exact rotate_excenterC_eq_excenterA T hA

@[simp] theorem excircleB_center (T : Triangle) (hT : T.IsNonMixed)
    (hB : T.excenterDenomB ≠ 0) :
    (T.excircleB hT hB).center = T.excenterB hB := by
  change T.rotateTwo.excenterC _ = T.excenterB hB
  exact rotateTwo_excenterC_eq_excenterB T hB

@[simp] theorem excircleA_radiusSq (T : Triangle) (hT : T.IsNonMixed)
    (hA : T.excenterDenomA ≠ 0) :
    (T.excircleA hT hA).radiusSq =
      (T.rotate.excircleC (rotateIsNonMixed T hT)
        (by simpa only [rotate_excenterDenomC] using hA)).radiusSq := rfl

@[simp] theorem excircleB_radiusSq (T : Triangle) (hT : T.IsNonMixed)
    (hB : T.excenterDenomB ≠ 0) :
    (T.excircleB hT hB).radiusSq =
      (T.rotateTwo.excircleC (rotateTwoIsNonMixed T hT)
        (by simpa only [rotateTwo_excenterDenomC] using hB)).radiusSq := rfl

end

end Triangle
end MinkowskiMerge
