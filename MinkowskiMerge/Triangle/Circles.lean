import MinkowskiMerge.Circle
import MinkowskiMerge.Triangle.NinePoint
import MinkowskiMerge.Triangle.Heron


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

noncomputable def ninePointCircle (T : Triangle) (hT : T.Nondegenerate) : LorentzCircle :=
  ⟨T.ninePointCenter hT, T.ninePointRadiusSq hT⟩

@[simp] theorem ninePointCircle_center (T : Triangle) (hT : T.Nondegenerate) :
    (T.ninePointCircle hT).center = T.ninePointCenter hT := rfl

@[simp] theorem ninePointCircle_radiusSq (T : Triangle) (hT : T.Nondegenerate) :
    (T.ninePointCircle hT).radiusSq = T.ninePointRadiusSq hT := rfl

theorem mem_ninePointCircle_iff (T : Triangle) (hT : T.Nondegenerate) (P : Point) :
    P ∈ T.ninePointCircle hT ↔ T.IsOnNinePointCircle hT P := Iff.rfl

theorem midpointA_mem_ninePointCircle (T : Triangle) (hT : T.Nondegenerate) :
    T.midpointA ∈ T.ninePointCircle hT := by
  exact T.midpointA_on_ninePointCircle hT

theorem midpointB_mem_ninePointCircle (T : Triangle) (hT : T.Nondegenerate) :
    T.midpointB ∈ T.ninePointCircle hT := by
  exact T.midpointB_on_ninePointCircle hT

theorem midpointC_mem_ninePointCircle (T : Triangle) (hT : T.Nondegenerate) :
    T.midpointC ∈ T.ninePointCircle hT := by
  exact T.midpointC_on_ninePointCircle hT

noncomputable def circumcircle (T : Triangle) (hT : T.Nondegenerate) : LorentzCircle :=
  ⟨T.circumcenter hT, T.circumradiusSqAt (T.circumcenter hT)⟩

@[simp] theorem circumcircle_center (T : Triangle) (hT : T.Nondegenerate) :
    (T.circumcircle hT).center = T.circumcenter hT := rfl

@[simp] theorem circumcircle_radiusSq (T : Triangle) (hT : T.Nondegenerate) :
    (T.circumcircle hT).radiusSq =
      T.circumradiusSqAt (T.circumcenter hT) := rfl

theorem vertexA_mem_circumcircle (T : Triangle) (hT : T.Nondegenerate) :
    T.A ∈ T.circumcircle hT := by
  rfl

theorem vertexB_mem_circumcircle (T : Triangle) (hT : T.Nondegenerate) :
    T.B ∈ T.circumcircle hT := by
  change intervalSq (T.circumcenter hT) T.B =
    T.circumradiusSqAt (T.circumcenter hT)
  exact (circumcenter_isCircumcenter T hT).intervalSq_B_eq_radius

theorem vertexC_mem_circumcircle (T : Triangle) (hT : T.Nondegenerate) :
    T.C ∈ T.circumcircle hT := by
  change intervalSq (T.circumcenter hT) T.C =
    T.circumradiusSqAt (T.circumcenter hT)
  exact (circumcenter_isCircumcenter T hT).intervalSq_C_eq_radius

noncomputable def incircle (T : Triangle) (hT : T.IsNonMixed) : LorentzCircle :=
  ⟨T.incenter hT, T.inradiusSq hT⟩

@[simp] theorem incircle_center (T : Triangle) (hT : T.IsNonMixed) :
    (T.incircle hT).center = T.incenter hT := rfl

@[simp] theorem incircle_radiusSq (T : Triangle) (hT : T.IsNonMixed) :
    (T.incircle hT).radiusSq = T.inradiusSq hT := rfl

noncomputable def excircleC (T : Triangle) (hT : T.IsNonMixed)
    (hC : T.excenterDenomC ≠ 0) : LorentzCircle :=
  ⟨T.excenterC hC, T.exradiusSqC hT hC⟩

@[simp] theorem excircleC_center (T : Triangle) (hT : T.IsNonMixed)
    (hC : T.excenterDenomC ≠ 0) :
    (T.excircleC hT hC).center = T.excenterC hC := rfl

@[simp] theorem excircleC_radiusSq (T : Triangle) (hT : T.IsNonMixed)
    (hC : T.excenterDenomC ≠ 0) :
    (T.excircleC hT hC).radiusSq = T.exradiusSqC hT hC := rfl

end

end Triangle
end MinkowskiMerge
