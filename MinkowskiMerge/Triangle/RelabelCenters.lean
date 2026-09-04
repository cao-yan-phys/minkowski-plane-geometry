import MinkowskiMerge.Triangle.Relabel


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

theorem rotate_orthocenter (T : Triangle) (hT : T.Nondegenerate)
    (hR : T.rotate.Nondegenerate) :
    T.rotate.orthocenter hR = T.orthocenter hT := by
  unfold orthocenter
  rw [rotate_circumcenter T hT]
  rw [orthocenterFromCircumcenter_apply, orthocenterFromCircumcenter_apply]
  change T.B + T.C + T.A - (2 : ℝ) • T.circumcenter hT =
    T.A + T.B + T.C - (2 : ℝ) • T.circumcenter hT
  module

theorem rotate_ninePointCenter (T : Triangle) (hT : T.Nondegenerate)
    (hR : T.rotate.Nondegenerate) :
    T.rotate.ninePointCenter hR = T.ninePointCenter hT := by
  unfold ninePointCenter
  rw [rotate_circumcenter T hT, rotate_orthocenter T hT hR]

theorem rotate_ninePointRadiusSq (T : Triangle) (hT : T.Nondegenerate)
    (hR : T.rotate.Nondegenerate) :
    T.rotate.ninePointRadiusSq hR = T.ninePointRadiusSq hT := by
  rw [ninePointRadiusSq_eq_quarter_circumradiusSq,
    ninePointRadiusSq_eq_quarter_circumradiusSq,
    rotate_circumradiusSqAt T hT]

end

end Triangle
end MinkowskiMerge
