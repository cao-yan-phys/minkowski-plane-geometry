import MinkowskiMerge.Triangle.Circles


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

private theorem q_circumcenterVecB (T : Triangle) (hT : T.Nondegenerate) :
    q (intervalVec (T.circumcenter hT) T.B) =
      T.circumradiusSqAt (T.circumcenter hT) := by
  change intervalSq (T.circumcenter hT) T.B =
    T.circumradiusSqAt (T.circumcenter hT)
  exact (circumcenter_isCircumcenter T hT).intervalSq_B_eq_radius

private theorem q_circumcenterVecC (T : Triangle) (hT : T.Nondegenerate) :
    q (intervalVec (T.circumcenter hT) T.C) =
      T.circumradiusSqAt (T.circumcenter hT) := by
  change intervalSq (T.circumcenter hT) T.C =
    T.circumradiusSqAt (T.circumcenter hT)
  exact (circumcenter_isCircumcenter T hT).intervalSq_C_eq_radius

private theorem dot_circumcenterVecA_B (T : Triangle) (hT : T.Nondegenerate) :
    dot (intervalVec (T.circumcenter hT) T.A)
        (intervalVec (T.circumcenter hT) T.B) =
      T.circumradiusSqAt (T.circumcenter hT) - T.sideSqC / 2 := by
  have hside : q (intervalVec (T.circumcenter hT) T.B -
      intervalVec (T.circumcenter hT) T.A) = T.sideSqC := by
    rw [← intervalVec_eq_sub_from (T.circumcenter hT) T.A T.B]
    rfl
  rw [q_sub, q_circumcenterVecB, show
    q (intervalVec (T.circumcenter hT) T.A) =
      T.circumradiusSqAt (T.circumcenter hT) by rfl,
    dot_comm] at hside
  linarith

private theorem dot_circumcenterVecA_C (T : Triangle) (hT : T.Nondegenerate) :
    dot (intervalVec (T.circumcenter hT) T.A)
        (intervalVec (T.circumcenter hT) T.C) =
      T.circumradiusSqAt (T.circumcenter hT) - T.sideSqB / 2 := by
  have hAC : q (intervalVec T.A T.C) = T.sideSqB := by
    change intervalSq T.A T.C = intervalSq T.C T.A
    exact intervalSq_comm T.A T.C
  have hside : q (intervalVec (T.circumcenter hT) T.C -
      intervalVec (T.circumcenter hT) T.A) = T.sideSqB := by
    rw [← intervalVec_eq_sub_from (T.circumcenter hT) T.A T.C]
    exact hAC
  rw [q_sub, q_circumcenterVecC, show
    q (intervalVec (T.circumcenter hT) T.A) =
      T.circumradiusSqAt (T.circumcenter hT) by rfl,
    dot_comm] at hside
  linarith

private theorem dot_circumcenterVecB_C (T : Triangle) (hT : T.Nondegenerate) :
    dot (intervalVec (T.circumcenter hT) T.B)
        (intervalVec (T.circumcenter hT) T.C) =
      T.circumradiusSqAt (T.circumcenter hT) - T.sideSqA / 2 := by
  have hside : q (intervalVec (T.circumcenter hT) T.C -
      intervalVec (T.circumcenter hT) T.B) = T.sideSqA := by
    rw [← intervalVec_eq_sub_from (T.circumcenter hT) T.B T.C]
    rfl
  rw [q_sub, q_circumcenterVecC, q_circumcenterVecB, dot_comm] at hside
  linarith

private theorem q_three_smul (x y z : ℝ) (u v w : Vec) :
    q (x • u + y • v + z • w) =
      x ^ 2 * q u + y ^ 2 * q v + z ^ 2 * q w +
        2 * x * y * dot u v + 2 * y * z * dot v w + 2 * z * x * dot u w := by
  rw [q_add, q_add, q_smul, q_smul, q_smul]
  simp only [dot_add_left, dot_smul_left, dot_smul_right]
  ring

theorem q_weighted_circumcenterVectors (T : Triangle) (hT : T.Nondegenerate)
    (x y z : ℝ) :
    q (x • intervalVec (T.circumcenter hT) T.A +
        y • intervalVec (T.circumcenter hT) T.B +
        z • intervalVec (T.circumcenter hT) T.C) =
      (x + y + z) ^ 2 * T.circumradiusSqAt (T.circumcenter hT) -
        x * y * T.sideSqC - y * z * T.sideSqA - z * x * T.sideSqB := by
  rw [q_three_smul,
    show q (intervalVec (T.circumcenter hT) T.A) =
      T.circumradiusSqAt (T.circumcenter hT) by rfl,
    q_circumcenterVecB, q_circumcenterVecC,
    dot_circumcenterVecA_B, dot_circumcenterVecB_C,
    dot_circumcenterVecA_C]
  ring

private theorem intervalVec_ninePointCenter_barycentricPoint (T : Triangle)
    (hT : T.Nondegenerate) (w : BarycentricWeights) :
    intervalVec (T.ninePointCenter hT) (T.barycentricPoint w) =
      (w.a - 1 / 2 : ℝ) • intervalVec (T.circumcenter hT) T.A +
        (w.b - 1 / 2 : ℝ) • intervalVec (T.circumcenter hT) T.B +
        (w.c - 1 / 2 : ℝ) • intervalVec (T.circumcenter hT) T.C := by
  rw [ninePointCenter_eq_affine_formula, barycentricPoint_eq_linearCombination]
  simp only [intervalVec, vsub_eq_sub]
  have hc : w.c = 1 - w.a - w.b := by
    linarith [w.sum_eq_one]
  rw [hc]
  module

theorem intervalSq_ninePointCenter_barycentricPoint (T : Triangle)
    (hT : T.Nondegenerate) (w : BarycentricWeights) :
    intervalSq (T.ninePointCenter hT) (T.barycentricPoint w) =
      T.circumradiusSqAt (T.circumcenter hT) / 4 -
        (w.b - 1 / 2) * (w.c - 1 / 2) * T.sideSqA -
        (w.c - 1 / 2) * (w.a - 1 / 2) * T.sideSqB -
        (w.a - 1 / 2) * (w.b - 1 / 2) * T.sideSqC := by
  rw [intervalSq, intervalVec_ninePointCenter_barycentricPoint,
    q_weighted_circumcenterVectors]
  have hsum : (w.a - 1 / 2 : ℝ) + (w.b - 1 / 2) + (w.c - 1 / 2) = -1 / 2 := by
    linarith [w.sum_eq_one]
  rw [hsum]
  ring

theorem intervalSq_ninePointCenter_incenter (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) :
    intervalSq (T.ninePointCenter hN) (T.incenter hT) =
      T.circumradiusSqAt (T.circumcenter hN) / 4 -
        ((T.incenterWeights hT).b - 1 / 2) *
          ((T.incenterWeights hT).c - 1 / 2) * T.sideSqA -
        ((T.incenterWeights hT).c - 1 / 2) *
          ((T.incenterWeights hT).a - 1 / 2) * T.sideSqB -
        ((T.incenterWeights hT).a - 1 / 2) *
          ((T.incenterWeights hT).b - 1 / 2) * T.sideSqC := by
  exact intervalSq_ninePointCenter_barycentricPoint T hN (T.incenterWeights hT)

theorem intervalSq_ninePointCenter_excenterC (T : Triangle)
    (hN : T.Nondegenerate) (hC : T.excenterDenomC ≠ 0) :
    intervalSq (T.ninePointCenter hN) (T.excenterC hC) =
      T.circumradiusSqAt (T.circumcenter hN) / 4 -
        ((T.excenterWeightsC hC).b - 1 / 2) *
          ((T.excenterWeightsC hC).c - 1 / 2) * T.sideSqA -
        ((T.excenterWeightsC hC).c - 1 / 2) *
          ((T.excenterWeightsC hC).a - 1 / 2) * T.sideSqB -
        ((T.excenterWeightsC hC).a - 1 / 2) *
          ((T.excenterWeightsC hC).b - 1 / 2) * T.sideSqC := by
  exact intervalSq_ninePointCenter_barycentricPoint T hN (T.excenterWeightsC hC)

end

end Triangle
end MinkowskiMerge
