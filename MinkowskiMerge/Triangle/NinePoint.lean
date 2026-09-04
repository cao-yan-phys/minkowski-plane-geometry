import MinkowskiMerge.Triangle.Radii


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

local instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

noncomputable def ninePointCenter (T : Triangle) (hT : T.Nondegenerate) : Point :=
  midpoint ℝ (T.circumcenter hT) (T.orthocenter hT)

noncomputable def orthocenterMidpointA (T : Triangle)
    (hT : T.Nondegenerate) : Point :=
  midpoint ℝ T.A (T.orthocenter hT)

noncomputable def orthocenterMidpointB (T : Triangle)
    (hT : T.Nondegenerate) : Point :=
  midpoint ℝ T.B (T.orthocenter hT)

noncomputable def orthocenterMidpointC (T : Triangle)
    (hT : T.Nondegenerate) : Point :=
  midpoint ℝ T.C (T.orthocenter hT)

noncomputable def ninePointRadiusSq (T : Triangle) (hT : T.Nondegenerate) : ℝ :=
  intervalSq (T.ninePointCenter hT) T.midpointA

def IsOnNinePointCircle (T : Triangle) (hT : T.Nondegenerate) (P : Point) : Prop :=
  intervalSq (T.ninePointCenter hT) P = T.ninePointRadiusSq hT

theorem ninePointCenter_eq_affine_formula (T : Triangle) (hT : T.Nondegenerate) :
    T.ninePointCenter hT =
      (1 / 2 : ℝ) • T.A + (1 / 2 : ℝ) • T.B +
        (1 / 2 : ℝ) • T.C - (1 / 2 : ℝ) • T.circumcenter hT := by
  unfold ninePointCenter orthocenter
  rw [orthocenterFromCircumcenter_apply, midpoint_eq_smul_add]
  simp only [invOf_eq_inv]
  module

private theorem intervalVec_ninePointCenter_midpointA (T : Triangle)
    (hT : T.Nondegenerate) :
    intervalVec (T.ninePointCenter hT) T.midpointA =
      (1 / 2 : ℝ) • intervalVec T.A (T.circumcenter hT) := by
  unfold ninePointCenter orthocenter
  rw [orthocenterFromCircumcenter_apply, midpoint_eq_smul_add]
  simp only [midpointA, midpoint_eq_smul_add, invOf_eq_inv,
    intervalVec, vsub_eq_sub]
  module

private theorem intervalVec_ninePointCenter_midpointB (T : Triangle)
    (hT : T.Nondegenerate) :
    intervalVec (T.ninePointCenter hT) T.midpointB =
      (1 / 2 : ℝ) • intervalVec T.B (T.circumcenter hT) := by
  unfold ninePointCenter orthocenter
  rw [orthocenterFromCircumcenter_apply, midpoint_eq_smul_add]
  simp only [midpointB, midpoint_eq_smul_add, invOf_eq_inv,
    intervalVec, vsub_eq_sub]
  module

private theorem intervalVec_ninePointCenter_midpointC (T : Triangle)
    (hT : T.Nondegenerate) :
    intervalVec (T.ninePointCenter hT) T.midpointC =
      (1 / 2 : ℝ) • intervalVec T.C (T.circumcenter hT) := by
  unfold ninePointCenter orthocenter
  rw [orthocenterFromCircumcenter_apply, midpoint_eq_smul_add]
  simp only [midpointC, midpoint_eq_smul_add, invOf_eq_inv,
    intervalVec, vsub_eq_sub]
  module

private theorem q_vertex_to_circumcenter (T : Triangle)
    (hT : T.Nondegenerate) (P : Point) (hP : P = T.A) :
    q (intervalVec P (T.circumcenter hT)) =
      T.circumradiusSqAt (T.circumcenter hT) := by
  subst P
  rw [circumradiusSqAt, intervalSq]
  simp [intervalVec]
  ring

private theorem q_vertex_to_circumcenter_B (T : Triangle)
    (hT : T.Nondegenerate) :
    q (intervalVec T.B (T.circumcenter hT)) =
      T.circumradiusSqAt (T.circumcenter hT) := by
  have hO := circumcenter_isCircumcenter T hT
  have hrev : intervalVec T.B (T.circumcenter hT) =
      -intervalVec (T.circumcenter hT) T.B := by
    simp [intervalVec, vsub_eq_sub]
  rw [hrev, q_neg]
  change intervalSq (T.circumcenter hT) T.B = _
  exact hO.1.symm

private theorem q_vertex_to_circumcenter_C (T : Triangle)
    (hT : T.Nondegenerate) :
    q (intervalVec T.C (T.circumcenter hT)) =
      T.circumradiusSqAt (T.circumcenter hT) := by
  have hO := circumcenter_isCircumcenter T hT
  have hrev : intervalVec T.C (T.circumcenter hT) =
      -intervalVec (T.circumcenter hT) T.C := by
    simp [intervalVec, vsub_eq_sub]
  rw [hrev, q_neg]
  change intervalSq (T.circumcenter hT) T.C = _
  exact hO.intervalSq_C_eq_radius

private theorem dot_circumcenterVec_B_sideVecA (T : Triangle)
    (hT : T.Nondegenerate) :
    dot (intervalVec (T.circumcenter hT) T.B) T.sideVecA =
      -T.sideSqA / 2 := by
  have hO := circumcenter_isCircumcenter T hT
  have hEq := hO.2
  simp only [intervalSq, intervalVec, sideVecA, sideSqA,
    vsub_eq_sub, q_apply, dot_apply, Vec.x_sub, Vec.t_sub] at hEq ⊢
  nlinarith [hEq]

private theorem intervalVec_midpoint_lineMap (A B C O : Point) (r : ℝ) :
    intervalVec (midpoint ℝ O (A + B + C - (2 : ℝ) • O))
        (AffineMap.lineMap B C r) =
      (r - 1 / 2) • intervalVec B C -
        (1 / 2 : ℝ) • intervalVec O A := by
  rw [intervalVec_lineMap]
  simp [midpoint_eq_smul_add, invOf_eq_inv, intervalVec, vsub_eq_sub]
  module

private theorem foot_midpoint_sq_from_parameter (A B C O : Point) (r : ℝ)
    (hparam : r * q (intervalVec B C) =
      dot (intervalVec O A) (intervalVec B C) + q (intervalVec B C) / 2) :
    q (intervalVec (midpoint ℝ O (A + B + C - (2 : ℝ) • O))
        (AffineMap.lineMap B C r)) = q (intervalVec O A) / 4 := by
  rw [intervalVec_midpoint_lineMap A B C O r, q_sub, q_smul, q_smul]
  simp only [dot_smul_left, dot_smul_right]
  rw [dot_comm]
  have hrel : (r - 1 / 2) * q (intervalVec B C) =
      dot (intervalVec O A) (intervalVec B C) := by
    nlinarith [hparam]
  calc
    _ = (r - 1 / 2) * ((r - 1 / 2) * q (intervalVec B C)) -
          (r - 1 / 2) * dot (intervalVec O A) (intervalVec B C) +
          (1 / 2) ^ 2 * q (intervalVec O A) := by ring
    _ = q (intervalVec O A) / 4 := by
      rw [hrel]
      norm_num
      ring

private theorem intervalVec_ninePointCenter_footA (T : Triangle)
    (hT : T.Nondegenerate) (hA : T.sideSqA ≠ 0) :
    intervalVec (T.ninePointCenter hT) (T.footA hA) =
  (footParameter T.A T.B T.C - 1 / 2) • T.sideVecA -
        (1 / 2 : ℝ) • intervalVec (T.circumcenter hT) T.A := by
  rw [footA]
  change intervalVec (T.ninePointCenter hT)
      (AffineMap.lineMap T.B T.C (footParameter T.A T.B T.C)) = _
  unfold ninePointCenter orthocenter
  rw [orthocenterFromCircumcenter_apply]
  exact intervalVec_midpoint_lineMap T.A T.B T.C (T.circumcenter hT)
    (footParameter T.A T.B T.C)

private theorem footParameter_mul_sideSqA (T : Triangle)
    (hT : T.Nondegenerate) (hA : T.sideSqA ≠ 0) :
    footParameter T.A T.B T.C * T.sideSqA =
      dot (intervalVec (T.circumcenter hT) T.A) T.sideVecA +
        T.sideSqA / 2 := by
  unfold footParameter
  change (dot (intervalVec T.B T.A) T.sideVecA / T.sideSqA) *
      T.sideSqA = _
  rw [intervalVec_eq_sub_from (T.circumcenter hT) T.B T.A,
    dot_sub_left, dot_circumcenterVec_B_sideVecA T hT]
  field_simp [hA]
  ring

theorem footA_on_ninePointCircle (T : Triangle)
    (hT : T.Nondegenerate) (hA : T.sideSqA ≠ 0) :
    T.IsOnNinePointCircle hT (T.footA hA) := by
  unfold IsOnNinePointCircle ninePointRadiusSq
  change q (intervalVec (T.ninePointCenter hT) (T.footA hA)) =
    q (intervalVec (T.ninePointCenter hT) T.midpointA)
  rw [intervalVec_ninePointCenter_footA T hT hA,
    q_sub, q_smul, q_smul]
  rw [intervalVec_ninePointCenter_midpointA T hT, q_smul]
  simp only [dot_smul_left, dot_smul_right]
  have hqa : q (intervalVec (T.circumcenter hT) T.A) =
      T.circumradiusSqAt (T.circumcenter hT) := rfl
  have hqa' : q (intervalVec T.A (T.circumcenter hT)) =
      T.circumradiusSqAt (T.circumcenter hT) := by
    rw [intervalVec_rev, q_neg]
    exact hqa
  rw [show q T.sideVecA = T.sideSqA by rfl, hqa, hqa', dot_comm]
  have hf := footParameter_mul_sideSqA T hT hA
  have hrel :
      (footParameter T.A T.B T.C - 1 / 2) * T.sideSqA =
        dot (intervalVec (T.circumcenter hT) T.A) T.sideVecA := by
    nlinarith [hf]
  calc
    _ = (footParameter T.A T.B T.C - 1 / 2) *
          ((footParameter T.A T.B T.C - 1 / 2) * T.sideSqA) -
        (footParameter T.A T.B T.C - 1 / 2) *
          dot (intervalVec (T.circumcenter hT) T.A) T.sideVecA +
        (1 / 2) ^ 2 * T.circumradiusSqAt (T.circumcenter hT) := by ring
    _ = (1 / 2) ^ 2 * T.circumradiusSqAt (T.circumcenter hT) := by
      rw [hrel]
      ring

private theorem dot_circumcenterVec_C_sideVecB (T : Triangle)
    (hT : T.Nondegenerate) :
    dot (intervalVec (T.circumcenter hT) T.C) T.sideVecB =
      -T.sideSqB / 2 := by
  have hO := circumcenter_isCircumcenter T hT
  have hEq := hO.intervalSq_A_eq_C
  simp only [intervalSq, intervalVec, sideVecB, sideSqB,
    vsub_eq_sub, q_apply, dot_apply, Vec.x_sub, Vec.t_sub] at hEq ⊢
  nlinarith [hEq]

private theorem footParameter_mul_sideSqB (T : Triangle)
    (hT : T.Nondegenerate) (hB : T.sideSqB ≠ 0) :
    footParameter T.B T.C T.A * T.sideSqB =
      dot (intervalVec (T.circumcenter hT) T.B) T.sideVecB +
        T.sideSqB / 2 := by
  unfold footParameter
  change (dot (intervalVec T.C T.B) T.sideVecB / T.sideSqB) *
      T.sideSqB = _
  rw [intervalVec_eq_sub_from (T.circumcenter hT) T.C T.B,
    dot_sub_left, dot_circumcenterVec_C_sideVecB T hT]
  field_simp [hB]
  ring

theorem footB_on_ninePointCircle (T : Triangle)
    (hT : T.Nondegenerate) (hB : T.sideSqB ≠ 0) :
    T.IsOnNinePointCircle hT (T.footB hB) := by
  unfold IsOnNinePointCircle ninePointRadiusSq
  change q (intervalVec (T.ninePointCenter hT) (T.footB hB)) =
    q (intervalVec (T.ninePointCenter hT) T.midpointA)
  have hparam := footParameter_mul_sideSqB T hT hB
  have hg := foot_midpoint_sq_from_parameter T.B T.C T.A
    (T.circumcenter hT) (footParameter T.B T.C T.A) hparam
  have hqb : q (intervalVec (T.circumcenter hT) T.B) =
      T.circumradiusSqAt (T.circumcenter hT) := by
    change intervalSq (T.circumcenter hT) T.B = _
    exact (circumcenter_isCircumcenter T hT).1.symm
  have hqa : q (intervalVec T.A (T.circumcenter hT)) =
      T.circumradiusSqAt (T.circumcenter hT) := by
    rw [intervalVec_rev, q_neg]
    change intervalSq (T.circumcenter hT) T.A = _
    rfl
  rw [intervalVec_ninePointCenter_midpointA, q_smul, hqa]
  have hquarter : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
  rw [hquarter]
  rw [footB]
  change q (intervalVec (T.ninePointCenter hT)
      (AffineMap.lineMap T.C T.A (footParameter T.B T.C T.A))) = _
  unfold ninePointCenter orthocenter
  rw [orthocenterFromCircumcenter_apply]
  rw [hqb] at hg
  have hsum : T.B + T.C + T.A - (2 : ℝ) • T.circumcenter hT =
      T.A + T.B + T.C - (2 : ℝ) • T.circumcenter hT := by
    module
  rw [hsum] at hg
  convert hg using 1 <;> ring

private theorem dot_circumcenterVec_A_sideVecC (T : Triangle)
    (hT : T.Nondegenerate) :
    dot (intervalVec (T.circumcenter hT) T.A) T.sideVecC =
      -T.sideSqC / 2 := by
  have hO := circumcenter_isCircumcenter T hT
  have hEq := hO.1
  simp only [intervalSq, intervalVec, sideVecC, sideSqC,
    vsub_eq_sub, q_apply, dot_apply, Vec.x_sub, Vec.t_sub] at hEq ⊢
  nlinarith [hEq]

private theorem footParameter_mul_sideSqC (T : Triangle)
    (hT : T.Nondegenerate) (hC : T.sideSqC ≠ 0) :
    footParameter T.C T.A T.B * T.sideSqC =
      dot (intervalVec (T.circumcenter hT) T.C) T.sideVecC +
        T.sideSqC / 2 := by
  unfold footParameter
  change (dot (intervalVec T.A T.C) T.sideVecC / T.sideSqC) *
      T.sideSqC = _
  rw [intervalVec_eq_sub_from (T.circumcenter hT) T.A T.C,
    dot_sub_left, dot_circumcenterVec_A_sideVecC T hT]
  field_simp [hC]
  ring

theorem footC_on_ninePointCircle (T : Triangle)
    (hT : T.Nondegenerate) (hC : T.sideSqC ≠ 0) :
    T.IsOnNinePointCircle hT (T.footC hC) := by
  unfold IsOnNinePointCircle ninePointRadiusSq
  change q (intervalVec (T.ninePointCenter hT) (T.footC hC)) =
    q (intervalVec (T.ninePointCenter hT) T.midpointA)
  have hparam := footParameter_mul_sideSqC T hT hC
  have hg := foot_midpoint_sq_from_parameter T.C T.A T.B
    (T.circumcenter hT) (footParameter T.C T.A T.B) hparam
  have hqc : q (intervalVec (T.circumcenter hT) T.C) =
      T.circumradiusSqAt (T.circumcenter hT) := by
    change intervalSq (T.circumcenter hT) T.C = _
    exact (circumcenter_isCircumcenter T hT).intervalSq_C_eq_radius
  have hqa : q (intervalVec T.A (T.circumcenter hT)) =
      T.circumradiusSqAt (T.circumcenter hT) := by
    rw [intervalVec_rev, q_neg]
    change intervalSq (T.circumcenter hT) T.A = _
    rfl
  rw [intervalVec_ninePointCenter_midpointA, q_smul, hqa]
  have hquarter : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
  rw [hquarter]
  rw [footC]
  change q (intervalVec (T.ninePointCenter hT)
      (AffineMap.lineMap T.A T.B (footParameter T.C T.A T.B))) = _
  unfold ninePointCenter orthocenter
  rw [orthocenterFromCircumcenter_apply]
  rw [hqc] at hg
  have hsum : T.C + T.A + T.B - (2 : ℝ) • T.circumcenter hT =
      T.A + T.B + T.C - (2 : ℝ) • T.circumcenter hT := by
    module
  rw [hsum] at hg
  convert hg using 1 <;> ring

theorem midpointA_on_ninePointCircle (T : Triangle) (hT : T.Nondegenerate) :
    T.IsOnNinePointCircle hT T.midpointA := by
  rfl

theorem midpointB_on_ninePointCircle (T : Triangle) (hT : T.Nondegenerate) :
    T.IsOnNinePointCircle hT T.midpointB := by
  unfold IsOnNinePointCircle ninePointRadiusSq
  rw [intervalSq, intervalSq, intervalVec_ninePointCenter_midpointB,
    q_smul, intervalVec_ninePointCenter_midpointA, q_smul,
    q_vertex_to_circumcenter_B T hT, q_vertex_to_circumcenter T hT T.A rfl]

theorem midpointC_on_ninePointCircle (T : Triangle) (hT : T.Nondegenerate) :
    T.IsOnNinePointCircle hT T.midpointC := by
  unfold IsOnNinePointCircle ninePointRadiusSq
  rw [intervalSq, intervalSq, intervalVec_ninePointCenter_midpointC,
    q_smul, intervalVec_ninePointCenter_midpointA, q_smul,
    q_vertex_to_circumcenter_C T hT, q_vertex_to_circumcenter T hT T.A rfl]

theorem ninePointRadiusSq_eq_quarter_circumradiusSq
    (T : Triangle) (hT : T.Nondegenerate) :
    T.ninePointRadiusSq hT =
      T.circumradiusSqAt (T.circumcenter hT) / 4 := by
  unfold ninePointRadiusSq
  rw [intervalSq, intervalVec_ninePointCenter_midpointA, q_smul,
    q_vertex_to_circumcenter T hT T.A rfl]
  ring

theorem ninePointRadiusSq_eq_sideSq_product_div_areaSq
    (T : Triangle) (hT : T.Nondegenerate) :
    T.ninePointRadiusSq hT =
      -(T.sideSqA * T.sideSqB * T.sideSqC) /
        (16 * T.signedDoubleArea ^ 2) := by
  rw [ninePointRadiusSq_eq_quarter_circumradiusSq,
    circumradiusSq_eq_sideSq_product_div_areaSq]
  ring

private theorem intervalVec_ninePointCenter_orthocenterMidpointA
    (T : Triangle) (hT : T.Nondegenerate) :
    intervalVec (T.ninePointCenter hT) (T.orthocenterMidpointA hT) =
      (1 / 2 : ℝ) • intervalVec (T.circumcenter hT) T.A := by
  unfold ninePointCenter orthocenterMidpointA
  change midpoint ℝ T.A (T.orthocenter hT) -ᵥ
      midpoint ℝ (T.circumcenter hT) (T.orthocenter hT) = _
  rw [midpoint_vsub_midpoint]
  simp [midpoint_eq_smul_add, invOf_eq_inv, intervalVec]

private theorem intervalVec_ninePointCenter_orthocenterMidpointB
    (T : Triangle) (hT : T.Nondegenerate) :
    intervalVec (T.ninePointCenter hT) (T.orthocenterMidpointB hT) =
      (1 / 2 : ℝ) • intervalVec (T.circumcenter hT) T.B := by
  unfold ninePointCenter orthocenterMidpointB
  change midpoint ℝ T.B (T.orthocenter hT) -ᵥ
      midpoint ℝ (T.circumcenter hT) (T.orthocenter hT) = _
  rw [midpoint_vsub_midpoint]
  simp [midpoint_eq_smul_add, invOf_eq_inv, intervalVec]

private theorem intervalVec_ninePointCenter_orthocenterMidpointC
    (T : Triangle) (hT : T.Nondegenerate) :
    intervalVec (T.ninePointCenter hT) (T.orthocenterMidpointC hT) =
      (1 / 2 : ℝ) • intervalVec (T.circumcenter hT) T.C := by
  unfold ninePointCenter orthocenterMidpointC
  change midpoint ℝ T.C (T.orthocenter hT) -ᵥ
      midpoint ℝ (T.circumcenter hT) (T.orthocenter hT) = _
  rw [midpoint_vsub_midpoint]
  simp [midpoint_eq_smul_add, invOf_eq_inv, intervalVec]

theorem orthocenterMidpointA_on_ninePointCircle (T : Triangle)
    (hT : T.Nondegenerate) :
    T.IsOnNinePointCircle hT (T.orthocenterMidpointA hT) := by
  unfold IsOnNinePointCircle
  rw [intervalSq, intervalVec_ninePointCenter_orthocenterMidpointA,
    q_smul, ninePointRadiusSq_eq_quarter_circumradiusSq]
  change (1 / 2 : ℝ) ^ 2 * T.circumradiusSqAt (T.circumcenter hT) =
    T.circumradiusSqAt (T.circumcenter hT) / 4
  ring

theorem orthocenterMidpointB_on_ninePointCircle (T : Triangle)
    (hT : T.Nondegenerate) :
    T.IsOnNinePointCircle hT (T.orthocenterMidpointB hT) := by
  unfold IsOnNinePointCircle
  rw [intervalSq, intervalVec_ninePointCenter_orthocenterMidpointB,
    q_smul, ninePointRadiusSq_eq_quarter_circumradiusSq]
  have hO := circumcenter_isCircumcenter T hT
  change (1 / 2) ^ 2 * intervalSq (T.circumcenter hT) T.B =
    T.circumradiusSqAt (T.circumcenter hT) / 4
  rw [hO.1.symm]
  change (1 / 2 : ℝ) ^ 2 * T.circumradiusSqAt (T.circumcenter hT) =
    T.circumradiusSqAt (T.circumcenter hT) / 4
  ring

theorem orthocenterMidpointC_on_ninePointCircle (T : Triangle)
    (hT : T.Nondegenerate) :
    T.IsOnNinePointCircle hT (T.orthocenterMidpointC hT) := by
  unfold IsOnNinePointCircle
  rw [intervalSq, intervalVec_ninePointCenter_orthocenterMidpointC,
    q_smul, ninePointRadiusSq_eq_quarter_circumradiusSq]
  have hO := circumcenter_isCircumcenter T hT
  change (1 / 2) ^ 2 * intervalSq (T.circumcenter hT) T.C =
    T.circumradiusSqAt (T.circumcenter hT) / 4
  rw [hO.intervalSq_C_eq_radius]
  change (1 / 2 : ℝ) ^ 2 * T.circumradiusSqAt (T.circumcenter hT) =
    T.circumradiusSqAt (T.circumcenter hT) / 4
  ring

end

end Triangle
end MinkowskiMerge
