import MinkowskiMerge.Triangle.Centers
import MinkowskiMerge.Triangle.Heron


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

noncomputable def branchSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

noncomputable def lambdaA (T : Triangle) : ℝ :=
  branchSign (T.sideAbsLengthB + T.sideAbsLengthC - T.sideAbsLengthA)

noncomputable def lambdaB (T : Triangle) : ℝ :=
  branchSign (T.sideAbsLengthC + T.sideAbsLengthA - T.sideAbsLengthB)

noncomputable def lambdaC (T : Triangle) : ℝ :=
  branchSign (T.sideAbsLengthA + T.sideAbsLengthB - T.sideAbsLengthC)

theorem branchSign_sq (x : ℝ) : branchSign x ^ 2 = 1 := by
  unfold branchSign
  by_cases h : 0 ≤ x <;> simp [h]

theorem branchSign_ne_zero (x : ℝ) : branchSign x ≠ 0 := by
  intro hzero
  have hsq := branchSign_sq x
  rw [hzero] at hsq
  norm_num at hsq

theorem branchSign_mul_abs (x : ℝ) : branchSign x * |x| = x := by
  unfold branchSign
  by_cases h : 0 ≤ x
  · rw [if_pos h, abs_of_nonneg h]
    ring
  · have h' : x < 0 := lt_of_not_ge h
    rw [if_neg h, abs_of_neg h']
    ring

theorem lambdaA_sq (T : Triangle) : T.lambdaA ^ 2 = 1 := by
  exact branchSign_sq _

theorem lambdaB_sq (T : Triangle) : T.lambdaB ^ 2 = 1 := by
  exact branchSign_sq _

theorem lambdaC_sq (T : Triangle) : T.lambdaC ^ 2 = 1 := by
  exact branchSign_sq _

theorem lambdaA_ne_zero (T : Triangle) : T.lambdaA ≠ 0 :=
  branchSign_ne_zero _

theorem lambdaB_ne_zero (T : Triangle) : T.lambdaB ≠ 0 :=
  branchSign_ne_zero _

theorem lambdaC_ne_zero (T : Triangle) : T.lambdaC ≠ 0 :=
  branchSign_ne_zero _

theorem lambdaC_mul_abs_denominator (T : Triangle) :
    T.lambdaC *
        |T.sideAbsLengthA + T.sideAbsLengthB - T.sideAbsLengthC| =
      T.excenterDenomC := by
  simpa [lambdaC, excenterDenomC, signedPerimeter] using
    branchSign_mul_abs
      (T.sideAbsLengthA + T.sideAbsLengthB - T.sideAbsLengthC)

theorem complexLength_eq_real_of_q_eq_sq {v : Vec} {r : ℝ}
    (hr : 0 ≤ r) (hqr : q v = r ^ 2) :
    complexLength v = (r : ℂ) := by
  by_cases hz : r = 0
  · have hq : q v = 0 := by rw [hqr, hz]; norm_num
    rw [complexLength_of_null hq, hz]
    norm_num
  · have hq : 0 < q v := by
      rw [hqr]
      exact sq_pos_of_ne_zero hz
    rw [complexLength_of_spacelike hq, hqr, Real.sqrt_sq hr]

theorem complexLength_eq_I_mul_real_of_q_eq_neg_sq {v : Vec} {r : ℝ}
    (hr : 0 ≤ r) (hqr : q v = -r ^ 2) :
    complexLength v = Complex.I * (r : ℂ) := by
  by_cases hz : r = 0
  · have hq : q v = 0 := by rw [hqr, hz]; norm_num
    rw [complexLength_of_null hq, hz]
    norm_num
  · have hq : q v < 0 := by
      rw [hqr]
      exact neg_lt_zero.mpr (sq_pos_of_ne_zero hz)
    rw [complexLength_of_timelike hq, hqr, neg_neg, Real.sqrt_sq hr]

private theorem semiperimeterComplex_spacelike
    {T : Triangle} (hT : T.IsSpacelike) :
    T.semiperimeterComplex = (T.perimeterAbs / 2 : ℂ) := by
  unfold semiperimeterComplex perimeterComplex sideComplexLengthA
    sideComplexLengthB sideComplexLengthC
  rw [complexLength_eq_absLength_of_spacelike hT.1,
    complexLength_eq_absLength_of_spacelike hT.2.1,
    complexLength_eq_absLength_of_spacelike hT.2.2]
  simp [sideAbsLengthA, sideAbsLengthB, sideAbsLengthC, perimeterAbs]

private theorem semiperimeterComplex_timelike
    {T : Triangle} (hT : T.IsTimelike) :
    T.semiperimeterComplex = Complex.I * (T.perimeterAbs / 2 : ℂ) := by
  unfold semiperimeterComplex perimeterComplex sideComplexLengthA
    sideComplexLengthB sideComplexLengthC
  rw [complexLength_eq_I_mul_absLength_of_timelike hT.1,
    complexLength_eq_I_mul_absLength_of_timelike hT.2.1,
    complexLength_eq_I_mul_absLength_of_timelike hT.2.2]
  simp [sideAbsLengthA, sideAbsLengthB, sideAbsLengthC, perimeterAbs]
  ring

private theorem semiperimeterComplex_sub_sideC_spacelike
    {T : Triangle} (hT : T.IsSpacelike) :
    T.semiperimeterComplex - T.sideComplexLengthC =
      (T.excenterDenomC / 2 : ℂ) := by
  rw [semiperimeterComplex_spacelike hT]
  unfold sideComplexLengthC
  rw [complexLength_eq_absLength_of_spacelike hT.2.2]
  simp [sideAbsLengthC, excenterDenomC, signedPerimeter, perimeterAbs]
  ring

private theorem semiperimeterComplex_sub_sideC_timelike
    {T : Triangle} (hT : T.IsTimelike) :
    T.semiperimeterComplex - T.sideComplexLengthC =
      Complex.I * (T.excenterDenomC / 2 : ℂ) := by
  rw [semiperimeterComplex_timelike hT]
  unfold sideComplexLengthC
  rw [complexLength_eq_I_mul_absLength_of_timelike hT.2.2]
  simp [sideAbsLengthC, excenterDenomC, signedPerimeter, perimeterAbs]
  ring

theorem inradius_eq_complexArea_div_semiperimeter
    (T : Triangle) (hT : T.IsNonMixed) :
    T.inradius hT = T.complexArea / T.semiperimeterComplex := by
  rcases hT with hS | hT
  · have hnm : T.IsNonMixed := Or.inl hS
    have hp : 0 < T.perimeterAbs := hnm.perimeterAbs_pos
    have hpC : (T.perimeterAbs : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hp)
    have hA : IsNonNullLine T.B T.C := hnm.sidesNonNull.1
    have hq : q (heightVec (T.incenter (Or.inl hS)) T.B T.C hA) =
        -(T.areaMagnitude * 2 / T.perimeterAbs) ^ 2 := by
      change T.inradiusSq (Or.inl hS) = _
      rw [inradiusSq_eq_spacelike_formula hS]
      unfold areaMagnitude
      field_simp [ne_of_gt hp]
      rw [sq_abs]
    have ha : 0 ≤ T.areaMagnitude := by
      unfold areaMagnitude
      positivity
    have hr : 0 ≤ T.areaMagnitude * 2 / T.perimeterAbs := by
      exact div_nonneg (mul_nonneg ha (by norm_num)) hp.le
    have hlen := complexLength_eq_I_mul_real_of_q_eq_neg_sq hr hq
    rw [inradius, pointLineDistance]
    change complexLength (heightVec (T.incenter (Or.inl hS)) T.B T.C hA) = _
    rw [hlen, complexArea, semiperimeterComplex_spacelike hS]
    unfold areaMagnitude
    field_simp [hpC]
    push_cast
    field_simp [hpC]
  · have hnm : T.IsNonMixed := Or.inr hT
    have hp : 0 < T.perimeterAbs := hnm.perimeterAbs_pos
    have hpC : (T.perimeterAbs : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hp)
    have hA : IsNonNullLine T.B T.C := hnm.sidesNonNull.1
    have hq : q (heightVec (T.incenter (Or.inr hT)) T.B T.C hA) =
        (T.areaMagnitude * 2 / T.perimeterAbs) ^ 2 := by
      change T.inradiusSq (Or.inr hT) = _
      rw [inradiusSq_eq_timelike_formula hT]
      unfold areaMagnitude
      field_simp [ne_of_gt hp]
      rw [sq_abs]
    have ha : 0 ≤ T.areaMagnitude := by
      unfold areaMagnitude
      positivity
    have hr : 0 ≤ T.areaMagnitude * 2 / T.perimeterAbs := by
      exact div_nonneg (mul_nonneg ha (by norm_num)) hp.le
    have hlen := complexLength_eq_real_of_q_eq_sq hr hq
    rw [inradius, pointLineDistance]
    change complexLength (heightVec (T.incenter (Or.inr hT)) T.B T.C hA) = _
    rw [hlen, complexArea, semiperimeterComplex_timelike hT]
    unfold areaMagnitude
    field_simp [hpC, Complex.I_ne_zero]
    push_cast
    field_simp [hpC, Complex.I_ne_zero]

theorem exradiusC_eq_lambdaC_mul_complexArea_div_semiperimeter_sub_side
    (T : Triangle) (hT : T.IsNonMixed) (hC : T.excenterDenomC ≠ 0) :
    T.exradiusC hT hC =
      (T.lambdaC : ℂ) * T.complexArea /
        (T.semiperimeterComplex - T.sideComplexLengthC) := by
  rcases hT with hS | hT
  · have hnm : T.IsNonMixed := Or.inl hS
    have hside : IsNonNullLine T.A T.B := hnm.sidesNonNull.2.2
    have hd : |T.excenterDenomC| ≠ 0 := abs_ne_zero.mpr hC
    have hq : q (heightVec (T.excenterC hC) T.A T.B hside) =
        -(T.areaMagnitude * 2 / |T.excenterDenomC|) ^ 2 := by
      change T.exradiusSqC (Or.inl hS) hC = _
      have hsq : (T.exradiusSqC (Or.inl hS) hC : ℂ) =
          T.complexArea ^ 2 /
            (T.semiperimeterComplex - T.sideComplexLengthC) ^ 2 := by
        rw [← exradiusC_sq_eq_sideDistanceSq T (Or.inl hS) hC]
        exact exradiusC_sq_eq_complexArea_div_semiperimeter_sub_side_sq
          T (Or.inl hS) hC
      have hratio : T.complexArea ^ 2 /
          (T.semiperimeterComplex - T.sideComplexLengthC) ^ 2 =
          ((-T.signedDoubleArea ^ 2 / T.excenterDenomC ^ 2 : ℝ) : ℂ) := by
        rw [complexArea_sq, semiperimeterComplex_sub_sideC_spacelike hS]
        push_cast
        field_simp [hC]
        ring
      rw [hratio] at hsq
      have hreal := congrArg Complex.re hsq
      have hreal' : T.exradiusSqC (Or.inl hS) hC =
          -T.signedDoubleArea ^ 2 / T.excenterDenomC ^ 2 := by
        simpa only [Complex.ofReal_re] using hreal
      rw [hreal']
      unfold areaMagnitude at ⊢
      field_simp [hC, hd]
      have hD : |T.signedDoubleArea| ^ 2 = T.signedDoubleArea ^ 2 :=
        sq_abs T.signedDoubleArea
      rw [hD]
      have hd2 : |T.excenterDenomC| ^ 2 = T.excenterDenomC ^ 2 :=
        sq_abs T.excenterDenomC
      rw [hd2]
      ring
    have ha : 0 ≤ T.areaMagnitude := by
      unfold areaMagnitude
      positivity
    have hr : 0 ≤ T.areaMagnitude * 2 / |T.excenterDenomC| := by
      exact div_nonneg (mul_nonneg ha (by norm_num)) (abs_nonneg _)
    have hlen := complexLength_eq_I_mul_real_of_q_eq_neg_sq hr hq
    rw [exradiusC, pointLineDistance]
    change complexLength (heightVec (T.excenterC hC) T.A T.B hside) = _
    rw [hlen, complexArea,
      semiperimeterComplex_sub_sideC_spacelike hS]
    unfold areaMagnitude
    have hlam := lambdaC_mul_abs_denominator T
    have hlam' : T.lambdaC * |T.excenterDenomC| = T.excenterDenomC := by
      simpa [excenterDenomC, signedPerimeter] using hlam
    have hlamC : (T.lambdaC : ℂ) * ((|T.excenterDenomC| : ℝ) : ℂ) =
        (T.excenterDenomC : ℂ) := by
      exact_mod_cast hlam'
    have hlambda : (T.lambdaC : ℂ) =
        (T.excenterDenomC : ℂ) / ((|T.excenterDenomC| : ℝ) : ℂ) := by
      field_simp [hd]
      exact hlamC
    rw [hlambda]
    push_cast
    field_simp [hC, hd]
  · have hnm : T.IsNonMixed := Or.inr hT
    have hside : IsNonNullLine T.A T.B := hnm.sidesNonNull.2.2
    have hd : |T.excenterDenomC| ≠ 0 := abs_ne_zero.mpr hC
    have hq : q (heightVec (T.excenterC hC) T.A T.B hside) =
        (T.areaMagnitude * 2 / |T.excenterDenomC|) ^ 2 := by
      change T.exradiusSqC (Or.inr hT) hC = _
      have hsq : (T.exradiusSqC (Or.inr hT) hC : ℂ) =
          T.complexArea ^ 2 /
            (T.semiperimeterComplex - T.sideComplexLengthC) ^ 2 := by
        rw [← exradiusC_sq_eq_sideDistanceSq T (Or.inr hT) hC]
        exact exradiusC_sq_eq_complexArea_div_semiperimeter_sub_side_sq
          T (Or.inr hT) hC
      have hratio : T.complexArea ^ 2 /
          (T.semiperimeterComplex - T.sideComplexLengthC) ^ 2 =
          ((T.signedDoubleArea ^ 2 / T.excenterDenomC ^ 2 : ℝ) : ℂ) := by
        rw [complexArea_sq, semiperimeterComplex_sub_sideC_timelike hT]
        rw [mul_pow, pow_two Complex.I, Complex.I_mul_I]
        push_cast
        field_simp [hC]
        ring
      rw [hratio] at hsq
      have hreal := congrArg Complex.re hsq
      have hreal' : T.exradiusSqC (Or.inr hT) hC =
          T.signedDoubleArea ^ 2 / T.excenterDenomC ^ 2 := by
        simpa only [Complex.ofReal_re] using hreal
      rw [hreal']
      unfold areaMagnitude at ⊢
      field_simp [hC, hd]
      have hD : |T.signedDoubleArea| ^ 2 = T.signedDoubleArea ^ 2 :=
        sq_abs T.signedDoubleArea
      rw [hD]
      have hd2 : |T.excenterDenomC| ^ 2 = T.excenterDenomC ^ 2 :=
        sq_abs T.excenterDenomC
      rw [hd2]
      ring
    have ha : 0 ≤ T.areaMagnitude := by
      unfold areaMagnitude
      positivity
    have hr : 0 ≤ T.areaMagnitude * 2 / |T.excenterDenomC| := by
      exact div_nonneg (mul_nonneg ha (by norm_num)) (abs_nonneg _)
    have hlen := complexLength_eq_real_of_q_eq_sq hr hq
    rw [exradiusC, pointLineDistance]
    change complexLength (heightVec (T.excenterC hC) T.A T.B hside) = _
    rw [hlen, complexArea,
      semiperimeterComplex_sub_sideC_timelike hT]
    unfold areaMagnitude
    have hlam := lambdaC_mul_abs_denominator T
    have hlam' : T.lambdaC * |T.excenterDenomC| = T.excenterDenomC := by
      simpa [excenterDenomC, signedPerimeter] using hlam
    have hlamC : (T.lambdaC : ℂ) * ((|T.excenterDenomC| : ℝ) : ℂ) =
        (T.excenterDenomC : ℂ) := by
      exact_mod_cast hlam'
    have hlambda : (T.lambdaC : ℂ) =
        (T.excenterDenomC : ℂ) / ((|T.excenterDenomC| : ℝ) : ℂ) := by
      field_simp [hd]
      exact hlamC
    rw [hlambda]
    push_cast
    field_simp [hC, hd, Complex.I_ne_zero]

theorem q_mul_br_sq_identity (x u v : Vec) :
    q x * br u v ^ 2 =
      -(dot x u) ^ 2 * q v - (dot x v) ^ 2 * q u +
        2 * dot x u * dot x v * dot u v := by
  simp only [q_apply, br_apply, dot_apply, Vec.x_sub, Vec.t_sub,
    Vec.x_add, Vec.t_add, Vec.x_smul, Vec.t_smul]
  ring

private theorem dot_sideVecC_intervalVec_AC (T : Triangle) :
    dot T.sideVecC (intervalVec T.A T.C) =
      (T.sideSqB + T.sideSqC - T.sideSqA) / 2 := by
  simp only [sideVecA, sideVecB, sideVecC, sideSqA, sideSqB, sideSqC,
    intervalVec, vsub_eq_sub, intervalSq, dot_apply, q_apply, br_apply,
    Vec.x_sub, Vec.t_sub]
  ring

private theorem q_intervalVec_AC (T : Triangle) :
    q (intervalVec T.A T.C) = T.sideSqB := by
  simp only [sideVecB, sideSqB, intervalVec, vsub_eq_sub, intervalSq, q_apply,
    Vec.x_sub, Vec.t_sub]
  ring

theorem circumradiusSq_eq_sideSq_product_div_areaSq
    (T : Triangle) (hT : T.Nondegenerate) :
    T.circumradiusSqAt (T.circumcenter hT) =
      -(T.sideSqA * T.sideSqB * T.sideSqC) /
        (4 * T.signedDoubleArea ^ 2) := by
  have hΔ : T.signedDoubleArea ≠ 0 := hT.signedDoubleArea_ne_zero
  have hq : q (T.circumcenterOffset hT) * T.signedDoubleArea ^ 2 =
      -(T.sideSqA * T.sideSqB * T.sideSqC) / 4 := by
    have hident := q_mul_br_sq_identity (T.circumcenterOffset hT)
      T.sideVecC (intervalVec T.A T.C)
    rw [show br T.sideVecC (intervalVec T.A T.C) = T.signedDoubleArea by
      rfl,
      dot_circumcenterOffset_sideVecC T hT,
      dot_circumcenterOffset_AC T hT,
      ← sideSqC_eq_q T, q_intervalVec_AC T,
      dot_sideVecC_intervalVec_AC T] at hident
    convert hident using 1 <;> ring
  have hcenter : T.circumradiusSqAt (T.circumcenter hT) =
      q (T.circumcenterOffset hT) := by
    rw [circumradiusSqAt, circumcenter]
    simp [intervalSq, intervalVec, vadd_eq_add, q_neg]
  rw [hcenter]
  field_simp [hΔ]
  nlinarith [hq]

end

end Triangle
end MinkowskiMerge
