import MinkowskiMerge.Triangle.Lines


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

def IsCircumcenter (T : Triangle) (O : Point) : Prop :=
  intervalSq O T.A = intervalSq O T.B ∧
    intervalSq O T.B = intervalSq O T.C

def circumradiusSqAt (T : Triangle) (O : Point) : ℝ := intervalSq O T.A

def orthocenterFromCircumcenter (T : Triangle) (O : Point) : Point :=
  (intervalVec O T.A + intervalVec O T.B + intervalVec O T.C) +ᵥ O

def orthocenterAtOrigin (T : Triangle) : Point :=
  T.orthocenterFromCircumcenter 0

def IsCircumcenterAtOrigin (T : Triangle) : Prop := T.IsCircumcenter 0

noncomputable def circumcenterOffset (T : Triangle) (_hT : T.Nondegenerate) : Vec :=
  let u := T.sideVecC
  let v := intervalVec T.A T.C
  let Δ := T.signedDoubleArea
  (q u / (2 * Δ)) • J v - (q v / (2 * Δ)) • J u

noncomputable def circumcenter (T : Triangle) (hT : T.Nondegenerate) : Point :=
  T.circumcenterOffset hT +ᵥ T.A

noncomputable def orthocenter (T : Triangle) (hT : T.Nondegenerate) : Point :=
  T.orthocenterFromCircumcenter (T.circumcenter hT)

theorem dot_circumcenterOffset_sideVecC (T : Triangle) (hT : T.Nondegenerate) :
    dot (T.circumcenterOffset hT) T.sideVecC = q T.sideVecC / 2 := by
  have hΔ : T.signedDoubleArea ≠ 0 := hT.signedDoubleArea_ne_zero
  rw [circumcenterOffset]
  simp only [dot_sub_left, dot_smul_left, dot_J_left, br_self, neg_zero,
    mul_zero, sub_zero]
  rw [← br_swap (intervalVec T.A T.C) T.sideVecC]
  rw [show br T.sideVecC (intervalVec T.A T.C) = T.signedDoubleArea by rfl]
  field_simp [hΔ]

theorem dot_circumcenterOffset_AC (T : Triangle) (hT : T.Nondegenerate) :
    dot (T.circumcenterOffset hT) (intervalVec T.A T.C) =
      q (intervalVec T.A T.C) / 2 := by
  have hΔ : T.signedDoubleArea ≠ 0 := hT.signedDoubleArea_ne_zero
  rw [circumcenterOffset]
  simp only [dot_sub_left, dot_smul_left, dot_J_left, br_self, neg_zero,
    mul_zero, zero_sub]
  rw [show br T.sideVecC (intervalVec T.A T.C) = T.signedDoubleArea by rfl]
  field_simp [hΔ]

private theorem intervalSq_vadd_eq_of_two_dot_eq_q (A B : Point) (x : Vec)
    (h : 2 * dot x (intervalVec A B) = q (intervalVec A B)) :
    intervalSq (x +ᵥ A) A = intervalSq (x +ᵥ A) B := by
  have hA : intervalVec (x +ᵥ A) A = -x := by
    simp [intervalVec, vadd_eq_add]
  have hB : intervalVec (x +ᵥ A) B = intervalVec A B - x := by
    simp only [intervalVec, vsub_eq_sub, vadd_eq_add]
    module
  rw [intervalSq, intervalSq, hA, hB, q_neg, q_sub, dot_comm]
  linarith

theorem circumcenter_isCircumcenter (T : Triangle) (hT : T.Nondegenerate) :
    T.IsCircumcenter (T.circumcenter hT) := by
  have hAB : intervalSq (T.circumcenter hT) T.A =
      intervalSq (T.circumcenter hT) T.B := by
    apply intervalSq_vadd_eq_of_two_dot_eq_q
    have hdot := dot_circumcenterOffset_sideVecC T hT
    change 2 * dot (T.circumcenterOffset hT) T.sideVecC = q T.sideVecC
    linarith
  have hAC : intervalSq (T.circumcenter hT) T.A =
      intervalSq (T.circumcenter hT) T.C := by
    apply intervalSq_vadd_eq_of_two_dot_eq_q
    have hdot := dot_circumcenterOffset_AC T hT
    linarith
  exact ⟨hAB, hAB.symm.trans hAC⟩

theorem IsCircumcenter.intervalSq_A_eq_C {T : Triangle} {O : Point}
    (hO : T.IsCircumcenter O) : intervalSq O T.A = intervalSq O T.C :=
  hO.1.trans hO.2

@[simp] theorem intervalSq_A_eq_radius (T : Triangle) (O : Point) :
    intervalSq O T.A = T.circumradiusSqAt O := rfl

theorem IsCircumcenter.intervalSq_B_eq_radius {T : Triangle} {O : Point}
    (hO : T.IsCircumcenter O) : intervalSq O T.B = T.circumradiusSqAt O := by
  exact hO.1.symm

theorem IsCircumcenter.intervalSq_C_eq_radius {T : Triangle} {O : Point}
    (hO : T.IsCircumcenter O) : intervalSq O T.C = T.circumradiusSqAt O := by
  exact hO.intervalSq_A_eq_C.symm

theorem intervalVec_A_orthocenterFromCircumcenter (T : Triangle) (O : Point) :
    intervalVec T.A (T.orthocenterFromCircumcenter O) =
      intervalVec O T.B + intervalVec O T.C := by
  simp only [orthocenterFromCircumcenter, intervalVec, vsub_eq_sub, vadd_eq_add]
  module

theorem intervalVec_B_orthocenterFromCircumcenter (T : Triangle) (O : Point) :
    intervalVec T.B (T.orthocenterFromCircumcenter O) =
      intervalVec O T.C + intervalVec O T.A := by
  simp only [orthocenterFromCircumcenter, intervalVec, vsub_eq_sub, vadd_eq_add]
  module

theorem intervalVec_C_orthocenterFromCircumcenter (T : Triangle) (O : Point) :
    intervalVec T.C (T.orthocenterFromCircumcenter O) =
      intervalVec O T.A + intervalVec O T.B := by
  simp only [orthocenterFromCircumcenter, intervalVec, vsub_eq_sub, vadd_eq_add]
  module

theorem orthocenterFromCircumcenter_apply (T : Triangle) (O : Point) :
    T.orthocenterFromCircumcenter O = T.A + T.B + T.C - (2 : ℝ) • O := by
  simp only [orthocenterFromCircumcenter, intervalVec, vsub_eq_sub, vadd_eq_add]
  module

theorem orthocenterFromCircumcenter_isOrthocenter (T : Triangle) (O : Point)
    (hO : T.IsCircumcenter O) :
    T.IsOrthocenter (T.orthocenterFromCircumcenter O) := by
  rw [isOrthocenter_iff]
  constructor
  · rw [intervalVec_A_orthocenterFromCircumcenter,
      show T.sideVecA = intervalVec O T.C - intervalVec O T.B by
        exact intervalVec_eq_sub_from O T.B T.C,
      isOrthogonal_iff_dot_eq_zero,
      dot_add_sub_self]
    exact sub_eq_zero.mpr hO.2.symm
  constructor
  · rw [intervalVec_B_orthocenterFromCircumcenter,
      show T.sideVecB = intervalVec O T.A - intervalVec O T.C by
        exact intervalVec_eq_sub_from O T.C T.A,
      isOrthogonal_iff_dot_eq_zero,
      dot_add_sub_self]
    exact sub_eq_zero.mpr hO.intervalSq_A_eq_C
  · rw [intervalVec_C_orthocenterFromCircumcenter,
      show T.sideVecC = intervalVec O T.B - intervalVec O T.A by
        exact intervalVec_eq_sub_from O T.A T.B,
      isOrthogonal_iff_dot_eq_zero,
      dot_add_sub_self]
    exact sub_eq_zero.mpr hO.1.symm

theorem IsOrthocenter.unique {T : Triangle} (hT : T.Nondegenerate)
    {H K : Point} (hH : T.IsOrthocenter H) (hK : T.IsOrthocenter K) : H = K := by
  rw [isOrthocenter_iff] at hH hK
  let d : Vec := intervalVec K H
  have hHC := hH.2.2
  have hKC := hK.2.2
  have hHB := hH.2.1
  have hKB := hK.2.1
  have hdC : d ⟂ₘ T.sideVecC := by
    rw [isOrthogonal_iff_dot_eq_zero]
    rw [isOrthogonal_iff_dot_eq_zero] at hHC hKC
    rw [show d = intervalVec T.C H - intervalVec T.C K by
      exact intervalVec_eq_sub_from T.C K H]
    simp only [dot_apply, Vec.x_sub, Vec.t_sub] at hHC hKC ⊢
    ring_nf at hHC hKC ⊢
    linarith
  have hdB : d ⟂ₘ T.sideVecB := by
    rw [isOrthogonal_iff_dot_eq_zero]
    rw [isOrthogonal_iff_dot_eq_zero] at hHB hKB
    rw [show d = intervalVec T.B H - intervalVec T.B K by
      exact intervalVec_eq_sub_from T.B K H]
    simp only [dot_apply, Vec.x_sub, Vec.t_sub] at hHB hKB ⊢
    ring_nf at hHB hKB ⊢
    linarith
  have hdAC : d ⟂ₘ intervalVec T.A T.C := by
    rw [isOrthogonal_iff_dot_eq_zero] at hdB ⊢
    rw [sideVecB, intervalVec_rev T.A T.C] at hdB
    simp only [dot_apply, Vec.x_neg, Vec.t_neg] at hdB ⊢
    linarith
  have hbr : br T.sideVecC (intervalVec T.A T.C) ≠ 0 := by
    simpa only [sideVecC, Triangle.signedDoubleArea,
      MinkowskiMerge.signedDoubleArea] using hT.signedDoubleArea_ne_zero
  have hd0 : d = 0 := eq_zero_of_orthogonal_pair hdC hdAC hbr
  simpa only [d, intervalVec, vsub_eq_sub, sub_eq_zero] using hd0

theorem IsCircumcenter.unique {T : Triangle} (hT : T.Nondegenerate)
    {O O' : Point} (hO : T.IsCircumcenter O) (hO' : T.IsCircumcenter O') : O = O' := by
  have hH : T.orthocenterFromCircumcenter O = T.orthocenterFromCircumcenter O' :=
    IsOrthocenter.unique hT
      (orthocenterFromCircumcenter_isOrthocenter T O hO)
      (orthocenterFromCircumcenter_isOrthocenter T O' hO')
  rw [orthocenterFromCircumcenter_apply, orthocenterFromCircumcenter_apply] at hH
  apply Vec.ext
  · have hx := congrArg Vec.x hH
    simp only [Vec.x_sub, Vec.x_add, Vec.x_smul] at hx
    linarith
  · have ht := congrArg Vec.t hH
    simp only [Vec.t_sub, Vec.t_add, Vec.t_smul] at ht
    linarith

theorem IsCircumcenter.eq_circumcenter {T : Triangle} (hT : T.Nondegenerate)
    {O : Point} (hO : T.IsCircumcenter O) : O = T.circumcenter hT := by
  exact hO.unique hT (circumcenter_isCircumcenter T hT)

theorem orthocenter_isOrthocenter (T : Triangle) (hT : T.Nondegenerate) :
    T.IsOrthocenter (T.orthocenter hT) := by
  exact orthocenterFromCircumcenter_isOrthocenter T (T.circumcenter hT)
    (circumcenter_isCircumcenter T hT)

theorem IsOrthocenter.eq_orthocenter {T : Triangle} (hT : T.Nondegenerate)
    {H : Point} (hH : T.IsOrthocenter H) : H = T.orthocenter hT := by
  exact hH.unique hT (orthocenter_isOrthocenter T hT)

theorem circumcenter_eq_zero_of_isCircumcenterAtOrigin (T : Triangle)
    (hT : T.Nondegenerate) (hO : T.IsCircumcenterAtOrigin) :
    T.circumcenter hT = 0 := by
  exact (IsCircumcenter.eq_circumcenter hT hO).symm

theorem orthocenter_eq_orthocenterAtOrigin (T : Triangle)
    (hT : T.Nondegenerate) (hO : T.IsCircumcenterAtOrigin) :
    T.orthocenter hT = T.orthocenterAtOrigin := by
  rw [orthocenter, circumcenter_eq_zero_of_isCircumcenterAtOrigin T hT hO]
  rfl

@[simp] theorem orthocenterAtOrigin_apply (T : Triangle) :
    T.orthocenterAtOrigin = T.A + T.B + T.C := by
  rw [orthocenterAtOrigin, orthocenterFromCircumcenter_apply]
  simp

theorem isCircumcenterAtOrigin_iff (T : Triangle) :
    T.IsCircumcenterAtOrigin ↔ q T.A = q T.B ∧ q T.B = q T.C := by
  simp only [IsCircumcenterAtOrigin, IsCircumcenter, intervalSq, intervalVec,
    vsub_eq_sub, sub_zero]

theorem orthocenterAtOrigin_isOrthocenter (T : Triangle)
    (hO : T.IsCircumcenterAtOrigin) : T.IsOrthocenter T.orthocenterAtOrigin := by
  exact orthocenterFromCircumcenter_isOrthocenter T 0 hO

end Triangle
end MinkowskiMerge
