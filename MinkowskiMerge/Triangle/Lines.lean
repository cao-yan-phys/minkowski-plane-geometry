import MinkowskiMerge.Triangle.Metric


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

def sideLineA (T : Triangle) : Line := lineThrough T.B T.C

def sideLineB (T : Triangle) : Line := lineThrough T.C T.A

def sideLineC (T : Triangle) : Line := lineThrough T.A T.B

def altitudeA (T : Triangle) : Line := perpendicularThrough T.A T.sideVecA

def altitudeB (T : Triangle) : Line := perpendicularThrough T.B T.sideVecB

def altitudeC (T : Triangle) : Line := perpendicularThrough T.C T.sideVecC

@[simp] theorem A_mem_altitudeA (T : Triangle) : T.A ∈ T.altitudeA := by
  exact self_mem_perpendicularThrough _ _

@[simp] theorem B_mem_altitudeB (T : Triangle) : T.B ∈ T.altitudeB := by
  exact self_mem_perpendicularThrough _ _

@[simp] theorem C_mem_altitudeC (T : Triangle) : T.C ∈ T.altitudeC := by
  exact self_mem_perpendicularThrough _ _

theorem mem_altitudeA_iff {T : Triangle} {X : Point} :
    X ∈ T.altitudeA ↔ intervalVec T.A X ⟂ₘ T.sideVecA :=
  mem_perpendicularThrough_iff

theorem mem_altitudeB_iff {T : Triangle} {X : Point} :
    X ∈ T.altitudeB ↔ intervalVec T.B X ⟂ₘ T.sideVecB :=
  mem_perpendicularThrough_iff

theorem mem_altitudeC_iff {T : Triangle} {X : Point} :
    X ∈ T.altitudeC ↔ intervalVec T.C X ⟂ₘ T.sideVecC :=
  mem_perpendicularThrough_iff

noncomputable def footA (T : Triangle) (hA : T.sideSqA ≠ 0) : Point :=
  perpendicularFoot T.A T.B T.C hA

noncomputable def footB (T : Triangle) (hB : T.sideSqB ≠ 0) : Point :=
  perpendicularFoot T.B T.C T.A hB

noncomputable def footC (T : Triangle) (hC : T.sideSqC ≠ 0) : Point :=
  perpendicularFoot T.C T.A T.B hC

theorem footA_mem_sideLine (T : Triangle) (hA : T.sideSqA ≠ 0) :
    T.footA hA ∈ T.sideLineA :=
  perpendicularFoot_mem_line _ _ _ hA

theorem footB_mem_sideLine (T : Triangle) (hB : T.sideSqB ≠ 0) :
    T.footB hB ∈ T.sideLineB :=
  perpendicularFoot_mem_line _ _ _ hB

theorem footC_mem_sideLine (T : Triangle) (hC : T.sideSqC ≠ 0) :
    T.footC hC ∈ T.sideLineC :=
  perpendicularFoot_mem_line _ _ _ hC

theorem footA_mem_altitude (T : Triangle) (hA : T.sideSqA ≠ 0) :
    T.footA hA ∈ T.altitudeA := by
  rw [mem_altitudeA_iff]
  exact perpendicularFoot_orthogonal _ _ _ hA

theorem footB_mem_altitude (T : Triangle) (hB : T.sideSqB ≠ 0) :
    T.footB hB ∈ T.altitudeB := by
  rw [mem_altitudeB_iff]
  exact perpendicularFoot_orthogonal _ _ _ hB

theorem footC_mem_altitude (T : Triangle) (hC : T.sideSqC ≠ 0) :
    T.footC hC ∈ T.altitudeC := by
  rw [mem_altitudeC_iff]
  exact perpendicularFoot_orthogonal _ _ _ hC

noncomputable def heightVecA (T : Triangle) (hA : T.sideSqA ≠ 0) : Vec :=
  MinkowskiMerge.heightVec T.A T.B T.C hA

noncomputable def heightVecB (T : Triangle) (hB : T.sideSqB ≠ 0) : Vec :=
  MinkowskiMerge.heightVec T.B T.C T.A hB

noncomputable def heightVecC (T : Triangle) (hC : T.sideSqC ≠ 0) : Vec :=
  MinkowskiMerge.heightVec T.C T.A T.B hC

noncomputable def heightSqA (T : Triangle) (hA : T.sideSqA ≠ 0) : ℝ :=
  q (T.heightVecA hA)

noncomputable def heightSqB (T : Triangle) (hB : T.sideSqB ≠ 0) : ℝ :=
  q (T.heightVecB hB)

noncomputable def heightSqC (T : Triangle) (hC : T.sideSqC ≠ 0) : ℝ :=
  q (T.heightVecC hC)

theorem heightSqA_eq_neg_area_sq_div_sideSq (T : Triangle)
    (hA : T.sideSqA ≠ 0) :
    T.heightSqA hA = -T.signedDoubleArea ^ 2 / T.sideSqA := by
  exact heightSq_eq_neg_area_sq_div_intervalSq T.A T.B T.C hA

theorem heightSqB_eq_neg_area_sq_div_sideSq (T : Triangle)
    (hB : T.sideSqB ≠ 0) :
    T.heightSqB hB = -T.signedDoubleArea ^ 2 / T.sideSqB := by
  rw [heightSqB, heightVecB]
  simpa only [sideSqB, signedDoubleArea_cyclic T] using
    heightSq_eq_neg_area_sq_div_intervalSq T.B T.C T.A hB

theorem heightSqC_eq_neg_area_sq_div_sideSq (T : Triangle)
    (hC : T.sideSqC ≠ 0) :
    T.heightSqC hC = -T.signedDoubleArea ^ 2 / T.sideSqC := by
  rw [heightSqC, heightVecC]
  simpa only [sideSqC, signedDoubleArea_cyclic_two T] using
    heightSq_eq_neg_area_sq_div_intervalSq T.C T.A T.B hC

def IsOrthocenter (T : Triangle) (H : Point) : Prop :=
  H ∈ T.altitudeA ∧ H ∈ T.altitudeB ∧ H ∈ T.altitudeC

theorem isOrthocenter_iff {T : Triangle} {H : Point} :
    T.IsOrthocenter H ↔
      intervalVec T.A H ⟂ₘ T.sideVecA ∧
      intervalVec T.B H ⟂ₘ T.sideVecB ∧
      intervalVec T.C H ⟂ₘ T.sideVecC := by
  simp only [IsOrthocenter, mem_altitudeA_iff, mem_altitudeB_iff, mem_altitudeC_iff]

theorem isOrthocenter_of_mem_altitudeA_altitudeB {T : Triangle} {H : Point}
    (hA : H ∈ T.altitudeA) (hB : H ∈ T.altitudeB) : T.IsOrthocenter H := by
  refine ⟨hA, hB, ?_⟩
  rw [mem_altitudeA_iff, isOrthogonal_iff_dot_eq_zero] at hA
  rw [mem_altitudeB_iff, isOrthogonal_iff_dot_eq_zero] at hB
  rw [mem_altitudeC_iff, isOrthogonal_iff_dot_eq_zero]
  simp only [sideVecA, sideVecB, sideVecC, intervalVec, vsub_eq_sub,
    dot_apply, Vec.x_sub, Vec.t_sub] at hA hB ⊢
  ring_nf at hA hB ⊢
  linarith

end Triangle
end MinkowskiMerge
