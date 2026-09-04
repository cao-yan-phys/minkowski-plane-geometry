import MinkowskiMerge.DirectionRotation
import MinkowskiMerge.Triangle.Metric


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

def euclideanRotationNonmixed (T : Triangle) (rho : ℝ) : Prop :=
  vectorTripleNonmixed T.sideVecA T.sideVecB T.sideVecC rho

theorem br_sideVecA_sideVecB (T : Triangle) :
    br T.sideVecA T.sideVecB = T.signedDoubleArea := by
  simp only [sideVecA, sideVecB, signedDoubleArea,
    MinkowskiMerge.signedDoubleArea, intervalVec, vsub_eq_sub, br_apply,
    Vec.x_sub, Vec.t_sub]
  ring

theorem br_sideVecB_sideVecC (T : Triangle) :
    br T.sideVecB T.sideVecC = T.signedDoubleArea := by
  simp only [sideVecB, sideVecC, signedDoubleArea,
    MinkowskiMerge.signedDoubleArea, intervalVec, vsub_eq_sub, br_apply,
    Vec.x_sub, Vec.t_sub]
  ring

theorem br_sideVecC_sideVecA (T : Triangle) :
    br T.sideVecC T.sideVecA = T.signedDoubleArea := by
  simp only [sideVecC, sideVecA, signedDoubleArea,
    MinkowskiMerge.signedDoubleArea, intervalVec, vsub_eq_sub, br_apply,
    Vec.x_sub, Vec.t_sub]
  ring

theorem Nondegenerate.br_sideVecA_sideVecB_ne_zero {T : Triangle}
    (hT : T.Nondegenerate) : br T.sideVecA T.sideVecB ≠ 0 := by
  rw [br_sideVecA_sideVecB]
  exact (nondegenerate_iff_signedDoubleArea_ne_zero T).mp hT

theorem Nondegenerate.br_sideVecB_sideVecC_ne_zero {T : Triangle}
    (hT : T.Nondegenerate) : br T.sideVecB T.sideVecC ≠ 0 := by
  rw [br_sideVecB_sideVecC]
  exact (nondegenerate_iff_signedDoubleArea_ne_zero T).mp hT

theorem Nondegenerate.br_sideVecC_sideVecA_ne_zero {T : Triangle}
    (hT : T.Nondegenerate) : br T.sideVecC T.sideVecA ≠ 0 := by
  rw [br_sideVecC_sideVecA]
  exact (nondegenerate_iff_signedDoubleArea_ne_zero T).mp hT

theorem Nondegenerate.side_direction_coordinates {T : Triangle}
    (hT : T.Nondegenerate) :
    ∃ sA a sB b sC c : ℝ,
      sA ≠ 0 ∧ sB ≠ 0 ∧ sC ≠ 0 ∧
      a ∈ Set.Ico 0 Real.pi ∧ b ∈ Set.Ico 0 Real.pi ∧ c ∈ Set.Ico 0 Real.pi ∧
      T.sideVecA = sA • edir a ∧ T.sideVecB = sB • edir b ∧
        T.sideVecC = sC • edir c := by
  obtain ⟨sA, a, hsA, ha, hA⟩ :=
    euclidean_projective_polar_representation T.sideVecA hT.sideVecA_ne_zero
  obtain ⟨sB, b, hsB, hb, hB⟩ :=
    euclidean_projective_polar_representation T.sideVecB hT.sideVecB_ne_zero
  obtain ⟨sC, c, hsC, hc, hC⟩ :=
    euclidean_projective_polar_representation T.sideVecC hT.sideVecC_ne_zero
  exact ⟨sA, a, sB, b, sC, c, hsA, hsB, hsC, ha, hb, hc, hA, hB, hC⟩

theorem Nondegenerate.side_direction_order_cases {T : Triangle}
    (hT : T.Nondegenerate) :
    ∃ sA a sB b sC c : ℝ,
      sA ≠ 0 ∧ sB ≠ 0 ∧ sC ≠ 0 ∧
      a ∈ Set.Ico 0 Real.pi ∧ b ∈ Set.Ico 0 Real.pi ∧ c ∈ Set.Ico 0 Real.pi ∧
      T.sideVecA = sA • edir a ∧ T.sideVecB = sB • edir b ∧
        T.sideVecC = sC • edir c ∧
      ((a < b ∧ b < c) ∨ (a < c ∧ c < b) ∨
        (b < a ∧ a < c) ∨ (b < c ∧ c < a) ∨
          (c < a ∧ a < b) ∨ (c < b ∧ b < a)) := by
  obtain ⟨sA, a, sB, b, sC, c, hsA, hsB, hsC, ha, hb, hc, hA, hB, hC⟩ :=
    hT.side_direction_coordinates
  have hab : a ≠ b := by
    intro hab
    apply hT.br_sideVecA_sideVecB_ne_zero
    rw [hA, hB, hab]
    simp
    ring
  have hbc : b ≠ c := by
    intro hbc
    apply hT.br_sideVecB_sideVecC_ne_zero
    rw [hB, hC, hbc]
    simp
    ring
  have hca : c ≠ a := by
    intro hca
    apply hT.br_sideVecC_sideVecA_ne_zero
    rw [hC, hA, hca]
    simp
    ring
  exact ⟨sA, a, sB, b, sC, c, hsA, hsB, hsC, ha, hb, hc, hA, hB, hC,
    three_distinct_real_order_cases hab hbc hca⟩

theorem euclidean_rotation_criterion_of_direction_coordinates
    (T : Triangle) (a b c sA sB sC : ℝ)
    (hab : a < b) (hbc : b < c) (hca : c < a + Real.pi)
    (hsA : sA ≠ 0) (hsB : sB ≠ 0) (hsC : sC ≠ 0)
    (hA : T.sideVecA = sA • edir a)
    (hB : T.sideVecB = sB • edir b)
    (hC : T.sideVecC = sC • edir c) :
    (∃ rho, T.euclideanRotationNonmixed rho) ↔
      orderedDirectionObtuse a b c := by
  change (∃ rho, vectorTripleNonmixed T.sideVecA T.sideVecB T.sideVecC rho) ↔
    orderedDirectionObtuse a b c
  rw [hA, hB, hC]
  exact ordered_vector_rotation_criterion a b c sA sB sC
    hab hbc hca hsA hsB hsC

end Triangle
end MinkowskiMerge
