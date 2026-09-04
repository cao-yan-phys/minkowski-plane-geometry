import MinkowskiMerge.Circle


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable section

namespace LorentzCircle

theorem intervalVec_lineMap_left (O₁ O₂ : Point) (r : ℝ) :
    intervalVec O₁ (AffineMap.lineMap O₁ O₂ r) =
      r • intervalVec O₁ O₂ := by
  rw [AffineMap.lineMap_apply_module']
  simp only [intervalVec, vsub_eq_sub]
  module

theorem intervalVec_lineMap_right (O₁ O₂ : Point) (r : ℝ) :
    intervalVec O₂ (AffineMap.lineMap O₁ O₂ r) =
      (r - 1) • intervalVec O₁ O₂ := by
  rw [AffineMap.lineMap_apply_module']
  simp only [intervalVec, vsub_eq_sub]
  module

theorem isTangentAt_of_mem_of_lineMap (C₁ C₂ : LorentzCircle) (r : ℝ)
    (h₁ : AffineMap.lineMap C₁.center C₂.center r ∈ C₁)
    (h₂ : AffineMap.lineMap C₁.center C₂.center r ∈ C₂) :
    IsTangentAt C₁ C₂ (AffineMap.lineMap C₁.center C₂.center r) := by
  refine ⟨h₁, h₂, ?_⟩
  rw [intervalVec_lineMap_left, intervalVec_lineMap_right,
    br_smul_left, br_smul_right, br_self]
  ring

theorem isTangentAt_of_mem_of_collinear {C₁ C₂ : LorentzCircle} {P : Point}
    (h₁ : P ∈ C₁) (h₂ : P ∈ C₂)
    (hline : IsCollinear C₁.center C₂.center P) :
    IsTangentAt C₁ C₂ P := by
  rcases (mem_line_iff.mp hline) with ⟨r, hr⟩
  subst P
  exact isTangentAt_of_mem_of_lineMap C₁ C₂ r h₁ h₂

end LorentzCircle

end

end MinkowskiMerge
