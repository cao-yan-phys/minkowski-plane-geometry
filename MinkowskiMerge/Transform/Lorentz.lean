import MinkowskiMerge.Affine
import MinkowskiMerge.Orthogonal
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv


set_option autoImplicit false

namespace MinkowskiMerge

abbrev LorentzEquiv := lorentzQ.IsometryEquiv lorentzQ

namespace LorentzEquiv

@[simp] theorem q_map (L : LorentzEquiv) (v : Vec) : q (L v) = q v := by
  exact L.map_app v

theorem dot_map (L : LorentzEquiv) (v w : Vec) :
    dot (L v) (L w) = dot v w := by
  have hsum := L.q_map (v + w)
  rw [map_add, q_add, q_add, L.q_map, L.q_map] at hsum
  linarith

theorem isOrthogonal_map (L : LorentzEquiv) (v w : Vec) :
    (L v) ⟂ₘ (L w) ↔ v ⟂ₘ w := by
  simp only [isOrthogonal_iff_dot_eq_zero, L.dot_map]

theorem br_sq_map (L : LorentzEquiv) (v w : Vec) :
    br (L v) (L w) ^ 2 = br v w ^ 2 := by
  have h := gram_identity (L v) (L w)
  rw [L.dot_map, L.q_map, L.q_map] at h
  exact h.symm.trans (gram_identity v w)

@[simp] theorem isTimelike_map (L : LorentzEquiv) (v : Vec) :
    IsTimelike (L v) ↔ IsTimelike v := by
  change q (L v) < 0 ↔ q v < 0
  rw [L.q_map]

@[simp] theorem isNull_map (L : LorentzEquiv) (v : Vec) :
    IsNull (L v) ↔ IsNull v := by
  change q (L v) = 0 ↔ q v = 0
  rw [L.q_map]

@[simp] theorem isSpacelike_map (L : LorentzEquiv) (v : Vec) :
    IsSpacelike (L v) ↔ IsSpacelike v := by
  change 0 < q (L v) ↔ 0 < q v
  rw [L.q_map]

@[simp] theorem isCausal_map (L : LorentzEquiv) (v : Vec) :
    IsCausal (L v) ↔ IsCausal v := by
  change q (L v) ≤ 0 ↔ q v ≤ 0
  rw [L.q_map]

@[simp] theorem causalType_map (L : LorentzEquiv) (v : Vec) :
    causalType (L v) = causalType v := by
  unfold causalType
  rw [L.q_map]

@[simp] theorem absLength_map (L : LorentzEquiv) (v : Vec) :
    absLength (L v) = absLength v := by
  unfold absLength
  rw [L.q_map]

@[simp] theorem complexLength_map (L : LorentzEquiv) (v : Vec) :
    complexLength (L v) = complexLength v := by
  unfold complexLength
  rw [L.q_map]

theorem intervalVec_map (L : LorentzEquiv) (P Q : Point) :
    intervalVec (L P) (L Q) = L (intervalVec P Q) := by
  simpa only [intervalVec] using (map_sub L Q P).symm

@[simp] theorem intervalSq_map (L : LorentzEquiv) (P Q : Point) :
    intervalSq (L P) (L Q) = intervalSq P Q := by
  rw [intervalSq, intervalSq, L.intervalVec_map, L.q_map]

end LorentzEquiv

noncomputable def boostLinearMap (η : ℝ) : Vec →ₗ[ℝ] Vec where
  toFun v :=
    (Real.cosh η * v.x + Real.sinh η * v.t,
      Real.sinh η * v.x + Real.cosh η * v.t)
  map_add' v w := by
    ext <;> simp <;> ring
  map_smul' r v := by
    ext <;> simp <;> ring

@[simp] theorem boostLinearMap_apply (η : ℝ) (v : Vec) :
    boostLinearMap η v =
      (Real.cosh η * v.x + Real.sinh η * v.t,
        Real.sinh η * v.x + Real.cosh η * v.t) := rfl

theorem boostLinearMap_add_apply (η θ : ℝ) (v : Vec) :
    boostLinearMap η (boostLinearMap θ v) = boostLinearMap (η + θ) v := by
  ext <;>
    simp only [boostLinearMap_apply, Vec.x_mk, Vec.t_mk, Real.cosh_add, Real.sinh_add] <;>
    ring

@[simp] theorem boostLinearMap_zero_apply (v : Vec) : boostLinearMap 0 v = v := by
  ext <;> simp

noncomputable def boostLinearEquiv (η : ℝ) : Vec ≃ₗ[ℝ] Vec :=
  LinearEquiv.mk (boostLinearMap η) (boostLinearMap (-η))
    (by
      intro v
      change boostLinearMap (-η) (boostLinearMap η v) = v
      rw [boostLinearMap_add_apply, neg_add_cancel, boostLinearMap_zero_apply])
    (by
      intro v
      change boostLinearMap η (boostLinearMap (-η) v) = v
      rw [boostLinearMap_add_apply, add_neg_cancel, boostLinearMap_zero_apply])

@[simp] theorem boostLinearEquiv_apply (η : ℝ) (v : Vec) :
    boostLinearEquiv η v = boostLinearMap η v := rfl

noncomputable def boostIsometry (η : ℝ) : LorentzEquiv where
  toLinearEquiv := boostLinearEquiv η
  map_app' v := by
    change q (boostLinearMap η v) = q v
    simp only [boostLinearMap_apply, q_apply, Vec.x_mk, Vec.t_mk]
    have h := Real.cosh_sq_sub_sinh_sq η
    calc
      (Real.cosh η * v.x + Real.sinh η * v.t) ^ 2 -
          (Real.sinh η * v.x + Real.cosh η * v.t) ^ 2 =
          (Real.cosh η ^ 2 - Real.sinh η ^ 2) * (v.x ^ 2 - v.t ^ 2) := by ring
      _ = v.x ^ 2 - v.t ^ 2 := by rw [h, one_mul]

@[simp] theorem boostIsometry_apply (η : ℝ) (v : Vec) :
    boostIsometry η v = boostLinearMap η v := rfl

@[simp] theorem boostIsometry_zero_apply (v : Vec) : boostIsometry 0 v = v := by
  exact boostLinearMap_zero_apply v

theorem boostIsometry_add_apply (η θ : ℝ) (v : Vec) :
    boostIsometry η (boostIsometry θ v) = boostIsometry (η + θ) v := by
  exact boostLinearMap_add_apply η θ v

@[simp] theorem boostIsometry_neg_apply (η : ℝ) (v : Vec) :
    boostIsometry (-η) (boostIsometry η v) = v := by
  rw [boostIsometry_add_apply, neg_add_cancel, boostIsometry_zero_apply]

@[simp] theorem boostIsometry_apply_neg (η : ℝ) (v : Vec) :
    boostIsometry η (boostIsometry (-η) v) = v := by
  rw [boostIsometry_add_apply, add_neg_cancel, boostIsometry_zero_apply]

theorem br_boostIsometry (η : ℝ) (v w : Vec) :
    br (boostIsometry η v) (boostIsometry η w) = br v w := by
  simp only [boostIsometry_apply, boostLinearMap_apply, br_apply,
    Vec.x_mk, Vec.t_mk]
  have h := Real.cosh_sq_sub_sinh_sq η
  calc
    (Real.cosh η * v.x + Real.sinh η * v.t) *
          (Real.sinh η * w.x + Real.cosh η * w.t) -
        (Real.sinh η * v.x + Real.cosh η * v.t) *
          (Real.cosh η * w.x + Real.sinh η * w.t) =
        (Real.cosh η ^ 2 - Real.sinh η ^ 2) *
          (v.x * w.t - v.t * w.x) := by ring
    _ = v.x * w.t - v.t * w.x := by rw [h, one_mul]

end MinkowskiMerge
