import MinkowskiMerge.CircleTangency
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable section

namespace LorentzCircle

noncomputable def signedHomothety (C₁ C₂ : LorentzCircle)
    (ρ q : ℝ) : Point →ᵃ[ℝ] Point :=
  AffineMap.homothety C₁.center (q / ρ) +
    AffineMap.const ℝ Point (intervalVec C₁.center C₂.center)

@[simp] theorem signedHomothety_apply (C₁ C₂ : LorentzCircle)
    (ρ q : ℝ) (P : Point) :
    signedHomothety C₁ C₂ ρ q P =
      C₂.center + (q / ρ) • intervalVec C₁.center P := by
  change (q / ρ) • (P - C₁.center) + C₁.center +
      (C₂.center - C₁.center) =
    C₂.center + (q / ρ) • (P - C₁.center)
  module

@[simp] theorem signedHomothety_linear (C₁ C₂ : LorentzCircle)
    (ρ q : ℝ) :
    (signedHomothety C₁ C₂ ρ q).linear =
      (q / ρ) • LinearMap.id := by
  simp [signedHomothety]

@[simp] theorem intervalVec_signedHomothety (C₁ C₂ : LorentzCircle)
    (ρ q : ℝ) (P : Point) :
    intervalVec C₂.center (signedHomothety C₁ C₂ ρ q P) =
      (q / ρ) • intervalVec C₁.center P := by
  rw [signedHomothety_apply]
  simp [intervalVec]

@[simp] theorem intervalSq_signedHomothety (C₁ C₂ : LorentzCircle)
    (ρ q : ℝ) (P : Point) :
    intervalSq C₂.center (signedHomothety C₁ C₂ ρ q P) =
      (q / ρ) ^ 2 * intervalSq C₁.center P := by
  rw [intervalSq, intervalVec_signedHomothety, q_smul]
  rfl

structure SignedHomothetyData (C₁ C₂ : LorentzCircle)
    (ε ρ q : ℝ) : Prop where
  epsilon_ne_zero : ε ≠ 0
  rho_ne_zero : ρ ≠ 0
  q_ne_zero : q ≠ 0
  centerSq_eq : intervalSq C₁.center C₂.center = ε * (ρ - q) ^ 2
  left_radiusSq_eq : C₁.radiusSq = ε * ρ ^ 2
  right_radiusSq_eq : C₂.radiusSq = ε * q ^ 2

theorem SignedHomothetyData.symm {C₁ C₂ : LorentzCircle} {ε ρ q : ℝ}
    (h : SignedHomothetyData C₁ C₂ ε ρ q) :
    SignedHomothetyData C₂ C₁ ε q ρ := by
  refine
    { epsilon_ne_zero := h.epsilon_ne_zero
      rho_ne_zero := h.q_ne_zero
      q_ne_zero := h.rho_ne_zero
      centerSq_eq := ?_
      left_radiusSq_eq := h.right_radiusSq_eq
      right_radiusSq_eq := h.left_radiusSq_eq }
  rw [intervalSq_comm C₂.center C₁.center, h.centerSq_eq]
  ring

theorem SignedHomothetyData.mapsTo {C₁ C₂ : LorentzCircle} {ε ρ q : ℝ}
    (h : SignedHomothetyData C₁ C₂ ε ρ q) :
    Set.MapsTo (signedHomothety C₁ C₂ ρ q)
      {P | P ∈ C₁} {P | P ∈ C₂} := by
  intro P hP
  change intervalSq C₂.center (signedHomothety C₁ C₂ ρ q P) =
    C₂.radiusSq
  rw [intervalSq_signedHomothety]
  change intervalSq C₁.center P = C₁.radiusSq at hP
  rw [hP, h.left_radiusSq_eq, h.right_radiusSq_eq]
  field_simp [h.rho_ne_zero]

@[simp] theorem signedHomothety_reverse_apply
    (C₁ C₂ : LorentzCircle) (ρ q : ℝ)
    (hρ : ρ ≠ 0) (hq : q ≠ 0) (P : Point) :
    signedHomothety C₂ C₁ q ρ (signedHomothety C₁ C₂ ρ q P) = P := by
  rw [signedHomothety_apply, intervalVec_signedHomothety]
  rw [smul_smul]
  have hscale : (ρ / q) * (q / ρ) = 1 := by
    field_simp [hρ, hq]
  rw [hscale, one_smul]
  simp [intervalVec]

@[simp] theorem signedHomothety_forward_reverse_apply
    (C₁ C₂ : LorentzCircle) (ρ q : ℝ)
    (hρ : ρ ≠ 0) (hq : q ≠ 0) (P : Point) :
    signedHomothety C₁ C₂ ρ q (signedHomothety C₂ C₁ q ρ P) = P := by
  exact signedHomothety_reverse_apply C₂ C₁ q ρ hq hρ P

theorem signedHomothety_bijective (C₁ C₂ : LorentzCircle) (ρ q : ℝ)
    (hρ : ρ ≠ 0) (hq : q ≠ 0) :
    Function.Bijective (signedHomothety C₁ C₂ ρ q) := by
  constructor
  · intro P Q hPQ
    have h := congrArg (signedHomothety C₂ C₁ q ρ) hPQ
    rw [signedHomothety_reverse_apply C₁ C₂ ρ q hρ hq P,
      signedHomothety_reverse_apply C₁ C₂ ρ q hρ hq Q] at h
    exact h
  · intro P
    refine ⟨signedHomothety C₂ C₁ q ρ P, ?_⟩
    exact signedHomothety_forward_reverse_apply C₁ C₂ ρ q hρ hq P

noncomputable def signedHomothetyEquiv (C₁ C₂ : LorentzCircle)
    (ρ q : ℝ) (hρ : ρ ≠ 0) (hq : q ≠ 0) : Point ≃ᵃ[ℝ] Point :=
  AffineEquiv.ofBijective
    (signedHomothety_bijective C₁ C₂ ρ q hρ hq)

theorem SignedHomothetyData.image_cycle_eq {C₁ C₂ : LorentzCircle}
    {ε ρ q : ℝ} (h : SignedHomothetyData C₁ C₂ ε ρ q) :
    signedHomothety C₁ C₂ ρ q '' {P | P ∈ C₁} = {P | P ∈ C₂} := by
  apply Set.Subset.antisymm
  · rintro P ⟨Q, hQ, rfl⟩
    exact h.mapsTo hQ
  · intro P hP
    refine ⟨signedHomothety C₂ C₁ q ρ P, h.symm.mapsTo hP, ?_⟩
    exact signedHomothety_forward_reverse_apply C₁ C₂ ρ q
      h.rho_ne_zero h.q_ne_zero P

noncomputable def signedHomothetyFixedPoint (C₁ C₂ : LorentzCircle)
    (ρ q : ℝ) : Point :=
  AffineMap.lineMap C₁.center C₂.center (ρ / (ρ - q))

@[simp] theorem signedHomothety_fixedPoint (C₁ C₂ : LorentzCircle)
    (ρ q : ℝ) (hρ : ρ ≠ 0) (hd : ρ - q ≠ 0) :
    signedHomothety C₁ C₂ ρ q (signedHomothetyFixedPoint C₁ C₂ ρ q) =
      signedHomothetyFixedPoint C₁ C₂ ρ q := by
  apply Vec.ext
  · simp only [signedHomothety_apply, signedHomothetyFixedPoint,
      AffineMap.lineMap_apply_module', intervalVec, vsub_eq_sub,
      Vec.x_add, Vec.x_smul, Vec.x_sub]
    field_simp [hρ, hd]
    ring
  · simp only [signedHomothety_apply, signedHomothetyFixedPoint,
      AffineMap.lineMap_apply_module', intervalVec, vsub_eq_sub,
      Vec.t_add, Vec.t_smul, Vec.t_sub]
    field_simp [hρ, hd]
    ring

theorem intervalVec_signedHomothetyFixedPoint
    (C₁ C₂ : LorentzCircle) (ρ q : ℝ)
    (hρ : ρ ≠ 0) (hd : ρ - q ≠ 0) (P : Point) :
    intervalVec (signedHomothetyFixedPoint C₁ C₂ ρ q)
        (signedHomothety C₁ C₂ ρ q P) =
      (q / ρ) • intervalVec (signedHomothetyFixedPoint C₁ C₂ ρ q) P := by
  calc
    intervalVec (signedHomothetyFixedPoint C₁ C₂ ρ q)
        (signedHomothety C₁ C₂ ρ q P) =
        intervalVec
          (signedHomothety C₁ C₂ ρ q
            (signedHomothetyFixedPoint C₁ C₂ ρ q))
          (signedHomothety C₁ C₂ ρ q P) := by
            rw [signedHomothety_fixedPoint C₁ C₂ ρ q hρ hd]
    _ = (signedHomothety C₁ C₂ ρ q).linear
        (intervalVec (signedHomothetyFixedPoint C₁ C₂ ρ q) P) := by
          exact (AffineMap.linearMap_vsub (signedHomothety C₁ C₂ ρ q) P
            (signedHomothetyFixedPoint C₁ C₂ ρ q)).symm
    _ = (q / ρ) • intervalVec (signedHomothetyFixedPoint C₁ C₂ ρ q) P := by
          rw [signedHomothety_linear]
          rfl

theorem signedHomothety_fixedPoint_unique
    (C₁ C₂ : LorentzCircle) (ρ q : ℝ)
    (hρ : ρ ≠ 0) (hd : ρ - q ≠ 0) (P : Point)
    (hP : signedHomothety C₁ C₂ ρ q P = P) :
    P = signedHomothetyFixedPoint C₁ C₂ ρ q := by
  have hv : intervalVec (signedHomothetyFixedPoint C₁ C₂ ρ q) P =
      (q / ρ) • intervalVec (signedHomothetyFixedPoint C₁ C₂ ρ q) P := by
    calc
      intervalVec (signedHomothetyFixedPoint C₁ C₂ ρ q) P =
          intervalVec (signedHomothetyFixedPoint C₁ C₂ ρ q)
            (signedHomothety C₁ C₂ ρ q P) := by rw [hP]
      _ = _ := intervalVec_signedHomothetyFixedPoint C₁ C₂ ρ q hρ hd P
  have hscale : 1 - q / ρ ≠ 0 := by
    have heq : 1 - q / ρ = (ρ - q) / ρ := by field_simp [hρ]
    rw [heq]
    exact div_ne_zero hd hρ
  have hvzero : (1 - q / ρ) •
      intervalVec (signedHomothetyFixedPoint C₁ C₂ ρ q) P = 0 := by
    rw [sub_smul, one_smul]
    exact sub_eq_zero.mpr hv
  have hvec := (smul_eq_zero.mp hvzero).resolve_left hscale
  exact vsub_eq_zero_iff_eq.mp hvec

theorem SignedHomothetyData.fixedPoint_mem_left
    {C₁ C₂ : LorentzCircle} {ε ρ q : ℝ}
    (h : SignedHomothetyData C₁ C₂ ε ρ q) (hd : ρ - q ≠ 0) :
    signedHomothetyFixedPoint C₁ C₂ ρ q ∈ C₁ := by
  change intervalSq C₁.center (signedHomothetyFixedPoint C₁ C₂ ρ q) = C₁.radiusSq
  rw [signedHomothetyFixedPoint, intervalSq, intervalVec_lineMap_left, q_smul]
  change (ρ / (ρ - q)) ^ 2 * intervalSq C₁.center C₂.center = C₁.radiusSq
  rw [h.centerSq_eq, h.left_radiusSq_eq]
  field_simp [hd]

theorem SignedHomothetyData.fixedPoint_mem_right
    {C₁ C₂ : LorentzCircle} {ε ρ q : ℝ}
    (h : SignedHomothetyData C₁ C₂ ε ρ q) (hd : ρ - q ≠ 0) :
    signedHomothetyFixedPoint C₁ C₂ ρ q ∈ C₂ := by
  change intervalSq C₂.center (signedHomothetyFixedPoint C₁ C₂ ρ q) = C₂.radiusSq
  rw [signedHomothetyFixedPoint, intervalSq, intervalVec_lineMap_right, q_smul]
  change (ρ / (ρ - q) - 1) ^ 2 * intervalSq C₁.center C₂.center = C₂.radiusSq
  rw [h.centerSq_eq, h.right_radiusSq_eq]
  field_simp [hd]
  ring

theorem SignedHomothetyData.centers_ne_zero
    {C₁ C₂ : LorentzCircle} {ε ρ q : ℝ}
    (h : SignedHomothetyData C₁ C₂ ε ρ q) (hd : ρ - q ≠ 0) :
    intervalVec C₁.center C₂.center ≠ 0 := by
  intro hcenters
  have hright : ε * (ρ - q) ^ 2 ≠ 0 :=
    mul_ne_zero h.epsilon_ne_zero (pow_ne_zero 2 hd)
  apply hright
  rw [← h.centerSq_eq, intervalSq, hcenters, q_zero]

theorem SignedHomothetyData.isProperTangentAt_fixedPoint
    {C₁ C₂ : LorentzCircle} {ε ρ q : ℝ}
    (h : SignedHomothetyData C₁ C₂ ε ρ q) (hd : ρ - q ≠ 0) :
    IsProperTangentAt C₁ C₂ (signedHomothetyFixedPoint C₁ C₂ ρ q) := by
  have hfirst : IsFirstOrderContactAt C₁ C₂
      (signedHomothetyFixedPoint C₁ C₂ ρ q) :=
    isTangentAt_of_mem_of_lineMap C₁ C₂ (ρ / (ρ - q))
      (h.fixedPoint_mem_left hd) (h.fixedPoint_mem_right hd)
  have hcenters := h.centers_ne_zero hd
  have hleftScalar : ρ / (ρ - q) ≠ 0 := div_ne_zero h.rho_ne_zero hd
  have hrightScalar : ρ / (ρ - q) - 1 ≠ 0 := by
    intro hzero
    apply h.q_ne_zero
    field_simp [hd] at hzero
    linarith
  refine ⟨hfirst, ⟨hfirst.1, ?_⟩, ⟨hfirst.2.1, ?_⟩, ?_⟩
  · rw [signedHomothetyFixedPoint, intervalVec_lineMap_left]
    exact smul_ne_zero hleftScalar hcenters
  · rw [signedHomothetyFixedPoint, intervalVec_lineMap_right]
    exact smul_ne_zero hrightScalar hcenters
  · intro hcoincident
    unfold AreCoincident at hcoincident
    subst C₂
    exact hcenters (intervalVec_self C₁.center)

end LorentzCircle

end

end MinkowskiMerge
