import MinkowskiMerge.CircleHomothety


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable section

namespace LorentzCircle

noncomputable def tangentPointOfRadiusSum (C₁ C₂ : LorentzCircle)
    (r₁ r₂ : ℝ) : Point :=
  AffineMap.lineMap C₁.center C₂.center (r₁ / (r₁ + r₂))

noncomputable def tangentPointOfRadiusDifference (C₁ C₂ : LorentzCircle)
    (r₁ r₂ : ℝ) : Point :=
  AffineMap.lineMap C₁.center C₂.center (r₁ / (r₁ - r₂))

private theorem tangentPointOfRadiusSum_mem_left (C₁ C₂ : LorentzCircle)
    (ε r₁ r₂ : ℝ) (hs : r₁ + r₂ ≠ 0)
    (hD : intervalSq C₁.center C₂.center = ε * (r₁ + r₂) ^ 2)
    (h₁ : C₁.radiusSq = ε * r₁ ^ 2) :
    tangentPointOfRadiusSum C₁ C₂ r₁ r₂ ∈ C₁ := by
  change intervalSq C₁.center
      (AffineMap.lineMap C₁.center C₂.center (r₁ / (r₁ + r₂))) = C₁.radiusSq
  rw [intervalSq, intervalVec_lineMap_left, q_smul]
  change (r₁ / (r₁ + r₂)) ^ 2 * intervalSq C₁.center C₂.center = C₁.radiusSq
  rw [hD, h₁]
  field_simp [hs]

private theorem tangentPointOfRadiusSum_mem_right (C₁ C₂ : LorentzCircle)
    (ε r₁ r₂ : ℝ) (hs : r₁ + r₂ ≠ 0)
    (hD : intervalSq C₁.center C₂.center = ε * (r₁ + r₂) ^ 2)
    (h₂ : C₂.radiusSq = ε * r₂ ^ 2) :
    tangentPointOfRadiusSum C₁ C₂ r₁ r₂ ∈ C₂ := by
  change intervalSq C₂.center
      (AffineMap.lineMap C₁.center C₂.center (r₁ / (r₁ + r₂))) = C₂.radiusSq
  rw [intervalSq, intervalVec_lineMap_right, q_smul]
  change (r₁ / (r₁ + r₂) - 1) ^ 2 * intervalSq C₁.center C₂.center = C₂.radiusSq
  rw [hD, h₂]
  field_simp [hs]
  ring

theorem isTangentAt_of_radiusSumData (C₁ C₂ : LorentzCircle) (ε r₁ r₂ : ℝ)
    (hs : r₁ + r₂ ≠ 0)
    (hD : intervalSq C₁.center C₂.center = ε * (r₁ + r₂) ^ 2)
    (h₁ : C₁.radiusSq = ε * r₁ ^ 2)
    (h₂ : C₂.radiusSq = ε * r₂ ^ 2) :
    IsTangentAt C₁ C₂ (tangentPointOfRadiusSum C₁ C₂ r₁ r₂) := by
  exact isTangentAt_of_mem_of_lineMap C₁ C₂ (r₁ / (r₁ + r₂))
    (tangentPointOfRadiusSum_mem_left C₁ C₂ ε r₁ r₂ hs hD h₁)
    (tangentPointOfRadiusSum_mem_right C₁ C₂ ε r₁ r₂ hs hD h₂)

theorem isProperTangentAt_of_radiusSumData
    (C₁ C₂ : LorentzCircle) (ε r₁ r₂ : ℝ)
    (hε : ε ≠ 0) (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hs : r₁ + r₂ ≠ 0)
    (hD : intervalSq C₁.center C₂.center = ε * (r₁ + r₂) ^ 2)
    (h₁ : C₁.radiusSq = ε * r₁ ^ 2)
    (h₂ : C₂.radiusSq = ε * r₂ ^ 2) :
    IsProperTangentAt C₁ C₂ (tangentPointOfRadiusSum C₁ C₂ r₁ r₂) := by
  have hdata : SignedHomothetyData C₁ C₂ ε r₁ (-r₂) :=
    { epsilon_ne_zero := hε
      rho_ne_zero := hr₁
      q_ne_zero := neg_ne_zero.mpr hr₂
      centerSq_eq := by simpa [sub_neg_eq_add] using hD
      left_radiusSq_eq := h₁
      right_radiusSq_eq := by simpa using h₂ }
  have hproper := hdata.isProperTangentAt_fixedPoint
    (by simpa [sub_neg_eq_add] using hs)
  simpa [tangentPointOfRadiusSum, signedHomothetyFixedPoint,
    sub_neg_eq_add] using hproper

private theorem tangentPointOfRadiusDifference_mem_left (C₁ C₂ : LorentzCircle)
    (ε r₁ r₂ : ℝ) (hd : r₁ - r₂ ≠ 0)
    (hD : intervalSq C₁.center C₂.center = ε * (r₁ - r₂) ^ 2)
    (h₁ : C₁.radiusSq = ε * r₁ ^ 2) :
    tangentPointOfRadiusDifference C₁ C₂ r₁ r₂ ∈ C₁ := by
  change intervalSq C₁.center
      (AffineMap.lineMap C₁.center C₂.center (r₁ / (r₁ - r₂))) = C₁.radiusSq
  rw [intervalSq, intervalVec_lineMap_left, q_smul]
  change (r₁ / (r₁ - r₂)) ^ 2 * intervalSq C₁.center C₂.center = C₁.radiusSq
  rw [hD, h₁]
  field_simp [hd]

private theorem tangentPointOfRadiusDifference_mem_right (C₁ C₂ : LorentzCircle)
    (ε r₁ r₂ : ℝ) (hd : r₁ - r₂ ≠ 0)
    (hD : intervalSq C₁.center C₂.center = ε * (r₁ - r₂) ^ 2)
    (h₂ : C₂.radiusSq = ε * r₂ ^ 2) :
    tangentPointOfRadiusDifference C₁ C₂ r₁ r₂ ∈ C₂ := by
  change intervalSq C₂.center
      (AffineMap.lineMap C₁.center C₂.center (r₁ / (r₁ - r₂))) = C₂.radiusSq
  rw [intervalSq, intervalVec_lineMap_right, q_smul]
  change (r₁ / (r₁ - r₂) - 1) ^ 2 * intervalSq C₁.center C₂.center = C₂.radiusSq
  rw [hD, h₂]
  field_simp [hd]
  ring

theorem isTangentAt_of_radiusDifferenceData (C₁ C₂ : LorentzCircle)
    (ε r₁ r₂ : ℝ) (hd : r₁ - r₂ ≠ 0)
    (hD : intervalSq C₁.center C₂.center = ε * (r₁ - r₂) ^ 2)
    (h₁ : C₁.radiusSq = ε * r₁ ^ 2)
    (h₂ : C₂.radiusSq = ε * r₂ ^ 2) :
    IsTangentAt C₁ C₂ (tangentPointOfRadiusDifference C₁ C₂ r₁ r₂) := by
  exact isTangentAt_of_mem_of_lineMap C₁ C₂ (r₁ / (r₁ - r₂))
    (tangentPointOfRadiusDifference_mem_left C₁ C₂ ε r₁ r₂ hd hD h₁)
    (tangentPointOfRadiusDifference_mem_right C₁ C₂ ε r₁ r₂ hd hD h₂)

theorem isProperTangentAt_of_radiusDifferenceData
    (C₁ C₂ : LorentzCircle) (ε r₁ r₂ : ℝ)
    (hε : ε ≠ 0) (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hd : r₁ - r₂ ≠ 0)
    (hD : intervalSq C₁.center C₂.center = ε * (r₁ - r₂) ^ 2)
    (h₁ : C₁.radiusSq = ε * r₁ ^ 2)
    (h₂ : C₂.radiusSq = ε * r₂ ^ 2) :
    IsProperTangentAt C₁ C₂
      (tangentPointOfRadiusDifference C₁ C₂ r₁ r₂) := by
  have hdata : SignedHomothetyData C₁ C₂ ε r₁ r₂ :=
    { epsilon_ne_zero := hε
      rho_ne_zero := hr₁
      q_ne_zero := hr₂
      centerSq_eq := hD
      left_radiusSq_eq := h₁
      right_radiusSq_eq := h₂ }
  simpa [tangentPointOfRadiusDifference, signedHomothetyFixedPoint] using
    hdata.isProperTangentAt_fixedPoint hd

end LorentzCircle

end

end MinkowskiMerge
