import MinkowskiMerge.CircleHomothety
import MinkowskiMerge.Causal
import MinkowskiMerge.Direction


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable section

namespace LorentzCircle

structure HasNullInfinityContact (C₁ C₂ : LorentzCircle) : Prop where
  radiusSq_eq : C₁.radiusSq = C₂.radiusSq
  displacement_ne_zero : intervalVec C₁.center C₂.center ≠ 0
  displacement_null : IsNull (intervalVec C₁.center C₂.center)

theorem HasNullInfinityContact.centers_ne
    {C₁ C₂ : LorentzCircle} (h : HasNullInfinityContact C₁ C₂) :
    C₁.center ≠ C₂.center := by
  intro hcenters
  apply h.displacement_ne_zero
  rw [hcenters, intervalVec_self]

theorem HasNullInfinityContact.not_coincident
    {C₁ C₂ : LorentzCircle} (h : HasNullInfinityContact C₁ C₂) :
    ¬AreCoincident C₁ C₂ := by
  intro hcoincident
  exact h.centers_ne (congrArg (fun C : LorentzCircle ↦ C.center) hcoincident)

noncomputable def HasNullInfinityContact.direction
    {C₁ C₂ : LorentzCircle} (h : HasNullInfinityContact C₁ C₂) :
    Direction :=
  directionOfVector (intervalVec C₁.center C₂.center)
    h.displacement_ne_zero

theorem HasNullInfinityContact.symm
    {C₁ C₂ : LorentzCircle} (h : HasNullInfinityContact C₁ C₂) :
    HasNullInfinityContact C₂ C₁ := by
  refine
    { radiusSq_eq := h.radiusSq_eq.symm
      displacement_ne_zero := ?_
      displacement_null := ?_ }
  · rw [intervalVec_rev]
    exact neg_ne_zero.mpr h.displacement_ne_zero
  · rw [intervalVec_rev, isNull_neg]
    exact h.displacement_null

theorem HasNullInfinityContact.direction_symm
    {C₁ C₂ : LorentzCircle} (h : HasNullInfinityContact C₁ C₂) :
    h.symm.direction = h.direction := by
  unfold HasNullInfinityContact.direction
  apply (same_direction_iff
    (intervalVec C₂.center C₁.center)
    (intervalVec C₁.center C₂.center)
    h.symm.displacement_ne_zero h.displacement_ne_zero).2
  refine ⟨-1, ?_⟩
  rw [neg_one_smul, intervalVec_rev]
  simp

@[simp] theorem signedHomothety_apply_equalRadius
    (C₁ C₂ : LorentzCircle) (ρ : ℝ) (hρ : ρ ≠ 0) (P : Point) :
    signedHomothety C₁ C₂ ρ ρ P =
      P + intervalVec C₁.center C₂.center := by
  rw [signedHomothety_apply, div_self hρ, one_smul]
  apply Vec.ext
  · simp only [intervalVec, vsub_eq_sub, Vec.x_add, Vec.x_sub]
    ring
  · simp only [intervalVec, vsub_eq_sub, Vec.t_add, Vec.t_sub]
    ring

theorem signedHomothety_no_fixedPoint_equalRadius
    (C₁ C₂ : LorentzCircle) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hdisp : intervalVec C₁.center C₂.center ≠ 0) (P : Point) :
    signedHomothety C₁ C₂ ρ ρ P ≠ P := by
  intro hfixed
  rw [signedHomothety_apply_equalRadius C₁ C₂ ρ hρ] at hfixed
  apply hdisp
  apply Vec.ext
  · simp only [Vec.x_zero]
    have hx := congrArg Vec.x hfixed
    simp only [Vec.x_add] at hx
    linarith
  · simp only [Vec.t_zero]
    have ht := congrArg Vec.t hfixed
    simp only [Vec.t_add] at ht
    linarith

theorem SignedHomothetyData.left_radiusSq_ne_zero
    {C₁ C₂ : LorentzCircle} {ε ρ q : ℝ}
    (h : SignedHomothetyData C₁ C₂ ε ρ q) :
    C₁.radiusSq ≠ 0 := by
  rw [h.left_radiusSq_eq]
  exact mul_ne_zero h.epsilon_ne_zero (pow_ne_zero 2 h.rho_ne_zero)

theorem SignedHomothetyData.right_radiusSq_ne_zero
    {C₁ C₂ : LorentzCircle} {ε ρ q : ℝ}
    (h : SignedHomothetyData C₁ C₂ ε ρ q) :
    C₂.radiusSq ≠ 0 := by
  rw [h.right_radiusSq_eq]
  exact mul_ne_zero h.epsilon_ne_zero (pow_ne_zero 2 h.q_ne_zero)

theorem SignedHomothetyData.hasNullInfinityContact
    {C₁ C₂ : LorentzCircle} {ε ρ q : ℝ}
    (h : SignedHomothetyData C₁ C₂ ε ρ q)
    (hradii : ρ = q) (hcenters : C₁.center ≠ C₂.center) :
    HasNullInfinityContact C₁ C₂ := by
  refine
    { radiusSq_eq := ?_
      displacement_ne_zero := ?_
      displacement_null := ?_ }
  · rw [h.left_radiusSq_eq, h.right_radiusSq_eq, hradii]
  · simpa [intervalVec] using sub_ne_zero.mpr hcenters.symm
  · unfold IsNull
    rw [← intervalSq, h.centerSq_eq, hradii]
    ring

theorem SignedHomothetyData.areCoincident_of_radii_eq_of_centers_eq
    {C₁ C₂ : LorentzCircle} {ε ρ q : ℝ}
    (h : SignedHomothetyData C₁ C₂ ε ρ q)
    (hradii : ρ = q) (hcenters : C₁.center = C₂.center) :
    AreCoincident C₁ C₂ := by
  unfold AreCoincident
  have hradius : C₁.radiusSq = C₂.radiusSq := by
    rw [h.left_radiusSq_eq, h.right_radiusSq_eq, hradii]
  cases C₁
  cases C₂
  simp_all

theorem SignedHomothetyData.no_fixedPoint_of_nullInfinity
    {C₁ C₂ : LorentzCircle} {ε ρ q : ℝ}
    (h : SignedHomothetyData C₁ C₂ ε ρ q)
    (hradii : ρ = q) (hcenters : C₁.center ≠ C₂.center) (P : Point) :
    signedHomothety C₁ C₂ ρ q P ≠ P := by
  subst q
  exact signedHomothety_no_fixedPoint_equalRadius C₁ C₂ ρ
    h.rho_ne_zero (h.hasNullInfinityContact rfl hcenters).displacement_ne_zero P

private theorem isNull_of_dot_null_eq_zero {v d : Vec}
    (hd0 : d ≠ 0) (hdnull : IsNull d) (hvdot : dot v d = 0) :
    IsNull v := by
  have hdq : q d = 0 := hdnull
  have hgram := gram_identity v d
  rw [hvdot, hdq] at hgram
  have hvbr : br d v = 0 := by
    rw [br_swap]
    nlinarith [sq_nonneg (br v d)]
  have hvspan := (mem_span_singleton_iff_br_eq_zero hd0 v).2 hvbr
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hvspan
  rw [← hr]
  unfold IsNull
  rw [q_smul, hdq]
  ring

theorem SignedHomothetyData.no_finite_commonPoint_of_nullInfinity
    {C₁ C₂ : LorentzCircle} {ε ρ q : ℝ}
    (h : SignedHomothetyData C₁ C₂ ε ρ q)
    (hradii : ρ = q) (hcenters : C₁.center ≠ C₂.center) :
    ¬∃ P : Point, P ∈ C₁ ∧ P ∈ C₂ := by
  intro hcommon
  obtain ⟨P, hP₁, hP₂⟩ := hcommon
  let d := intervalVec C₁.center C₂.center
  let v := intervalVec C₁.center P
  have hinfinity := h.hasNullInfinityContact hradii hcenters
  have hdnull : IsNull d := hinfinity.displacement_null
  have hd0 : d ≠ 0 := hinfinity.displacement_ne_zero
  have hP₁' : MinkowskiMerge.q v = C₁.radiusSq := by
    simpa [v, intervalSq] using hP₁
  have hP₂' : MinkowskiMerge.q (v - d) = C₂.radiusSq := by
    change intervalSq C₂.center P = C₂.radiusSq at hP₂
    rw [intervalSq, intervalVec_eq_sub_from C₁.center C₂.center P] at hP₂
    simpa [v, d] using hP₂
  have hvdot : dot v d = 0 := by
    rw [q_sub] at hP₂'
    have hdq : MinkowskiMerge.q d = 0 := hdnull
    rw [hdq, ← hinfinity.radiusSq_eq, ← hP₁'] at hP₂'
    linarith
  have hvnull := isNull_of_dot_null_eq_zero hd0 hdnull hvdot
  apply h.left_radiusSq_ne_zero
  rw [← hP₁']
  exact hvnull

theorem SignedHomothetyData.contact_trichotomy
    {C₁ C₂ : LorentzCircle} {ε ρ q : ℝ}
    (h : SignedHomothetyData C₁ C₂ ε ρ q) :
    (ρ - q ≠ 0 ∧
      IsProperTangentAt C₁ C₂ (signedHomothetyFixedPoint C₁ C₂ ρ q)) ∨
    (ρ = q ∧ HasNullInfinityContact C₁ C₂) ∨
    (ρ = q ∧ AreCoincident C₁ C₂) := by
  by_cases hd : ρ - q = 0
  · have hradii : ρ = q := sub_eq_zero.mp hd
    by_cases hcenters : C₁.center = C₂.center
    · exact Or.inr (Or.inr ⟨hradii,
        h.areCoincident_of_radii_eq_of_centers_eq hradii hcenters⟩)
    · exact Or.inr (Or.inl ⟨hradii,
        h.hasNullInfinityContact hradii hcenters⟩)
  · exact Or.inl ⟨hd, h.isProperTangentAt_fixedPoint hd⟩

end LorentzCircle

end

end MinkowskiMerge
