import MinkowskiMerge.CircleHomothetyTrichotomy
import MinkowskiMerge.Cycle.Compactified


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable section

open scoped OnePoint

namespace LorentzCircle

def uNullInfinityPoint (C : LorentzCircle) : CompactifiedPoint :=
  Cycle.Compactified.uInfinityPoint (Cycle.lightconeU C.center)

def vNullInfinityPoint (C : LorentzCircle) : CompactifiedPoint :=
  Cycle.Compactified.vInfinityPoint (Cycle.lightconeV C.center)

@[simp] theorem uNullInfinityPoint_isBoundary (C : LorentzCircle) :
    Cycle.Compactified.IsBoundary C.uNullInfinityPoint := by
  simp [uNullInfinityPoint]

@[simp] theorem vNullInfinityPoint_isBoundary (C : LorentzCircle) :
    Cycle.Compactified.IsBoundary C.vNullInfinityPoint := by
  simp [vNullInfinityPoint]

@[simp] theorem ofCircle_isOn_uNullInfinityPoint (C : LorentzCircle) :
    Cycle.Compactified.IsOn (Cycle.ofCircle C) C.uNullInfinityPoint := by
  simp [Cycle.Compactified.IsOn, Cycle.Compactified.matrixEval,
    uNullInfinityPoint, Cycle.Compactified.uInfinityPoint,
    Cycle.Compactified.coordVector, Cycle.toMatrix, Cycle.ofCircle,
    Cycle.lightconeU, q_apply, dotProduct, Matrix.mulVec]

@[simp] theorem ofCircle_isOn_vNullInfinityPoint (C : LorentzCircle) :
    Cycle.Compactified.IsOn (Cycle.ofCircle C) C.vNullInfinityPoint := by
  simp [Cycle.Compactified.IsOn, Cycle.Compactified.matrixEval,
    vNullInfinityPoint, Cycle.Compactified.vInfinityPoint,
    Cycle.Compactified.coordVector, Cycle.toMatrix, Cycle.ofCircle,
    Cycle.lightconeV, q_apply, dotProduct, Matrix.mulVec]
  ring

@[simp] theorem localGradient_ofCircle_uNullInfinityPoint
    (C : LorentzCircle) :
    Cycle.Compactified.localGradient (Cycle.ofCircle C).toMatrix
      C.uNullInfinityPoint = (-1, -C.radiusSq) := by
  ext <;> (simp [uNullInfinityPoint, Cycle.Compactified.uInfinityPoint,
      Cycle.Compactified.localGradient, Cycle.toMatrix, Cycle.ofCircle,
      Cycle.lightconeU, q_apply] <;> ring)

@[simp] theorem localGradient_ofCircle_vNullInfinityPoint
    (C : LorentzCircle) :
    Cycle.Compactified.localGradient (Cycle.ofCircle C).toMatrix
      C.vNullInfinityPoint = (-C.radiusSq, -1) := by
  ext <;> (simp [vNullInfinityPoint, Cycle.Compactified.vInfinityPoint,
      Cycle.Compactified.localGradient, Cycle.toMatrix, Cycle.ofCircle,
      Cycle.lightconeV, q_apply] <;> ring)

theorem compactified_firstOrderContactAt_uNullInfinity
    {C₁ C₂ : LorentzCircle}
    (hu : Cycle.lightconeU C₁.center = Cycle.lightconeU C₂.center)
    (hr : C₁.radiusSq = C₂.radiusSq) :
    Cycle.Compactified.IsFirstOrderContactAt
      (Cycle.ofCircle C₁) (Cycle.ofCircle C₂) C₁.uNullInfinityPoint := by
  have hpoint : C₁.uNullInfinityPoint = C₂.uNullInfinityPoint := by
    simp [uNullInfinityPoint, Cycle.Compactified.uInfinityPoint, hu]
  refine ⟨ofCircle_isOn_uNullInfinityPoint C₁, ?_, ?_⟩
  · rw [hpoint]
    exact ofCircle_isOn_uNullInfinityPoint C₂
  · rw [localGradient_ofCircle_uNullInfinityPoint]
    rw [hpoint, localGradient_ofCircle_uNullInfinityPoint, hr]
    simp [br_apply]

theorem compactified_firstOrderContactAt_vNullInfinity
    {C₁ C₂ : LorentzCircle}
    (hv : Cycle.lightconeV C₁.center = Cycle.lightconeV C₂.center)
    (hr : C₁.radiusSq = C₂.radiusSq) :
    Cycle.Compactified.IsFirstOrderContactAt
      (Cycle.ofCircle C₁) (Cycle.ofCircle C₂) C₁.vNullInfinityPoint := by
  have hpoint : C₁.vNullInfinityPoint = C₂.vNullInfinityPoint := by
    simp [vNullInfinityPoint, Cycle.Compactified.vInfinityPoint, hv]
  refine ⟨ofCircle_isOn_vNullInfinityPoint C₁, ?_, ?_⟩
  · rw [hpoint]
    exact ofCircle_isOn_vNullInfinityPoint C₂
  · rw [localGradient_ofCircle_vNullInfinityPoint]
    rw [hpoint, localGradient_ofCircle_vNullInfinityPoint, hr]
    simp [br_apply]

def HasProjectiveNullInfinityContact (C₁ C₂ : LorentzCircle) : Prop :=
  ∃ Z : CompactifiedPoint,
    Cycle.Compactified.IsBoundary Z ∧
    Cycle.Compactified.IsFirstOrderContactAt
      (Cycle.ofCircle C₁) (Cycle.ofCircle C₂) Z ∧
    Cycle.Compactified.IsRegularAt (Cycle.ofCircle C₁) Z ∧
    Cycle.Compactified.IsRegularAt (Cycle.ofCircle C₂) Z ∧
    ¬C₁.AreCoincident C₂

theorem HasNullInfinityContact.hasProjectiveContact
    {C₁ C₂ : LorentzCircle} (h : C₁.HasNullInfinityContact C₂) :
    C₁.HasProjectiveNullInfinityContact C₂ := by
  have hlightcone :=
    (Cycle.Compactified.isNull_intervalVec_iff_lightcone_eq
      C₁.center C₂.center).1 h.displacement_null
  rcases hlightcone with hu | hv
  · have hpoint : C₁.uNullInfinityPoint = C₂.uNullInfinityPoint := by
      simp [uNullInfinityPoint, Cycle.Compactified.uInfinityPoint, hu]
    refine ⟨C₁.uNullInfinityPoint, uNullInfinityPoint_isBoundary C₁,
      compactified_firstOrderContactAt_uNullInfinity hu h.radiusSq_eq,
      ⟨ofCircle_isOn_uNullInfinityPoint C₁, ?_⟩,
      ⟨?_, ?_⟩, h.not_coincident⟩
    · simp
    · rw [hpoint]
      exact ofCircle_isOn_uNullInfinityPoint C₂
    · rw [hpoint]
      simp
  · have hpoint : C₁.vNullInfinityPoint = C₂.vNullInfinityPoint := by
      simp [vNullInfinityPoint, Cycle.Compactified.vInfinityPoint, hv]
    refine ⟨C₁.vNullInfinityPoint, vNullInfinityPoint_isBoundary C₁,
      compactified_firstOrderContactAt_vNullInfinity hv h.radiusSq_eq,
      ⟨ofCircle_isOn_vNullInfinityPoint C₁, ?_⟩,
      ⟨?_, ?_⟩, h.not_coincident⟩
    · simp
    · rw [hpoint]
      exact ofCircle_isOn_vNullInfinityPoint C₂
    · rw [hpoint]
      simp

end LorentzCircle

end
end MinkowskiMerge
