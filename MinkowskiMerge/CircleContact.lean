import MinkowskiMerge.Circle
import MinkowskiMerge.ComplexRadius


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable section

namespace LorentzCircle

noncomputable def complexRadius (C : LorentzCircle) : ℂ :=
  positiveComplexSqrt C.radiusSq

@[simp] theorem complexRadius_sq (C : LorentzCircle) :
    C.complexRadius ^ 2 = (C.radiusSq : ℂ) :=
  positiveComplexSqrt_sq C.radiusSq

noncomputable def centerDistance (C₁ C₂ : LorentzCircle) : ℂ :=
  complexLength (intervalVec C₁.center C₂.center)

@[simp] theorem centerDistance_sq (C₁ C₂ : LorentzCircle) :
    C₁.centerDistance C₂ ^ 2 = (intervalSq C₁.center C₂.center : ℂ) := by
  unfold centerDistance
  rw [complexLength_sq]
  rfl

theorem centerDistance_eq_positiveComplexSqrt_intervalSq
    (C₁ C₂ : LorentzCircle) :
    C₁.centerDistance C₂ =
      positiveComplexSqrt (intervalSq C₁.center C₂.center) := by
  unfold centerDistance intervalSq
  exact complexLength_eq_positiveComplexSqrt _

def HasRadiusSumEquation (C₁ C₂ : LorentzCircle) : Prop :=
  C₁.centerDistance C₂ = C₁.complexRadius + C₂.complexRadius

def HasSignedRadiusDifferenceSqEquation (C₁ C₂ : LorentzCircle) (sign : ℝ) : Prop :=
  C₁.centerDistance C₂ ^ 2 =
    (C₁.complexRadius - (sign : ℂ) * C₂.complexRadius) ^ 2

end LorentzCircle

end

end MinkowskiMerge
