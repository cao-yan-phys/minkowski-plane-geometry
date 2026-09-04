import MinkowskiMerge.Affine


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable section

structure LorentzCircle where
  center : Point
  radiusSq : ℝ

namespace LorentzCircle

def IsOn (C : LorentzCircle) (P : Point) : Prop :=
  intervalSq C.center P = C.radiusSq

instance : Membership Point LorentzCircle :=
  ⟨fun C P => IsOn C P⟩

@[simp] theorem mem_iff (C : LorentzCircle) (P : Point) :
    P ∈ C ↔ intervalSq C.center P = C.radiusSq := Iff.rfl

def through (O P : Point) : LorentzCircle :=
  ⟨O, intervalSq O P⟩

@[simp] theorem through_center (O P : Point) :
    (through O P).center = O := rfl

@[simp] theorem through_radiusSq (O P : Point) :
    (through O P).radiusSq = intervalSq O P := rfl

theorem through_mem (O P : Point) : P ∈ through O P := by
  change intervalSq O P = intervalSq O P
  rfl

@[simp] theorem center_mem_iff (C : LorentzCircle) :
    C.center ∈ C ↔ C.radiusSq = 0 := by
  change intervalSq C.center C.center = C.radiusSq ↔ C.radiusSq = 0
  rw [intervalSq_self]
  exact eq_comm

def IsOnRadicalAxis (C₁ C₂ : LorentzCircle) (P : Point) : Prop :=
  intervalSq C₁.center P - C₁.radiusSq =
    intervalSq C₂.center P - C₂.radiusSq

theorem isOnRadicalAxis_of_mem {C₁ C₂ : LorentzCircle} {P : Point}
    (h₁ : P ∈ C₁) (h₂ : P ∈ C₂) : IsOnRadicalAxis C₁ C₂ P := by
  unfold IsOnRadicalAxis
  change intervalSq C₁.center P = C₁.radiusSq at h₁
  change intervalSq C₂.center P = C₂.radiusSq at h₂
  rw [h₁, h₂]
  ring

theorem isOnRadicalAxis_iff_dot (C₁ C₂ : LorentzCircle) (P : Point) :
    IsOnRadicalAxis C₁ C₂ P ↔
      2 * dot (intervalVec C₁.center P)
          (intervalVec C₁.center C₂.center) =
        intervalSq C₁.center C₂.center + C₁.radiusSq - C₂.radiusSq := by
  unfold IsOnRadicalAxis intervalSq
  rw [intervalVec_eq_sub_from C₁.center C₂.center P, q_sub]
  constructor <;> intro h <;> linarith

def IsFirstOrderContactAt (C₁ C₂ : LorentzCircle) (P : Point) : Prop :=
  P ∈ C₁ ∧ P ∈ C₂ ∧
    br (intervalVec C₁.center P) (intervalVec C₂.center P) = 0

abbrev IsTangentAt := IsFirstOrderContactAt

def IsRegularAt (C : LorentzCircle) (P : Point) : Prop :=
  P ∈ C ∧ intervalVec C.center P ≠ 0

def AreCoincident (C₁ C₂ : LorentzCircle) : Prop := C₁ = C₂

def IsProperTangentAt (C₁ C₂ : LorentzCircle) (P : Point) : Prop :=
  IsFirstOrderContactAt C₁ C₂ P ∧
    IsRegularAt C₁ P ∧ IsRegularAt C₂ P ∧ ¬AreCoincident C₁ C₂

theorem IsFirstOrderContactAt.isOnRadicalAxis
    {C₁ C₂ : LorentzCircle} {P : Point}
    (h : IsFirstOrderContactAt C₁ C₂ P) : IsOnRadicalAxis C₁ C₂ P :=
  isOnRadicalAxis_of_mem h.1 h.2.1

theorem IsFirstOrderContactAt.center_line
    {C₁ C₂ : LorentzCircle} {P : Point}
    (h : IsFirstOrderContactAt C₁ C₂ P) :
    br (intervalVec C₁.center C₂.center)
      (intervalVec C₁.center P) = 0 := by
  have hrel : intervalVec C₂.center P =
      intervalVec C₁.center P - intervalVec C₁.center C₂.center := by
    exact intervalVec_eq_sub_from C₁.center C₂.center P
  have hnormal := h.2.2
  rw [hrel, br_sub_right, br_self] at hnormal
  rw [br_swap]
  linarith

theorem IsTangentAt.isOnRadicalAxis
    {C₁ C₂ : LorentzCircle} {P : Point}
    (h : IsTangentAt C₁ C₂ P) : IsOnRadicalAxis C₁ C₂ P :=
  IsFirstOrderContactAt.isOnRadicalAxis h

theorem IsTangentAt.center_line
    {C₁ C₂ : LorentzCircle} {P : Point}
    (h : IsTangentAt C₁ C₂ P) :
    br (intervalVec C₁.center C₂.center)
      (intervalVec C₁.center P) = 0 :=
  IsFirstOrderContactAt.center_line h

theorem IsProperTangentAt.firstOrderContact
    {C₁ C₂ : LorentzCircle} {P : Point}
    (h : IsProperTangentAt C₁ C₂ P) :
    IsFirstOrderContactAt C₁ C₂ P :=
  h.1

theorem IsProperTangentAt.isRegularAt_left
    {C₁ C₂ : LorentzCircle} {P : Point}
    (h : IsProperTangentAt C₁ C₂ P) : IsRegularAt C₁ P :=
  h.2.1

theorem IsProperTangentAt.isRegularAt_right
    {C₁ C₂ : LorentzCircle} {P : Point}
    (h : IsProperTangentAt C₁ C₂ P) : IsRegularAt C₂ P :=
  h.2.2.1

theorem IsProperTangentAt.not_coincident
    {C₁ C₂ : LorentzCircle} {P : Point}
    (h : IsProperTangentAt C₁ C₂ P) : ¬AreCoincident C₁ C₂ :=
  h.2.2.2

end LorentzCircle

end

end MinkowskiMerge
