import MinkowskiMerge.Cycle.DoubleCompactified
import MinkowskiMerge.Cycle.CompactifiedCircle


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable section

open scoped OnePoint Topology

namespace Cycle
namespace DoubleCompactified

def IsOn (C : Cycle) (Z : ConformalPoint) : Prop :=
  Cycle.Compactified.IsOn C (collapse Z)

def IsFirstOrderContactAt (C D : Cycle) (Z : ConformalPoint) : Prop :=
  Cycle.Compactified.IsFirstOrderContactAt C D (collapse Z)

def IsRegularAt (C : Cycle) (Z : ConformalPoint) : Prop :=
  Cycle.Compactified.IsRegularAt C (collapse Z)

@[simp] theorem isOn_collapse_iff (C : Cycle) (Z : ConformalPoint) :
    IsOn C Z ↔ Cycle.Compactified.IsOn C (collapse Z) := Iff.rfl

@[simp] theorem isFirstOrderContactAt_collapse_iff
    (C D : Cycle) (Z : ConformalPoint) :
    IsFirstOrderContactAt C D Z ↔
      Cycle.Compactified.IsFirstOrderContactAt C D (collapse Z) := Iff.rfl

@[simp] theorem isRegularAt_collapse_iff (C : Cycle) (Z : ConformalPoint) :
    IsRegularAt C Z ↔ Cycle.Compactified.IsRegularAt C (collapse Z) := Iff.rfl

end DoubleCompactified
end Cycle

namespace LorentzCircle

def uPlusNullInfinityPoint (C : LorentzCircle) : ConformalPoint :=
  Cycle.DoubleCompactified.uPlusInfinityPoint (Cycle.lightconeU C.center)

def uMinusNullInfinityPoint (C : LorentzCircle) : ConformalPoint :=
  Cycle.DoubleCompactified.uMinusInfinityPoint (Cycle.lightconeU C.center)

def vPlusNullInfinityPoint (C : LorentzCircle) : ConformalPoint :=
  Cycle.DoubleCompactified.vPlusInfinityPoint (Cycle.lightconeV C.center)

def vMinusNullInfinityPoint (C : LorentzCircle) : ConformalPoint :=
  Cycle.DoubleCompactified.vMinusInfinityPoint (Cycle.lightconeV C.center)

@[simp] theorem uPlusNullInfinityPoint_ne_uMinusNullInfinityPoint
    (C : LorentzCircle) :
    C.uPlusNullInfinityPoint ≠ C.uMinusNullInfinityPoint := by
  intro h
  have hs := congrArg Prod.snd h
  have hne : (⊥ : EReal) ≠ ⊤ := by simp
  apply hne
  change (⊤ : EReal) = ⊥ at hs
  exact hs.symm

@[simp] theorem vPlusNullInfinityPoint_ne_vMinusNullInfinityPoint
    (C : LorentzCircle) :
    C.vPlusNullInfinityPoint ≠ C.vMinusNullInfinityPoint := by
  intro h
  have hs := congrArg Prod.fst h
  have hne : (⊥ : EReal) ≠ ⊤ := by simp
  apply hne
  change (⊤ : EReal) = ⊥ at hs
  exact hs.symm

@[simp] theorem collapse_uPlusNullInfinityPoint (C : LorentzCircle) :
    Cycle.DoubleCompactified.collapse C.uPlusNullInfinityPoint = C.uNullInfinityPoint := by
  rfl

@[simp] theorem collapse_uMinusNullInfinityPoint (C : LorentzCircle) :
    Cycle.DoubleCompactified.collapse C.uMinusNullInfinityPoint = C.uNullInfinityPoint := by
  rfl

@[simp] theorem collapse_vPlusNullInfinityPoint (C : LorentzCircle) :
    Cycle.DoubleCompactified.collapse C.vPlusNullInfinityPoint = C.vNullInfinityPoint := by
  rfl

@[simp] theorem collapse_vMinusNullInfinityPoint (C : LorentzCircle) :
    Cycle.DoubleCompactified.collapse C.vMinusNullInfinityPoint = C.vNullInfinityPoint := by
  rfl

@[simp] theorem double_firstOrderContactAt_uPlusNullInfinity
    {C₁ C₂ : LorentzCircle}
    (hu : Cycle.lightconeU C₁.center = Cycle.lightconeU C₂.center)
    (hr : C₁.radiusSq = C₂.radiusSq) :
    Cycle.DoubleCompactified.IsFirstOrderContactAt
      (Cycle.ofCircle C₁) (Cycle.ofCircle C₂) C₁.uPlusNullInfinityPoint := by
  simpa [Cycle.DoubleCompactified.IsFirstOrderContactAt]
    using compactified_firstOrderContactAt_uNullInfinity hu hr

@[simp] theorem double_firstOrderContactAt_uMinusNullInfinity
    {C₁ C₂ : LorentzCircle}
    (hu : Cycle.lightconeU C₁.center = Cycle.lightconeU C₂.center)
    (hr : C₁.radiusSq = C₂.radiusSq) :
    Cycle.DoubleCompactified.IsFirstOrderContactAt
      (Cycle.ofCircle C₁) (Cycle.ofCircle C₂) C₁.uMinusNullInfinityPoint := by
  simpa [Cycle.DoubleCompactified.IsFirstOrderContactAt]
    using compactified_firstOrderContactAt_uNullInfinity hu hr

@[simp] theorem double_firstOrderContactAt_vPlusNullInfinity
    {C₁ C₂ : LorentzCircle}
    (hv : Cycle.lightconeV C₁.center = Cycle.lightconeV C₂.center)
    (hr : C₁.radiusSq = C₂.radiusSq) :
    Cycle.DoubleCompactified.IsFirstOrderContactAt
      (Cycle.ofCircle C₁) (Cycle.ofCircle C₂) C₁.vPlusNullInfinityPoint := by
  simpa [Cycle.DoubleCompactified.IsFirstOrderContactAt]
    using compactified_firstOrderContactAt_vNullInfinity hv hr

@[simp] theorem double_firstOrderContactAt_vMinusNullInfinity
    {C₁ C₂ : LorentzCircle}
    (hv : Cycle.lightconeV C₁.center = Cycle.lightconeV C₂.center)
    (hr : C₁.radiusSq = C₂.radiusSq) :
    Cycle.DoubleCompactified.IsFirstOrderContactAt
      (Cycle.ofCircle C₁) (Cycle.ofCircle C₂) C₁.vMinusNullInfinityPoint := by
  simpa [Cycle.DoubleCompactified.IsFirstOrderContactAt]
    using compactified_firstOrderContactAt_vNullInfinity hv hr

def HasDoubleNullInfinityContact (C₁ C₂ : LorentzCircle) : Prop :=
  ∃ Zplus Zminus : ConformalPoint,
    Zplus ≠ Zminus ∧
    Cycle.DoubleCompactified.IsFirstOrderContactAt
      (Cycle.ofCircle C₁) (Cycle.ofCircle C₂) Zplus ∧
    Cycle.DoubleCompactified.IsFirstOrderContactAt
      (Cycle.ofCircle C₁) (Cycle.ofCircle C₂) Zminus ∧
    Cycle.DoubleCompactified.IsBoundary Zplus ∧
    Cycle.DoubleCompactified.IsBoundary Zminus

theorem HasNullInfinityContact.hasDoubleContact
    {C₁ C₂ : LorentzCircle} (h : C₁.HasNullInfinityContact C₂) :
    C₁.HasDoubleNullInfinityContact C₂ := by
  have hlightcone :=
    (Cycle.Compactified.isNull_intervalVec_iff_lightcone_eq
      C₁.center C₂.center).1 h.displacement_null
  rcases hlightcone with hu | hv
  · refine ⟨C₁.uPlusNullInfinityPoint, C₁.uMinusNullInfinityPoint, ?_,
      double_firstOrderContactAt_uPlusNullInfinity hu h.radiusSq_eq,
      double_firstOrderContactAt_uMinusNullInfinity hu h.radiusSq_eq, ?_, ?_⟩
    · exact uPlusNullInfinityPoint_ne_uMinusNullInfinityPoint C₁
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · refine ⟨C₁.vPlusNullInfinityPoint, C₁.vMinusNullInfinityPoint, ?_,
      double_firstOrderContactAt_vPlusNullInfinity hv h.radiusSq_eq,
      double_firstOrderContactAt_vMinusNullInfinity hv h.radiusSq_eq, ?_, ?_⟩
    · exact vPlusNullInfinityPoint_ne_vMinusNullInfinityPoint C₁
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

end LorentzCircle

end
end MinkowskiMerge
