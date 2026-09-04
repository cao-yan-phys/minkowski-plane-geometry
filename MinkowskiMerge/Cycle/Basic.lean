import MinkowskiMerge.Circle
import MinkowskiMerge.Perpendicular


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable section

@[ext]
structure Cycle where
  quadCoeff : ℝ
  linearCoeff : Vec
  constantCoeff : ℝ

namespace Cycle

def eval (C : Cycle) (P : Point) : ℝ :=
  C.quadCoeff * q P + 2 * dot C.linearCoeff P + C.constantCoeff

def carrier (C : Cycle) : Set Point :=
  {P | C.eval P = 0}

instance : Membership Point Cycle :=
  ⟨fun C P => C.eval P = 0⟩

@[simp] theorem mem_iff (C : Cycle) (P : Point) :
    P ∈ C ↔ C.eval P = 0 := Iff.rfl

@[simp] theorem mem_carrier_iff (C : Cycle) (P : Point) :
    P ∈ C.carrier ↔ P ∈ C := Iff.rfl

def scale (a : ℝ) (C : Cycle) : Cycle where
  quadCoeff := a * C.quadCoeff
  linearCoeff := a • C.linearCoeff
  constantCoeff := a * C.constantCoeff

@[simp] theorem scale_quadCoeff (a : ℝ) (C : Cycle) :
    (C.scale a).quadCoeff = a * C.quadCoeff := rfl

@[simp] theorem scale_linearCoeff (a : ℝ) (C : Cycle) :
    (C.scale a).linearCoeff = a • C.linearCoeff := rfl

@[simp] theorem scale_constantCoeff (a : ℝ) (C : Cycle) :
    (C.scale a).constantCoeff = a * C.constantCoeff := rfl

@[simp] theorem scale_one (C : Cycle) : C.scale 1 = C := by
  ext <;> simp [scale]

theorem scale_scale (a b : ℝ) (C : Cycle) :
    (C.scale a).scale b = C.scale (b * a) := by
  ext <;> simp [scale, smul_smul, mul_assoc]

@[simp] theorem eval_scale (a : ℝ) (C : Cycle) (P : Point) :
    (C.scale a).eval P = a * C.eval P := by
  simp only [eval, scale_quadCoeff, scale_linearCoeff, scale_constantCoeff,
    dot_smul_left]
  ring

theorem mem_scale_iff (C : Cycle) (P : Point) {a : ℝ} (ha : a ≠ 0) :
    P ∈ C.scale a ↔ P ∈ C := by
  simp [mem_iff, ha]

def ScaleEquivalent (C D : Cycle) : Prop :=
  ∃ a : ℝ, a ≠ 0 ∧ D = C.scale a

@[refl] theorem scaleEquivalent_refl (C : Cycle) : ScaleEquivalent C C := by
  exact ⟨1, one_ne_zero, (scale_one C).symm⟩

@[symm] theorem ScaleEquivalent.symm {C D : Cycle}
    (h : ScaleEquivalent C D) : ScaleEquivalent D C := by
  rcases h with ⟨a, ha, rfl⟩
  refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
  ext <;> simp [scale, smul_smul, ha]

@[trans] theorem ScaleEquivalent.trans {C D E : Cycle}
    (hCD : ScaleEquivalent C D) (hDE : ScaleEquivalent D E) :
    ScaleEquivalent C E := by
  rcases hCD with ⟨a, ha, rfl⟩
  rcases hDE with ⟨b, hb, rfl⟩
  exact ⟨b * a, mul_ne_zero hb ha, scale_scale a b C⟩

def scaleSetoid : Setoid Cycle where
  r := ScaleEquivalent
  iseqv :=
    { refl := scaleEquivalent_refl
      symm := fun h => h.symm
      trans := fun hCD hDE => hCD.trans hDE }

theorem ScaleEquivalent.mem_iff {C D : Cycle}
    (h : ScaleEquivalent C D) (P : Point) : P ∈ C ↔ P ∈ D := by
  rcases h with ⟨a, ha, rfl⟩
  exact (mem_scale_iff C P ha).symm

theorem ScaleEquivalent.carrier_eq {C D : Cycle}
    (h : ScaleEquivalent C D) : C.carrier = D.carrier := by
  ext P
  exact h.mem_iff P

def ofCircle (C : LorentzCircle) : Cycle where
  quadCoeff := 1
  linearCoeff := -C.center
  constantCoeff := q C.center - C.radiusSq

@[simp] theorem ofCircle_quadCoeff (C : LorentzCircle) :
    (ofCircle C).quadCoeff = 1 := rfl

@[simp] theorem ofCircle_linearCoeff (C : LorentzCircle) :
    (ofCircle C).linearCoeff = -C.center := rfl

@[simp] theorem ofCircle_constantCoeff (C : LorentzCircle) :
    (ofCircle C).constantCoeff = q C.center - C.radiusSq := rfl

@[simp] theorem eval_ofCircle (C : LorentzCircle) (P : Point) :
    (ofCircle C).eval P = intervalSq C.center P - C.radiusSq := by
  simp only [eval, ofCircle_quadCoeff, ofCircle_linearCoeff,
    ofCircle_constantCoeff, one_mul, intervalSq, intervalVec, vsub_eq_sub,
    q_apply, dot_apply, Vec.x_neg, Vec.t_neg, Vec.x_sub, Vec.t_sub]
  ring

@[simp] theorem mem_ofCircle_iff (C : LorentzCircle) (P : Point) :
    P ∈ ofCircle C ↔ P ∈ C := by
  rw [mem_iff, eval_ofCircle, LorentzCircle.mem_iff]
  constructor <;> intro h <;> linarith

@[simp] theorem carrier_ofCircle (C : LorentzCircle) :
    (ofCircle C).carrier = {P | P ∈ C} := by
  ext P
  simp [sub_eq_zero]

def ofPointNormalLine (O : Point) (normal : Vec) : Cycle where
  quadCoeff := 0
  linearCoeff := (2 : ℝ)⁻¹ • normal
  constantCoeff := -dot normal O

@[simp] theorem ofPointNormalLine_quadCoeff (O : Point) (normal : Vec) :
    (ofPointNormalLine O normal).quadCoeff = 0 := rfl

@[simp] theorem eval_ofPointNormalLine (O : Point) (normal : Vec) (P : Point) :
    (ofPointNormalLine O normal).eval P =
      dot normal (intervalVec O P) := by
  simp only [eval, ofPointNormalLine, zero_mul, zero_add, dot_apply,
    intervalVec, vsub_eq_sub, Vec.x_smul, Vec.t_smul, Vec.x_sub, Vec.t_sub]
  ring

theorem mem_ofPointNormalLine_iff (O : Point) (normal : Vec) (P : Point) :
    P ∈ ofPointNormalLine O normal ↔ P ∈ perpendicularThrough O normal := by
  rw [mem_iff, eval_ofPointNormalLine, mem_perpendicularThrough_iff,
    isOrthogonal_iff_dot_eq_zero, dot_comm normal (intervalVec O P)]

end Cycle

end

end MinkowskiMerge
