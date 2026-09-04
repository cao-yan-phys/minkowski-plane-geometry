import MinkowskiMerge.Form
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt


set_option autoImplicit false

namespace MinkowskiMerge

inductive CausalType
  | timelike
  | null
  | spacelike
  deriving DecidableEq, Repr

def IsTimelike (v : Vec) : Prop := q v < 0

def IsNull (v : Vec) : Prop := q v = 0

def IsSpacelike (v : Vec) : Prop := 0 < q v

def IsCausal (v : Vec) : Prop := q v ≤ 0

noncomputable def causalType (v : Vec) : CausalType :=
  if q v < 0 then .timelike else if q v = 0 then .null else .spacelike

noncomputable def absLength (v : Vec) : ℝ := Real.sqrt |q v|

noncomputable def complexLength (v : Vec) : ℂ :=
  if 0 < q v then (Real.sqrt (q v) : ℂ)
  else if q v < 0 then Complex.I * (Real.sqrt (-q v) : ℂ)
  else 0

theorem causal_trichotomy (v : Vec) :
    IsTimelike v ∨ IsNull v ∨ IsSpacelike v := by
  rcases lt_trichotomy (q v) 0 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem not_timelike_and_null (v : Vec) : ¬(IsTimelike v ∧ IsNull v) := by
  rintro ⟨ht, hn⟩
  change q v < 0 at ht
  change q v = 0 at hn
  linarith

theorem not_timelike_and_spacelike (v : Vec) :
    ¬(IsTimelike v ∧ IsSpacelike v) := by
  rintro ⟨ht, hs⟩
  change q v < 0 at ht
  change 0 < q v at hs
  linarith

theorem not_null_and_spacelike (v : Vec) : ¬(IsNull v ∧ IsSpacelike v) := by
  rintro ⟨hn, hs⟩
  change q v = 0 at hn
  change 0 < q v at hs
  linarith

@[simp] theorem causalType_eq_timelike_iff (v : Vec) :
    causalType v = .timelike ↔ IsTimelike v := by
  unfold causalType IsTimelike
  by_cases hneg : q v < 0
  · rw [if_pos hneg]
    constructor
    · intro _
      exact hneg
    · intro _
      rfl
  · rw [if_neg hneg]
    constructor
    · intro h
      split at h <;> cases h
    · intro h
      exact (hneg h).elim

@[simp] theorem causalType_eq_null_iff (v : Vec) :
    causalType v = .null ↔ IsNull v := by
  unfold causalType IsNull
  by_cases hneg : q v < 0
  · rw [if_pos hneg]
    constructor
    · intro h
      cases h
    · intro hzero
      linarith
  · rw [if_neg hneg]
    by_cases hzero : q v = 0
    · rw [if_pos hzero]
      constructor
      · intro _
        exact hzero
      · intro _
        rfl
    · rw [if_neg hzero]
      constructor
      · intro h
        cases h
      · intro h
        exact (hzero h).elim

@[simp] theorem causalType_eq_spacelike_iff (v : Vec) :
    causalType v = .spacelike ↔ IsSpacelike v := by
  unfold causalType IsSpacelike
  by_cases hneg : q v < 0
  · rw [if_pos hneg]
    constructor
    · intro h
      cases h
    · intro h
      linarith
  · rw [if_neg hneg]
    by_cases hzero : q v = 0
    · rw [if_pos hzero]
      constructor
      · intro h
        cases h
      · intro h
        linarith
    · rw [if_neg hzero]
      constructor
      · intro _
        exact lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hzero)
      · intro _
        rfl

@[simp] theorem isTimelike_neg (v : Vec) : IsTimelike (-v) ↔ IsTimelike v := by
  simp [IsTimelike]

@[simp] theorem isNull_neg (v : Vec) : IsNull (-v) ↔ IsNull v := by
  simp [IsNull]

@[simp] theorem isSpacelike_neg (v : Vec) : IsSpacelike (-v) ↔ IsSpacelike v := by
  simp [IsSpacelike]

theorem isTimelike_smul_iff {r : ℝ} (hr : r ≠ 0) (v : Vec) :
    IsTimelike (r • v) ↔ IsTimelike v := by
  simp only [IsTimelike, q_smul]
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  constructor <;> intro h <;> nlinarith

theorem isNull_smul_iff {r : ℝ} (hr : r ≠ 0) (v : Vec) :
    IsNull (r • v) ↔ IsNull v := by
  unfold IsNull
  rw [q_smul]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hr)
  · intro h
    rw [h, mul_zero]

theorem isSpacelike_smul_iff {r : ℝ} (hr : r ≠ 0) (v : Vec) :
    IsSpacelike (r • v) ↔ IsSpacelike v := by
  simp only [IsSpacelike, q_smul]
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  constructor <;> intro h <;> nlinarith

theorem isTimelike_iff_abs (v : Vec) : IsTimelike v ↔ |v.x| < |v.t| := by
  rw [IsTimelike, q_apply]
  constructor
  · intro h
    exact sq_lt_sq.mp (by linarith)
  · intro h
    have hsq := sq_lt_sq.mpr h
    linarith

theorem isSpacelike_iff_abs (v : Vec) : IsSpacelike v ↔ |v.t| < |v.x| := by
  rw [IsSpacelike, q_apply]
  constructor
  · intro h
    exact sq_lt_sq.mp (by linarith)
  · intro h
    have hsq := sq_lt_sq.mpr h
    linarith

theorem isNull_iff_abs (v : Vec) : IsNull v ↔ |v.x| = |v.t| := by
  rw [IsNull, q_apply]
  constructor
  · intro h
    have hsq : v.x ^ 2 = v.t ^ 2 := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · simp [h]
    · simp [h]
  · intro h
    rcases abs_eq_abs.mp h with h | h
    · rw [h]
      ring
    · rw [h]
      ring

@[simp] theorem absLength_nonneg (v : Vec) : 0 ≤ absLength v := by
  exact Real.sqrt_nonneg _

@[simp] theorem absLength_sq (v : Vec) : absLength v ^ 2 = |q v| := by
  exact Real.sq_sqrt (abs_nonneg _)

theorem complexLength_of_spacelike {v : Vec} (h : IsSpacelike v) :
    complexLength v = (Real.sqrt (q v) : ℂ) := by
  change 0 < q v at h
  unfold complexLength
  rw [if_pos h]

theorem complexLength_of_timelike {v : Vec} (h : IsTimelike v) :
    complexLength v = Complex.I * (Real.sqrt (-q v) : ℂ) := by
  change q v < 0 at h
  have hnot : ¬0 < q v := not_lt_of_ge h.le
  unfold complexLength
  rw [if_neg hnot, if_pos h]

theorem complexLength_of_null {v : Vec} (h : IsNull v) : complexLength v = 0 := by
  change q v = 0 at h
  unfold complexLength
  rw [h]
  norm_num

@[simp] theorem complexLength_sq (v : Vec) : complexLength v ^ 2 = (q v : ℂ) := by
  by_cases hpos : 0 < q v
  · rw [complexLength_of_spacelike hpos]
    rw [(Complex.ofReal_pow (Real.sqrt (q v)) 2).symm]
    rw [Real.sq_sqrt hpos.le]
  · by_cases hneg : q v < 0
    · rw [complexLength_of_timelike hneg]
      calc
        (Complex.I * (Real.sqrt (-q v) : ℂ)) ^ 2 =
            -((Real.sqrt (-q v) : ℂ) ^ 2) := by
              ring_nf
              simp
        _ = -(((Real.sqrt (-q v)) ^ 2 : ℝ) : ℂ) := by
              rw [(Complex.ofReal_pow (Real.sqrt (-q v)) 2).symm]
        _ = -((-q v : ℝ) : ℂ) := by
              rw [Real.sq_sqrt (by linarith)]
        _ = (q v : ℂ) := by norm_num
    · have hzero : q v = 0 := by linarith
      rw [complexLength_of_null hzero]
      rw [hzero]
      norm_num

end MinkowskiMerge
