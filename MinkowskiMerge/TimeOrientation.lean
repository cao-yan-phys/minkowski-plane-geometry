import MinkowskiMerge.Transform.Lorentz


set_option autoImplicit false

namespace MinkowskiMerge

def IsFutureDirected (v : Vec) : Prop :=
  IsCausal v ∧ 0 ≤ v.t

def IsPastDirected (v : Vec) : Prop :=
  IsCausal v ∧ v.t ≤ 0

def IsFutureTimelike (v : Vec) : Prop :=
  IsTimelike v ∧ 0 < v.t

def IsPastTimelike (v : Vec) : Prop :=
  IsTimelike v ∧ v.t < 0

def CausallyPrecedes (P Q : Point) : Prop :=
  IsFutureDirected (intervalVec P Q)

def ChronologicallyPrecedes (P Q : Point) : Prop :=
  IsFutureTimelike (intervalVec P Q)

def LorentzEquiv.IsTimeOrientationPreserving (L : LorentzEquiv) : Prop :=
  ∀ v : Vec, IsFutureDirected v ↔ IsFutureDirected (L v)

theorem abs_x_le_t_of_futureDirected {v : Vec} (h : IsFutureDirected v) :
    |v.x| ≤ v.t := by
  change IsCausal v ∧ 0 ≤ v.t at h
  have hsq : v.x ^ 2 ≤ v.t ^ 2 := by
    have hcausal : IsCausal v := h.1
    change q v ≤ 0 at hcausal
    rw [q_apply] at hcausal
    linarith
  exact abs_le_of_sq_le_sq hsq h.2

theorem neg_futureDirected_iff (v : Vec) :
    IsFutureDirected (-v) ↔ IsPastDirected v := by
  simp [IsFutureDirected, IsPastDirected, IsCausal]

theorem neg_pastDirected_iff (v : Vec) :
    IsPastDirected (-v) ↔ IsFutureDirected v := by
  simp [IsFutureDirected, IsPastDirected, IsCausal]

theorem IsFutureDirected.add {v w : Vec}
    (hv : IsFutureDirected v) (hw : IsFutureDirected w) :
    IsFutureDirected (v + w) := by
  have hv_bounds := (abs_le.mp (abs_x_le_t_of_futureDirected hv))
  have hw_bounds := (abs_le.mp (abs_x_le_t_of_futureDirected hw))
  constructor
  · change IsCausal (v + w)
    change q (v + w) ≤ 0
    rw [q_apply, Vec.x_add, Vec.t_add]
    have hlower : -(v.t + w.t) ≤ v.x + w.x := by linarith
    have hupper : v.x + w.x ≤ v.t + w.t := by linarith
    have hsq := sq_le_sq' hlower hupper
    linarith
  · simp only [Vec.t_add]
    linarith [hv.2, hw.2]

theorem IsPastDirected.add {v w : Vec}
    (hv : IsPastDirected v) (hw : IsPastDirected w) :
    IsPastDirected (v + w) := by
  have hv' : IsFutureDirected (-v) := (neg_futureDirected_iff v).mpr hv
  have hw' : IsFutureDirected (-w) := (neg_futureDirected_iff w).mpr hw
  have hsum : IsFutureDirected ((-v) + (-w)) := hv'.add hw'
  have hneg : IsFutureDirected (-(v + w)) := by
    simpa [neg_add, add_comm] using hsum
  exact (neg_futureDirected_iff (v + w)).mp hneg

@[simp] theorem isFutureDirected_zero : IsFutureDirected (0 : Vec) := by
  norm_num [IsFutureDirected, IsCausal, q]

@[simp] theorem isPastDirected_zero : IsPastDirected (0 : Vec) := by
  norm_num [IsPastDirected, IsCausal, q]

theorem future_and_past_iff_eq_zero (v : Vec) :
    IsFutureDirected v ∧ IsPastDirected v ↔ v = 0 := by
  constructor
  · rintro ⟨hf, hp⟩
    change IsCausal v ∧ 0 ≤ v.t at hf
    change IsCausal v ∧ v.t ≤ 0 at hp
    have ht : v.t = 0 := le_antisymm hp.2 hf.2
    apply Vec.ext
    · have hx_sq : v.x ^ 2 ≤ 0 := by
        have hcausal : IsCausal v := hf.1
        change q v ≤ 0 at hcausal
        rw [q_apply, ht] at hcausal
        linarith
      exact sq_eq_zero_iff.mp (by linarith [sq_nonneg v.x])
    · simp [ht]
  · intro h
    subst v
    exact ⟨isFutureDirected_zero, isPastDirected_zero⟩

theorem futureTimelike_isFutureDirected {v : Vec} (h : IsFutureTimelike v) :
    IsFutureDirected v :=
  ⟨h.1.le, h.2.le⟩

theorem pastTimelike_isPastDirected {v : Vec} (h : IsPastTimelike v) :
    IsPastDirected v :=
  ⟨h.1.le, h.2.le⟩

theorem causallyPrecedes_refl (P : Point) : CausallyPrecedes P P := by
  simp [CausallyPrecedes, isFutureDirected_zero]

theorem causallyPrecedes_trans {P Q R : Point}
    (hPQ : CausallyPrecedes P Q) (hQR : CausallyPrecedes Q R) :
    CausallyPrecedes P R := by
  change IsFutureDirected (intervalVec P R)
  rw [← intervalVec_add P Q R]
  exact hPQ.add hQR

theorem causallyPrecedes_antisymm {P Q : Point}
    (hPQ : CausallyPrecedes P Q) (hQP : CausallyPrecedes Q P) : P = Q := by
  have hpast : IsPastDirected (intervalVec P Q) := by
    have hneg : IsFutureDirected (-(intervalVec P Q)) := by
      rw [← intervalVec_rev P Q]
      exact hQP
    exact (neg_futureDirected_iff (intervalVec P Q)).mp hneg
  have hzero : intervalVec P Q = 0 :=
    (future_and_past_iff_eq_zero (intervalVec P Q)).mp ⟨hPQ, hpast⟩
  change Q - P = 0 at hzero
  exact sub_eq_zero.mp hzero |>.symm

theorem chronologicallyPrecedes_irrefl (P : Point) :
    ¬ChronologicallyPrecedes P P := by
  intro h
  change IsFutureTimelike (intervalVec P P) at h
  rw [intervalVec_self] at h
  change IsFutureTimelike (0 : Vec) at h
  rcases h with ⟨ht, htime⟩
  norm_num [IsTimelike, q] at ht

private theorem abs_sinh_le_cosh (η : ℝ) :
    |Real.sinh η| ≤ Real.cosh η := by
  apply abs_le_of_sq_le_sq
  · nlinarith [Real.cosh_sq_sub_sinh_sq η]
  · exact (Real.cosh_pos η).le

private theorem futureDirected_boost
    (η : ℝ) {v : Vec} (hv : IsFutureDirected v) :
    IsFutureDirected (boostIsometry η v) := by
  constructor
  · exact ((boostIsometry η).isCausal_map v).mpr hv.1
  · change 0 ≤ Real.sinh η * v.x + Real.cosh η * v.t
    have hx : |v.x| ≤ v.t := abs_x_le_t_of_futureDirected hv
    have hs : |Real.sinh η| ≤ Real.cosh η := abs_sinh_le_cosh η
    have hprod : |Real.sinh η * v.x| ≤ Real.cosh η * v.t := by
      rw [abs_mul]
      exact mul_le_mul hs hx (abs_nonneg _) (Real.cosh_pos _).le
    have hlower := (abs_le.mp hprod).1
    linarith

theorem futureDirected_boost_iff (η : ℝ) (v : Vec) :
    IsFutureDirected (boostIsometry η v) ↔ IsFutureDirected v := by
  constructor
  · intro h
    have h' := futureDirected_boost (-η) h
    simpa only [boostIsometry_neg_apply] using h'
  · exact futureDirected_boost η

theorem LorentzEquiv.boost_isTimeOrientationPreserving (η : ℝ) :
    (boostIsometry η).IsTimeOrientationPreserving := by
  intro v
  exact (futureDirected_boost_iff η v).symm

theorem LorentzEquiv.causallyPrecedes_map_iff
    {L : LorentzEquiv} (hL : L.IsTimeOrientationPreserving) (P Q : Point) :
    CausallyPrecedes (L P) (L Q) ↔ CausallyPrecedes P Q := by
  change IsFutureDirected (intervalVec (L P) (L Q)) ↔
    IsFutureDirected (intervalVec P Q)
  rw [L.intervalVec_map]
  exact (hL _).symm

theorem causallyPrecedes_boost_iff (η : ℝ) (P Q : Point) :
    CausallyPrecedes (boostIsometry η P) (boostIsometry η Q) ↔
      CausallyPrecedes P Q := by
  exact (boostIsometry η).causallyPrecedes_map_iff
    (LorentzEquiv.boost_isTimeOrientationPreserving η) P Q

end MinkowskiMerge
