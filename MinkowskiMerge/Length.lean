import MinkowskiMerge.Causal


set_option autoImplicit false

namespace MinkowskiMerge

theorem absLength_sq_of_spacelike {v : Vec} (hv : IsSpacelike v) :
    absLength v ^ 2 = q v := by
  rw [absLength_sq, abs_of_pos hv]

theorem absLength_sq_of_timelike {v : Vec} (hv : IsTimelike v) :
    absLength v ^ 2 = -q v := by
  rw [absLength_sq, abs_of_neg hv]

theorem absLength_pos_iff {v : Vec} : 0 < absLength v ↔ q v ≠ 0 := by
  rw [absLength, Real.sqrt_pos.iff, abs_pos]
  exact Iff.rfl

theorem complexLength_eq_absLength_of_spacelike {v : Vec} (hv : IsSpacelike v) :
    complexLength v = (absLength v : ℂ) := by
  rw [complexLength_of_spacelike hv]
  simp only [absLength, abs_of_pos hv]

theorem complexLength_eq_I_mul_absLength_of_timelike {v : Vec} (hv : IsTimelike v) :
    complexLength v = Complex.I * (absLength v : ℂ) := by
  rw [complexLength_of_timelike hv]
  simp only [absLength, abs_of_neg hv]

end MinkowskiMerge
