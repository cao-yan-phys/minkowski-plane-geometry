import MinkowskiMerge.Length


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable def positiveComplexSqrt (s : ℝ) : ℂ :=
  if 0 < s then (Real.sqrt s : ℂ)
  else if s < 0 then Complex.I * (Real.sqrt (-s) : ℂ)
  else 0

theorem positiveComplexSqrt_of_pos {s : ℝ} (h : 0 < s) :
    positiveComplexSqrt s = (Real.sqrt s : ℂ) := by
  unfold positiveComplexSqrt
  rw [if_pos h]

theorem positiveComplexSqrt_of_neg {s : ℝ} (h : s < 0) :
    positiveComplexSqrt s = Complex.I * (Real.sqrt (-s) : ℂ) := by
  unfold positiveComplexSqrt
  rw [if_neg (not_lt_of_ge h.le), if_pos h]

theorem positiveComplexSqrt_of_zero {s : ℝ} (h : s = 0) :
    positiveComplexSqrt s = 0 := by
  subst s
  norm_num [positiveComplexSqrt]

@[simp] theorem positiveComplexSqrt_sq (s : ℝ) :
    positiveComplexSqrt s ^ 2 = (s : ℂ) := by
  by_cases hpos : 0 < s
  · rw [positiveComplexSqrt_of_pos hpos]
    rw [(Complex.ofReal_pow (Real.sqrt s) 2).symm]
    rw [Real.sq_sqrt hpos.le]
  · by_cases hneg : s < 0
    · rw [positiveComplexSqrt_of_neg hneg]
      calc
        (Complex.I * (Real.sqrt (-s) : ℂ)) ^ 2 =
            -((Real.sqrt (-s) : ℂ) ^ 2) := by
              ring_nf
              simp
        _ = -(((Real.sqrt (-s)) ^ 2 : ℝ) : ℂ) := by
              rw [(Complex.ofReal_pow (Real.sqrt (-s)) 2).symm]
        _ = -((-s : ℝ) : ℂ) := by
              rw [Real.sq_sqrt (by linarith)]
        _ = (s : ℂ) := by norm_num
    · have hzero : s = 0 := by linarith
      rw [positiveComplexSqrt_of_zero hzero]
      rw [hzero]
      norm_num

theorem positiveComplexSqrt_eq_real_of_eq_sq {s r : ℝ}
    (hr : 0 ≤ r) (hs : s = r ^ 2) :
    positiveComplexSqrt s = (r : ℂ) := by
  by_cases hr0 : r = 0
  · subst r
    have hs0 : s = 0 := by simpa using hs
    rw [positiveComplexSqrt_of_zero hs0]
    norm_num
  · have hspos : 0 < s := by
      rw [hs]
      exact sq_pos_of_ne_zero hr0
    rw [positiveComplexSqrt_of_pos hspos, hs, Real.sqrt_sq hr]

theorem positiveComplexSqrt_eq_I_mul_real_of_eq_neg_sq {s r : ℝ}
    (hr : 0 ≤ r) (hs : s = -r ^ 2) :
    positiveComplexSqrt s = Complex.I * (r : ℂ) := by
  by_cases hr0 : r = 0
  · subst r
    have hs0 : s = 0 := by simpa using hs
    rw [positiveComplexSqrt_of_zero hs0]
    norm_num
  · have hsneg : s < 0 := by
      rw [hs]
      exact neg_lt_zero.mpr (sq_pos_of_ne_zero hr0)
    rw [positiveComplexSqrt_of_neg hsneg, hs, neg_neg, Real.sqrt_sq hr]

theorem complexLength_eq_positiveComplexSqrt (v : Vec) :
    complexLength v = positiveComplexSqrt (q v) := rfl

private theorem sqrt_four : Real.sqrt (4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num

theorem positiveComplexSqrt_div_four (s : ℝ) :
    positiveComplexSqrt (s / 4) = positiveComplexSqrt s / 2 := by
  by_cases hpos : 0 < s
  · have hpos' : 0 < s / 4 := by linarith
    have hroot : Real.sqrt (s / 4) = Real.sqrt s / 2 := by
      rw [Real.sqrt_div hpos.le]
      rw [sqrt_four]
    rw [positiveComplexSqrt_of_pos hpos', positiveComplexSqrt_of_pos hpos]
    exact_mod_cast hroot
  · by_cases hneg : s < 0
    · have hneg' : s / 4 < 0 := by linarith
      have hroot : Real.sqrt (-(s / 4)) = Real.sqrt (-s) / 2 := by
        rw [show -(s / 4) = (-s) / 4 by ring]
        rw [Real.sqrt_div (by linarith)]
        rw [sqrt_four]
      rw [positiveComplexSqrt_of_neg hneg', positiveComplexSqrt_of_neg hneg,
        hroot]
      push_cast
      ring
    · have hzero : s = 0 := by linarith
      subst s
      norm_num [positiveComplexSqrt]

end MinkowskiMerge
