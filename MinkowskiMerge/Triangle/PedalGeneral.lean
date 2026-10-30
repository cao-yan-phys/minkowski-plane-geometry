import MinkowskiMerge.Triangle.Pedal
import MinkowskiMerge.Triangle.Heron
import MinkowskiMerge.Triangle.Relabel

set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

private theorem q_sub_rev (u v : Vec) : q (u - v) = q (v - u) := by
  rw [show u - v = -(v - u) by module, q_neg]

theorem perpendicularFoot_eq_side_squares (A B C : Point)
    (hBC : IsNonNullLine B C) :
    perpendicularFoot A B C hBC =
      C + ((q (B - C) + q (A - C) - q (A - B)) /
        (2 * q (B - C))) • (B - C) := by
  have hn : q (B - C) ≠ 0 := by
    simpa only [IsNonNullLine, intervalSq, intervalVec, vsub_eq_sub,
      q_sub_rev C B] using hBC
  simp only [perpendicularFoot, footParameter, AffineMap.lineMap_apply_module',
    intervalVec, intervalSq, vsub_eq_sub]
  rw [q_sub_rev C B]
  apply Vec.ext <;>
    simp only [Vec.x_add, Vec.t_add, Vec.x_sub, Vec.t_sub, Vec.x_smul, Vec.t_smul] <;>
    field_simp [hn] <;> simp only [q_apply, dot_apply, Vec.x_sub, Vec.t_sub] <;> ring

def pedalAtOrthocenter (T : Triangle) (hS : T.SidesNonNull) : Triangle :=
  ⟨perpendicularFoot T.A T.B T.C hS.1,
    perpendicularFoot T.B T.C T.A hS.2.1,
    perpendicularFoot T.C T.A T.B hS.2.2⟩

def pedalSquareWeightA (T : Triangle) : ℝ :=
  T.sideSqA * (T.sideSqA - T.sideSqB - T.sideSqC)

def pedalSquareWeightB (T : Triangle) : ℝ :=
  T.sideSqB * (T.sideSqB - T.sideSqC - T.sideSqA)

def pedalSquareWeightC (T : Triangle) : ℝ :=
  T.sideSqC * (T.sideSqC - T.sideSqA - T.sideSqB)

def pedalSquareWeightSum (T : Triangle) : ℝ :=
  T.pedalSquareWeightA + T.pedalSquareWeightB + T.pedalSquareWeightC

private theorem side_squares_reverse (T : Triangle) :
    T.sideSqA = q (T.B - T.C) ∧ T.sideSqB = q (T.A - T.C) ∧
      T.sideSqC = q (T.A - T.B) := by
  simp only [sideSqA, sideSqB, sideSqC, intervalSq, intervalVec, vsub_eq_sub]
  exact ⟨q_sub_rev _ _, trivial, q_sub_rev _ _⟩

theorem pedalAtOrthocenter_feet (T : Triangle) (hS : T.SidesNonNull) :
    (T.pedalAtOrthocenter hS).A =
        T.C + ((T.sideSqA + T.sideSqB - T.sideSqC) /
          (2 * T.sideSqA)) • (T.B - T.C) ∧
      (T.pedalAtOrthocenter hS).B =
        T.C + ((T.sideSqA + T.sideSqB - T.sideSqC) /
          (2 * T.sideSqB)) • (T.A - T.C) ∧
      (T.pedalAtOrthocenter hS).C =
        T.B + ((T.sideSqA + T.sideSqC - T.sideSqB) /
          (2 * T.sideSqC)) • (T.A - T.B) := by
  obtain ⟨hA, hB, hC⟩ := side_squares_reverse T
  have hAn : T.sideSqA ≠ 0 := hS.1
  have hBn : T.sideSqB ≠ 0 := hS.2.1
  have hCn : T.sideSqC ≠ 0 := hS.2.2
  change perpendicularFoot T.A T.B T.C hS.1 = _ ∧
    perpendicularFoot T.B T.C T.A hS.2.1 = _ ∧
    perpendicularFoot T.C T.A T.B hS.2.2 = _
  rw [perpendicularFoot_eq_side_squares, perpendicularFoot_eq_side_squares,
    perpendicularFoot_eq_side_squares]
  rw [← hA, ← hB, ← hC, q_sub_rev T.C T.A, ← hB,
    q_sub_rev T.B T.A, ← hC, q_sub_rev T.C T.B, ← hA]
  refine ⟨rfl, ?_, ?_⟩ <;> apply Vec.ext <;>
    simp only [Vec.x_add, Vec.t_add, Vec.x_sub, Vec.t_sub, Vec.x_smul, Vec.t_smul] <;>
    field_simp [hBn, hCn] <;> ring

theorem pedal_square_weight_sum (T : Triangle) :
    T.pedalSquareWeightSum = 4 * T.signedDoubleArea ^ 2 := by
  have h := sideSq_heron_polynomial T
  change T.sideSqA * (T.sideSqA - T.sideSqB - T.sideSqC) +
    T.sideSqB * (T.sideSqB - T.sideSqC - T.sideSqA) +
    T.sideSqC * (T.sideSqC - T.sideSqA - T.sideSqB) = _
  nlinarith [h]

theorem pedal_square_weight_sum_ne_zero (T : Triangle) (hN : T.Nondegenerate) :
    T.pedalSquareWeightSum ≠ 0 := by
  rw [pedal_square_weight_sum]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hN.signedDoubleArea_ne_zero)

theorem pedal_weighted_foot_identity_general
    (A B C PA PB PC : Point) (x y z : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hqx : x = q (B - C)) (hqy : y = q (C - A)) (hqz : z = q (A - B))
    (hAB : q A = q B) (hAC : q A = q C)
    (hPA : PA = C + ((x + y - z) / (2 * x)) • (B - C))
    (hPB : PB = C + ((x + y - z) / (2 * y)) • (A - C))
    (hPC : PC = B + ((x + z - y) / (2 * z)) • (A - B)) :
    (x * (x - y - z)) • PA + (y * (y - z - x)) • PB +
        (z * (z - x - y)) • PC =
      (x * (x - y - z) + y * (y - z - x) + z * (z - x - y)) •
        normalizedOrthocenter A B C := by
  have hrel := pedal_circumcentric_relation A B C x y z hqx hqy hqz hAB hAC
  have hrelx := congrArg Vec.x hrel
  have hrelt := congrArg Vec.t hrel
  rw [hPA, hPB, hPC]
  apply Vec.ext <;>
    simp only [Vec.x_add, Vec.t_add, Vec.x_sub, Vec.t_sub, Vec.x_smul,
      Vec.t_smul, Vec.x_zero, Vec.t_zero, normalizedOrthocenter_apply] at hrelx hrelt ⊢ <;>
    field_simp [hx, hy, hz] <;> nlinarith [hrelx, hrelt]

theorem pedal_barycentric_identity_general (T : Triangle)
    (hN : T.Nondegenerate) (hS : T.SidesNonNull)
    (hO : T.IsCircumcenterAtOrigin) :
    T.orthocenterAtOrigin =
      (T.pedalSquareWeightA / T.pedalSquareWeightSum) • (T.pedalAtOrthocenter hS).A +
      (T.pedalSquareWeightB / T.pedalSquareWeightSum) • (T.pedalAtOrthocenter hS).B +
      (T.pedalSquareWeightC / T.pedalSquareWeightSum) • (T.pedalAtOrthocenter hS).C := by
  obtain ⟨hA, hB, hC⟩ := side_squares_reverse T
  obtain ⟨hfA, hfB, hfC⟩ := pedalAtOrthocenter_feet T hS
  obtain ⟨hAB, hBC⟩ := (isCircumcenterAtOrigin_iff T).mp hO
  have hAC := hAB.trans hBC
  have hrel := pedal_weighted_foot_identity_general T.A T.B T.C
    (T.pedalAtOrthocenter hS).A (T.pedalAtOrthocenter hS).B
    (T.pedalAtOrthocenter hS).C T.sideSqA T.sideSqB T.sideSqC
    hS.1 hS.2.1 hS.2.2 hA (hB.trans (q_sub_rev _ _)) hC hAB hAC hfA hfB hfC
  have hn := pedal_square_weight_sum_ne_zero T hN
  change T.orthocenterAtOrigin = _
  change T.pedalSquareWeightA • _ + T.pedalSquareWeightB • _ +
    T.pedalSquareWeightC • _ = T.pedalSquareWeightSum • T.orthocenterAtOrigin at hrel
  have hx := congrArg Vec.x hrel
  have ht := congrArg Vec.t hrel
  apply Vec.ext <;>
    simp only [Vec.x_add, Vec.t_add, Vec.x_smul, Vec.t_smul] at hx ht ⊢ <;>
    field_simp [hn] <;> nlinarith [hx, ht]

private def rotateSidesNonNull (T : Triangle) (hS : T.SidesNonNull) :
    T.rotate.SidesNonNull := ⟨hS.2.1, hS.2.2, hS.1⟩

theorem pedal_side_sq_general_A (T : Triangle) (hS : T.SidesNonNull) :
    (T.pedalAtOrthocenter hS).sideSqA =
      T.sideSqA * (T.sideSqA - T.sideSqB - T.sideSqC) ^ 2 /
        (4 * T.sideSqB * T.sideSqC) := by
  obtain ⟨hA, hB, hC⟩ := side_squares_reverse T
  obtain ⟨_, hfB, hfC⟩ := pedalAtOrthocenter_feet T hS
  change q ((T.pedalAtOrthocenter hS).C - (T.pedalAtOrthocenter hS).B) = _
  rw [q_sub_rev]
  exact pedal_side_A_sq_from_param T.A T.B T.C _ _ T.sideSqA T.sideSqB T.sideSqC
    hS.2.1 hS.2.2 hA hB hC hfB hfC

theorem pedal_side_sq_general (T : Triangle) (hS : T.SidesNonNull) :
    (T.pedalAtOrthocenter hS).sideSqA =
        T.pedalSquareWeightA ^ 2 / (4 * T.sideSqA * T.sideSqB * T.sideSqC) ∧
      (T.pedalAtOrthocenter hS).sideSqB =
        T.pedalSquareWeightB ^ 2 / (4 * T.sideSqA * T.sideSqB * T.sideSqC) ∧
      (T.pedalAtOrthocenter hS).sideSqC =
        T.pedalSquareWeightC ^ 2 / (4 * T.sideSqA * T.sideSqB * T.sideSqC) := by
  have hA := pedal_side_sq_general_A T hS
  have hB := pedal_side_sq_general_A T.rotate (rotateSidesNonNull T hS)
  have hC := pedal_side_sq_general_A T.rotate.rotate
    (rotateSidesNonNull T.rotate (rotateSidesNonNull T hS))
  change (T.pedalAtOrthocenter hS).sideSqB =
    T.sideSqB * (T.sideSqB - T.sideSqC - T.sideSqA) ^ 2 /
      (4 * T.sideSqC * T.sideSqA) at hB
  change (T.pedalAtOrthocenter hS).sideSqC =
    T.sideSqC * (T.sideSqC - T.sideSqA - T.sideSqB) ^ 2 /
      (4 * T.sideSqA * T.sideSqB) at hC
  rw [hA, hB, hC]
  change _ = (T.sideSqA * (T.sideSqA - T.sideSqB - T.sideSqC)) ^ 2 / _ ∧
    _ = (T.sideSqB * (T.sideSqB - T.sideSqC - T.sideSqA)) ^ 2 / _ ∧
    _ = (T.sideSqC * (T.sideSqC - T.sideSqA - T.sideSqB)) ^ 2 / _
  constructor
  · field_simp [hS.1, hS.2.1, hS.2.2]
  constructor <;> field_simp [hS.1, hS.2.1, hS.2.2]

private theorem pedal_area_from_side_squares
    (A B C PA PB PC : Point) (x y z : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hPA : PA = C + ((x + y - z) / (2 * x)) • (B - C))
    (hPB : PB = C + ((x + y - z) / (2 * y)) • (A - C))
    (hPC : PC = B + ((x + z - y) / (2 * z)) • (A - B)) :
    MinkowskiMerge.signedDoubleArea PA PB PC =
      -((x - y - z) * (x - y + z) * (x + y - z)) /
        (4 * x * y * z) * MinkowskiMerge.signedDoubleArea A B C := by
  rw [hPA, hPB, hPC]
  simp only [MinkowskiMerge.signedDoubleArea, intervalVec, vsub_eq_sub,
    br_apply, Vec.x_add, Vec.t_add, Vec.x_sub, Vec.t_sub, Vec.x_smul, Vec.t_smul]
  field_simp [hx, hy, hz]
  ring

theorem pedal_area_general (T : Triangle) (hS : T.SidesNonNull) :
    (T.pedalAtOrthocenter hS).signedDoubleArea =
      -((T.sideSqA - T.sideSqB - T.sideSqC) *
        (T.sideSqA - T.sideSqB + T.sideSqC) *
        (T.sideSqA + T.sideSqB - T.sideSqC)) /
        (4 * T.sideSqA * T.sideSqB * T.sideSqC) * T.signedDoubleArea := by
  obtain ⟨hA, hB, hC⟩ := pedalAtOrthocenter_feet T hS
  exact pedal_area_from_side_squares T.A T.B T.C _ _ _
    T.sideSqA T.sideSqB T.sideSqC hS.1 hS.2.1 hS.2.2 hA hB hC

def NonorthogonalAdjacentSides (T : Triangle) : Prop :=
  dot (T.B - T.A) (T.C - T.A) ≠ 0 ∧
    dot (T.C - T.B) (T.A - T.B) ≠ 0 ∧
    dot (T.A - T.C) (T.B - T.C) ≠ 0

theorem nonorthogonalAdjacentSides_iff (T : Triangle) :
    T.NonorthogonalAdjacentSides ↔
      T.sideSqA - T.sideSqB - T.sideSqC ≠ 0 ∧
        T.sideSqB - T.sideSqC - T.sideSqA ≠ 0 ∧
          T.sideSqC - T.sideSqA - T.sideSqB ≠ 0 := by
  have hA : T.sideSqA - T.sideSqB - T.sideSqC =
      -2 * dot (T.B - T.A) (T.C - T.A) := by
    simp only [sideSqA, sideSqB, sideSqC, intervalSq, intervalVec, vsub_eq_sub,
      q_apply, dot_apply, Vec.x_sub, Vec.t_sub]
    ring
  have hB : T.sideSqB - T.sideSqC - T.sideSqA =
      -2 * dot (T.C - T.B) (T.A - T.B) := by
    simp only [sideSqA, sideSqB, sideSqC, intervalSq, intervalVec, vsub_eq_sub,
      q_apply, dot_apply, Vec.x_sub, Vec.t_sub]
    ring
  have hC : T.sideSqC - T.sideSqA - T.sideSqB =
      -2 * dot (T.A - T.C) (T.B - T.C) := by
    simp only [sideSqA, sideSqB, sideSqC, intervalSq, intervalVec, vsub_eq_sub,
      q_apply, dot_apply, Vec.x_sub, Vec.t_sub]
    ring
  rw [hA, hB, hC]
  norm_num [NonorthogonalAdjacentSides, mul_ne_zero_iff]

theorem pedal_nondegenerate_general (T : Triangle) (hN : T.Nondegenerate)
    (hS : T.SidesNonNull) (hAngles : T.NonorthogonalAdjacentSides) :
    (T.pedalAtOrthocenter hS).Nondegenerate := by
  obtain ⟨hA, hB, hC⟩ := (nonorthogonalAdjacentSides_iff T).mp hAngles
  apply (nondegenerate_iff_signedDoubleArea_ne_zero _).mpr
  rw [pedal_area_general]
  have hB' : T.sideSqA - T.sideSqB + T.sideSqC ≠ 0 := by
    intro hz
    apply hB
    linarith
  have hC' : T.sideSqA + T.sideSqB - T.sideSqC ≠ 0 := by
    intro hz
    apply hC
    linarith
  exact mul_ne_zero (div_ne_zero
    (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hA hB') hC'))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hS.1) hS.2.1) hS.2.2))
    hN.signedDoubleArea_ne_zero

theorem pedal_nonmixed_general (T : Triangle) (hS : T.SidesNonNull)
    (hAngles : T.NonorthogonalAdjacentSides) :
    (T.pedalAtOrthocenter hS).IsNonMixed := by
  obtain ⟨hA, hB, hC⟩ := (nonorthogonalAdjacentSides_iff T).mp hAngles
  have hwA : T.pedalSquareWeightA ≠ 0 := mul_ne_zero hS.1 hA
  have hwB : T.pedalSquareWeightB ≠ 0 := mul_ne_zero hS.2.1 hB
  have hwC : T.pedalSquareWeightC ≠ 0 := mul_ne_zero hS.2.2 hC
  obtain ⟨heA, heB, heC⟩ := pedal_side_sq_general T hS
  have hd : 4 * T.sideSqA * T.sideSqB * T.sideSqC ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hS.1) hS.2.1) hS.2.2
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · right
    change (T.pedalAtOrthocenter hS).sideSqA < 0 ∧
      (T.pedalAtOrthocenter hS).sideSqB < 0 ∧ (T.pedalAtOrthocenter hS).sideSqC < 0
    rw [heA, heB, heC]
    exact ⟨div_neg_of_pos_of_neg (sq_pos_of_ne_zero hwA) hneg,
      div_neg_of_pos_of_neg (sq_pos_of_ne_zero hwB) hneg,
      div_neg_of_pos_of_neg (sq_pos_of_ne_zero hwC) hneg⟩
  · left
    change 0 < (T.pedalAtOrthocenter hS).sideSqA ∧
      0 < (T.pedalAtOrthocenter hS).sideSqB ∧ 0 < (T.pedalAtOrthocenter hS).sideSqC
    rw [heA, heB, heC]
    exact ⟨div_pos (sq_pos_of_ne_zero hwA) hpos,
      div_pos (sq_pos_of_ne_zero hwB) hpos, div_pos (sq_pos_of_ne_zero hwC) hpos⟩

def pedalComplexSideA (T : Triangle) : ℂ :=
  T.sideComplexLengthA *
    (T.sideComplexLengthA ^ 2 - T.sideComplexLengthB ^ 2 - T.sideComplexLengthC ^ 2) /
      (2 * T.sideComplexLengthB * T.sideComplexLengthC)

def pedalComplexSideB (T : Triangle) : ℂ :=
  T.sideComplexLengthB *
    (T.sideComplexLengthB ^ 2 - T.sideComplexLengthC ^ 2 - T.sideComplexLengthA ^ 2) /
      (2 * T.sideComplexLengthC * T.sideComplexLengthA)

def pedalComplexSideC (T : Triangle) : ℂ :=
  T.sideComplexLengthC *
    (T.sideComplexLengthC ^ 2 - T.sideComplexLengthA ^ 2 - T.sideComplexLengthB ^ 2) /
      (2 * T.sideComplexLengthA * T.sideComplexLengthB)

private theorem complex_sides_ne_zero (T : Triangle) (hS : T.SidesNonNull) :
    T.sideComplexLengthA ≠ 0 ∧ T.sideComplexLengthB ≠ 0 ∧
      T.sideComplexLengthC ≠ 0 := by
  have hA := T.sideComplexLengthA_sq
  have hB := T.sideComplexLengthB_sq
  have hC := T.sideComplexLengthC_sq
  constructor
  · intro hz
    rw [hz, zero_pow (by norm_num)] at hA
    exact hS.1 (by exact_mod_cast hA.symm)
  constructor
  · intro hz
    rw [hz, zero_pow (by norm_num)] at hB
    exact hS.2.1 (by exact_mod_cast hB.symm)
  · intro hz
    rw [hz, zero_pow (by norm_num)] at hC
    exact hS.2.2 (by exact_mod_cast hC.symm)

theorem pedal_complex_sides_scale (T : Triangle) (hS : T.SidesNonNull) :
    (2 * T.sideComplexLengthA * T.sideComplexLengthB * T.sideComplexLengthC) *
        T.pedalComplexSideA = (T.pedalSquareWeightA : ℂ) ∧
      (2 * T.sideComplexLengthA * T.sideComplexLengthB * T.sideComplexLengthC) *
        T.pedalComplexSideB = (T.pedalSquareWeightB : ℂ) ∧
      (2 * T.sideComplexLengthA * T.sideComplexLengthB * T.sideComplexLengthC) *
        T.pedalComplexSideC = (T.pedalSquareWeightC : ℂ) := by
  obtain ⟨ha, hb, hc⟩ := complex_sides_ne_zero T hS
  have hA := T.sideComplexLengthA_sq
  have hB := T.sideComplexLengthB_sq
  have hC := T.sideComplexLengthC_sq
  simp only [pedalComplexSideA, pedalComplexSideB, pedalComplexSideC,
    pedalSquareWeightA, pedalSquareWeightB, pedalSquareWeightC]
  push_cast
  simp only [← hA, ← hB, ← hC]
  constructor
  · field_simp [ha, hb, hc]
  constructor <;> field_simp [ha, hb, hc]

theorem pedal_complex_side_sum_general (T : Triangle) (hS : T.SidesNonNull) :
    T.pedalComplexSideA + T.pedalComplexSideB + T.pedalComplexSideC =
      -8 * T.complexArea ^ 2 /
        (T.sideComplexLengthA * T.sideComplexLengthB * T.sideComplexLengthC) := by
  obtain ⟨ha, hb, hc⟩ := complex_sides_ne_zero T hS
  obtain ⟨hA, hB, hC⟩ := pedal_complex_sides_scale T hS
  have hsum :
      (2 * T.sideComplexLengthA * T.sideComplexLengthB * T.sideComplexLengthC) *
        (T.pedalComplexSideA + T.pedalComplexSideB + T.pedalComplexSideC) =
          (T.pedalSquareWeightSum : ℂ) := by
    change _ = ((T.pedalSquareWeightA + T.pedalSquareWeightB +
      T.pedalSquareWeightC : ℝ) : ℂ)
    push_cast
    linear_combination hA + hB + hC
  rw [pedal_square_weight_sum] at hsum
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero ha hb) hc)).2
  rw [complexArea_sq]
  push_cast at hsum ⊢
  linear_combination hsum / 2

theorem pedal_complex_side_sum_ne_zero (T : Triangle)
    (hN : T.Nondegenerate) (hS : T.SidesNonNull) :
    T.pedalComplexSideA + T.pedalComplexSideB + T.pedalComplexSideC ≠ 0 := by
  rw [pedal_complex_side_sum_general T hS]
  obtain ⟨ha, hb, hc⟩ := complex_sides_ne_zero T hS
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hN.complexArea_ne_zero))
    (mul_ne_zero (mul_ne_zero ha hb) hc)

private theorem normalized_complex_weight (K S p : ℂ) (W w : ℝ)
    (hKS : K * S = (W : ℂ)) (hKp : K * p = (w : ℂ))
    (hS : S ≠ 0) (hW : W ≠ 0) :
    p / S = ((w / W : ℝ) : ℂ) := by
  push_cast
  apply (div_eq_div_iff hS (by exact_mod_cast hW)).2
  rw [← hKS, ← hKp]
  ring

theorem pedal_complex_coefficients_general (T : Triangle)
    (hN : T.Nondegenerate) (hS : T.SidesNonNull) :
    T.pedalComplexSideA /
        (T.pedalComplexSideA + T.pedalComplexSideB + T.pedalComplexSideC) =
          ((T.pedalSquareWeightA / T.pedalSquareWeightSum : ℝ) : ℂ) ∧
      T.pedalComplexSideB /
        (T.pedalComplexSideA + T.pedalComplexSideB + T.pedalComplexSideC) =
          ((T.pedalSquareWeightB / T.pedalSquareWeightSum : ℝ) : ℂ) ∧
      T.pedalComplexSideC /
        (T.pedalComplexSideA + T.pedalComplexSideB + T.pedalComplexSideC) =
          ((T.pedalSquareWeightC / T.pedalSquareWeightSum : ℝ) : ℂ) := by
  obtain ⟨hA, hB, hC⟩ := pedal_complex_sides_scale T hS
  have hsum :
      (2 * T.sideComplexLengthA * T.sideComplexLengthB * T.sideComplexLengthC) *
        (T.pedalComplexSideA + T.pedalComplexSideB + T.pedalComplexSideC) =
          (T.pedalSquareWeightSum : ℂ) := by
    change _ = ((T.pedalSquareWeightA + T.pedalSquareWeightB +
      T.pedalSquareWeightC : ℝ) : ℂ)
    push_cast
    linear_combination hA + hB + hC
  have hs := pedal_complex_side_sum_ne_zero T hN hS
  have hw := pedal_square_weight_sum_ne_zero T hN
  exact ⟨normalized_complex_weight _ _ _ _ _ hsum hA hs hw,
    normalized_complex_weight _ _ _ _ _ hsum hB hs hw,
    normalized_complex_weight _ _ _ _ _ hsum hC hs hw⟩

private theorem complex_square_from_weight (K p : ℂ) (w d s : ℝ)
    (hKp : K * p = (w : ℂ)) (hK : K ^ 2 = (d : ℂ))
    (hd : d ≠ 0) (hs : s = w ^ 2 / d) : p ^ 2 = (s : ℂ) := by
  rw [hs]
  push_cast
  apply (eq_div_iff (by exact_mod_cast hd)).2
  calc
    p ^ 2 * (d : ℂ) = (K * p) ^ 2 := by rw [← hK]; ring
    _ = (w : ℂ) ^ 2 := by rw [hKp]

theorem pedal_complex_sides_sq_general (T : Triangle) (hS : T.SidesNonNull) :
    T.pedalComplexSideA ^ 2 = (T.pedalAtOrthocenter hS).sideComplexLengthA ^ 2 ∧
      T.pedalComplexSideB ^ 2 = (T.pedalAtOrthocenter hS).sideComplexLengthB ^ 2 ∧
      T.pedalComplexSideC ^ 2 = (T.pedalAtOrthocenter hS).sideComplexLengthC ^ 2 := by
  obtain ⟨hA, hB, hC⟩ := pedal_complex_sides_scale T hS
  obtain ⟨hsA, hsB, hsC⟩ := pedal_side_sq_general T hS
  have hK : (2 * T.sideComplexLengthA * T.sideComplexLengthB *
      T.sideComplexLengthC) ^ 2 =
        ((4 * T.sideSqA * T.sideSqB * T.sideSqC : ℝ) : ℂ) := by
    rw [mul_pow, mul_pow, mul_pow, T.sideComplexLengthA_sq,
      T.sideComplexLengthB_sq, T.sideComplexLengthC_sq]
    push_cast
    ring
  have hd : 4 * T.sideSqA * T.sideSqB * T.sideSqC ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hS.1) hS.2.1) hS.2.2
  rw [(T.pedalAtOrthocenter hS).sideComplexLengthA_sq,
    (T.pedalAtOrthocenter hS).sideComplexLengthB_sq,
    (T.pedalAtOrthocenter hS).sideComplexLengthC_sq]
  exact ⟨complex_square_from_weight _ _ _ _ _ hA hK hd hsA,
    complex_square_from_weight _ _ _ _ _ hB hK hd hsB,
    complex_square_from_weight _ _ _ _ _ hC hK hd hsC⟩

def IsSignedIncenterWithSides (U : Triangle) (P : Point) (pA pB pC : ℂ) : Prop :=
  U.Nondegenerate ∧ U.IsNonMixed ∧
    ∃ sa sb sc : ℝ, sa ^ 2 = 1 ∧ sb ^ 2 = 1 ∧ sc ^ 2 = 1 ∧
      pA = (sa : ℂ) * U.sideComplexLengthA ∧
      pB = (sb : ℂ) * U.sideComplexLengthB ∧
      pC = (sc : ℂ) * U.sideComplexLengthC ∧
      (MinkowskiMerge.signedDoubleArea P U.B U.C : ℂ) / pA =
        (MinkowskiMerge.signedDoubleArea P U.C U.A : ℂ) / pB ∧
      (MinkowskiMerge.signedDoubleArea P U.C U.A : ℂ) / pB =
        (MinkowskiMerge.signedDoubleArea P U.A U.B : ℂ) / pC

private theorem exists_signed_square_root (p l : ℂ) (h : p ^ 2 = l ^ 2) :
    ∃ s : ℝ, s ^ 2 = 1 ∧ p = (s : ℂ) * l := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact ⟨1, by norm_num, by simpa using h⟩
  · exact ⟨-1, by norm_num, by simpa using h⟩

private theorem complex_area_ratio (D : ℝ) (p S : ℂ) (w : ℝ)
    (hp : p ≠ 0) (hS : S ≠ 0) (hw : p / S = (w : ℂ)) :
    ((w * D : ℝ) : ℂ) / p = (D : ℂ) / S := by
  push_cast
  rw [← hw]
  field_simp [hp, hS]

theorem pedal_signed_incenter_general (T : Triangle)
    (hN : T.Nondegenerate) (hS : T.SidesNonNull)
    (hO : T.IsCircumcenterAtOrigin) (hAngles : T.NonorthogonalAdjacentSides) :
    (T.pedalAtOrthocenter hS).IsSignedIncenterWithSides T.orthocenterAtOrigin
      T.pedalComplexSideA T.pedalComplexSideB T.pedalComplexSideC := by
  let U := T.pedalAtOrthocenter hS
  have hUN : U.Nondegenerate := pedal_nondegenerate_general T hN hS hAngles
  have hUT : U.IsNonMixed := pedal_nonmixed_general T hS hAngles
  obtain ⟨hA, hB, hC⟩ := pedal_complex_sides_sq_general T hS
  obtain ⟨sa, hsa, hpa⟩ := exists_signed_square_root _ _ hA
  obtain ⟨sb, hsb, hpb⟩ := exists_signed_square_root _ _ hB
  obtain ⟨sc, hsc, hpc⟩ := exists_signed_square_root _ _ hC
  have hpnA : T.pedalComplexSideA ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num), U.sideComplexLengthA_sq] at hA
    exact hUT.sidesNonNull.1 (by exact_mod_cast hA.symm)
  have hpnB : T.pedalComplexSideB ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num), U.sideComplexLengthB_sq] at hB
    exact hUT.sidesNonNull.2.1 (by exact_mod_cast hB.symm)
  have hpnC : T.pedalComplexSideC ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num), U.sideComplexLengthC_sq] at hC
    exact hUT.sidesNonNull.2.2 (by exact_mod_cast hC.symm)
  have hW := pedal_square_weight_sum_ne_zero T hN
  let w : BarycentricWeights :=
    ⟨T.pedalSquareWeightA / T.pedalSquareWeightSum,
      T.pedalSquareWeightB / T.pedalSquareWeightSum,
      T.pedalSquareWeightC / T.pedalSquareWeightSum, by
        dsimp [pedalSquareWeightSum] at hW ⊢
        field_simp [hW]⟩
  have hP : U.barycentricPoint w = T.orthocenterAtOrigin := by
    rw [barycentricPoint_eq_linearCombination]
    exact (pedal_barycentric_identity_general T hN hS hO).symm
  have hDA := U.signedDoubleArea_barycentric_BC w
  have hDB := U.signedDoubleArea_barycentric_CA w
  have hDC := U.signedDoubleArea_barycentric_AB w
  rw [hP] at hDA hDB hDC
  obtain ⟨hcA, hcB, hcC⟩ := pedal_complex_coefficients_general T hN hS
  have hsum := pedal_complex_side_sum_ne_zero T hN hS
  have hratioA := complex_area_ratio U.signedDoubleArea _ _ w.a hpnA hsum hcA
  have hratioB := complex_area_ratio U.signedDoubleArea _ _ w.b hpnB hsum hcB
  have hratioC := complex_area_ratio U.signedDoubleArea _ _ w.c hpnC hsum hcC
  refine ⟨hUN, hUT, sa, sb, sc, hsa, hsb, hsc, hpa, hpb, hpc, ?_, ?_⟩
  · rw [hDA, hDB]
    exact hratioA.trans hratioB.symm
  · rw [hDB, hDC]
    exact hratioB.trans hratioC.symm

theorem nonmixed_nonorthogonalAdjacentSides (T : Triangle) (hT : T.IsNonMixed) :
    T.NonorthogonalAdjacentSides := by
  have hprod : 0 < T.sideSqA * T.sideSqB ∧ 0 < T.sideSqB * T.sideSqC ∧
      0 < T.sideSqC * T.sideSqA := by
    rcases hT with hS | hTi
    · change 0 < T.sideSqA ∧ 0 < T.sideSqB ∧ 0 < T.sideSqC at hS
      exact ⟨mul_pos hS.1 hS.2.1, mul_pos hS.2.1 hS.2.2, mul_pos hS.2.2 hS.1⟩
    · change T.sideSqA < 0 ∧ T.sideSqB < 0 ∧ T.sideSqC < 0 at hTi
      exact ⟨mul_pos_of_neg_of_neg hTi.1 hTi.2.1,
        mul_pos_of_neg_of_neg hTi.2.1 hTi.2.2, mul_pos_of_neg_of_neg hTi.2.2 hTi.1⟩
  have hdot (u v : Vec) (h : 0 < q u * q v) : dot u v ≠ 0 := by
    intro hz
    have hg := gram_identity u v
    rw [hz] at hg
    nlinarith [sq_nonneg (br u v)]
  obtain ⟨hA, hB, hC⟩ := side_squares_reverse T
  refine ⟨hdot _ _ ?_, hdot _ _ ?_, hdot _ _ ?_⟩
  · rw [q_sub_rev T.B T.A, ← hC, q_sub_rev T.C T.A, ← hB]
    nlinarith [hprod.2.1]
  · rw [q_sub_rev T.C T.B, ← hA, ← hC]
    nlinarith [hprod.2.2]
  · rw [← hB, ← hA]
    nlinarith [hprod.1]

theorem pedal_nondegenerate_iff_general (T : Triangle) (hN : T.Nondegenerate)
    (hS : T.SidesNonNull) :
    (T.pedalAtOrthocenter hS).Nondegenerate ↔ T.NonorthogonalAdjacentSides := by
  constructor
  · intro hU
    have hn := hU.signedDoubleArea_ne_zero
    rw [pedal_area_general] at hn
    apply (nonorthogonalAdjacentSides_iff T).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro hz
      apply hn
      rw [hz]
      simp only [zero_mul, neg_zero, zero_div]
    · intro hz
      have he : T.sideSqA - T.sideSqB + T.sideSqC = 0 := by linarith
      apply hn
      rw [he]
      simp only [mul_zero, neg_zero, zero_div, zero_mul]
    · intro hz
      have he : T.sideSqA + T.sideSqB - T.sideSqC = 0 := by linarith
      apply hn
      rw [he]
      simp only [mul_zero, neg_zero, zero_div, zero_mul]
  · exact pedal_nondegenerate_general T hN hS

theorem pedal_triangle_center_theorem_general (T : Triangle)
    (hN : T.Nondegenerate) (hS : T.SidesNonNull)
    (hO : T.IsCircumcenterAtOrigin) :
    T.pedalComplexSideA + T.pedalComplexSideB + T.pedalComplexSideC =
        -8 * T.complexArea ^ 2 /
          (T.sideComplexLengthA * T.sideComplexLengthB * T.sideComplexLengthC) ∧
      T.pedalComplexSideA + T.pedalComplexSideB + T.pedalComplexSideC ≠ 0 ∧
      (T.pedalComplexSideA /
          (T.pedalComplexSideA + T.pedalComplexSideB + T.pedalComplexSideC) =
            ((T.pedalSquareWeightA / T.pedalSquareWeightSum : ℝ) : ℂ) ∧
        T.pedalComplexSideB /
          (T.pedalComplexSideA + T.pedalComplexSideB + T.pedalComplexSideC) =
            ((T.pedalSquareWeightB / T.pedalSquareWeightSum : ℝ) : ℂ) ∧
        T.pedalComplexSideC /
          (T.pedalComplexSideA + T.pedalComplexSideB + T.pedalComplexSideC) =
            ((T.pedalSquareWeightC / T.pedalSquareWeightSum : ℝ) : ℂ)) ∧
      (T.pedalComplexSideA ^ 2 =
          (T.pedalAtOrthocenter hS).sideComplexLengthA ^ 2 ∧
        T.pedalComplexSideB ^ 2 =
          (T.pedalAtOrthocenter hS).sideComplexLengthB ^ 2 ∧
        T.pedalComplexSideC ^ 2 =
          (T.pedalAtOrthocenter hS).sideComplexLengthC ^ 2) ∧
      T.orthocenterAtOrigin =
        (T.pedalComplexSideA /
          (T.pedalComplexSideA + T.pedalComplexSideB + T.pedalComplexSideC)).re •
            (T.pedalAtOrthocenter hS).A +
        (T.pedalComplexSideB /
          (T.pedalComplexSideA + T.pedalComplexSideB + T.pedalComplexSideC)).re •
            (T.pedalAtOrthocenter hS).B +
        (T.pedalComplexSideC /
          (T.pedalComplexSideA + T.pedalComplexSideB + T.pedalComplexSideC)).re •
            (T.pedalAtOrthocenter hS).C ∧
      (T.NonorthogonalAdjacentSides →
        (T.pedalAtOrthocenter hS).IsSignedIncenterWithSides T.orthocenterAtOrigin
          T.pedalComplexSideA T.pedalComplexSideB T.pedalComplexSideC) ∧
      (T.IsNonMixed → T.NonorthogonalAdjacentSides) := by
  obtain ⟨hcA, hcB, hcC⟩ := pedal_complex_coefficients_general T hN hS
  refine ⟨pedal_complex_side_sum_general T hS,
    pedal_complex_side_sum_ne_zero T hN hS, ⟨hcA, hcB, hcC⟩,
    pedal_complex_sides_sq_general T hS, ?_,
    pedal_signed_incenter_general T hN hS hO, nonmixed_nonorthogonalAdjacentSides T⟩
  rw [hcA, hcB, hcC]
  simpa only [Complex.ofReal_re] using pedal_barycentric_identity_general T hN hS hO

end
end Triangle
end MinkowskiMerge
