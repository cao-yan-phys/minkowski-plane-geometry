import MinkowskiMerge.Triangle.Pedal
import MinkowskiMerge.Triangle.Radii
import MinkowskiMerge.Triangle.Relabel
import Mathlib.Tactic


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

def pedalSignedLengthA (T : Triangle) : ℝ :=
  T.sideAbsLengthA *
    (T.sideAbsLengthA ^ 2 - T.sideAbsLengthB ^ 2 - T.sideAbsLengthC ^ 2) /
      (2 * T.sideAbsLengthB * T.sideAbsLengthC)

def pedalSignedLengthB (T : Triangle) : ℝ :=
  T.sideAbsLengthB *
    (T.sideAbsLengthB ^ 2 - T.sideAbsLengthC ^ 2 - T.sideAbsLengthA ^ 2) /
      (2 * T.sideAbsLengthC * T.sideAbsLengthA)

def pedalSignedLengthC (T : Triangle) : ℝ :=
  T.sideAbsLengthC *
    (T.sideAbsLengthC ^ 2 - T.sideAbsLengthA ^ 2 - T.sideAbsLengthB ^ 2) /
      (2 * T.sideAbsLengthA * T.sideAbsLengthB)

def pedalLengthA (T : Triangle) : ℝ :=
  T.sideAbsLengthA *
    |T.sideAbsLengthA ^ 2 - T.sideAbsLengthB ^ 2 - T.sideAbsLengthC ^ 2| /
      (2 * T.sideAbsLengthB * T.sideAbsLengthC)

def pedalLengthB (T : Triangle) : ℝ :=
  T.sideAbsLengthB *
    |T.sideAbsLengthB ^ 2 - T.sideAbsLengthC ^ 2 - T.sideAbsLengthA ^ 2| /
      (2 * T.sideAbsLengthC * T.sideAbsLengthA)

def pedalLengthC (T : Triangle) : ℝ :=
  T.sideAbsLengthC *
    |T.sideAbsLengthC ^ 2 - T.sideAbsLengthA ^ 2 - T.sideAbsLengthB ^ 2| /
      (2 * T.sideAbsLengthA * T.sideAbsLengthB)

private theorem real_heron_polynomial (a b c : ℝ) :
    4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 =
      (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) := by
  ring

private theorem unique_long_side_of_negative_heron
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hneg :
      (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) < 0) :
    b + c < a ∨ c + a < b ∨ a + b < c := by
  by_contra hlong
  have hA : ¬ b + c < a := by
    intro h
    exact hlong (Or.inl h)
  have hB : ¬ c + a < b := by
    intro h
    exact hlong (Or.inr (Or.inl h))
  have hC : ¬ a + b < c := by
    intro h
    exact hlong (Or.inr (Or.inr h))
  have hsum : 0 ≤ a + b + c := by linarith
  have hAf : 0 ≤ -a + b + c := by linarith
  have hBf : 0 ≤ a - b + c := by linarith
  have hCf : 0 ≤ a + b - c := by linarith
  have hnonneg :
      0 ≤ (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) :=
    mul_nonneg (mul_nonneg (mul_nonneg hsum hAf) hBf) hCf
  linarith

theorem nonmixed_side_moduli_heron (T : Triangle) (hT : T.IsNonMixed) :
    (T.sideAbsLengthA + T.sideAbsLengthB + T.sideAbsLengthC) *
        (-T.sideAbsLengthA + T.sideAbsLengthB + T.sideAbsLengthC) *
        (T.sideAbsLengthA - T.sideAbsLengthB + T.sideAbsLengthC) *
        (T.sideAbsLengthA + T.sideAbsLengthB - T.sideAbsLengthC) =
      -4 * T.signedDoubleArea ^ 2 := by
  have h := sideSq_heron_polynomial T
  rcases hT with hS | hTi
  · have hA : T.sideSqA = T.sideAbsLengthA ^ 2 := by
      simpa only [T.sideSqA_eq_q] using (absLength_sq_of_spacelike hS.1).symm
    have hB : T.sideSqB = T.sideAbsLengthB ^ 2 := by
      simpa only [T.sideSqB_eq_q] using (absLength_sq_of_spacelike hS.2.1).symm
    have hC : T.sideSqC = T.sideAbsLengthC ^ 2 := by
      simpa only [T.sideSqC_eq_q] using (absLength_sq_of_spacelike hS.2.2).symm
    rw [hA, hB, hC] at h
    calc
      (T.sideAbsLengthA + T.sideAbsLengthB + T.sideAbsLengthC) *
          (-T.sideAbsLengthA + T.sideAbsLengthB + T.sideAbsLengthC) *
          (T.sideAbsLengthA - T.sideAbsLengthB + T.sideAbsLengthC) *
          (T.sideAbsLengthA + T.sideAbsLengthB - T.sideAbsLengthC) =
        4 * T.sideAbsLengthB ^ 2 * T.sideAbsLengthC ^ 2 -
          (T.sideAbsLengthB ^ 2 + T.sideAbsLengthC ^ 2 -
            T.sideAbsLengthA ^ 2) ^ 2 :=
          (real_heron_polynomial T.sideAbsLengthA T.sideAbsLengthB
            T.sideAbsLengthC).symm
      _ = -4 * T.signedDoubleArea ^ 2 := h
  · have hA : T.sideSqA = -(T.sideAbsLengthA ^ 2) := by
      have hA' := absLength_sq_of_timelike hTi.1
      change T.sideAbsLengthA ^ 2 = -T.sideSqA at hA'
      linarith
    have hB : T.sideSqB = -(T.sideAbsLengthB ^ 2) := by
      have hB' := absLength_sq_of_timelike hTi.2.1
      change T.sideAbsLengthB ^ 2 = -T.sideSqB at hB'
      linarith
    have hC : T.sideSqC = -(T.sideAbsLengthC ^ 2) := by
      have hC' := absLength_sq_of_timelike hTi.2.2
      change T.sideAbsLengthC ^ 2 = -T.sideSqC at hC'
      linarith
    rw [hA, hB, hC] at h
    calc
      (T.sideAbsLengthA + T.sideAbsLengthB + T.sideAbsLengthC) *
          (-T.sideAbsLengthA + T.sideAbsLengthB + T.sideAbsLengthC) *
          (T.sideAbsLengthA - T.sideAbsLengthB + T.sideAbsLengthC) *
          (T.sideAbsLengthA + T.sideAbsLengthB - T.sideAbsLengthC) =
        4 * T.sideAbsLengthB ^ 2 * T.sideAbsLengthC ^ 2 -
          (T.sideAbsLengthB ^ 2 + T.sideAbsLengthC ^ 2 -
            T.sideAbsLengthA ^ 2) ^ 2 :=
          (real_heron_polynomial T.sideAbsLengthA T.sideAbsLengthB
            T.sideAbsLengthC).symm
      _ = -4 * T.signedDoubleArea ^ 2 := by nlinarith [h]

theorem nonmixed_unique_long_side (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) :
    T.sideAbsLengthB + T.sideAbsLengthC < T.sideAbsLengthA ∨
      T.sideAbsLengthC + T.sideAbsLengthA < T.sideAbsLengthB ∨
        T.sideAbsLengthA + T.sideAbsLengthB < T.sideAbsLengthC := by
  apply unique_long_side_of_negative_heron
    hT.sideAbsLengthA_pos hT.sideAbsLengthB_pos hT.sideAbsLengthC_pos
  rw [nonmixed_side_moduli_heron T hT]
  nlinarith [sq_pos_of_ne_zero hN.signedDoubleArea_ne_zero]

private theorem pedal_signed_lengths_of_A_long (T : Triangle)
    (hT : T.IsNonMixed)
    (hlong : T.sideAbsLengthB + T.sideAbsLengthC < T.sideAbsLengthA) :
    T.pedalSignedLengthA = -T.lambdaA * T.pedalLengthA ∧
      T.pedalSignedLengthB = -T.lambdaB * T.pedalLengthB ∧
        T.pedalSignedLengthC = -T.lambdaC * T.pedalLengthC ∧
          T.lambdaA = -1 ∧ T.lambdaB = 1 ∧ T.lambdaC = 1 := by
  have hA : 0 < T.sideAbsLengthA ^ 2 - T.sideAbsLengthB ^ 2 -
      T.sideAbsLengthC ^ 2 := by
    nlinarith [mul_pos (show 0 < T.sideAbsLengthA - T.sideAbsLengthB -
      T.sideAbsLengthC by linarith)
      (show 0 < T.sideAbsLengthA + T.sideAbsLengthB + T.sideAbsLengthC by
        linarith [hT.sideAbsLengthA_pos, hT.sideAbsLengthB_pos,
          hT.sideAbsLengthC_pos]),
      mul_pos hT.sideAbsLengthB_pos hT.sideAbsLengthC_pos]
  have hB : T.sideAbsLengthB ^ 2 - T.sideAbsLengthC ^ 2 -
      T.sideAbsLengthA ^ 2 < 0 := by
    nlinarith [mul_pos (show 0 < T.sideAbsLengthA - T.sideAbsLengthB by
      linarith [hlong, hT.sideAbsLengthC_pos])
      (show 0 < T.sideAbsLengthA + T.sideAbsLengthB by
        linarith [hT.sideAbsLengthA_pos, hT.sideAbsLengthB_pos]),
      sq_nonneg T.sideAbsLengthC]
  have hC : T.sideAbsLengthC ^ 2 - T.sideAbsLengthA ^ 2 -
      T.sideAbsLengthB ^ 2 < 0 := by
    nlinarith [mul_pos (show 0 < T.sideAbsLengthA - T.sideAbsLengthC by
      linarith [hlong, hT.sideAbsLengthB_pos])
      (show 0 < T.sideAbsLengthA + T.sideAbsLengthC by
        linarith [hT.sideAbsLengthA_pos, hT.sideAbsLengthC_pos]),
      sq_nonneg T.sideAbsLengthB]
  have hLambdaA : T.lambdaA = -1 := by
    rw [lambdaA, branchSign,
      if_neg (by linarith : ¬ 0 ≤
        T.sideAbsLengthB + T.sideAbsLengthC - T.sideAbsLengthA)]
  have hLambdaB : T.lambdaB = 1 := by
    rw [lambdaB, branchSign,
      if_pos (by linarith [hlong, hT.sideAbsLengthC_pos] : 0 ≤
        T.sideAbsLengthC + T.sideAbsLengthA - T.sideAbsLengthB)]
  have hLambdaC : T.lambdaC = 1 := by
    rw [lambdaC, branchSign,
      if_pos (by linarith [hlong, hT.sideAbsLengthB_pos] : 0 ≤
        T.sideAbsLengthA + T.sideAbsLengthB - T.sideAbsLengthC)]
  refine ⟨?_, ?_, ?_, hLambdaA, hLambdaB, hLambdaC⟩ <;>
    simp [pedalSignedLengthA, pedalSignedLengthB, pedalSignedLengthC,
      pedalLengthA, pedalLengthB, pedalLengthC, hLambdaA, hLambdaB,
      hLambdaC, abs_of_pos hA, abs_of_neg hB, abs_of_neg hC] <;> ring

private theorem pedal_signed_lengths_of_B_long (T : Triangle)
    (hT : T.IsNonMixed)
    (hlong : T.sideAbsLengthC + T.sideAbsLengthA < T.sideAbsLengthB) :
    T.pedalSignedLengthA = -T.lambdaA * T.pedalLengthA ∧
      T.pedalSignedLengthB = -T.lambdaB * T.pedalLengthB ∧
        T.pedalSignedLengthC = -T.lambdaC * T.pedalLengthC ∧
          T.lambdaA = 1 ∧ T.lambdaB = -1 ∧ T.lambdaC = 1 := by
  have hA : T.sideAbsLengthA ^ 2 - T.sideAbsLengthB ^ 2 -
      T.sideAbsLengthC ^ 2 < 0 := by
    nlinarith [mul_pos (show 0 < T.sideAbsLengthB - T.sideAbsLengthA by
      linarith [hlong, hT.sideAbsLengthC_pos])
      (show 0 < T.sideAbsLengthB + T.sideAbsLengthA by
        linarith [hT.sideAbsLengthA_pos, hT.sideAbsLengthB_pos]),
      sq_nonneg T.sideAbsLengthC]
  have hB : 0 < T.sideAbsLengthB ^ 2 - T.sideAbsLengthC ^ 2 -
      T.sideAbsLengthA ^ 2 := by
    nlinarith [mul_pos (show 0 < T.sideAbsLengthB - T.sideAbsLengthC -
      T.sideAbsLengthA by linarith)
      (show 0 < T.sideAbsLengthA + T.sideAbsLengthB + T.sideAbsLengthC by
        linarith [hT.sideAbsLengthA_pos, hT.sideAbsLengthB_pos,
          hT.sideAbsLengthC_pos]),
      mul_pos hT.sideAbsLengthC_pos hT.sideAbsLengthA_pos]
  have hC : T.sideAbsLengthC ^ 2 - T.sideAbsLengthA ^ 2 -
      T.sideAbsLengthB ^ 2 < 0 := by
    nlinarith [mul_pos (show 0 < T.sideAbsLengthB - T.sideAbsLengthC by
      linarith [hlong, hT.sideAbsLengthA_pos])
      (show 0 < T.sideAbsLengthB + T.sideAbsLengthC by
        linarith [hT.sideAbsLengthB_pos, hT.sideAbsLengthC_pos]),
      sq_nonneg T.sideAbsLengthA]
  have hLambdaA : T.lambdaA = 1 := by
    rw [lambdaA, branchSign,
      if_pos (by linarith [hlong, hT.sideAbsLengthC_pos] : 0 ≤
        T.sideAbsLengthB + T.sideAbsLengthC - T.sideAbsLengthA)]
  have hLambdaB : T.lambdaB = -1 := by
    rw [lambdaB, branchSign,
      if_neg (by linarith : ¬ 0 ≤
        T.sideAbsLengthC + T.sideAbsLengthA - T.sideAbsLengthB)]
  have hLambdaC : T.lambdaC = 1 := by
    rw [lambdaC, branchSign,
      if_pos (by linarith [hlong, hT.sideAbsLengthA_pos] : 0 ≤
        T.sideAbsLengthA + T.sideAbsLengthB - T.sideAbsLengthC)]
  refine ⟨?_, ?_, ?_, hLambdaA, hLambdaB, hLambdaC⟩ <;>
    simp [pedalSignedLengthA, pedalSignedLengthB, pedalSignedLengthC,
      pedalLengthA, pedalLengthB, pedalLengthC, hLambdaA, hLambdaB,
      hLambdaC, abs_of_neg hA, abs_of_pos hB, abs_of_neg hC] <;> ring

private theorem pedal_signed_lengths_of_C_long (T : Triangle)
    (hT : T.IsNonMixed)
    (hlong : T.sideAbsLengthA + T.sideAbsLengthB < T.sideAbsLengthC) :
    T.pedalSignedLengthA = -T.lambdaA * T.pedalLengthA ∧
      T.pedalSignedLengthB = -T.lambdaB * T.pedalLengthB ∧
        T.pedalSignedLengthC = -T.lambdaC * T.pedalLengthC ∧
          T.lambdaA = 1 ∧ T.lambdaB = 1 ∧ T.lambdaC = -1 := by
  have hA : T.sideAbsLengthA ^ 2 - T.sideAbsLengthB ^ 2 -
      T.sideAbsLengthC ^ 2 < 0 := by
    nlinarith [mul_pos (show 0 < T.sideAbsLengthC - T.sideAbsLengthA by
      linarith [hlong, hT.sideAbsLengthB_pos])
      (show 0 < T.sideAbsLengthC + T.sideAbsLengthA by
        linarith [hT.sideAbsLengthA_pos, hT.sideAbsLengthC_pos]),
      sq_nonneg T.sideAbsLengthB]
  have hB : T.sideAbsLengthB ^ 2 - T.sideAbsLengthC ^ 2 -
      T.sideAbsLengthA ^ 2 < 0 := by
    nlinarith [mul_pos (show 0 < T.sideAbsLengthC - T.sideAbsLengthB by
      linarith [hlong, hT.sideAbsLengthA_pos])
      (show 0 < T.sideAbsLengthC + T.sideAbsLengthB by
        linarith [hT.sideAbsLengthB_pos, hT.sideAbsLengthC_pos]),
      sq_nonneg T.sideAbsLengthA]
  have hC : 0 < T.sideAbsLengthC ^ 2 - T.sideAbsLengthA ^ 2 -
      T.sideAbsLengthB ^ 2 := by
    nlinarith [mul_pos (show 0 < T.sideAbsLengthC - T.sideAbsLengthA -
      T.sideAbsLengthB by linarith)
      (show 0 < T.sideAbsLengthA + T.sideAbsLengthB + T.sideAbsLengthC by
        linarith [hT.sideAbsLengthA_pos, hT.sideAbsLengthB_pos,
          hT.sideAbsLengthC_pos]),
      mul_pos hT.sideAbsLengthA_pos hT.sideAbsLengthB_pos]
  have hLambdaA : T.lambdaA = 1 := by
    rw [lambdaA, branchSign,
      if_pos (by linarith [hlong, hT.sideAbsLengthB_pos] : 0 ≤
        T.sideAbsLengthB + T.sideAbsLengthC - T.sideAbsLengthA)]
  have hLambdaB : T.lambdaB = 1 := by
    rw [lambdaB, branchSign,
      if_pos (by linarith [hlong, hT.sideAbsLengthA_pos] : 0 ≤
        T.sideAbsLengthC + T.sideAbsLengthA - T.sideAbsLengthB)]
  have hLambdaC : T.lambdaC = -1 := by
    rw [lambdaC, branchSign,
      if_neg (by linarith : ¬ 0 ≤
        T.sideAbsLengthA + T.sideAbsLengthB - T.sideAbsLengthC)]
  refine ⟨?_, ?_, ?_, hLambdaA, hLambdaB, hLambdaC⟩ <;>
    simp [pedalSignedLengthA, pedalSignedLengthB, pedalSignedLengthC,
      pedalLengthA, pedalLengthB, pedalLengthC, hLambdaA, hLambdaB,
      hLambdaC, abs_of_neg hA, abs_of_neg hB, abs_of_pos hC] <;> ring

theorem pedal_nonmixed_signed_length_formula (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) :
    T.pedalSignedLengthA = -T.lambdaA * T.pedalLengthA ∧
      T.pedalSignedLengthB = -T.lambdaB * T.pedalLengthB ∧
        T.pedalSignedLengthC = -T.lambdaC * T.pedalLengthC ∧
          ((T.lambdaA = -1 ∧ T.lambdaB = 1 ∧ T.lambdaC = 1) ∨
            (T.lambdaA = 1 ∧ T.lambdaB = -1 ∧ T.lambdaC = 1) ∨
              (T.lambdaA = 1 ∧ T.lambdaB = 1 ∧ T.lambdaC = -1)) := by
  rcases nonmixed_unique_long_side T hN hT with hA | hB | hC
  · rcases pedal_signed_lengths_of_A_long T hT hA with ⟨hsA, hsB, hsC, hA', hB', hC'⟩
    exact ⟨hsA, hsB, hsC, Or.inl ⟨hA', hB', hC'⟩⟩
  · rcases pedal_signed_lengths_of_B_long T hT hB with ⟨hsA, hsB, hsC, hA', hB', hC'⟩
    exact ⟨hsA, hsB, hsC, Or.inr (Or.inl ⟨hA', hB', hC'⟩)⟩
  · rcases pedal_signed_lengths_of_C_long T hT hC with ⟨hsA, hsB, hsC, hA', hB', hC'⟩
    exact ⟨hsA, hsB, hsC, Or.inr (Or.inr ⟨hA', hB', hC'⟩)⟩

theorem pedal_signed_length_sum (T : Triangle) (hT : T.IsNonMixed) :
    2 * T.sideAbsLengthA * T.sideAbsLengthB * T.sideAbsLengthC *
        (T.pedalSignedLengthA + T.pedalSignedLengthB + T.pedalSignedLengthC) =
      -((T.sideAbsLengthA + T.sideAbsLengthB + T.sideAbsLengthC) *
        (-T.sideAbsLengthA + T.sideAbsLengthB + T.sideAbsLengthC) *
        (T.sideAbsLengthA - T.sideAbsLengthB + T.sideAbsLengthC) *
        (T.sideAbsLengthA + T.sideAbsLengthB - T.sideAbsLengthC)) := by
  have hA : T.sideAbsLengthA ≠ 0 := ne_of_gt hT.sideAbsLengthA_pos
  have hB : T.sideAbsLengthB ≠ 0 := ne_of_gt hT.sideAbsLengthB_pos
  have hC : T.sideAbsLengthC ≠ 0 := ne_of_gt hT.sideAbsLengthC_pos
  have hBsq : T.sideAbsLengthB ^ 2 ≠ 0 := pow_ne_zero _ hB
  have hCsq : T.sideAbsLengthC ^ 2 ≠ 0 := pow_ne_zero _ hC
  unfold pedalSignedLengthA pedalSignedLengthB pedalSignedLengthC
  field_simp [hA, hB, hC]
  ring

theorem pedal_signed_length_sum_ne_zero (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) :
    T.pedalSignedLengthA + T.pedalSignedLengthB + T.pedalSignedLengthC ≠ 0 := by
  intro hzero
  have hsum := pedal_signed_length_sum T hT
  rw [hzero] at hsum
  rw [nonmixed_side_moduli_heron T hT] at hsum
  have hAreaSq : T.signedDoubleArea ^ 2 = 0 := by
    nlinarith [hsum]
  exact hN.signedDoubleArea_ne_zero (sq_eq_zero_iff.mp hAreaSq)

private theorem excenterA_eq_of_signed_balance (U : Triangle) (H : Point)
    (pA pB pC : ℝ)
    (hA : U.sideAbsLengthA = pA) (hB : U.sideAbsLengthB = pB)
    (hC : U.sideAbsLengthC = pC)
    (hbalance :
      pA • U.A - pB • U.B - pC • U.C = (pA - pB - pC) • H)
    (hsum : pA - pB - pC ≠ 0) :
    H = U.excenterA (by
      have hden : U.excenterDenomA = -pA + pB + pC := by
        simp only [excenterDenomA, signedPerimeter, hA, hB, hC]
        ring
      rw [hden]
      intro hzero
      apply hsum
      linarith) := by
  have hdenValue : U.excenterDenomA = -pA + pB + pC := by
    simp only [excenterDenomA, signedPerimeter, hA, hB, hC]
    ring
  have hdenLinear : -pA + pB + pC ≠ 0 := by
    intro hzero
    apply hsum
    linarith
  let hden : U.excenterDenomA ≠ 0 := by
    rw [hdenValue]
    exact hdenLinear
  change H = U.excenterA hden
  rw [excenterA_eq_sideCombination U hden, hA, hB, hC, hdenValue]
  apply Vec.ext
  · have hx := congrArg Vec.x hbalance
    simp only [Vec.x_sub, Vec.x_add, Vec.x_smul] at hx ⊢
    field_simp [hdenLinear]
    linarith
  · have ht := congrArg Vec.t hbalance
    simp only [Vec.t_sub, Vec.t_add, Vec.t_smul] at ht ⊢
    field_simp [hdenLinear]
    linarith

private theorem excenterB_eq_of_signed_balance (U : Triangle) (H : Point)
    (pA pB pC : ℝ)
    (hA : U.sideAbsLengthA = pA) (hB : U.sideAbsLengthB = pB)
    (hC : U.sideAbsLengthC = pC)
    (hbalance :
      -pA • U.A + pB • U.B - pC • U.C = (-pA + pB - pC) • H)
    (hsum : -pA + pB - pC ≠ 0) :
    H = U.excenterB (by
      have hden : U.excenterDenomB = pA - pB + pC := by
        simp only [excenterDenomB, signedPerimeter, hA, hB, hC]
        ring
      rw [hden]
      intro hzero
      apply hsum
      linarith) := by
  have hdenValue : U.excenterDenomB = pA - pB + pC := by
    simp only [excenterDenomB, signedPerimeter, hA, hB, hC]
    ring
  have hdenLinear : pA - pB + pC ≠ 0 := by
    intro hzero
    apply hsum
    linarith
  let hden : U.excenterDenomB ≠ 0 := by
    rw [hdenValue]
    exact hdenLinear
  change H = U.excenterB hden
  rw [excenterB_eq_sideCombination U hden, hA, hB, hC, hdenValue]
  apply Vec.ext
  · have hx := congrArg Vec.x hbalance
    simp only [Vec.x_sub, Vec.x_add, Vec.x_smul] at hx ⊢
    field_simp [hdenLinear]
    linarith
  · have ht := congrArg Vec.t hbalance
    simp only [Vec.t_sub, Vec.t_add, Vec.t_smul] at ht ⊢
    field_simp [hdenLinear]
    linarith

private theorem excenterC_eq_of_signed_balance (U : Triangle) (H : Point)
    (pA pB pC : ℝ)
    (hA : U.sideAbsLengthA = pA) (hB : U.sideAbsLengthB = pB)
    (hC : U.sideAbsLengthC = pC)
    (hbalance :
      -pA • U.A - pB • U.B + pC • U.C = (-pA - pB + pC) • H)
    (hsum : -pA - pB + pC ≠ 0) :
    H = U.excenterC (by
      have hden : U.excenterDenomC = pA + pB - pC := by
        simp only [excenterDenomC, signedPerimeter, hA, hB, hC]
        ring
      rw [hden]
      intro hzero
      apply hsum
      linarith) := by
  have hdenValue : U.excenterDenomC = pA + pB - pC := by
    simp only [excenterDenomC, signedPerimeter, hA, hB, hC]
    ring
  have hdenLinear : pA + pB - pC ≠ 0 := by
    intro hzero
    apply hsum
    linarith
  let hden : U.excenterDenomC ≠ 0 := by
    rw [hdenValue]
    exact hdenLinear
  change H = U.excenterC hden
  rw [excenterC_eq_sideCombination U hden, hA, hB, hC, hdenValue]
  apply Vec.ext
  · have hx := congrArg Vec.x hbalance
    simp only [Vec.x_sub, Vec.x_add, Vec.x_smul] at hx ⊢
    field_simp [hdenLinear]
    linarith
  · have ht := congrArg Vec.t hbalance
    simp only [Vec.t_sub, Vec.t_add, Vec.t_smul] at ht ⊢
    field_simp [hdenLinear]
    linarith

def HasNormalizedPedalFeet (T : Triangle) (PA PB PC : Point) : Prop :=
  PA = T.C +
      ((T.sideAbsLengthA ^ 2 + T.sideAbsLengthB ^ 2 - T.sideAbsLengthC ^ 2) /
        (2 * T.sideAbsLengthA ^ 2)) • (T.B - T.C) ∧
    PB = T.C +
      ((T.sideAbsLengthA ^ 2 + T.sideAbsLengthB ^ 2 - T.sideAbsLengthC ^ 2) /
        (2 * T.sideAbsLengthB ^ 2)) • (T.A - T.C) ∧
      PC = T.B +
        ((T.sideAbsLengthA ^ 2 + T.sideAbsLengthC ^ 2 - T.sideAbsLengthB ^ 2) /
          (2 * T.sideAbsLengthC ^ 2)) • (T.A - T.B)

def pedalTriangle (PA PB PC : Point) : Triangle := triangleOfVertices PA PB PC

private theorem pedalLengthA_sq_formula (T : Triangle) (hT : T.IsNonMixed) :
    T.pedalLengthA ^ 2 =
      T.sideAbsLengthA ^ 2 *
        (T.sideAbsLengthA ^ 2 - T.sideAbsLengthB ^ 2 - T.sideAbsLengthC ^ 2) ^ 2 /
          (4 * T.sideAbsLengthB ^ 2 * T.sideAbsLengthC ^ 2) := by
  have hB : T.sideAbsLengthB ≠ 0 := ne_of_gt hT.sideAbsLengthB_pos
  have hC : T.sideAbsLengthC ≠ 0 := ne_of_gt hT.sideAbsLengthC_pos
  unfold pedalLengthA
  rw [div_pow, mul_pow, sq_abs]
  field_simp [hB, hC]
  ring

private theorem pedalTriangle_sideAbsLengthA_eq_pedalLengthA
    (T : Triangle) (PA PB PC : Point) (hT : T.IsNonMixed)
    (hfeet : T.HasNormalizedPedalFeet PA PB PC) :
    (pedalTriangle PA PB PC).sideAbsLengthA = T.pedalLengthA := by
  have hB : T.sideAbsLengthB ≠ 0 := ne_of_gt hT.sideAbsLengthB_pos
  have hC : T.sideAbsLengthC ≠ 0 := ne_of_gt hT.sideAbsLengthC_pos
  have hBsq : T.sideAbsLengthB ^ 2 ≠ 0 := pow_ne_zero _ hB
  have hCsq : T.sideAbsLengthC ^ 2 ≠ 0 := pow_ne_zero _ hC
  have hqabs : |q (PB - PC)| = T.pedalLengthA ^ 2 := by
    rcases hT with hS | hTi
    · have hAq : T.sideAbsLengthA ^ 2 = q (T.B - T.C) := by
        have h := absLength_sq_of_spacelike hS.1
        change T.sideAbsLengthA ^ 2 = q (T.C - T.B) at h
        rw [show T.B - T.C = -(T.C - T.B) by module, q_neg]
        exact h
      have hBq : T.sideAbsLengthB ^ 2 = q (T.A - T.C) := by
        simpa only [sideVecB, intervalVec, vsub_eq_sub, q_neg] using
          absLength_sq_of_spacelike hS.2.1
      have hCq : T.sideAbsLengthC ^ 2 = q (T.A - T.B) := by
        have h := absLength_sq_of_spacelike hS.2.2
        change T.sideAbsLengthC ^ 2 = q (T.B - T.A) at h
        rw [show T.A - T.B = -(T.B - T.A) by module, q_neg]
        exact h
      have hraw := pedal_side_A_sq_from_param T.A T.B T.C PB PC
        (T.sideAbsLengthA ^ 2) (T.sideAbsLengthB ^ 2) (T.sideAbsLengthC ^ 2)
        (by positivity) (by positivity) hAq hBq hCq hfeet.2.1 hfeet.2.2
      rw [hraw, pedalLengthA_sq_formula T (Or.inl hS)]
      rw [abs_of_nonneg]
      positivity
    · have hAq : -(T.sideAbsLengthA ^ 2) = q (T.B - T.C) := by
        have h := absLength_sq_of_timelike hTi.1
        change T.sideAbsLengthA ^ 2 = -q (T.C - T.B) at h
        rw [show T.B - T.C = -(T.C - T.B) by module, q_neg]
        linarith
      have hBq : -(T.sideAbsLengthB ^ 2) = q (T.A - T.C) := by
        have h := absLength_sq_of_timelike hTi.2.1
        change T.sideAbsLengthB ^ 2 = -q (T.A - T.C) at h
        linarith
      have hCq : -(T.sideAbsLengthC ^ 2) = q (T.A - T.B) := by
        have h := absLength_sq_of_timelike hTi.2.2
        change T.sideAbsLengthC ^ 2 = -q (T.B - T.A) at h
        rw [show T.A - T.B = -(T.B - T.A) by module, q_neg]
        linarith
      have hPB : PB = T.C +
          ((-(T.sideAbsLengthA ^ 2) + -(T.sideAbsLengthB ^ 2) -
              -(T.sideAbsLengthC ^ 2)) /
            (2 * -(T.sideAbsLengthB ^ 2))) • (T.A - T.C) := by
        have hcoeff :
            (-(T.sideAbsLengthA ^ 2) + -(T.sideAbsLengthB ^ 2) -
                -(T.sideAbsLengthC ^ 2)) /
              (2 * -(T.sideAbsLengthB ^ 2)) =
              (T.sideAbsLengthA ^ 2 + T.sideAbsLengthB ^ 2 -
                T.sideAbsLengthC ^ 2) / (2 * T.sideAbsLengthB ^ 2) := by
          field_simp [hBsq]
          ring
        rw [hcoeff]
        exact hfeet.2.1
      have hPC : PC = T.B +
          ((-(T.sideAbsLengthA ^ 2) + -(T.sideAbsLengthC ^ 2) -
              -(T.sideAbsLengthB ^ 2)) /
            (2 * -(T.sideAbsLengthC ^ 2))) • (T.A - T.B) := by
        have hcoeff :
            (-(T.sideAbsLengthA ^ 2) + -(T.sideAbsLengthC ^ 2) -
                -(T.sideAbsLengthB ^ 2)) /
              (2 * -(T.sideAbsLengthC ^ 2)) =
              (T.sideAbsLengthA ^ 2 + T.sideAbsLengthC ^ 2 -
                T.sideAbsLengthB ^ 2) / (2 * T.sideAbsLengthC ^ 2) := by
          field_simp [hCsq]
          ring
        rw [hcoeff]
        exact hfeet.2.2
      have hraw := pedal_side_A_sq_from_param T.A T.B T.C PB PC
        (-(T.sideAbsLengthA ^ 2)) (-(T.sideAbsLengthB ^ 2))
        (-(T.sideAbsLengthC ^ 2))
        (neg_ne_zero.mpr hBsq) (neg_ne_zero.mpr hCsq) hAq hBq hCq hPB hPC
      have halgebra :
          (-(T.sideAbsLengthA ^ 2)) *
              (-(T.sideAbsLengthA ^ 2) - -(T.sideAbsLengthB ^ 2) -
                -(T.sideAbsLengthC ^ 2)) ^ 2 /
                (4 * -(T.sideAbsLengthB ^ 2) * -(T.sideAbsLengthC ^ 2)) =
            -(T.sideAbsLengthA ^ 2 *
              (T.sideAbsLengthA ^ 2 - T.sideAbsLengthB ^ 2 -
                T.sideAbsLengthC ^ 2) ^ 2 /
                (4 * T.sideAbsLengthB ^ 2 * T.sideAbsLengthC ^ 2)) := by
        field_simp [hBsq, hCsq]
        ring
      rw [halgebra] at hraw
      rw [hraw, abs_neg]
      rw [pedalLengthA_sq_formula T (Or.inr hTi)]
      apply abs_of_nonneg
      positivity
  have hsq : (pedalTriangle PA PB PC).sideAbsLengthA ^ 2 = T.pedalLengthA ^ 2 := by
    change absLength (pedalTriangle PA PB PC).sideVecA ^ 2 = _
    rw [absLength_sq]
    change |q (PC - PB)| = _
    rw [show PC - PB = -(PB - PC) by module, q_neg]
    exact hqabs
  have hleft : 0 ≤ (pedalTriangle PA PB PC).sideAbsLengthA := by
    exact Real.sqrt_nonneg _
  have hright : 0 ≤ T.pedalLengthA := by
    unfold pedalLengthA
    apply div_nonneg
    · exact mul_nonneg (le_of_lt hT.sideAbsLengthA_pos) (abs_nonneg _)
    · exact (mul_pos (mul_pos (by norm_num) hT.sideAbsLengthB_pos)
        hT.sideAbsLengthC_pos).le
  nlinarith

private theorem normalizedPedalFeet_rotate (T : Triangle) (PA PB PC : Point)
    (hT : T.IsNonMixed) (hfeet : T.HasNormalizedPedalFeet PA PB PC) :
    T.rotate.HasNormalizedPedalFeet PB PC PA := by
  rcases hfeet with ⟨hPA, hPB, hPC⟩
  have hA : T.sideAbsLengthA ≠ 0 := ne_of_gt hT.sideAbsLengthA_pos
  have hB : T.sideAbsLengthB ≠ 0 := ne_of_gt hT.sideAbsLengthB_pos
  have hC : T.sideAbsLengthC ≠ 0 := ne_of_gt hT.sideAbsLengthC_pos
  have hAsq : T.sideAbsLengthA ^ 2 ≠ 0 := pow_ne_zero _ hA
  have hBsq : T.sideAbsLengthB ^ 2 ≠ 0 := pow_ne_zero _ hB
  have hCsq : T.sideAbsLengthC ^ 2 ≠ 0 := pow_ne_zero _ hC
  unfold HasNormalizedPedalFeet
  simp only [rotate_A, rotate_B, rotate_C, rotate_sideAbsLengthA,
    rotate_sideAbsLengthB, rotate_sideAbsLengthC]
  refine ⟨?_, ?_, ?_⟩
  · have hcoeff :
        (T.sideAbsLengthA ^ 2 + T.sideAbsLengthB ^ 2 - T.sideAbsLengthC ^ 2) /
            (2 * T.sideAbsLengthB ^ 2) =
          1 - (T.sideAbsLengthB ^ 2 + T.sideAbsLengthC ^ 2 -
            T.sideAbsLengthA ^ 2) / (2 * T.sideAbsLengthB ^ 2) := by
        field_simp [hBsq]
        ring
    rw [hPB, hcoeff]
    module
  · have hcoeff :
        (T.sideAbsLengthA ^ 2 + T.sideAbsLengthC ^ 2 - T.sideAbsLengthB ^ 2) /
            (2 * T.sideAbsLengthC ^ 2) =
          1 - (T.sideAbsLengthB ^ 2 + T.sideAbsLengthC ^ 2 -
            T.sideAbsLengthA ^ 2) / (2 * T.sideAbsLengthC ^ 2) := by
        field_simp [hCsq]
        ring
    rw [hPC, hcoeff]
    module
  · simpa [add_comm] using hPA

private theorem pedalTriangle_sideAbsLengthB_eq_pedalLengthB
    (T : Triangle) (PA PB PC : Point) (hT : T.IsNonMixed)
    (hfeet : T.HasNormalizedPedalFeet PA PB PC) :
    (pedalTriangle PA PB PC).sideAbsLengthB = T.pedalLengthB := by
  have hfeetRotate : T.rotate.HasNormalizedPedalFeet PB PC PA :=
    normalizedPedalFeet_rotate T PA PB PC hT hfeet
  have h := pedalTriangle_sideAbsLengthA_eq_pedalLengthA T.rotate PB PC PA
    (rotateIsNonMixed T hT) hfeetRotate
  simpa [pedalTriangle, triangleOfVertices, pedalLengthA, pedalLengthB,
    rotate_sideAbsLengthA, rotate_sideAbsLengthB, rotate_sideAbsLengthC] using h

private theorem pedalTriangle_sideAbsLengthC_eq_pedalLengthC
    (T : Triangle) (PA PB PC : Point) (hT : T.IsNonMixed)
    (hfeet : T.HasNormalizedPedalFeet PA PB PC) :
    (pedalTriangle PA PB PC).sideAbsLengthC = T.pedalLengthC := by
  have hfeetRotate : T.rotate.HasNormalizedPedalFeet PB PC PA :=
    normalizedPedalFeet_rotate T PA PB PC hT hfeet
  have hfeetRotateTwo : T.rotate.rotate.HasNormalizedPedalFeet PC PA PB := by
    exact normalizedPedalFeet_rotate T.rotate PB PC PA
      (rotateIsNonMixed T hT) hfeetRotate
  have h := pedalTriangle_sideAbsLengthA_eq_pedalLengthA T.rotate.rotate PC PA PB
    (rotateIsNonMixed T.rotate (rotateIsNonMixed T hT)) hfeetRotateTwo
  simpa [pedalTriangle, triangleOfVertices, pedalLengthA, pedalLengthC,
    rotate_sideAbsLengthA, rotate_sideAbsLengthB, rotate_sideAbsLengthC] using h

private theorem pedal_weighted_foot_identity_nonmixed
    (T : Triangle) (PA PB PC : Point) (hT : T.IsNonMixed)
    (hAB : q T.A = q T.B) (hAC : q T.A = q T.C)
    (hfeet : T.HasNormalizedPedalFeet PA PB PC) :
    T.pedalSignedLengthA • PA + T.pedalSignedLengthB • PB +
        T.pedalSignedLengthC • PC =
      (T.pedalSignedLengthA + T.pedalSignedLengthB + T.pedalSignedLengthC) •
        normalizedOrthocenter T.A T.B T.C := by
  rcases hT with hS | hTi
  · have hAq : T.sideAbsLengthA ^ 2 = q (T.B - T.C) := by
      have h := absLength_sq_of_spacelike hS.1
      change T.sideAbsLengthA ^ 2 = q (T.C - T.B) at h
      rw [show T.B - T.C = -(T.C - T.B) by module, q_neg]
      exact h
    have hBq : T.sideAbsLengthB ^ 2 = q (T.C - T.A) := by
      have h := absLength_sq_of_spacelike hS.2.1
      change T.sideAbsLengthB ^ 2 = q (T.A - T.C) at h
      rw [show T.C - T.A = -(T.A - T.C) by module, q_neg]
      exact h
    have hCq : T.sideAbsLengthC ^ 2 = q (T.A - T.B) := by
      have h := absLength_sq_of_spacelike hS.2.2
      change T.sideAbsLengthC ^ 2 = q (T.B - T.A) at h
      rw [show T.A - T.B = -(T.B - T.A) by module, q_neg]
      exact h
    have h := pedal_weighted_foot_identity T.A T.B T.C PA PB PC
      T.sideAbsLengthA T.sideAbsLengthB T.sideAbsLengthC
      (ne_of_gt (absLength_pos_iff.mpr (ne_of_gt hS.1)))
      (ne_of_gt (absLength_pos_iff.mpr (ne_of_gt hS.2.1)))
      (ne_of_gt (absLength_pos_iff.mpr (ne_of_gt hS.2.2)))
      hAq hBq hCq hAB hAC hfeet.1 hfeet.2.1 hfeet.2.2
    simpa [pedalSignedLengthA, pedalSignedLengthB, pedalSignedLengthC] using h
  · have hAq : -(T.sideAbsLengthA ^ 2) = q (T.B - T.C) := by
      have h := absLength_sq_of_timelike hTi.1
      change T.sideAbsLengthA ^ 2 = -q (T.C - T.B) at h
      rw [show T.B - T.C = -(T.C - T.B) by module, q_neg]
      linarith
    have hBq : -(T.sideAbsLengthB ^ 2) = q (T.C - T.A) := by
      have h := absLength_sq_of_timelike hTi.2.1
      change T.sideAbsLengthB ^ 2 = -q (T.A - T.C) at h
      rw [show T.C - T.A = -(T.A - T.C) by module, q_neg]
      linarith
    have hCq : -(T.sideAbsLengthC ^ 2) = q (T.A - T.B) := by
      have h := absLength_sq_of_timelike hTi.2.2
      change T.sideAbsLengthC ^ 2 = -q (T.B - T.A) at h
      rw [show T.A - T.B = -(T.B - T.A) by module, q_neg]
      linarith
    have hrel := pedal_circumcentric_relation T.A T.B T.C
      (-(T.sideAbsLengthA ^ 2)) (-(T.sideAbsLengthB ^ 2))
      (-(T.sideAbsLengthC ^ 2)) hAq hBq hCq hAB hAC
    have hrelx := congrArg Vec.x hrel
    have hrelt := congrArg Vec.t hrel
    have ha : T.sideAbsLengthA ≠ 0 :=
      ne_of_gt (absLength_pos_iff.mpr (ne_of_lt hTi.1))
    have hb : T.sideAbsLengthB ≠ 0 :=
      ne_of_gt (absLength_pos_iff.mpr (ne_of_lt hTi.2.1))
    have hc : T.sideAbsLengthC ≠ 0 :=
      ne_of_gt (absLength_pos_iff.mpr (ne_of_lt hTi.2.2))
    rw [hfeet.1, hfeet.2.1, hfeet.2.2]
    apply Vec.ext
    · simp [pedalSignedLengthA, pedalSignedLengthB, pedalSignedLengthC,
        normalizedOrthocenter_apply] at hrelx ⊢
      field_simp [ha, hb, hc]
      linear_combination 4 * hrelx
    · simp [pedalSignedLengthA, pedalSignedLengthB, pedalSignedLengthC,
        normalizedOrthocenter_apply] at hrelt ⊢
      field_simp [ha, hb, hc]
      linear_combination 4 * hrelt

theorem pedal_nonmixed_excenter_classification
    (T : Triangle) (hN : T.Nondegenerate) (hT : T.IsNonMixed)
    (hO : T.IsCircumcenterAtOrigin) (PA PB PC : Point)
    (hfeet : T.HasNormalizedPedalFeet PA PB PC) :
    (pedalTriangle PA PB PC).sideAbsLengthA = T.pedalLengthA ∧
      (pedalTriangle PA PB PC).sideAbsLengthB = T.pedalLengthB ∧
        (pedalTriangle PA PB PC).sideAbsLengthC = T.pedalLengthC ∧
          T.pedalSignedLengthA = -T.lambdaA * T.pedalLengthA ∧
            T.pedalSignedLengthB = -T.lambdaB * T.pedalLengthB ∧
              T.pedalSignedLengthC = -T.lambdaC * T.pedalLengthC ∧
                ((T.lambdaA = -1 ∧ T.lambdaB = 1 ∧ T.lambdaC = 1 ∧
                    ∃ hA : (pedalTriangle PA PB PC).excenterDenomA ≠ 0,
                      T.orthocenterAtOrigin =
                        (pedalTriangle PA PB PC).excenterA hA) ∨
                  (T.lambdaA = 1 ∧ T.lambdaB = -1 ∧ T.lambdaC = 1 ∧
                    ∃ hB : (pedalTriangle PA PB PC).excenterDenomB ≠ 0,
                      T.orthocenterAtOrigin =
                        (pedalTriangle PA PB PC).excenterB hB) ∨
                  (T.lambdaA = 1 ∧ T.lambdaB = 1 ∧ T.lambdaC = -1 ∧
                    ∃ hC : (pedalTriangle PA PB PC).excenterDenomC ≠ 0,
                      T.orthocenterAtOrigin =
                        (pedalTriangle PA PB PC).excenterC hC)) := by
  have hAB : q T.A = q T.B := by
    simpa [IsCircumcenterAtOrigin, IsCircumcenter, intervalSq, intervalVec,
      vsub_eq_sub] using hO.1
  have hBC : q T.B = q T.C := by
    simpa [IsCircumcenterAtOrigin, IsCircumcenter, intervalSq, intervalVec,
      vsub_eq_sub] using hO.2
  have hAC : q T.A = q T.C := hAB.trans hBC
  have hsideA := pedalTriangle_sideAbsLengthA_eq_pedalLengthA T PA PB PC hT hfeet
  have hsideB := pedalTriangle_sideAbsLengthB_eq_pedalLengthB T PA PB PC hT hfeet
  have hsideC := pedalTriangle_sideAbsLengthC_eq_pedalLengthC T PA PB PC hT hfeet
  have hweighted :=
    pedal_weighted_foot_identity_nonmixed T PA PB PC hT hAB hAC hfeet
  rcases pedal_nonmixed_signed_length_formula T hN hT with
    ⟨hsa, hsb, hsc, hbranches⟩
  refine ⟨hsideA, hsideB, hsideC, hsa, hsb, hsc, ?_⟩
  rcases hbranches with hA | hB | hC
  · rcases hA with ⟨hLA, hLB, hLC⟩
    have hbalance :
        T.pedalLengthA • PA - T.pedalLengthB • PB - T.pedalLengthC • PC =
          (T.pedalLengthA - T.pedalLengthB - T.pedalLengthC) •
            normalizedOrthocenter T.A T.B T.C := by
      rw [hsa, hsb, hsc, hLA, hLB, hLC] at hweighted
      simpa [sub_eq_add_neg] using hweighted
    have hsum : T.pedalLengthA - T.pedalLengthB - T.pedalLengthC ≠ 0 := by
      intro hzero
      apply pedal_signed_length_sum_ne_zero T hN hT
      rw [hsa, hsb, hsc, hLA, hLB, hLC]
      linarith
    have hden : (pedalTriangle PA PB PC).excenterDenomA ≠ 0 := by
      intro hzero
      apply hsum
      simp only [excenterDenomA, signedPerimeter, hsideA, hsideB, hsideC] at hzero
      linarith
    refine Or.inl ⟨hLA, hLB, hLC, hden, ?_⟩
    simpa [normalizedOrthocenter, triangleOfVertices] using
      excenterA_eq_of_signed_balance (pedalTriangle PA PB PC)
        (normalizedOrthocenter T.A T.B T.C)
        T.pedalLengthA T.pedalLengthB T.pedalLengthC
        hsideA hsideB hsideC hbalance hsum
  · rcases hB with ⟨hLA, hLB, hLC⟩
    have hbalance :
        -T.pedalLengthA • PA + T.pedalLengthB • PB - T.pedalLengthC • PC =
          (-T.pedalLengthA + T.pedalLengthB - T.pedalLengthC) •
            normalizedOrthocenter T.A T.B T.C := by
      rw [hsa, hsb, hsc, hLA, hLB, hLC] at hweighted
      simpa [sub_eq_add_neg] using hweighted
    have hsum : -T.pedalLengthA + T.pedalLengthB - T.pedalLengthC ≠ 0 := by
      intro hzero
      apply pedal_signed_length_sum_ne_zero T hN hT
      rw [hsa, hsb, hsc, hLA, hLB, hLC]
      linarith
    have hden : (pedalTriangle PA PB PC).excenterDenomB ≠ 0 := by
      intro hzero
      apply hsum
      simp only [excenterDenomB, signedPerimeter, hsideA, hsideB, hsideC] at hzero
      linarith
    refine Or.inr (Or.inl ⟨hLA, hLB, hLC, hden, ?_⟩)
    simpa [normalizedOrthocenter, triangleOfVertices] using
      excenterB_eq_of_signed_balance (pedalTriangle PA PB PC)
        (normalizedOrthocenter T.A T.B T.C)
        T.pedalLengthA T.pedalLengthB T.pedalLengthC
        hsideA hsideB hsideC hbalance hsum
  · rcases hC with ⟨hLA, hLB, hLC⟩
    have hbalance :
        -T.pedalLengthA • PA - T.pedalLengthB • PB + T.pedalLengthC • PC =
          (-T.pedalLengthA - T.pedalLengthB + T.pedalLengthC) •
            normalizedOrthocenter T.A T.B T.C := by
      rw [hsa, hsb, hsc, hLA, hLB, hLC] at hweighted
      simpa [sub_eq_add_neg] using hweighted
    have hsum : -T.pedalLengthA - T.pedalLengthB + T.pedalLengthC ≠ 0 := by
      intro hzero
      apply pedal_signed_length_sum_ne_zero T hN hT
      rw [hsa, hsb, hsc, hLA, hLB, hLC]
      linarith
    have hden : (pedalTriangle PA PB PC).excenterDenomC ≠ 0 := by
      intro hzero
      apply hsum
      simp only [excenterDenomC, signedPerimeter, hsideA, hsideB, hsideC] at hzero
      linarith
    refine Or.inr (Or.inr ⟨hLA, hLB, hLC, hden, ?_⟩)
    simpa [normalizedOrthocenter, triangleOfVertices] using
      excenterC_eq_of_signed_balance (pedalTriangle PA PB PC)
        (normalizedOrthocenter T.A T.B T.C)
        T.pedalLengthA T.pedalLengthB T.pedalLengthC
        hsideA hsideB hsideC hbalance hsum

end

end Triangle
end MinkowskiMerge
