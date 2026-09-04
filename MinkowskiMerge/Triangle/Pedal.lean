import MinkowskiMerge.Triangle.Centers
import Mathlib.Tactic


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

def triangleOfVertices (A B C : Point) : Triangle := ⟨A, B, C⟩

def normalizedOrthocenter (A B C : Point) : Point :=
  (triangleOfVertices A B C).orthocenterAtOrigin

@[simp] theorem normalizedOrthocenter_apply (A B C : Point) :
    normalizedOrthocenter A B C = A + B + C := by
  simp [normalizedOrthocenter, triangleOfVertices,
    Triangle.orthocenterAtOrigin_apply]

def pedalBary3 (alpha beta gamma : ℝ) (A B C : Point) : Point :=
  alpha • A + beta • B + gamma • C

theorem pedal_side_A_line
    (A PB PC : Point) (hconstant : dot A PB = dot A PC) :
    dot A (PB - PC) = 0 := by
  rw [dot_sub_right]
  linarith

theorem pedal_side_A_constant
    (A PB PC : Point) (hline : dot A (PB - PC) = 0) :
    dot A PB = dot A PC := by
  rw [dot_sub_right] at hline
  linarith

theorem pedal_side_line_package
    (A PB PC : Point) (qA : ℝ)
    (hB : dot A PB = qA) (hC : dot A PC = qA) :
    dot A (PB - PC) = 0 ∧ dot A PB = dot A PC := by
  exact ⟨pedal_side_A_line A PB PC (by rw [hB, hC]), by rw [hB, hC]⟩

theorem pedal_H_equal_signed_distances
    (A B C H : Point) (qA qB qC K : ℝ)
    (hA : dot A H - qA = K)
    (hB : dot B H - qB = K)
    (hC : dot C H - qC = K) :
    dot A H - qA = dot B H - qB ∧
      dot B H - qB = dot C H - qC := by
  constructor <;> linarith

theorem pedal_H_equal_signed_distances_from_formula
    (A B C : Point) (R a2 b2 c2 qA qB qC : ℝ)
    (hA : q A = R) (hB : q B = R) (hC : q C = R)
    (ha2 : a2 = q (B - C))
    (hb2 : b2 = q (C - A))
    (hc2 : c2 = q (A - B))
    (hqA : qA = R + (a2 - b2 - c2) / 4)
    (hqB : qB = R + (b2 - c2 - a2) / 4)
    (hqC : qC = R + (c2 - a2 - b2) / 4) :
    dot A (normalizedOrthocenter A B C) - qA =
      dot B (normalizedOrthocenter A B C) - qB ∧
      dot B (normalizedOrthocenter A B C) - qB =
        dot C (normalizedOrthocenter A B C) - qC := by
  subst qA
  subst qB
  subst qC
  subst a2
  subst b2
  subst c2
  simp [normalizedOrthocenter_apply, q_apply, dot_apply] at hA hB hC ⊢
  ring_nf at hA hB hC ⊢
  constructor <;> nlinarith

theorem pedal_dot_from_side_sq
    (A B C : Point) (a2 b2 c2 : ℝ)
    (ha2 : a2 = q (B - C))
    (hb2 : b2 = q (A - C))
    (hc2 : c2 = q (A - B)) :
    dot (A - C) (A - B) = (b2 + c2 - a2) / 2 := by
  subst a2
  subst b2
  subst c2
  simp [q_apply, dot_apply]
  ring

theorem pedal_side_A_sq_from_param
    (A B C PB PC : Point) (a2 b2 c2 : ℝ)
    (hb : b2 ≠ 0) (hc : c2 ≠ 0)
    (ha2 : a2 = q (B - C))
    (hb2 : b2 = q (A - C))
    (hc2 : c2 = q (A - B))
    (hPB : PB = C + ((a2 + b2 - c2) / (2 * b2)) • (A - C))
    (hPC : PC = B + ((a2 + c2 - b2) / (2 * c2)) • (A - B)) :
    q (PB - PC) = a2 * (a2 - b2 - c2) ^ 2 / (4 * b2 * c2) := by
  let U := A - C
  let W := A - B
  let K := a2 - b2 - c2
  have hdot : dot U W = (b2 + c2 - a2) / 2 := by
    simpa [U, W] using pedal_dot_from_side_sq A B C a2 b2 c2 ha2 hb2 hc2
  have hPBPC :
      PB - PC = (K / 2) • ((1 / b2) • U - (1 / c2) • W) := by
    rw [hPB, hPC]
    subst K
    subst U
    subst W
    apply Vec.ext <;> simp <;> field_simp [hb, hc] <;> ring
  rw [hPBPC, q_smul, q_sub, q_smul, q_smul,
    dot_smul_left, dot_smul_right]
  have hqU : q U = b2 := by simpa [U] using hb2.symm
  have hqW : q W = c2 := by simpa [W] using hc2.symm
  rw [hqU, hqW, hdot]
  subst K
  field_simp [hb, hc]
  ring

theorem pedal_signed_side_sum
    (a b c Delta : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hHeron :
      16 * Delta ^ 2 =
        2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 -
          a ^ 4 - b ^ 4 - c ^ 4) :
    a * (a ^ 2 - b ^ 2 - c ^ 2) / (2 * b * c) +
        b * (b ^ 2 - c ^ 2 - a ^ 2) / (2 * c * a) +
        c * (c ^ 2 - a ^ 2 - b ^ 2) / (2 * a * b) =
      -8 * Delta ^ 2 / (a * b * c) := by
  field_simp [ha, hb, hc]
  nlinarith

theorem pedal_circumcentric_relation
    (A B C : Point) (a2 b2 c2 : ℝ)
    (ha2 : a2 = q (B - C))
    (hb2 : b2 = q (C - A))
    (hc2 : c2 = q (A - B))
    (hAB : q A = q B) (hAC : q A = q C) :
    (-a2 * (a2 - b2 - c2)) • A +
        (b2 * (a2 - b2 + c2)) • B +
          (c2 * (a2 + b2 - c2)) • C = 0 := by
  have hBC : q B = q C := hAB.symm.trans hAC
  subst a2
  subst b2
  subst c2
  apply Vec.ext
  · simp [q_apply] at hAC hBC ⊢
    linear_combination
      (-2 * ((B.x - A.x) * (C.t - A.t) - (B.t - A.t) * (C.x - A.x)) *
        (B.t - C.t)) * hAC +
        (2 * ((B.x - A.x) * (C.t - A.t) - (B.t - A.t) * (C.x - A.x)) *
          (A.t - C.t)) * hBC
  · simp [q_apply] at hAC hBC ⊢
    linear_combination
      (-2 * ((B.x - A.x) * (C.t - A.t) - (B.t - A.t) * (C.x - A.x)) *
        (B.x - C.x)) * hAC +
        (2 * ((B.x - A.x) * (C.t - A.t) - (B.t - A.t) * (C.x - A.x)) *
          (A.x - C.x)) * hBC

theorem pedal_weighted_foot_identity
    (A B C PA PB PC : Point) (a b c : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ha2 : a ^ 2 = q (B - C))
    (hb2 : b ^ 2 = q (C - A))
    (hc2 : c ^ 2 = q (A - B))
    (hAB : q A = q B) (hAC : q A = q C)
    (hPA : PA = C + ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a ^ 2)) • (B - C))
    (hPB : PB = C + ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * b ^ 2)) • (A - C))
    (hPC : PC = B + ((a ^ 2 + c ^ 2 - b ^ 2) / (2 * c ^ 2)) • (A - B)) :
    let pA := a * (a ^ 2 - b ^ 2 - c ^ 2) / (2 * b * c)
    let pB := b * (b ^ 2 - c ^ 2 - a ^ 2) / (2 * c * a)
    let pC := c * (c ^ 2 - a ^ 2 - b ^ 2) / (2 * a * b)
    pA • PA + pB • PB + pC • PC =
      (pA + pB + pC) • normalizedOrthocenter A B C := by
  dsimp
  have hrel := pedal_circumcentric_relation A B C
    (a ^ 2) (b ^ 2) (c ^ 2) ha2 hb2 hc2 hAB hAC
  have hrelx := congrArg Vec.x hrel
  have hrelt := congrArg Vec.t hrel
  rw [hPA, hPB, hPC]
  apply Vec.ext
  · simp [normalizedOrthocenter_apply] at hrelx ⊢
    field_simp [ha, hb, hc]
    linear_combination 4 * hrelx
  · simp [normalizedOrthocenter_apply] at hrelt ⊢
    field_simp [ha, hb, hc]
    linear_combination 4 * hrelt

theorem pedal_incenter_barycentric_core
    (pA pB pC denom alpha beta gamma Delta : ℝ) (PA PB PC H : Point)
    (hdenom : denom = pA + pB + pC)
    (hden : denom ≠ 0)
    (hpA : pA ≠ 0) (hpB : pB ≠ 0) (hpC : pC ≠ 0)
    (hDelta : Delta ≠ 0)
    (hsum : alpha + beta + gamma = 1)
    (hH : H = pedalBary3 alpha beta gamma PA PB PC)
    (hab : 2 * alpha * Delta / pA = 2 * beta * Delta / pB)
    (hbc : 2 * beta * Delta / pB = 2 * gamma * Delta / pC) :
    H = (1 / (pA + pB + pC)) •
      (pA • PA + pB • PB + pC • PC) := by
  have hsum_ne : pA + pB + pC ≠ 0 := by rwa [hdenom] at hden
  have hab' : alpha / pA = beta / pB := by
    have h := hab
    field_simp [hpA, hpB, hDelta] at h
    field_simp [hpA, hpB]
    nlinarith
  have hbc' : beta / pB = gamma / pC := by
    have h := hbc
    field_simp [hpB, hpC, hDelta] at h
    field_simp [hpB, hpC]
    nlinarith
  have halpha : alpha = pA / (pA + pB + pC) := by
    have h1 : beta = alpha * pB / pA := by
      field_simp [hpA, hpB] at hab'
      field_simp [hpA]
      nlinarith
    have h2 : gamma = alpha * pC / pA := by
      field_simp [hpB, hpC] at hbc'
      rw [h1] at hbc'
      field_simp [hpA, hpB, hpC] at hbc'
      field_simp [hpA]
      nlinarith
    rw [h1, h2] at hsum
    field_simp [hpA] at hsum
    field_simp [hsum_ne]
    nlinarith
  have hbeta : beta = pB / (pA + pB + pC) := by
    field_simp [hpA, hpB] at hab'
    rw [halpha] at hab'
    have h : beta * (pA + pB + pC) = pB := by
      field_simp [hpA, hsum_ne] at hab'
      nlinarith
    field_simp [hsum_ne]
    nlinarith
  have hgamma : gamma = pC / (pA + pB + pC) := by
    field_simp [hpB, hpC] at hbc'
    rw [hbeta] at hbc'
    have h : gamma * (pA + pB + pC) = pC := by
      field_simp [hpB, hsum_ne] at hbc'
      nlinarith
    field_simp [hsum_ne]
    nlinarith
  rw [hH, halpha, hbeta, hgamma]
  apply Vec.ext <;> simp [pedalBary3] <;> field_simp [hsum_ne]

theorem pedal_triangle_center_theorem
    (A B C PA PB PC : Point) (a b c : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ha2 : a ^ 2 = q (B - C))
    (hb2 : b ^ 2 = q (C - A))
    (hc2 : c ^ 2 = q (A - B))
    (hAB : q A = q B) (hAC : q A = q C)
    (hPA : PA = C + ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a ^ 2)) • (B - C))
    (hPB : PB = C + ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * b ^ 2)) • (A - C))
    (hPC : PC = B + ((a ^ 2 + c ^ 2 - b ^ 2) / (2 * c ^ 2)) • (A - B)) :
    let pA := a * (a ^ 2 - b ^ 2 - c ^ 2) / (2 * b * c)
    let pB := b * (b ^ 2 - c ^ 2 - a ^ 2) / (2 * c * a)
    let pC := c * (c ^ 2 - a ^ 2 - b ^ 2) / (2 * a * b)
    pA • PA + pB • PB + pC • PC =
      (pA + pB + pC) • normalizedOrthocenter A B C :=
  pedal_weighted_foot_identity A B C PA PB PC a b c ha hb hc ha2 hb2 hc2
    hAB hAC hPA hPB hPC

end Triangle
end MinkowskiMerge
