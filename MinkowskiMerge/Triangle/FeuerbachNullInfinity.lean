import MinkowskiMerge.Cycle.CompactifiedCircle
import MinkowskiMerge.Triangle.FeuerbachHomothety


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

private theorem excircleC_center_formula (T : Triangle) (hN : T.Nondegenerate)
    (hC : T.excenterDenomC ≠ 0)
    (hEq : T.excenterC hC = T.ninePointCenter hN) :
    intervalVec T.A (T.circumcenter hN) =
      ((T.sideAbsLengthA - T.sideAbsLengthB - T.sideAbsLengthC) /
        T.excenterDenomC) • T.sideVecC +
      ((T.sideAbsLengthA + T.sideAbsLengthB + T.sideAbsLengthC) /
        T.excenterDenomC) • intervalVec T.A T.C := by
  rw [excenterC_eq_sideCombination, ninePointCenter_eq_affine_formula] at hEq
  apply_fun (fun P : Point => intervalVec T.A P) at hEq
  simp only [intervalVec, vsub_eq_sub, sideVecC] at hEq ⊢
  have hEq' := congrArg (fun V : Vec => T.excenterDenomC • V) hEq
  simp only [smul_sub, smul_add, smul_smul] at hEq'
  field_simp [hC] at hEq'
  apply (smul_right_injective Vec hC)
  simp only [smul_add, smul_smul]
  field_simp [hC]
  ext
  · have hx := congrArg Vec.x hEq'
    simp only [excenterDenomC, signedPerimeter, one_mul, neg_one_mul,
      Vec.x_add, Vec.x_sub, Vec.x_smul] at hx ⊢
    ring_nf at hx ⊢
    nlinarith
  · have ht := congrArg Vec.t hEq'
    simp only [excenterDenomC, signedPerimeter, one_mul, neg_one_mul,
      Vec.t_add, Vec.t_sub, Vec.t_smul] at ht ⊢
    ring_nf at ht ⊢
    nlinarith

private theorem excircleC_ne_ninePointCenter (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) (hC : T.excenterDenomC ≠ 0) :
    T.excenterC hC ≠ T.ninePointCenter hN := by
  intro hEq
  have hO := excircleC_center_formula T hN hC hEq
  have hdotU : dot (intervalVec T.A (T.circumcenter hN)) T.sideVecC =
      T.sideSqC / 2 := by
    simpa [circumcenter, intervalVec, vsub_eq_sub] using
      dot_circumcenterOffset_sideVecC T hN
  have hdotV : dot (intervalVec T.A (T.circumcenter hN))
      (intervalVec T.A T.C) = T.sideSqB / 2 := by
    convert dot_circumcenterOffset_AC T hN using 1 <;>
      simp [circumcenter, sideSqB, intervalSq, intervalVec, vsub_eq_sub,
        q_apply, dot_apply] <;> ring
  have hUV : dot T.sideVecC (intervalVec T.A T.C) =
      (T.sideSqB + T.sideSqC - T.sideSqA) / 2 := by
    simp [sideVecC, sideSqA, sideSqB, sideSqC, intervalSq, intervalVec,
      vsub_eq_sub, q_apply, dot_apply]
    ring
  have hVV : dot (intervalVec T.A T.C) (intervalVec T.A T.C) = T.sideSqB := by
    change q (intervalVec T.A T.C) = intervalSq T.C T.A
    rw [intervalSq, intervalVec_rev, q_neg]
  rw [hO] at hdotU hdotV
  simp only [dot_add_left, dot_smul_left] at hdotU hdotV
  rw [show dot T.sideVecC T.sideVecC = T.sideSqC by rfl,
    dot_comm (intervalVec T.A T.C) T.sideVecC, hUV] at hdotU
  rw [hUV, hVV] at hdotV
  have hposA := hT.sideAbsLengthA_pos
  have hposB := hT.sideAbsLengthB_pos
  have hposC := hT.sideAbsLengthC_pos
  rcases hT with hS | hT
  · have ha : T.sideAbsLengthA ^ 2 = T.sideSqA :=
      absLength_sq_of_spacelike hS.1
    have hb : T.sideAbsLengthB ^ 2 = T.sideSqB :=
      absLength_sq_of_spacelike hS.2.1
    have hc : T.sideAbsLengthC ^ 2 = T.sideSqC :=
      absLength_sq_of_spacelike hS.2.2
    field_simp [hC] at hdotU hdotV
    simp only [excenterDenomC, signedPerimeter, one_mul, neg_one_mul] at hdotU hdotV
    have hdotU' := hdotU
    have hdotV' := hdotV
    rw [← ha, ← hb, ← hc] at hdotU' hdotV'
    have hfactorU :
        (T.sideAbsLengthA - T.sideAbsLengthB) *
          T.excenterDenomC *
          (T.sideAbsLengthA + T.sideAbsLengthB + 2 * T.sideAbsLengthC) = 0 := by
      simp only [excenterDenomC, signedPerimeter, one_mul, neg_one_mul]
      ring_nf at hdotU' ⊢
      linarith [hdotU']
    have hfactorV :
        (T.sideAbsLengthA + T.sideAbsLengthC) *
          T.excenterDenomC *
          (T.sideAbsLengthA - 2 * T.sideAbsLengthB - T.sideAbsLengthC) = 0 := by
      simp only [excenterDenomC, signedPerimeter, one_mul, neg_one_mul]
      ring_nf at hdotV' ⊢
      linarith [hdotV']
    rcases mul_eq_zero.mp hfactorU with hleft | hsum
    · rcases mul_eq_zero.mp hleft with hab | hden
      · have hab' : T.sideAbsLengthA = T.sideAbsLengthB := by linarith
        rcases mul_eq_zero.mp hfactorV with hleft' | hrel
        · rcases mul_eq_zero.mp hleft' with hsum' | hden'
          · nlinarith
          · exact hC hden'
        · nlinarith
      · exact hC hden
    · nlinarith
  · have ha : T.sideAbsLengthA ^ 2 = -T.sideSqA :=
      absLength_sq_of_timelike hT.1
    have hb : T.sideAbsLengthB ^ 2 = -T.sideSqB :=
      absLength_sq_of_timelike hT.2.1
    have hc : T.sideAbsLengthC ^ 2 = -T.sideSqC :=
      absLength_sq_of_timelike hT.2.2
    field_simp [hC] at hdotU hdotV
    simp only [excenterDenomC, signedPerimeter, one_mul, neg_one_mul] at hdotU hdotV
    have hdotU' := hdotU
    have hdotV' := hdotV
    have ha' : T.sideSqA = -T.sideAbsLengthA ^ 2 := by linarith
    have hb' : T.sideSqB = -T.sideAbsLengthB ^ 2 := by linarith
    have hc' : T.sideSqC = -T.sideAbsLengthC ^ 2 := by linarith
    rw [ha', hb', hc'] at hdotU' hdotV'
    have hfactorU :
        (T.sideAbsLengthA - T.sideAbsLengthB) *
          T.excenterDenomC *
          (T.sideAbsLengthA + T.sideAbsLengthB + 2 * T.sideAbsLengthC) = 0 := by
      simp only [excenterDenomC, signedPerimeter, one_mul, neg_one_mul]
      ring_nf at hdotU' ⊢
      linarith [hdotU']
    have hfactorV :
        (T.sideAbsLengthA + T.sideAbsLengthC) *
          T.excenterDenomC *
          (T.sideAbsLengthA - 2 * T.sideAbsLengthB - T.sideAbsLengthC) = 0 := by
      simp only [excenterDenomC, signedPerimeter, one_mul, neg_one_mul]
      ring_nf at hdotV' ⊢
      linarith [hdotV']
    rcases mul_eq_zero.mp hfactorU with hleft | hsum
    · rcases mul_eq_zero.mp hleft with hab | hden
      · have hab' : T.sideAbsLengthA = T.sideAbsLengthB := by linarith
        rcases mul_eq_zero.mp hfactorV with hleft' | hrel
        · rcases mul_eq_zero.mp hleft' with hsum' | hden'
          · nlinarith
          · exact hC hden'
        · nlinarith
      · exact hC hden
    · nlinarith

private theorem excircleA_ne_ninePointCenter (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) (hA : T.excenterDenomA ≠ 0) :
    T.excenterA hA ≠ T.ninePointCenter hN := by
  have hR : T.rotate.Nondegenerate := rotateNondegenerate T hN
  have hC : T.rotate.excenterDenomC ≠ 0 := by
    simpa only [rotate_excenterDenomC] using hA
  have hne := excircleC_ne_ninePointCenter T.rotate hR
    (rotateIsNonMixed T hT) hC
  intro hEq
  apply hne
  rw [rotate_excenterC_eq_excenterA T hA, rotate_ninePointCenter T hN hR]
  exact hEq

private theorem excircleB_ne_ninePointCenter (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) (hB : T.excenterDenomB ≠ 0) :
    T.excenterB hB ≠ T.ninePointCenter hN := by
  have hR : T.rotate.Nondegenerate := rotateNondegenerate T hN
  have hRR : T.rotateTwo.Nondegenerate := rotateTwoNondegenerate T hN
  have hC : T.rotateTwo.excenterDenomC ≠ 0 := by
    simpa only [rotateTwo_excenterDenomC] using hB
  have hne := excircleC_ne_ninePointCenter T.rotateTwo hRR
    (rotateTwoIsNonMixed T hT) hC
  intro hEq
  apply hne
  calc
    T.rotateTwo.excenterC hC = T.excenterB hB := rotateTwo_excenterC_eq_excenterB T hB
    _ = T.ninePointCenter hN := hEq
    _ = T.rotateTwo.ninePointCenter hRR :=
      (calc
        T.rotateTwo.ninePointCenter hRR = T.rotate.ninePointCenter hR :=
          rotate_ninePointCenter T.rotate hR hRR
        _ = T.ninePointCenter hN := rotate_ninePointCenter T hN hR).symm

theorem excenterAt_ne_ninePointCenter (T : Triangle)
    (hN : T.Nondegenerate) (hT : T.IsNonMixed) (i : ExcenterIndex)
    (hD : T.excenterDenomAt i ≠ 0) :
    T.excenterAt i hD ≠ T.ninePointCenter hN := by
  cases i with
  | A => exact excircleA_ne_ninePointCenter T hN hT hD
  | B => exact excircleB_ne_ninePointCenter T hN hT hD
  | C => exact excircleC_ne_ninePointCenter T hN hT hD

def HasExcircleFeuerbachContact (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (i : ExcenterIndex) : Prop :=
  let hD := hN.excenterDenomAt_ne_zero hT i
  (T.excircleFeuerbachGap i ≠ 0 ∧
    LorentzCircle.IsProperTangentAt (T.ninePointCircle hN)
      (T.excircleAt hT i hD)
      (T.excircleFeuerbachContactPoint hN hT i hD)) ∨
  (T.excircleFeuerbachGap i = 0 ∧
    LorentzCircle.HasProjectiveNullInfinityContact (T.ninePointCircle hN)
      (T.excircleAt hT i hD))

theorem excircleFeuerbachContact (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (i : ExcenterIndex) :
    T.HasExcircleFeuerbachContact hN hT i := by
  let hD := hN.excenterDenomAt_ne_zero hT i
  by_cases hgap : T.excircleFeuerbachGap i = 0
  · right
    refine ⟨hgap, ?_⟩
    obtain ⟨ε, hdata⟩ := excircleSignedHomothetyData T hN hT i hD
    have hradii : T.ninePointRadiusMagnitude =
        T.lambdaAt i * T.exradiusMagnitudeAt i := by
      exact sub_eq_zero.mp hgap
    have hcenters : (T.ninePointCircle hN).center ≠
        (T.excircleAt hT i hD).center := by
      simpa only [ninePointCircle_center, excircleAt_center] using
        (excenterAt_ne_ninePointCenter T hN hT i hD).symm
    exact (hdata.hasNullInfinityContact hradii hcenters).hasProjectiveContact
  · left
    exact ⟨hgap, isProperTangentAt_excircle T hN hT i hD hgap⟩

end
end Triangle
end MinkowskiMerge
