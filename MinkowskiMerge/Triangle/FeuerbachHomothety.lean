import MinkowskiMerge.CircleHomothety
import MinkowskiMerge.Triangle.GeneralizedFeuerbach


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

noncomputable section

theorem excircleCSignedHomothetyData (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (hC : T.excenterDenomC ≠ 0) :
    ∃ ε : ℝ, LorentzCircle.SignedHomothetyData
      (T.ninePointCircle hN) (T.excircleC hT hC) ε
      T.ninePointRadiusMagnitude (T.lambdaC * T.exradiusCMagnitude) := by
  rcases hT with hS | hT
  · have hD :=
      ninePointCenter_excenterC_intervalSq_eq_neg_signedDifference_sq_spacelike
        T hN hS hC
    have h₁ := ninePointCircle_radiusSq_eq_neg_magnitude_sq_spacelike T hN hS
    have h₂ := excircleC_radiusSq_eq_neg_magnitude_sq_spacelike T hN hS hC
    have hLambda := lambdaC_sq T
    refine ⟨-1, ?_⟩
    refine
      { epsilon_ne_zero := by norm_num
        rho_ne_zero := ne_of_gt (ninePointRadiusMagnitude_pos T hN (Or.inl hS))
        q_ne_zero := mul_ne_zero (lambdaC_ne_zero T)
          (ne_of_gt (exradiusCMagnitude_pos T hN hC))
        centerSq_eq := ?_
        left_radiusSq_eq := ?_
        right_radiusSq_eq := ?_ }
    · simpa using hD
    · simpa using h₁
    · rw [h₂, mul_pow, hLambda]
      ring
  · have hD :=
      ninePointCenter_excenterC_intervalSq_eq_signedDifference_sq_timelike
        T hN hT hC
    have h₁ := ninePointCircle_radiusSq_eq_magnitude_sq_timelike T hN hT
    have h₂ := excircleC_radiusSq_eq_magnitude_sq_timelike T hN hT hC
    have hLambda := lambdaC_sq T
    refine ⟨1, ?_⟩
    refine
      { epsilon_ne_zero := by norm_num
        rho_ne_zero := ne_of_gt (ninePointRadiusMagnitude_pos T hN (Or.inr hT))
        q_ne_zero := mul_ne_zero (lambdaC_ne_zero T)
          (ne_of_gt (exradiusCMagnitude_pos T hN hC))
        centerSq_eq := ?_
        left_radiusSq_eq := ?_
        right_radiusSq_eq := ?_ }
    · simpa using hD
    · simpa using h₁
    · rw [h₂, mul_pow, hLambda]
      ring

theorem excircleSignedHomothetyData (T : Triangle) (hN : T.Nondegenerate)
    (hT : T.IsNonMixed) (i : ExcenterIndex)
    (hD : T.excenterDenomAt i ≠ 0) :
    ∃ ε : ℝ, LorentzCircle.SignedHomothetyData
      (T.ninePointCircle hN) (T.excircleAt hT i hD) ε
      T.ninePointRadiusMagnitude
      (T.lambdaAt i * T.exradiusMagnitudeAt i) := by
  cases i with
  | A =>
      have hR : T.rotate.Nondegenerate := rotateNondegenerate T hN
      have hC : T.rotate.excenterDenomC ≠ 0 := by
        simpa only [rotate_excenterDenomC] using hD
      obtain ⟨ε, hdata⟩ := excircleCSignedHomothetyData T.rotate hR
        (rotateIsNonMixed T hT) hC
      rw [rotate_ninePointCircle T hN hR] at hdata
      refine ⟨ε, ?_⟩
      simpa [excircleAt, excircleA, lambdaAt, exradiusMagnitudeAt] using hdata
  | B =>
      have hR : T.rotate.Nondegenerate := rotateNondegenerate T hN
      have hRR : T.rotateTwo.Nondegenerate := rotateTwoNondegenerate T hN
      have hC : T.rotateTwo.excenterDenomC ≠ 0 := by
        simpa only [rotateTwo_excenterDenomC] using hD
      obtain ⟨ε, hdata⟩ := excircleCSignedHomothetyData T.rotateTwo hRR
        (rotateTwoIsNonMixed T hT) hC
      refine ⟨ε, ?_⟩
      simpa [excircleAt, excircleB, lambdaAt, exradiusMagnitudeAt,
        rotateTwo_ninePointCircle T hN hR hRR] using hdata
  | C =>
      simpa [excircleAt, lambdaAt, exradiusMagnitudeAt] using
        excircleCSignedHomothetyData T hN hT hD

end

end Triangle
end MinkowskiMerge
