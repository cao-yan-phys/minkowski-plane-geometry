import MinkowskiMerge.TimeOrientation
import MinkowskiMerge.Cycle.DoubleCompactified
import MinkowskiMerge.Cycle.Mobius


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable section

open Filter
open scoped Topology
open LightconeMobius

def IsFutureNull (v : Vec) : Prop :=
  IsNull v ∧ v ≠ 0 ∧ 0 < v.t

def IsPastNull (v : Vec) : Prop :=
  IsNull v ∧ v ≠ 0 ∧ v.t < 0

def NullPrecedes (P Q : Point) : Prop :=
  IsFutureNull (intervalVec P Q)

theorem isFutureNull_isFutureDirected {v : Vec} (h : IsFutureNull v) :
    IsFutureDirected v := by
  exact ⟨le_of_eq h.1, h.2.2.le⟩

theorem isPastNull_isPastDirected {v : Vec} (h : IsPastNull v) :
    IsPastDirected v := by
  exact ⟨le_of_eq h.1, h.2.2.le⟩

theorem futureNull_neg_iff (v : Vec) :
    IsFutureNull (-v) ↔ IsPastNull v := by
  simp [IsFutureNull, IsPastNull]

theorem pastNull_neg_iff (v : Vec) :
    IsPastNull (-v) ↔ IsFutureNull v := by
  simp [IsFutureNull, IsPastNull]

theorem nullPrecedes_irrefl (P : Point) : ¬NullPrecedes P P := by
  intro h
  change IsFutureNull (intervalVec P P) at h
  have hzero : intervalVec P P = 0 := intervalVec_self P
  rw [hzero] at h
  exact h.2.1 rfl

theorem nullPrecedes_causallyPrecedes {P Q : Point}
    (h : NullPrecedes P Q) : CausallyPrecedes P Q :=
  isFutureNull_isFutureDirected h

theorem uNullRay_intervalVec (u v s : ℝ) :
    intervalVec (pointOfLightcone u v) (pointOfLightcone u (v + s)) =
      (s / 2, s / 2) := by
  ext <;> simp [intervalVec, pointOfLightcone] <;> ring

theorem vNullRay_intervalVec (u v s : ℝ) :
    intervalVec (pointOfLightcone u v) (pointOfLightcone (u + s) v) =
      (-s / 2, s / 2) := by
  ext <;> simp [intervalVec, pointOfLightcone] <;> ring

theorem uNullRay_isFutureNull {u v s : ℝ} (hs : 0 < s) :
    IsFutureNull (intervalVec (pointOfLightcone u v)
      (pointOfLightcone u (v + s))) := by
  rw [uNullRay_intervalVec]
  refine ⟨?_, ?_, ?_⟩
  · simp [IsNull, q]
  · intro h
    have := congrArg Vec.t h
    simp at this
    linarith
  · simp only [Vec.t_mk]
    linarith

theorem vNullRay_isFutureNull {u v s : ℝ} (hs : 0 < s) :
    IsFutureNull (intervalVec (pointOfLightcone u v)
      (pointOfLightcone (u + s) v)) := by
  rw [vNullRay_intervalVec]
  refine ⟨?_, ?_, ?_⟩
  · norm_num [IsNull, q]
    ring
  · intro h
    have := congrArg Vec.t h
    simp at this
    linarith
  · simp only [Vec.t_mk]
    linarith

theorem uNullRay_isPastNull {u v s : ℝ} (hs : s < 0) :
    IsPastNull (intervalVec (pointOfLightcone u v)
      (pointOfLightcone u (v + s))) := by
  rw [uNullRay_intervalVec]
  refine ⟨?_, ?_, ?_⟩
  · simp [IsNull, q]
  · intro h
    have := congrArg Vec.t h
    simp at this
    linarith
  · simp only [Vec.t_mk]
    linarith

theorem vNullRay_isPastNull {u v s : ℝ} (hs : s < 0) :
    IsPastNull (intervalVec (pointOfLightcone u v)
      (pointOfLightcone (u + s) v)) := by
  rw [vNullRay_intervalVec]
  refine ⟨?_, ?_, ?_⟩
  · norm_num [IsNull, q]
    ring
  · intro h
    have := congrArg Vec.t h
    simp at this
    linarith
  · simp only [Vec.t_mk]
    linarith

namespace Cycle.DoubleCompactified

def IsFutureNullInfinityEdge (Z : ConformalPoint) : Prop :=
  Z.1 = ⊤ ∨ Z.2 = ⊤

def IsPastNullInfinityEdge (Z : ConformalPoint) : Prop :=
  Z.1 = ⊥ ∨ Z.2 = ⊥

@[simp] theorem isFutureNullInfinityEdge_uPlusInfinityPoint (u : ℝ) :
    IsFutureNullInfinityEdge (uPlusInfinityPoint u) := by
  exact Or.inr rfl

@[simp] theorem isPastNullInfinityEdge_uMinusInfinityPoint (u : ℝ) :
    IsPastNullInfinityEdge (uMinusInfinityPoint u) := by
  exact Or.inr rfl

@[simp] theorem isFutureNullInfinityEdge_vPlusInfinityPoint (v : ℝ) :
    IsFutureNullInfinityEdge (vPlusInfinityPoint v) := by
  exact Or.inl rfl

@[simp] theorem isPastNullInfinityEdge_vMinusInfinityPoint (v : ℝ) :
    IsPastNullInfinityEdge (vMinusInfinityPoint v) := by
  exact Or.inl rfl

theorem boundary_future_or_past (Z : ConformalPoint) (hZ : IsBoundary Z) :
    IsFutureNullInfinityEdge Z ∨ IsPastNullInfinityEdge Z := by
  rcases hZ with h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)

theorem tendsto_ofPoint_uNullRay_atTop (u v : ℝ) :
    Tendsto (fun s : ℝ =>
      DoubleCompactified.ofPoint (pointOfLightcone u (v + s))) atTop
      (𝓝 (uPlusInfinityPoint u)) := by
  have hv : Tendsto (fun s : ℝ => v + s) atTop atTop :=
    tendsto_atTop_add_const_left atTop v tendsto_id
  have hpair := Filter.Tendsto.prodMk_nhds
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (u : EReal)) atTop (𝓝 (u : EReal)))
    (EReal.tendsto_coe_atTop.comp hv)
  have hfun : (fun s : ℝ =>
      DoubleCompactified.ofPoint (pointOfLightcone u (v + s))) =
      fun s => ((u : EReal), ((v + s : ℝ) : EReal)) := by
    funext s
    apply Prod.ext
    · change (((u + (v + s)) / 2 - ((v + s) - u) / 2 : ℝ) : EReal) = (u : EReal)
      norm_cast
      ring
    · change (((u + (v + s)) / 2 + ((v + s) - u) / 2 : ℝ) : EReal) =
        ((v + s : ℝ) : EReal)
      norm_cast
      ring
  rw [hfun]
  exact hpair

theorem tendsto_ofPoint_vNullRay_atTop (u v : ℝ) :
    Tendsto (fun s : ℝ =>
      DoubleCompactified.ofPoint (pointOfLightcone (u + s) v)) atTop
      (𝓝 (vPlusInfinityPoint v)) := by
  have hu : Tendsto (fun s : ℝ => u + s) atTop atTop :=
    tendsto_atTop_add_const_left atTop u tendsto_id
  have hpair := Filter.Tendsto.prodMk_nhds
    (EReal.tendsto_coe_atTop.comp hu)
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (v : EReal)) atTop (𝓝 (v : EReal)))
  have hfun : (fun s : ℝ =>
      DoubleCompactified.ofPoint (pointOfLightcone (u + s) v)) =
      fun s => (((u + s : ℝ) : EReal), (v : EReal)) := by
    funext s
    apply Prod.ext
    · change ((((u + s) + v) / 2 - (v - (u + s)) / 2 : ℝ) : EReal) =
        ((u + s : ℝ) : EReal)
      norm_cast
      ring
    · change ((((u + s) + v) / 2 + (v - (u + s)) / 2 : ℝ) : EReal) = (v : EReal)
      norm_cast
      ring
  rw [hfun]
  exact hpair

end Cycle.DoubleCompactified

end
end MinkowskiMerge
