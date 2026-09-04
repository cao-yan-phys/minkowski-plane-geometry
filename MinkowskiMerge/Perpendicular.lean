import MinkowskiMerge.Affine
import MinkowskiMerge.Causal
import MinkowskiMerge.Orthogonal


set_option autoImplicit false

namespace MinkowskiMerge

def orthogonalDirection (v : Vec) : Submodule ℝ Vec :=
  lorentzForm.orthogonal (ℝ ∙ v)

def perpendicularThrough (P : Point) (v : Vec) : Line :=
  AffineSubspace.mk' P (orthogonalDirection v)

@[simp] theorem perpendicularThrough_direction (P : Point) (v : Vec) :
    (perpendicularThrough P v).direction = orthogonalDirection v := by
  exact AffineSubspace.direction_mk' _ _

@[simp] theorem self_mem_perpendicularThrough (P : Point) (v : Vec) :
    P ∈ perpendicularThrough P v := by
  exact AffineSubspace.self_mem_mk' _ _

theorem mem_perpendicularThrough_iff {X P : Point} {v : Vec} :
    X ∈ perpendicularThrough P v ↔ intervalVec P X ⟂ₘ v := by
  change intervalVec P X ∈ orthogonalDirection v ↔ intervalVec P X ⟂ₘ v
  constructor
  · intro hX
    have hvX := hX v (Submodule.mem_span_singleton_self v)
    exact (isOrthogonal_comm v (intervalVec P X)).mp hvX
  · intro hX n hn
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hn
    have hvX : v ⟂ₘ intervalVec P X :=
      (isOrthogonal_comm v (intervalVec P X)).mpr hX
    rw [isOrthogonal_iff_dot_eq_zero] at hvX
    change dot (r • v) (intervalVec P X) = 0
    calc
      dot (r • v) (intervalVec P X) = r * dot v (intervalVec P X) := by
        simp only [dot_apply, Vec.x_smul, Vec.t_smul]
        ring
      _ = 0 := by rw [hvX, mul_zero]

def IsNonNullLine (B C : Point) : Prop := intervalSq B C ≠ 0

noncomputable def footParameter (P B C : Point) : ℝ :=
  dot (intervalVec B P) (intervalVec B C) / intervalSq B C

noncomputable def perpendicularFoot (P B C : Point)
    (_hBC : IsNonNullLine B C) : Point :=
  AffineMap.lineMap B C (footParameter P B C)

def IsPerpendicularFoot (H P B C : Point) : Prop :=
  H ∈ lineThrough B C ∧ intervalVec P H ⟂ₘ intervalVec B C

def signedDoubleArea (A B C : Point) : ℝ :=
  br (intervalVec A B) (intervalVec A C)

noncomputable def heightVec (P B C : Point)
    (hBC : IsNonNullLine B C) : Vec :=
  intervalVec P (perpendicularFoot P B C hBC)

noncomputable def heightSq (P B C : Point)
    (hBC : IsNonNullLine B C) : ℝ :=
  q (heightVec P B C hBC)

noncomputable def pointLineDistance (P B C : Point)
    (hBC : IsNonNullLine B C) : ℂ :=
  complexLength (heightVec P B C hBC)

theorem nonNullLine_ne {B C : Point} (hBC : IsNonNullLine B C) : B ≠ C := by
  intro h
  subst C
  exact hBC (intervalSq_self B)

theorem intervalVec_lineMap (P B C : Point) (r : ℝ) :
    intervalVec P (AffineMap.lineMap B C r) =
      r • intervalVec B C - intervalVec B P := by
  rw [AffineMap.lineMap_apply_module']
  simp only [intervalVec, vsub_eq_sub]
  module

theorem dot_intervalVec_lineMap_right (P B C : Point) (r : ℝ) :
    dot (intervalVec P (AffineMap.lineMap B C r)) (intervalVec B C) =
      r * intervalSq B C - dot (intervalVec B P) (intervalVec B C) := by
  rw [intervalVec_lineMap]
  simp only [dot_apply, intervalSq, q_apply, Vec.x_sub, Vec.t_sub,
    Vec.x_smul, Vec.t_smul]
  ring

theorem perpendicularFoot_mem_line (P B C : Point) (hBC : IsNonNullLine B C) :
    perpendicularFoot P B C hBC ∈ lineThrough B C := by
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

theorem perpendicularFoot_orthogonal (P B C : Point)
    (hBC : IsNonNullLine B C) :
    intervalVec P (perpendicularFoot P B C hBC) ⟂ₘ intervalVec B C := by
  rw [isOrthogonal_iff_dot_eq_zero]
  rw [perpendicularFoot, dot_intervalVec_lineMap_right]
  apply sub_eq_zero.mpr
  exact (div_mul_cancel₀ _ hBC)

theorem perpendicularFoot_spec (P B C : Point) (hBC : IsNonNullLine B C) :
    IsPerpendicularFoot (perpendicularFoot P B C hBC) P B C := by
  exact ⟨perpendicularFoot_mem_line P B C hBC,
    perpendicularFoot_orthogonal P B C hBC⟩

theorem perpendicularFoot_unique {H P B C : Point} (hBC : IsNonNullLine B C)
    (hH : IsPerpendicularFoot H P B C) :
    H = perpendicularFoot P B C hBC := by
  rcases hH with ⟨hHline, hHorth⟩
  rcases (mem_line_iff.mp hHline) with ⟨r, hr⟩
  subst H
  congr 1
  rw [isOrthogonal_iff_dot_eq_zero, dot_intervalVec_lineMap_right] at hHorth
  exact (eq_div_iff hBC).2 (sub_eq_zero.mp hHorth)

theorem isPerpendicularFoot_iff {H P B C : Point} (hBC : IsNonNullLine B C) :
    IsPerpendicularFoot H P B C ↔ H = perpendicularFoot P B C hBC := by
  constructor
  · exact perpendicularFoot_unique hBC
  · rintro rfl
    exact perpendicularFoot_spec P B C hBC

theorem heightVec_formula (P B C : Point) (hBC : IsNonNullLine B C) :
    heightVec P B C hBC =
      footParameter P B C • intervalVec B C - intervalVec B P := by
  exact intervalVec_lineMap P B C (footParameter P B C)

theorem heightSq_projection_formula (P B C : Point) (hBC : IsNonNullLine B C) :
    heightSq P B C hBC =
      q (intervalVec B P) -
        dot (intervalVec B P) (intervalVec B C) ^ 2 / intervalSq B C := by
  rw [heightSq, heightVec_formula, footParameter]
  simp only [intervalSq]
  rw [q_sub, q_smul]
  simp only [dot_apply, q_apply, Vec.x_smul, Vec.t_smul]
  field_simp
  ring

theorem signedDoubleArea_eq_neg_br (P B C : Point) :
    signedDoubleArea P B C =
      -br (intervalVec B P) (intervalVec B C) := by
  simp only [signedDoubleArea, intervalVec, br_apply, vsub_eq_sub,
    Vec.x_sub, Vec.t_sub]
  ring

theorem heightSq_eq_neg_area_sq_div_intervalSq (P B C : Point)
    (hBC : IsNonNullLine B C) :
    heightSq P B C hBC =
      -(signedDoubleArea P B C) ^ 2 / intervalSq B C := by
  rw [heightSq_projection_formula P B C hBC]
  rw [signedDoubleArea_eq_neg_br]
  change q (intervalVec B C) ≠ 0 at hBC
  rw [intervalSq]
  have hgram := gram_identity (intervalVec B P) (intervalVec B C)
  field_simp [hBC]
  nlinarith [hgram]

@[simp] theorem pointLineDistance_sq (P B C : Point)
    (hBC : IsNonNullLine B C) :
    pointLineDistance P B C hBC ^ 2 =
      (-(signedDoubleArea P B C) ^ 2 / intervalSq B C : ℝ) := by
  rw [pointLineDistance, complexLength_sq]
  exact_mod_cast heightSq_eq_neg_area_sq_div_intervalSq P B C hBC

end MinkowskiMerge
