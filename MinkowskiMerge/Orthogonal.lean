import MinkowskiMerge.Causal
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal


set_option autoImplicit false

namespace MinkowskiMerge

def IsOrthogonal (v w : Vec) : Prop := lorentzForm.IsOrtho v w

infix:50 " ⟂ₘ " => IsOrthogonal

theorem lorentzForm_isSymm : lorentzForm.IsSymm := by
  constructor
  intro v w
  change dot v w = dot w v
  exact dot_comm v w

theorem lorentzForm_nondegenerate : lorentzForm.Nondegenerate := by
  constructor
  · intro v h
    apply Vec.ext
    · have hx := h (1, 0)
      simpa only [lorentzForm_apply, Vec.x_mk, Vec.t_mk, mul_one, mul_zero,
        sub_zero] using hx
    · have ht := h (0, 1)
      simpa only [lorentzForm_apply, Vec.x_mk, Vec.t_mk, mul_zero, mul_one,
        zero_sub, neg_eq_zero] using ht
  · intro v h
    apply Vec.ext
    · have hx := h (1, 0)
      simpa only [lorentzForm_apply, Vec.x_mk, Vec.t_mk, one_mul, zero_mul,
        sub_zero] using hx
    · have ht := h (0, 1)
      simpa only [lorentzForm_apply, Vec.x_mk, Vec.t_mk, zero_mul, one_mul,
        zero_sub, neg_eq_zero] using ht

@[simp] theorem isOrthogonal_iff_dot_eq_zero {v w : Vec} :
    v ⟂ₘ w ↔ dot v w = 0 := Iff.rfl

theorem isOrthogonal_comm (v w : Vec) : v ⟂ₘ w ↔ w ⟂ₘ v := by
  exact lorentzForm_isSymm.ortho_comm

@[simp] theorem zero_isOrthogonal (v : Vec) : (0 : Vec) ⟂ₘ v := by
  exact LinearMap.BilinForm.isOrtho_zero_left v

@[simp] theorem isOrthogonal_zero (v : Vec) : v ⟂ₘ (0 : Vec) := by
  exact LinearMap.BilinForm.isOrtho_zero_right v

@[simp] theorem isOrthogonal_smul_left {r : ℝ} (hr : r ≠ 0) (v w : Vec) :
    (r • v) ⟂ₘ w ↔ v ⟂ₘ w := by
  exact LinearMap.BilinForm.isOrtho_smul_left hr

@[simp] theorem isOrthogonal_smul_right {r : ℝ} (hr : r ≠ 0) (v w : Vec) :
    v ⟂ₘ (r • w) ↔ v ⟂ₘ w := by
  exact LinearMap.BilinForm.isOrtho_smul_right hr

theorem isNull_iff_self_orthogonal (v : Vec) : IsNull v ↔ v ⟂ₘ v := by
  rfl

theorem null_self_orthogonal {v : Vec} (h : IsNull v) : v ⟂ₘ v :=
  (isNull_iff_self_orthogonal v).mp h

theorem isOrthogonal_causal_types {v w : Vec}
    (hvw : v ⟂ₘ w) (hv : ¬IsNull v) (hw : ¬IsNull w) :
    (IsTimelike v ∧ IsSpacelike w) ∨ (IsSpacelike v ∧ IsTimelike w) := by
  have hvq : q v ≠ 0 := by simpa only [IsNull] using hv
  have hwq : q w ≠ 0 := by simpa only [IsNull] using hw
  have hdot : dot v w = 0 := isOrthogonal_iff_dot_eq_zero.mp hvw
  have hgram := gram_identity v w
  have hnonpos : q v * q w ≤ 0 := by
    rw [hdot] at hgram
    nlinarith [sq_nonneg (br v w)]
  have hprod : q v * q w < 0 :=
    lt_of_le_of_ne hnonpos (mul_ne_zero hvq hwq)
  rcases mul_neg_iff.mp hprod with h | h
  · exact Or.inr ⟨h.1, h.2⟩
  · exact Or.inl ⟨h.1, h.2⟩

theorem eq_zero_of_orthogonal_pair {d u w : Vec}
    (hdu : d ⟂ₘ u) (hdw : d ⟂ₘ w) (huw : br u w ≠ 0) : d = 0 := by
  rw [isOrthogonal_iff_dot_eq_zero] at hdu hdw
  have hxprod : d.x * br u w = 0 := by
    calc
      d.x * br u w = dot d u * w.t - dot d w * u.t := by
        simp only [dot_apply, br_apply]
        ring
      _ = 0 := by rw [hdu, hdw]; ring
  have htprod : d.t * br u w = 0 := by
    calc
      d.t * br u w = dot d u * w.x - dot d w * u.x := by
        simp only [dot_apply, br_apply]
        ring
      _ = 0 := by rw [hdu, hdw]; ring
  have hx : d.x = 0 := (mul_eq_zero.mp hxprod).resolve_right huw
  have ht : d.t = 0 := (mul_eq_zero.mp htprod).resolve_right huw
  exact Vec.ext hx ht

end MinkowskiMerge
