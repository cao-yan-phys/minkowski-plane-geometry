import MinkowskiMerge.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas


set_option autoImplicit false

namespace MinkowskiMerge

def lorentzForm : LinearMap.BilinForm ℝ Vec :=
  LinearMap.mk₂ ℝ
    (fun v w : Vec => v.x * w.x - v.t * w.t)
    (by intros; simp; ring)
    (by intros; simp; ring)
    (by intros; simp; ring)
    (by intros; simp; ring)

def dot (v w : Vec) : ℝ := lorentzForm v w

def lorentzQ : QuadraticMap ℝ Vec ℝ := lorentzForm.toQuadraticMap

def q (v : Vec) : ℝ := lorentzQ v

def areaForm : LinearMap.BilinForm ℝ Vec :=
  LinearMap.mk₂ ℝ
    (fun v w : Vec => v.x * w.t - v.t * w.x)
    (by intros; simp; ring)
    (by intros; simp; ring)
    (by intros; simp; ring)
    (by intros; simp; ring)

def br (v w : Vec) : ℝ := areaForm v w

private def swapLinearMap : Vec →ₗ[ℝ] Vec where
  toFun v := (v.t, v.x)
  map_add' v w := by ext <;> simp
  map_smul' r v := by ext <;> simp

def J : Vec ≃ₗ[ℝ] Vec :=
  LinearEquiv.ofInvolutive swapLinearMap (by
    intro v
    ext <;> rfl)

@[simp] theorem lorentzForm_apply (v w : Vec) :
    lorentzForm v w = v.x * w.x - v.t * w.t := rfl

@[simp] theorem dot_apply (v w : Vec) :
    dot v w = v.x * w.x - v.t * w.t := rfl

@[simp] theorem lorentzQ_apply (v : Vec) :
    lorentzQ v = v.x ^ 2 - v.t ^ 2 := by
  simp [lorentzQ, pow_two]

@[simp] theorem q_apply (v : Vec) : q v = v.x ^ 2 - v.t ^ 2 := by
  simp [q]

@[simp] theorem areaForm_apply (v w : Vec) :
    areaForm v w = v.x * w.t - v.t * w.x := rfl

@[simp] theorem br_apply (v w : Vec) :
    br v w = v.x * w.t - v.t * w.x := rfl

@[simp] theorem J_apply (v : Vec) : J v = (v.t, v.x) := rfl

theorem dot_comm (v w : Vec) : dot v w = dot w v := by
  simp only [dot_apply]
  ring

@[simp] theorem dot_add_left (u v w : Vec) :
    dot (u + v) w = dot u w + dot v w := by
  simp only [dot_apply, Vec.x_add, Vec.t_add]
  ring

@[simp] theorem dot_add_right (u v w : Vec) :
    dot u (v + w) = dot u v + dot u w := by
  rw [dot_comm, dot_add_left, dot_comm v u, dot_comm w u]

@[simp] theorem dot_sub_left (u v w : Vec) :
    dot (u - v) w = dot u w - dot v w := by
  simp only [dot_apply, Vec.x_sub, Vec.t_sub]
  ring

@[simp] theorem dot_sub_right (u v w : Vec) :
    dot u (v - w) = dot u v - dot u w := by
  rw [dot_comm, dot_sub_left, dot_comm v u, dot_comm w u]

@[simp] theorem dot_smul_left (r : ℝ) (v w : Vec) :
    dot (r • v) w = r * dot v w := by
  simp only [dot_apply, Vec.x_smul, Vec.t_smul]
  ring

@[simp] theorem dot_smul_right (r : ℝ) (v w : Vec) :
    dot v (r • w) = r * dot v w := by
  rw [dot_comm, dot_smul_left, dot_comm w v]

@[simp] theorem q_zero : q (0 : Vec) = 0 := by simp

@[simp] theorem q_neg (v : Vec) : q (-v) = q v := by
  simp only [q_apply, Vec.x_neg, Vec.t_neg]
  ring

theorem q_smul (r : ℝ) (v : Vec) : q (r • v) = r ^ 2 * q v := by
  simp only [q_apply, Vec.x_smul, Vec.t_smul]
  ring

theorem q_add (v w : Vec) :
    q (v + w) = q v + 2 * dot v w + q w := by
  simp only [q_apply, dot_apply, Vec.x_add, Vec.t_add]
  ring

theorem q_sub (v w : Vec) :
    q (v - w) = q v - 2 * dot v w + q w := by
  simp only [q_apply, dot_apply, Vec.x_sub, Vec.t_sub]
  ring

theorem dot_add_sub_self (u v : Vec) :
    dot (u + v) (v - u) = q v - q u := by
  simp only [dot_apply, q_apply, Vec.x_add, Vec.t_add, Vec.x_sub, Vec.t_sub]
  ring

@[simp] theorem br_self (v : Vec) : br v v = 0 := by
  simp only [br_apply]
  ring

theorem br_swap (v w : Vec) : br w v = -br v w := by
  simp only [br_apply]
  ring

@[simp] theorem br_add_left (u v w : Vec) :
    br (u + v) w = br u w + br v w := by
  simp only [br_apply, Vec.x_add, Vec.t_add]
  ring

@[simp] theorem br_add_right (u v w : Vec) :
    br u (v + w) = br u v + br u w := by
  simp only [br_apply, Vec.x_add, Vec.t_add]
  ring

@[simp] theorem br_sub_left (u v w : Vec) :
    br (u - v) w = br u w - br v w := by
  simp only [br_apply, Vec.x_sub, Vec.t_sub]
  ring

@[simp] theorem br_sub_right (u v w : Vec) :
    br u (v - w) = br u v - br u w := by
  simp only [br_apply, Vec.x_sub, Vec.t_sub]
  ring

@[simp] theorem br_smul_left (r : ℝ) (v w : Vec) :
    br (r • v) w = r * br v w := by
  simp only [br_apply, Vec.x_smul, Vec.t_smul]
  ring

@[simp] theorem br_smul_right (r : ℝ) (v w : Vec) :
    br v (r • w) = r * br v w := by
  simp only [br_apply, Vec.x_smul, Vec.t_smul]
  ring

theorem gram_identity (v w : Vec) :
    dot v w ^ 2 - q v * q w = br v w ^ 2 := by
  simp only [dot_apply, q_apply, br_apply]
  ring

theorem mem_span_singleton_iff_br_eq_zero {v : Vec} (hv : v ≠ 0) (w : Vec) :
    w ∈ ℝ ∙ v ↔ br v w = 0 := by
  constructor
  · intro hw
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp only [br_apply, Vec.x_smul, Vec.t_smul]
    ring
  · intro hbr
    apply Submodule.mem_span_singleton.mpr
    by_cases hx : v.x ≠ 0
    · refine ⟨w.x / v.x, ?_⟩
      apply Vec.ext
      · simp [hx]
      · rw [br_apply] at hbr
        simp only [Vec.t_smul]
        field_simp [hx]
        nlinarith
    · have hvx : v.x = 0 := not_ne_iff.mp hx
      have ht : v.t ≠ 0 := by
        intro hvt
        apply hv
        apply Vec.ext <;> simp [hvx, hvt]
      have hwx : w.x = 0 := by
        rw [br_apply, hvx] at hbr
        simp only [zero_mul, zero_sub, neg_eq_zero] at hbr
        exact (mul_eq_zero.mp hbr).resolve_left ht
      refine ⟨w.t / v.t, ?_⟩
      apply Vec.ext
      · simp [hvx, hwx]
      · simp [ht] 
        

theorem linearIndependent_pair_iff_br_ne_zero (v w : Vec) :
    LinearIndependent ℝ ![v, w] ↔ br v w ≠ 0 := by
  constructor
  · intro hlin hbr
    have hv : v ≠ 0 := hlin.ne_zero 0
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp
      ((mem_span_singleton_iff_br_eq_zero hv w).2 hbr)
    exact ((LinearIndependent.pair_iff' hv).mp hlin r) hr
  · intro hbr
    have hv : v ≠ 0 := by
      intro hv
      subst v
      simp only [br_apply, Vec.x_zero, Vec.t_zero, zero_mul, zero_sub] at hbr
      exact hbr neg_zero
    rw [LinearIndependent.pair_iff' hv]
    intro r hr
    apply hbr
    rw [← hr]
    simp only [br_apply, Vec.x_smul, Vec.t_smul]
    ring

@[simp] theorem J_involutive (v : Vec) : J (J v) = v := by
  exact J.left_inv v

@[simp] theorem q_J (v : Vec) : q (J v) = -q v := by
  simp only [J_apply, q_apply, Vec.x_mk, Vec.t_mk]
  ring

@[simp] theorem dot_J_self (v : Vec) : dot v (J v) = 0 := by
  simp only [J_apply, dot_apply, Vec.x_mk, Vec.t_mk]
  ring

theorem dot_J_left (v w : Vec) : dot (J v) w = -br v w := by
  simp only [J_apply, dot_apply, br_apply, Vec.x_mk, Vec.t_mk]
  ring

theorem dot_J_right (v w : Vec) : dot v (J w) = br v w := by
  simp only [J_apply, dot_apply, br_apply, Vec.x_mk, Vec.t_mk]

end MinkowskiMerge
