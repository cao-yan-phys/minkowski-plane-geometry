import MinkowskiMerge.Form
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable def edir (theta : ℝ) : Vec :=
  (Real.cos theta, Real.sin theta)

noncomputable def complexOfVec (v : Vec) : ℂ :=
  (v.x : ℂ) + (v.t : ℂ) * Complex.I

@[simp] theorem complexOfVec_re (v : Vec) : (complexOfVec v).re = v.x := by
  simp [complexOfVec]

@[simp] theorem complexOfVec_im (v : Vec) : (complexOfVec v).im = v.t := by
  simp [complexOfVec]

theorem complexOfVec_ne_zero (v : Vec) (hv : v ≠ 0) : complexOfVec v ≠ 0 := by
  intro hz
  apply hv
  apply Vec.ext
  · calc
      v.x = (complexOfVec v).re := (complexOfVec_re v).symm
      _ = (0 : ℂ).re := congrArg Complex.re hz
      _ = 0 := rfl
  · calc
      v.t = (complexOfVec v).im := (complexOfVec_im v).symm
      _ = (0 : ℂ).im := congrArg Complex.im hz
      _ = 0 := rfl

theorem euclidean_polar_representation_arg (v : Vec) :
    v = ‖complexOfVec v‖ • edir (Complex.arg (complexOfVec v)) := by
  apply Vec.ext
  · change v.x = ‖complexOfVec v‖ * Real.cos (Complex.arg (complexOfVec v))
    calc
      v.x = (complexOfVec v).re := (complexOfVec_re v).symm
      _ = ‖complexOfVec v‖ * Real.cos (Complex.arg (complexOfVec v)) :=
        (Complex.norm_mul_cos_arg (complexOfVec v)).symm
  · change v.t = ‖complexOfVec v‖ * Real.sin (Complex.arg (complexOfVec v))
    calc
      v.t = (complexOfVec v).im := (complexOfVec_im v).symm
      _ = ‖complexOfVec v‖ * Real.sin (Complex.arg (complexOfVec v)) :=
        (Complex.norm_mul_sin_arg (complexOfVec v)).symm

theorem euclidean_polar_representation (v : Vec) (hv : v ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ ∃ theta : ℝ, v = s • edir theta := by
  refine ⟨‖complexOfVec v‖,
    norm_pos_iff.mpr (complexOfVec_ne_zero v hv),
    Complex.arg (complexOfVec v), euclidean_polar_representation_arg v⟩

theorem edir_add_pi (theta : ℝ) : edir (theta + Real.pi) = -edir theta := by
  ext <;> simp [edir, Real.cos_add_pi, Real.sin_add_pi]

theorem euclidean_projective_polar_representation (v : Vec) (hv : v ≠ 0) :
    ∃ s theta : ℝ, s ≠ 0 ∧ theta ∈ Set.Ico 0 Real.pi ∧ v = s • edir theta := by
  let z := complexOfVec v
  let r := ‖z‖
  let theta := Complex.arg z
  have hr : 0 < r := by
    dsimp [r, z]
    exact norm_pos_iff.mpr (complexOfVec_ne_zero v hv)
  have hvec : v = r • edir theta := by
    simpa [r, theta, z] using euclidean_polar_representation_arg v
  have htheta_low : -Real.pi < theta := by
    dsimp [theta, z]
    exact Complex.neg_pi_lt_arg _
  have htheta_le : theta ≤ Real.pi := by
    dsimp [theta, z]
    exact Complex.arg_le_pi _
  by_cases hneg : theta < 0
  · refine ⟨-r, theta + Real.pi, neg_ne_zero.mpr (ne_of_gt hr), ?_, ?_⟩
    · constructor <;> linarith
    · calc
        v = r • edir theta := hvec
        _ = (-r) • edir (theta + Real.pi) := by
          rw [edir_add_pi]
          module
  · have htheta_nonneg : 0 ≤ theta := le_of_not_gt hneg
    by_cases hlt : theta < Real.pi
    · refine ⟨r, theta, ne_of_gt hr, ⟨htheta_nonneg, hlt⟩, hvec⟩
    · have htheta_eq : theta = Real.pi := le_antisymm htheta_le (le_of_not_gt hlt)
      refine ⟨-r, 0, neg_ne_zero.mpr (ne_of_gt hr), ⟨le_rfl, Real.pi_pos⟩, ?_⟩
      calc
        v = r • edir theta := hvec
        _ = r • edir (0 + Real.pi) := by
          rw [htheta_eq]
          congr 2
          ring
        _ = (-r) • edir 0 := by
          rw [edir_add_pi]
          module

theorem three_distinct_real_order_cases {x y z : ℝ}
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    (x < y ∧ y < z) ∨ (x < z ∧ z < y) ∨
      (y < x ∧ x < z) ∨ (y < z ∧ z < x) ∨
        (z < x ∧ x < y) ∨ (z < y ∧ y < x) := by
  rcases lt_or_gt_of_ne hxy with hxy_lt | hyx_lt
  · rcases lt_or_gt_of_ne hyz with hyz_lt | hzy_lt
    · exact Or.inl ⟨hxy_lt, hyz_lt⟩
    · rcases lt_or_gt_of_ne hzx with hzx_lt | hxz_lt
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hzx_lt, hxy_lt⟩))))
      · exact Or.inr (Or.inl ⟨hxz_lt, hzy_lt⟩)
  · rcases lt_or_gt_of_ne hzx with hzx_lt | hxz_lt
    · rcases lt_or_gt_of_ne hyz with hyz_lt | hzy_lt
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hyz_lt, hzx_lt⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hzy_lt, hyx_lt⟩))))
    · exact Or.inr (Or.inr (Or.inl ⟨hyx_lt, hxz_lt⟩))

noncomputable def euclideanRotateVec (rho : ℝ) (v : Vec) : Vec :=
  (Real.cos rho * v.x - Real.sin rho * v.t,
    Real.sin rho * v.x + Real.cos rho * v.t)

theorem euclideanRotateVec_smul (rho s : ℝ) (v : Vec) :
    euclideanRotateVec rho (s • v) = s • euclideanRotateVec rho v := by
  ext <;> simp [euclideanRotateVec] <;> ring

theorem euclideanRotateVec_edir (phi rho : ℝ) :
    euclideanRotateVec rho (edir phi) = edir (phi + rho) := by
  ext <;> simp [euclideanRotateVec, edir, Real.cos_add, Real.sin_add] <;> ring

theorem q_euclideanRotateVec_smul_edir (s phi rho : ℝ) :
    q (euclideanRotateVec rho (s • edir phi)) =
      s ^ 2 * q (edir (phi + rho)) := by
  rw [euclideanRotateVec_smul, euclideanRotateVec_edir, q_smul]

theorem euclideanRotateVec_smul_edir_spacelike_iff
    (s phi rho : ℝ) (hs : s ≠ 0) :
    0 < q (euclideanRotateVec rho (s • edir phi)) ↔
      0 < q (edir (phi + rho)) := by
  rw [q_euclideanRotateVec_smul_edir,
    mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hs)]

theorem euclideanRotateVec_smul_edir_timelike_iff
    (s phi rho : ℝ) (hs : s ≠ 0) :
    q (euclideanRotateVec rho (s • edir phi)) < 0 ↔
      q (edir (phi + rho)) < 0 := by
  rw [q_euclideanRotateVec_smul_edir, mul_neg_iff]
  constructor
  · rintro (h | h)
    · exact h.2
    · exact (not_lt_of_ge (sq_nonneg s) h.1).elim
  · intro h
    exact Or.inl ⟨sq_pos_of_ne_zero hs, h⟩

theorem euclideanRotateVec_smul_edir_null_iff
    (s phi rho : ℝ) (hs : s ≠ 0) :
    q (euclideanRotateVec rho (s • edir phi)) = 0 ↔
      q (edir (phi + rho)) = 0 := by
  rw [q_euclideanRotateVec_smul_edir]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hs)
  · intro h
    rw [h, mul_zero]

theorem edir_q (theta : ℝ) : q (edir theta) = Real.cos (2 * theta) := by
  simp only [edir, q_apply, Vec.x_mk, Vec.t_mk]
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq theta]

theorem edir_spacelike_iff (theta : ℝ) :
    0 < q (edir theta) ↔ 0 < Real.cos (2 * theta) := by
  rw [edir_q]

theorem edir_timelike_iff (theta : ℝ) :
    q (edir theta) < 0 ↔ Real.cos (2 * theta) < 0 := by
  rw [edir_q]

theorem edir_null_iff (theta : ℝ) :
    q (edir theta) = 0 ↔ Real.cos (2 * theta) = 0 := by
  rw [edir_q]

theorem euclidean_direction_q (theta : ℝ) :
    Real.cos theta ^ 2 - Real.sin theta ^ 2 = Real.cos (2 * theta) := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq theta]

theorem rotated_direction_q (phi rho : ℝ) :
    q (Real.cos (phi + rho), Real.sin (phi + rho)) =
      Real.cos (2 * (phi + rho)) := by
  simp only [q_apply, Vec.x_mk, Vec.t_mk]
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (phi + rho)]

theorem edir_spacelike_of_double_angle_mem_principal
    (theta : ℝ)
    (h : 2 * theta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    0 < q (edir theta) := by
  exact (edir_spacelike_iff theta).2 (Real.cos_pos_of_mem_Ioo h)

theorem edir_timelike_of_double_angle_mem_upper
    (theta : ℝ)
    (hlo : Real.pi / 2 < 2 * theta)
    (hhi : 2 * theta < Real.pi + Real.pi / 2) :
    q (edir theta) < 0 := by
  exact (edir_timelike_iff theta).2
    (Real.cos_neg_of_pi_div_two_lt_of_lt hlo hhi)

theorem edir_null_of_double_angle_eq_pi_div_two
    (theta : ℝ) (h : 2 * theta = Real.pi / 2) :
    q (edir theta) = 0 := by
  rw [edir_q, h, Real.cos_pi_div_two]

theorem edir_spacelike_of_double_angle_eq_zero
    (theta : ℝ) (h : 2 * theta = 0) :
    0 < q (edir theta) := by
  rw [edir_q, h, Real.cos_zero]
  norm_num

theorem edir_timelike_of_double_angle_eq_pi
    (theta : ℝ) (h : 2 * theta = Real.pi) :
    q (edir theta) < 0 := by
  rw [edir_q, h, Real.cos_pi]
  norm_num

theorem rotation_spacelike_classification
    (phi rho1 rho2 rho3 : ℝ)
    (h1 : 0 < Real.cos (2 * (phi + rho1)))
    (h2 : 0 < Real.cos (2 * (phi + rho2)))
    (h3 : 0 < Real.cos (2 * (phi + rho3))) :
    0 < q (edir (phi + rho1)) ∧
      0 < q (edir (phi + rho2)) ∧ 0 < q (edir (phi + rho3)) := by
  exact ⟨(edir_spacelike_iff _).2 h1, (edir_spacelike_iff _).2 h2,
    (edir_spacelike_iff _).2 h3⟩

theorem rotation_obtuse_normal_form_spacelike
    (beta gamma : ℝ)
    (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hshort : beta + gamma < Real.pi / 2) :
    let rho := -(beta + gamma) / 2
    0 < q (edir (0 + rho)) ∧
      0 < q (edir (beta + rho)) ∧
        0 < q (edir ((beta + gamma) + rho)) := by
  intro rho
  have hLpos : 0 < beta + gamma := by linarith
  have h1 : 0 < q (edir (0 + rho)) := by
    apply edir_spacelike_of_double_angle_mem_principal
    exact Set.mem_Ioo.mpr ⟨by dsimp [rho]; linarith, by dsimp [rho]; linarith⟩
  have h2 : 0 < q (edir (beta + rho)) := by
    apply edir_spacelike_of_double_angle_mem_principal
    exact Set.mem_Ioo.mpr ⟨by dsimp [rho]; linarith, by dsimp [rho]; linarith⟩
  have h3 : 0 < q (edir ((beta + gamma) + rho)) := by
    apply edir_spacelike_of_double_angle_mem_principal
    exact Set.mem_Ioo.mpr ⟨by dsimp [rho]; linarith, by dsimp [rho]; linarith⟩
  exact ⟨h1, h2, h3⟩

theorem rotation_right_normal_form_null
    (beta gamma : ℝ)
    (hsum : beta + gamma = Real.pi / 2) :
    let rho := -(beta + gamma) / 2
    q (edir (0 + rho)) = 0 ∧ q (edir ((beta + gamma) + rho)) = 0 := by
  intro rho
  have hleft : q (edir (0 + rho)) = 0 := by
    rw [edir_q]
    dsimp [rho]
    rw [hsum]
    ring_nf
    convert (by rw [Real.cos_neg, Real.cos_pi_div_two] :
      Real.cos (-(Real.pi / 2)) = 0) using 2
    all_goals ring
  have hright : q (edir ((beta + gamma) + rho)) = 0 := by
    rw [edir_q]
    dsimp [rho]
    rw [hsum]
    ring_nf
    convert Real.cos_pi_div_two using 2
    all_goals ring
  exact ⟨hleft, hright⟩

theorem rotation_acute_normal_form_mixed
    (beta gamma : ℝ)
    (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hbeta_lt : beta < Real.pi / 2) (hgamma_lt : gamma < Real.pi / 2)
    (hlong : Real.pi / 2 < beta + gamma) :
    let rho := -(beta + gamma) / 2
    q (edir (0 + rho)) < 0 ∧
      0 < q (edir (beta + rho)) ∧
        q (edir ((beta + gamma) + rho)) < 0 := by
  intro rho
  have hLhi : beta + gamma < Real.pi + Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hcos : Real.cos (beta + gamma) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hlong hLhi
  have hleft : q (edir (0 + rho)) < 0 := by
    rw [edir_q]
    have harg : 2 * (0 + rho) = -(beta + gamma) := by
      dsimp [rho]
      ring
    rw [harg, Real.cos_neg]
    exact hcos
  have hmid : 0 < q (edir (beta + rho)) := by
    apply edir_spacelike_of_double_angle_mem_principal
    exact Set.mem_Ioo.mpr
      ⟨by dsimp [rho]; nlinarith, by dsimp [rho]; nlinarith⟩
  have hright : q (edir ((beta + gamma) + rho)) < 0 := by
    rw [edir_q]
    have harg : 2 * ((beta + gamma) + rho) = beta + gamma := by
      dsimp [rho]
      ring
    rw [harg]
    exact hcos
  exact ⟨hleft, hmid, hright⟩

theorem acute_rotation_weighted_cos_identity
    (alpha beta gamma rho : ℝ)
    (hsum : alpha + beta + gamma = Real.pi) :
    Real.sin (2 * gamma) * Real.cos (2 * rho) +
        Real.sin (2 * alpha) * Real.cos (2 * (beta + rho)) +
          Real.sin (2 * beta) * Real.cos (2 * (beta + gamma + rho)) = 0 := by
  have halpha : 2 * alpha = 2 * Real.pi - (2 * beta + 2 * gamma) := by
    linarith
  rw [halpha, Real.sin_two_pi_sub]
  rw [show 2 * (beta + rho) = 2 * beta + 2 * rho by ring]
  rw [show 2 * (beta + gamma + rho) = (2 * beta + 2 * gamma) + 2 * rho by ring]
  rw [Real.sin_add (2 * beta) (2 * gamma)]
  rw [Real.cos_add (2 * beta) (2 * rho)]
  rw [Real.cos_add (2 * beta + 2 * gamma) (2 * rho)]
  rw [Real.cos_add (2 * beta) (2 * gamma)]
  rw [Real.sin_add (2 * beta) (2 * gamma)]
  linear_combination
    -Real.sin (2 * gamma) * Real.cos (2 * rho) *
      Real.sin_sq_add_cos_sq (2 * beta)

theorem acute_rotation_not_nonmixed
    (alpha beta gamma rho : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (halpha_lt : alpha < Real.pi / 2)
    (hbeta_lt : beta < Real.pi / 2)
    (hgamma_lt : gamma < Real.pi / 2)
    (hsum : alpha + beta + gamma = Real.pi) :
    ¬ ((0 < q (edir rho) ∧ 0 < q (edir (beta + rho)) ∧
          0 < q (edir (beta + gamma + rho))) ∨
        (q (edir rho) < 0 ∧ q (edir (beta + rho)) < 0 ∧
          q (edir (beta + gamma + rho)) < 0)) := by
  have hsin_alpha : 0 < Real.sin (2 * alpha) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have hsin_beta : 0 < Real.sin (2 * beta) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have hsin_gamma : 0 < Real.sin (2 * gamma) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have hidentity := acute_rotation_weighted_cos_identity alpha beta gamma rho hsum
  intro hsame
  rcases hsame with hspace | htime
  · have h0 := (edir_spacelike_iff rho).1 hspace.1
    have h1 := (edir_spacelike_iff (beta + rho)).1 hspace.2.1
    have h2 := (edir_spacelike_iff (beta + gamma + rho)).1 hspace.2.2
    have ht0 : 0 < Real.sin (2 * gamma) * Real.cos (2 * rho) :=
      mul_pos hsin_gamma h0
    have ht1 : 0 < Real.sin (2 * alpha) * Real.cos (2 * (beta + rho)) :=
      mul_pos hsin_alpha h1
    have ht2 : 0 < Real.sin (2 * beta) * Real.cos (2 * (beta + gamma + rho)) :=
      mul_pos hsin_beta h2
    linarith
  · have h0 := (edir_timelike_iff rho).1 htime.1
    have h1 := (edir_timelike_iff (beta + rho)).1 htime.2.1
    have h2 := (edir_timelike_iff (beta + gamma + rho)).1 htime.2.2
    have ht0 : Real.sin (2 * gamma) * Real.cos (2 * rho) < 0 :=
      mul_neg_of_pos_of_neg hsin_gamma h0
    have ht1 : Real.sin (2 * alpha) * Real.cos (2 * (beta + rho)) < 0 :=
      mul_neg_of_pos_of_neg hsin_alpha h1
    have ht2 : Real.sin (2 * beta) * Real.cos (2 * (beta + gamma + rho)) < 0 :=
      mul_neg_of_pos_of_neg hsin_beta h2
    linarith

def normalFormNonmixed (beta gamma rho : ℝ) : Prop :=
  (0 < q (edir rho) ∧ 0 < q (edir (beta + rho)) ∧
      0 < q (edir (beta + gamma + rho))) ∨
    (q (edir rho) < 0 ∧ q (edir (beta + rho)) < 0 ∧
      q (edir (beta + gamma + rho)) < 0)

def angleTripleObtuse (alpha beta gamma : ℝ) : Prop :=
  Real.pi / 2 < alpha ∨ Real.pi / 2 < beta ∨ Real.pi / 2 < gamma

theorem angleTripleObtuse_alpha_rotation
    (alpha beta gamma : ℝ)
    (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsum : alpha + beta + gamma = Real.pi)
    (halpha : Real.pi / 2 < alpha) :
    ∃ rho, normalFormNonmixed beta gamma rho := by
  refine ⟨-(beta + gamma) / 2, Or.inl ?_⟩
  have hshort : beta + gamma < Real.pi / 2 := by linarith
  simpa [normalFormNonmixed] using
    rotation_obtuse_normal_form_spacelike beta gamma hbeta hgamma hshort

theorem angleTripleObtuse_beta_rotation
    (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsum : alpha + beta + gamma = Real.pi)
    (hbeta : Real.pi / 2 < beta) :
    ∃ rho, normalFormNonmixed beta gamma rho := by
  refine ⟨-(beta + Real.pi) / 2, Or.inl ?_⟩
  have hbeta_lt : beta < Real.pi + Real.pi / 2 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith
  have hcos_beta : Real.cos beta < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hbeta hbeta_lt
  have hsmall : alpha + gamma < Real.pi / 2 := by linarith
  have hdiff : gamma - alpha ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hcos_diff : 0 < Real.cos (gamma - alpha) :=
    Real.cos_pos_of_mem_Ioo hdiff
  constructor
  · rw [edir_q]
    have hphase : 2 * (-(beta + Real.pi) / 2) = -(beta + Real.pi) := by ring
    rw [hphase, Real.cos_neg, Real.cos_add_pi]
    linarith
  constructor
  · rw [edir_q]
    have hphase : 2 * (beta + -(beta + Real.pi) / 2) = beta - Real.pi := by
      ring
    rw [hphase, Real.cos_sub_pi]
    linarith
  · rw [edir_q]
    have hphase :
        2 * (beta + gamma + -(beta + Real.pi) / 2) = gamma - alpha := by
      linarith
    rw [hphase]
    exact hcos_diff

theorem angleTripleObtuse_gamma_rotation
    (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hsum : alpha + beta + gamma = Real.pi)
    (hgamma : Real.pi / 2 < gamma) :
    ∃ rho, normalFormNonmixed beta gamma rho := by
  refine ⟨(alpha - beta) / 2, Or.inl ?_⟩
  have hsmall : alpha + beta < Real.pi / 2 := by linarith
  have hdiff : alpha - beta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hsum_mem : alpha + beta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hcos_diff : 0 < Real.cos (alpha - beta) :=
    Real.cos_pos_of_mem_Ioo hdiff
  have hcos_sum : 0 < Real.cos (alpha + beta) :=
    Real.cos_pos_of_mem_Ioo hsum_mem
  have hgamma_lt : gamma < Real.pi + Real.pi / 2 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith
  have hcos_gamma : Real.cos gamma < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hgamma hgamma_lt
  constructor
  · rw [edir_q]
    have hphase : 2 * ((alpha - beta) / 2) = alpha - beta := by ring
    rw [hphase]
    exact hcos_diff
  constructor
  · rw [edir_q]
    have hphase : 2 * (beta + (alpha - beta) / 2) = alpha + beta := by ring
    rw [hphase]
    exact hcos_sum
  · rw [edir_q]
    have hphase : 2 * (beta + gamma + (alpha - beta) / 2) = Real.pi + gamma := by
      linarith
    rw [hphase, show Real.pi + gamma = gamma + Real.pi by ring,
      Real.cos_add_pi]
    linarith

theorem angleTripleObtuse_rotation_exists
    (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsum : alpha + beta + gamma = Real.pi)
    (hObtuse : angleTripleObtuse alpha beta gamma) :
    ∃ rho, normalFormNonmixed beta gamma rho := by
  rcases hObtuse with h | h | h
  · exact angleTripleObtuse_alpha_rotation alpha beta gamma hbeta hgamma hsum h
  · exact angleTripleObtuse_beta_rotation alpha beta gamma halpha hgamma hsum h
  · exact angleTripleObtuse_gamma_rotation alpha beta gamma halpha hbeta hsum h

theorem q_edir_add_pi_div_two (theta : ℝ) :
    q (edir (theta + Real.pi / 2)) = -q (edir theta) := by
  rw [edir_q, edir_q]
  have hphase : 2 * (theta + Real.pi / 2) = 2 * theta + Real.pi := by ring
  rw [hphase, Real.cos_add_pi]

theorem right_alpha_rotation_not_nonmixed
    (alpha beta gamma rho : ℝ)
    (hsum : alpha + beta + gamma = Real.pi)
    (halpha : alpha = Real.pi / 2) :
    ¬ normalFormNonmixed beta gamma rho := by
  intro h
  rcases h with hspace | htime
  · have hq := q_edir_add_pi_div_two rho
    have hphase : beta + gamma + rho = rho + Real.pi / 2 := by linarith
    rw [← hphase] at hq
    linarith
  · have hq := q_edir_add_pi_div_two rho
    have hphase : beta + gamma + rho = rho + Real.pi / 2 := by linarith
    rw [← hphase] at hq
    linarith

theorem right_beta_rotation_not_nonmixed
    (beta gamma rho : ℝ) (hbeta : beta = Real.pi / 2) :
    ¬ normalFormNonmixed beta gamma rho := by
  intro h
  rcases h with hspace | htime
  · have hq := q_edir_add_pi_div_two rho
    have hphase : beta + rho = rho + Real.pi / 2 := by linarith
    rw [← hphase] at hq
    linarith
  · have hq := q_edir_add_pi_div_two rho
    have hphase : beta + rho = rho + Real.pi / 2 := by linarith
    rw [← hphase] at hq
    linarith

theorem right_gamma_rotation_not_nonmixed
    (gamma beta rho : ℝ) (hgamma : gamma = Real.pi / 2) :
    ¬ normalFormNonmixed beta gamma rho := by
  intro h
  rcases h with hspace | htime
  · have hq := q_edir_add_pi_div_two (beta + rho)
    have hphase : beta + gamma + rho = (beta + rho) + Real.pi / 2 := by linarith
    rw [← hphase] at hq
    linarith
  · have hq := q_edir_add_pi_div_two (beta + rho)
    have hphase : beta + gamma + rho = (beta + rho) + Real.pi / 2 := by linarith
    rw [← hphase] at hq
    linarith

theorem acute_rotation_not_normalFormNonmixed
    (alpha beta gamma rho : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (halpha_lt : alpha < Real.pi / 2)
    (hbeta_lt : beta < Real.pi / 2)
    (hgamma_lt : gamma < Real.pi / 2)
    (hsum : alpha + beta + gamma = Real.pi) :
    ¬ normalFormNonmixed beta gamma rho := by
  simpa [normalFormNonmixed] using
    acute_rotation_not_nonmixed alpha beta gamma rho halpha hbeta hgamma
      halpha_lt hbeta_lt hgamma_lt hsum

theorem angleTriple_not_obtuse_cases
    (alpha beta gamma : ℝ)
    (hnot : ¬ angleTripleObtuse alpha beta gamma) :
    (alpha < Real.pi / 2 ∧ beta < Real.pi / 2 ∧ gamma < Real.pi / 2) ∨
      alpha = Real.pi / 2 ∨ beta = Real.pi / 2 ∨ gamma = Real.pi / 2 := by
  simp only [angleTripleObtuse, not_or] at hnot
  have halpha_le : alpha ≤ Real.pi / 2 := le_of_not_gt hnot.1
  have hbeta_le : beta ≤ Real.pi / 2 := le_of_not_gt hnot.2.1
  have hgamma_le : gamma ≤ Real.pi / 2 := le_of_not_gt hnot.2.2
  rcases lt_or_eq_of_le halpha_le with halpha_lt | halpha_eq
  · rcases lt_or_eq_of_le hbeta_le with hbeta_lt | hbeta_eq
    · rcases lt_or_eq_of_le hgamma_le with hgamma_lt | hgamma_eq
      · exact Or.inl ⟨halpha_lt, hbeta_lt, hgamma_lt⟩
      · exact Or.inr (Or.inr (Or.inr hgamma_eq))
    · exact Or.inr (Or.inr (Or.inl hbeta_eq))
  · exact Or.inr (Or.inl halpha_eq)

theorem normalFormNonmixed_implies_angleTripleObtuse
    (alpha beta gamma rho : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsum : alpha + beta + gamma = Real.pi)
    (hnonmixed : normalFormNonmixed beta gamma rho) :
    angleTripleObtuse alpha beta gamma := by
  by_contra hnot
  rcases angleTriple_not_obtuse_cases alpha beta gamma hnot with hacute |
      halpha_right | hbeta_right | hgamma_right
  · exact (acute_rotation_not_normalFormNonmixed alpha beta gamma rho
      halpha hbeta hgamma hacute.1 hacute.2.1 hacute.2.2 hsum hnonmixed).elim
  · exact (right_alpha_rotation_not_nonmixed alpha beta gamma rho hsum
      halpha_right hnonmixed).elim
  · exact (right_beta_rotation_not_nonmixed beta gamma rho hbeta_right
      hnonmixed).elim
  · exact (right_gamma_rotation_not_nonmixed gamma beta rho hgamma_right
      hnonmixed).elim

theorem normalForm_rotation_criterion
    (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsum : alpha + beta + gamma = Real.pi) :
    (∃ rho, normalFormNonmixed beta gamma rho) ↔
      angleTripleObtuse alpha beta gamma := by
  constructor
  · rintro ⟨rho, hnonmixed⟩
    exact normalFormNonmixed_implies_angleTripleObtuse alpha beta gamma rho
      halpha hbeta hgamma hsum hnonmixed
  · exact angleTripleObtuse_rotation_exists alpha beta gamma
      halpha hbeta hgamma hsum

theorem right_alpha_has_null_boundary
    (alpha beta gamma : ℝ)
    (hsum : alpha + beta + gamma = Real.pi)
    (halpha : alpha = Real.pi / 2) :
    ∃ rho, q (edir rho) = 0 ∧ q (edir (beta + gamma + rho)) = 0 := by
  refine ⟨-(beta + gamma) / 2, ?_⟩
  have hbg : beta + gamma = Real.pi / 2 := by linarith
  simpa using rotation_right_normal_form_null beta gamma hbg

theorem right_beta_has_null_boundary
    (beta : ℝ) (hbeta : beta = Real.pi / 2) :
    ∃ rho, q (edir rho) = 0 ∧ q (edir (beta + rho)) = 0 := by
  refine ⟨-beta / 2, ?_, ?_⟩
  · rw [edir_q]
    have hphase : 2 * (-beta / 2) = -beta := by ring
    rw [hphase, hbeta, Real.cos_neg, Real.cos_pi_div_two]
  · rw [edir_q]
    have hphase : 2 * (beta + -beta / 2) = beta := by ring
    rw [hphase, hbeta, Real.cos_pi_div_two]

theorem right_gamma_has_null_boundary
    (beta gamma : ℝ) (hgamma : gamma = Real.pi / 2) :
    ∃ rho, q (edir (beta + rho)) = 0 ∧
      q (edir (beta + gamma + rho)) = 0 := by
  refine ⟨-beta - gamma / 2, ?_, ?_⟩
  · rw [edir_q]
    have hphase : 2 * (beta + (-beta - gamma / 2)) = -gamma := by ring
    rw [hphase, hgamma, Real.cos_neg, Real.cos_pi_div_two]
  · rw [edir_q]
    have hphase : 2 * (beta + gamma + (-beta - gamma / 2)) = gamma := by ring
    rw [hphase, hgamma, Real.cos_pi_div_two]

def directionTripleNonmixed (a b c rho : ℝ) : Prop :=
  (0 < q (edir (a + rho)) ∧ 0 < q (edir (b + rho)) ∧
      0 < q (edir (c + rho))) ∨
    (q (edir (a + rho)) < 0 ∧ q (edir (b + rho)) < 0 ∧
      q (edir (c + rho)) < 0)

def orderedDirectionObtuse (a b c : ℝ) : Prop :=
  angleTripleObtuse (Real.pi - (c - a)) (b - a) (c - b)

theorem ordered_direction_rotation_criterion
    (a b c : ℝ)
    (hab : a < b) (hbc : b < c) (hca : c < a + Real.pi) :
    (∃ rho, directionTripleNonmixed a b c rho) ↔
      orderedDirectionObtuse a b c := by
  let alpha := Real.pi - (c - a)
  let beta := b - a
  let gamma := c - b
  have halpha : 0 < alpha := by
    dsimp [alpha]
    linarith
  have hbeta : 0 < beta := by
    dsimp [beta]
    linarith
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    linarith
  have hsum : alpha + beta + gamma = Real.pi := by
    dsimp [alpha, beta, gamma]
    ring
  constructor
  · rintro ⟨rho, hnonmixed⟩
    have hnormal : normalFormNonmixed beta gamma (a + rho) := by
      have hB : beta + (a + rho) = b + rho := by
        dsimp [beta]
        ring
      have hC : beta + gamma + (a + rho) = c + rho := by
        dsimp [beta, gamma]
        ring
      dsimp only [normalFormNonmixed, directionTripleNonmixed]
      rcases hnonmixed with hspace | htime
      · exact Or.inl (by simpa only [hB, hC] using hspace)
      · exact Or.inr (by simpa only [hB, hC] using htime)
    have hObtuse := normalFormNonmixed_implies_angleTripleObtuse
      alpha beta gamma (a + rho) halpha hbeta hgamma hsum hnormal
    simpa [orderedDirectionObtuse, alpha, beta, gamma] using hObtuse
  · intro hObtuse
    have hObtuse' : angleTripleObtuse alpha beta gamma := by
      simpa [orderedDirectionObtuse, alpha, beta, gamma] using hObtuse
    obtain ⟨rho, hnonmixed⟩ :=
      angleTripleObtuse_rotation_exists alpha beta gamma
        halpha hbeta hgamma hsum hObtuse'
    refine ⟨rho - a, ?_⟩
    have hA : a + (rho - a) = rho := by ring
    have hB : b + (rho - a) = beta + rho := by
      dsimp [beta]
      ring
    have hC : c + (rho - a) = beta + gamma + rho := by
      dsimp [beta, gamma]
      ring
    dsimp only [normalFormNonmixed, directionTripleNonmixed] at hnonmixed ⊢
    rcases hnonmixed with hspace | htime
    · exact Or.inl (by simpa only [hA, hB, hC] using hspace)
    · exact Or.inr (by simpa only [hA, hB, hC] using htime)

theorem ordered_direction_acute_no_nonmixed
    (a b c rho : ℝ)
    (hab : a < b) (hbc : b < c) (hca : c < a + Real.pi)
    (halpha_lt : Real.pi - (c - a) < Real.pi / 2)
    (hbeta_lt : b - a < Real.pi / 2)
    (hgamma_lt : c - b < Real.pi / 2) :
    ¬ directionTripleNonmixed a b c rho := by
  let alpha := Real.pi - (c - a)
  let beta := b - a
  let gamma := c - b
  have halpha : 0 < alpha := by
    dsimp [alpha]
    linarith
  have hbeta : 0 < beta := by
    dsimp [beta]
    linarith
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    linarith
  have hsum : alpha + beta + gamma = Real.pi := by
    dsimp [alpha, beta, gamma]
    ring
  have hnormal : ¬ normalFormNonmixed beta gamma (a + rho) :=
    acute_rotation_not_normalFormNonmixed alpha beta gamma (a + rho)
      halpha hbeta hgamma (by simpa [alpha] using halpha_lt)
      (by simpa [beta] using hbeta_lt) (by simpa [gamma] using hgamma_lt) hsum
  intro hnonmixed
  apply hnormal
  have hB : beta + (a + rho) = b + rho := by
    dsimp [beta]
    ring
  have hC : beta + gamma + (a + rho) = c + rho := by
    dsimp [beta, gamma]
    ring
  dsimp only [normalFormNonmixed, directionTripleNonmixed]
  rcases hnonmixed with hspace | htime
  · exact Or.inl (by simpa only [hB, hC] using hspace)
  · exact Or.inr (by simpa only [hB, hC] using htime)

theorem ordered_direction_right_alpha_null_boundary
    (a b c : ℝ) (halpha : Real.pi - (c - a) = Real.pi / 2) :
    ∃ rho, q (edir (a + rho)) = 0 ∧ q (edir (c + rho)) = 0 := by
  let alpha := Real.pi - (c - a)
  let beta := b - a
  let gamma := c - b
  have hsum : alpha + beta + gamma = Real.pi := by
    dsimp [alpha, beta, gamma]
    ring
  obtain ⟨rho, hleft, hright⟩ :=
    right_alpha_has_null_boundary alpha beta gamma hsum (by simpa [alpha] using halpha)
  refine ⟨rho - a, ?_, ?_⟩
  · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hleft
  · simpa [beta, gamma, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hright

theorem ordered_direction_right_beta_null_boundary
    (a b : ℝ) (hbeta : b - a = Real.pi / 2) :
    ∃ rho, q (edir (a + rho)) = 0 ∧ q (edir (b + rho)) = 0 := by
  let beta := b - a
  obtain ⟨rho, hleft, hright⟩ :=
    right_beta_has_null_boundary beta (by simpa [beta] using hbeta)
  refine ⟨rho - a, ?_, ?_⟩
  · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hleft
  · simpa [beta, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hright

theorem ordered_direction_right_gamma_null_boundary
    (a b c : ℝ) (hgamma : c - b = Real.pi / 2) :
    ∃ rho, q (edir (b + rho)) = 0 ∧ q (edir (c + rho)) = 0 := by
  let beta := b - a
  let gamma := c - b
  obtain ⟨rho, hleft, hright⟩ :=
    right_gamma_has_null_boundary beta gamma (by simpa [gamma] using hgamma)
  refine ⟨rho - a, ?_, ?_⟩
  · simpa [beta, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hleft
  · simpa [beta, gamma, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hright

theorem ordered_direction_rotation_classification
    (a b c : ℝ)
    (hab : a < b) (hbc : b < c) (hca : c < a + Real.pi) :
    ((∃ rho, directionTripleNonmixed a b c rho) ↔
      orderedDirectionObtuse a b c) ∧
    (∀ rho, Real.pi - (c - a) < Real.pi / 2 →
      b - a < Real.pi / 2 → c - b < Real.pi / 2 →
      ¬ directionTripleNonmixed a b c rho) ∧
    (Real.pi - (c - a) = Real.pi / 2 →
      ∃ rho, q (edir (a + rho)) = 0 ∧ q (edir (c + rho)) = 0) ∧
    (b - a = Real.pi / 2 →
      ∃ rho, q (edir (a + rho)) = 0 ∧ q (edir (b + rho)) = 0) ∧
    (c - b = Real.pi / 2 →
      ∃ rho, q (edir (b + rho)) = 0 ∧ q (edir (c + rho)) = 0) := by
  refine ⟨ordered_direction_rotation_criterion a b c hab hbc hca, ?_, ?_, ?_, ?_⟩
  · intro rho halpha hbeta hgamma
    exact ordered_direction_acute_no_nonmixed a b c rho hab hbc hca
      halpha hbeta hgamma
  · exact ordered_direction_right_alpha_null_boundary a b c
  · exact ordered_direction_right_beta_null_boundary a b
  · exact ordered_direction_right_gamma_null_boundary a b c

def vectorTripleNonmixed (u v w : Vec) (rho : ℝ) : Prop :=
  (0 < q (euclideanRotateVec rho u) ∧ 0 < q (euclideanRotateVec rho v) ∧
      0 < q (euclideanRotateVec rho w)) ∨
    (q (euclideanRotateVec rho u) < 0 ∧ q (euclideanRotateVec rho v) < 0 ∧
      q (euclideanRotateVec rho w) < 0)

theorem vectorTripleNonmixed_swapAB (u v w : Vec) (rho : ℝ) :
    vectorTripleNonmixed u v w rho ↔ vectorTripleNonmixed v u w rho := by
  constructor
  · rintro (hspace | htime)
    · exact Or.inl ⟨hspace.2.1, hspace.1, hspace.2.2⟩
    · exact Or.inr ⟨htime.2.1, htime.1, htime.2.2⟩
  · rintro (hspace | htime)
    · exact Or.inl ⟨hspace.2.1, hspace.1, hspace.2.2⟩
    · exact Or.inr ⟨htime.2.1, htime.1, htime.2.2⟩

theorem vectorTripleNonmixed_swapBC (u v w : Vec) (rho : ℝ) :
    vectorTripleNonmixed u v w rho ↔ vectorTripleNonmixed u w v rho := by
  constructor
  · rintro (hspace | htime)
    · exact Or.inl ⟨hspace.1, hspace.2.2, hspace.2.1⟩
    · exact Or.inr ⟨htime.1, htime.2.2, htime.2.1⟩
  · rintro (hspace | htime)
    · exact Or.inl ⟨hspace.1, hspace.2.2, hspace.2.1⟩
    · exact Or.inr ⟨htime.1, htime.2.2, htime.2.1⟩

theorem directionTripleNonmixed_iff_vectorTripleNonmixed
    (a b c sA sB sC rho : ℝ)
    (hsA : sA ≠ 0) (hsB : sB ≠ 0) (hsC : sC ≠ 0) :
    directionTripleNonmixed a b c rho ↔
      vectorTripleNonmixed (sA • edir a) (sB • edir b) (sC • edir c) rho := by
  constructor
  · intro h
    rcases h with hspace | htime
    · refine Or.inl ⟨?_, ?_, ?_⟩
      · exact (euclideanRotateVec_smul_edir_spacelike_iff sA a rho hsA).mpr hspace.1
      · exact (euclideanRotateVec_smul_edir_spacelike_iff sB b rho hsB).mpr hspace.2.1
      · exact (euclideanRotateVec_smul_edir_spacelike_iff sC c rho hsC).mpr hspace.2.2
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · exact (euclideanRotateVec_smul_edir_timelike_iff sA a rho hsA).mpr htime.1
      · exact (euclideanRotateVec_smul_edir_timelike_iff sB b rho hsB).mpr htime.2.1
      · exact (euclideanRotateVec_smul_edir_timelike_iff sC c rho hsC).mpr htime.2.2
  · intro h
    rcases h with hspace | htime
    · refine Or.inl ⟨?_, ?_, ?_⟩
      · exact (euclideanRotateVec_smul_edir_spacelike_iff sA a rho hsA).mp hspace.1
      · exact (euclideanRotateVec_smul_edir_spacelike_iff sB b rho hsB).mp hspace.2.1
      · exact (euclideanRotateVec_smul_edir_spacelike_iff sC c rho hsC).mp hspace.2.2
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · exact (euclideanRotateVec_smul_edir_timelike_iff sA a rho hsA).mp htime.1
      · exact (euclideanRotateVec_smul_edir_timelike_iff sB b rho hsB).mp htime.2.1
      · exact (euclideanRotateVec_smul_edir_timelike_iff sC c rho hsC).mp htime.2.2

theorem ordered_vector_rotation_criterion
    (a b c sA sB sC : ℝ)
    (hab : a < b) (hbc : b < c) (hca : c < a + Real.pi)
    (hsA : sA ≠ 0) (hsB : sB ≠ 0) (hsC : sC ≠ 0) :
    (∃ rho, vectorTripleNonmixed (sA • edir a) (sB • edir b) (sC • edir c) rho) ↔
      orderedDirectionObtuse a b c := by
  constructor
  · rintro ⟨rho, hnonmixed⟩
    apply (ordered_direction_rotation_criterion a b c hab hbc hca).mp
    exact ⟨rho, (directionTripleNonmixed_iff_vectorTripleNonmixed
      a b c sA sB sC rho hsA hsB hsC).mpr hnonmixed⟩
  · intro hObtuse
    obtain ⟨rho, hnonmixed⟩ :=
      (ordered_direction_rotation_criterion a b c hab hbc hca).mpr hObtuse
    exact ⟨rho, (directionTripleNonmixed_iff_vectorTripleNonmixed
      a b c sA sB sC rho hsA hsB hsC).mp hnonmixed⟩
end MinkowskiMerge
