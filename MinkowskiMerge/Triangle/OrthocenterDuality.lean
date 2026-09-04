import MinkowskiMerge.PseudoComplex


set_option autoImplicit false

namespace MinkowskiMerge
namespace Triangle

def dualOrthocenter (kappa : ℝ)
    (a b c : PseudoComplex kappa) : PseudoComplex kappa :=
  PseudoComplex.neg
    (PseudoComplex.conj (PseudoComplex.mul kappa (PseudoComplex.mul kappa a b) c))

theorem re_eq_zero_of_conj_eq_neg {kappa : ℝ} (z : PseudoComplex kappa)
    (h : PseudoComplex.conj z = PseudoComplex.neg z) :
    PseudoComplex.re z = 0 := by
  cases z
  simp [PseudoComplex.conj, PseudoComplex.neg, PseudoComplex.re] at h ⊢
  linarith

theorem orthocenter_duality_altitude_a
    (kappa : ℝ) (a b c : PseudoComplex kappa)
    (ha : PseudoComplex.norm kappa a = 1) (hb : PseudoComplex.norm kappa b = 1)
    (hc : PseudoComplex.norm kappa c = 1) :
    PseudoComplex.re
      (PseudoComplex.mul kappa (PseudoComplex.sub (dualOrthocenter kappa a b c) a)
        (PseudoComplex.sub b c)) = 0 := by
  cases a
  rename_i ax au
  cases b
  rename_i bx bu
  cases c
  rename_i cx cu
  simp [dualOrthocenter, PseudoComplex.norm, PseudoComplex.mul,
    PseudoComplex.conj, PseudoComplex.sub, PseudoComplex.add,
    PseudoComplex.neg, PseudoComplex.re] at *
  ring_nf at *
  linear_combination
    (-au * cu * kappa - ax * cx) * hb +
      (au * bu * kappa + ax * bx) * hc

theorem orthocenter_duality_altitude_b
    (kappa : ℝ) (a b c : PseudoComplex kappa)
    (ha : PseudoComplex.norm kappa a = 1) (hb : PseudoComplex.norm kappa b = 1)
    (hc : PseudoComplex.norm kappa c = 1) :
    PseudoComplex.re
      (PseudoComplex.mul kappa (PseudoComplex.sub (dualOrthocenter kappa a b c) b)
        (PseudoComplex.sub c a)) = 0 := by
  cases a
  rename_i ax au
  cases b
  rename_i bx bu
  cases c
  rename_i cx cu
  simp [dualOrthocenter, PseudoComplex.norm, PseudoComplex.mul,
    PseudoComplex.conj, PseudoComplex.sub, PseudoComplex.add,
    PseudoComplex.neg, PseudoComplex.re] at *
  ring_nf at *
  linear_combination
    (bu * cu * kappa + bx * cx) * ha +
      (-au * bu * kappa - ax * bx) * hc

theorem orthocenter_duality_altitude_c
    (kappa : ℝ) (a b c : PseudoComplex kappa)
    (ha : PseudoComplex.norm kappa a = 1) (hb : PseudoComplex.norm kappa b = 1)
    (hc : PseudoComplex.norm kappa c = 1) :
    PseudoComplex.re
      (PseudoComplex.mul kappa (PseudoComplex.sub (dualOrthocenter kappa a b c) c)
        (PseudoComplex.sub a b)) = 0 := by
  cases a
  rename_i ax au
  cases b
  rename_i bx bu
  cases c
  rename_i cx cu
  simp [dualOrthocenter, PseudoComplex.norm, PseudoComplex.mul,
    PseudoComplex.conj, PseudoComplex.sub, PseudoComplex.add,
    PseudoComplex.neg, PseudoComplex.re] at *
  ring_nf at *
  linear_combination
    (-bu * cu * kappa - bx * cx) * ha +
      (au * cu * kappa + ax * cx) * hb

theorem orthocenter_duality_on_conic
    (kappa : ℝ) (a b c : PseudoComplex kappa)
    (ha : PseudoComplex.norm kappa a = 1) (hb : PseudoComplex.norm kappa b = 1)
    (hc : PseudoComplex.norm kappa c = 1) :
    PseudoComplex.norm kappa (dualOrthocenter kappa a b c) = 1 := by
  simp [dualOrthocenter, PseudoComplex.norm_neg, PseudoComplex.norm_conj,
    PseudoComplex.norm_mul, ha, hb, hc]

def unitInverse (g : PseudoComplex 1) : PseudoComplex 1 := PseudoComplex.conj g

theorem unitInverse_is_inverse (g : PseudoComplex 1)
    (hg : PseudoComplex.norm 1 g = 1) :
    PseudoComplex.mul 1 g (unitInverse g) = PseudoComplex.one 1 := by
  simpa [unitInverse, hg, PseudoComplex.smul, PseudoComplex.one] using
    PseudoComplex.mul_conj 1 g

def pcCube {kappa : ℝ} (z : PseudoComplex kappa) : PseudoComplex kappa :=
  PseudoComplex.mul kappa (PseudoComplex.mul kappa z z) z

theorem orthocenter_duality_weight_law_exact
    (kappa : ℝ) (g a b c : PseudoComplex kappa) :
    dualOrthocenter kappa
        (PseudoComplex.mul kappa g a) (PseudoComplex.mul kappa g b)
        (PseudoComplex.mul kappa g c) =
    PseudoComplex.mul kappa
      (PseudoComplex.mul kappa
        (PseudoComplex.mul kappa (PseudoComplex.conj g) (PseudoComplex.conj g))
        (PseudoComplex.conj g))
      (dualOrthocenter kappa a b c) := by
  cases g
  cases a
  cases b
  cases c
  apply PseudoComplex.ext <;>
    simp [dualOrthocenter, PseudoComplex.mul, PseudoComplex.conj,
      PseudoComplex.neg] <;> ring

theorem orthocenter_duality_weight_minus_three
    (g a b c : PseudoComplex 1) (_hg : PseudoComplex.norm 1 g = 1) :
    dualOrthocenter 1
        (PseudoComplex.mul 1 g a) (PseudoComplex.mul 1 g b)
        (PseudoComplex.mul 1 g c) =
      PseudoComplex.mul 1 (pcCube (unitInverse g)) (dualOrthocenter 1 a b c) := by
  simpa [unitInverse, pcCube] using
    orthocenter_duality_weight_law_exact 1 g a b c

end Triangle
end MinkowskiMerge
