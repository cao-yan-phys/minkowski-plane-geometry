import MinkowskiMerge.Form
import Mathlib.Tactic


set_option autoImplicit false

namespace MinkowskiMerge

abbrev PseudoComplex (_kappa : ℝ) := Vec

namespace PseudoComplex

def add {kappa : ℝ} (z w : PseudoComplex kappa) : PseudoComplex kappa :=
  (z.x + w.x, z.t + w.t)

def neg {kappa : ℝ} (z : PseudoComplex kappa) : PseudoComplex kappa :=
  (-z.x, -z.t)

def sub {kappa : ℝ} (z w : PseudoComplex kappa) : PseudoComplex kappa :=
  add z (neg w)

def smul {kappa : ℝ} (r : ℝ) (z : PseudoComplex kappa) : PseudoComplex kappa :=
  (r * z.x, r * z.t)

def mul (kappa : ℝ) (z w : PseudoComplex kappa) : PseudoComplex kappa :=
  (z.x * w.x + kappa * z.t * w.t, z.x * w.t + z.t * w.x)

def conj {kappa : ℝ} (z : PseudoComplex kappa) : PseudoComplex kappa :=
  (z.x, -z.t)

def norm (kappa : ℝ) (z : PseudoComplex kappa) : ℝ :=
  z.x ^ 2 - kappa * z.t ^ 2

def re {kappa : ℝ} (z : PseudoComplex kappa) : ℝ := z.x

def toVec {kappa : ℝ} (z : PseudoComplex kappa) : Vec := z

theorem ext {kappa : ℝ} {z w : PseudoComplex kappa}
    (hx : z.x = w.x) (ht : z.t = w.t) : z = w :=
  Vec.ext hx ht

theorem norm_one_eq_q (z : PseudoComplex 1) : norm 1 z = q z := by
  simp [norm, q_apply]

theorem norm_mul (kappa : ℝ) (z w : PseudoComplex kappa) :
    norm kappa (mul kappa z w) = norm kappa z * norm kappa w := by
  cases z
  cases w
  simp [norm, mul]
  ring

theorem conj_conj {kappa : ℝ} (z : PseudoComplex kappa) : conj (conj z) = z := by
  cases z
  apply ext <;> simp [conj]

theorem conj_mul (kappa : ℝ) (z w : PseudoComplex kappa) :
    conj (mul kappa z w) = mul kappa (conj z) (conj w) := by
  cases z
  cases w
  apply ext
  · simp [conj, mul]
  · simp only [conj, mul, Vec.x_mk, Vec.t_mk]
    ring

theorem norm_conj (kappa : ℝ) (z : PseudoComplex kappa) :
    norm kappa (conj z) = norm kappa z := by
  cases z
  simp [norm, conj]

theorem norm_neg (kappa : ℝ) (z : PseudoComplex kappa) :
    norm kappa (neg z) = norm kappa z := by
  cases z
  simp [norm, neg]

theorem mul_comm (kappa : ℝ) (z w : PseudoComplex kappa) :
    mul kappa z w = mul kappa w z := by
  apply ext <;> simp [mul] <;> ring

theorem mul_assoc (kappa : ℝ) (a b c : PseudoComplex kappa) :
    mul kappa (mul kappa a b) c = mul kappa a (mul kappa b c) := by
  apply ext <;> simp [mul] <;> ring

def one (kappa : ℝ) : PseudoComplex kappa := (1, 0)

theorem mul_conj (kappa : ℝ) (z : PseudoComplex kappa) :
    mul kappa z (conj z) = smul (norm kappa z) (one kappa) := by
  cases z
  apply ext <;> simp [mul, conj, norm, smul, one] <;> ring

end PseudoComplex

noncomputable def pcFootA (delta : ℝ)
    (A B C : PseudoComplex 1) : PseudoComplex 1 :=
  PseudoComplex.smul (1 / 2)
    (PseudoComplex.sub (PseudoComplex.add A (PseudoComplex.add B C))
      (PseudoComplex.smul delta
        (PseudoComplex.mul 1 (PseudoComplex.mul 1 (PseudoComplex.conj A) B) C)))

theorem pc_foot_formula_incidence
    (delta : ℝ) (A B C : PseudoComplex 1)
    (hdelta : delta ^ 2 = 1)
    (hA : PseudoComplex.norm 1 A = delta)
    (hB : PseudoComplex.norm 1 B = delta)
    (hC : PseudoComplex.norm 1 C = delta) :
    br (PseudoComplex.toVec (pcFootA delta A B C) - PseudoComplex.toVec C)
        (PseudoComplex.toVec B - PseudoComplex.toVec C) = 0 ∧
      dot (PseudoComplex.toVec (pcFootA delta A B C) - PseudoComplex.toVec A)
        (PseudoComplex.toVec B - PseudoComplex.toVec C) = 0 := by
  constructor
  · cases A
    rename_i ax au
    cases B
    rename_i bx bu
    cases C
    rename_i cx cu
    simp [pcFootA, PseudoComplex.toVec, PseudoComplex.norm, PseudoComplex.smul,
      PseudoComplex.mul, PseudoComplex.conj, PseudoComplex.sub,
      PseudoComplex.add, PseudoComplex.neg, br_apply] at hA hB hC ⊢
    ring_nf at hA hB hC ⊢
    linear_combination
      (delta / 2 * (-au * cx + ax * cu)) * hB +
        (delta / 2 * (au * bx - ax * bu)) * hC +
        ((au * bx - au * cx - ax * bu + ax * cu) / 2) * hdelta
  · cases A
    rename_i ax au
    cases B
    rename_i bx bu
    cases C
    rename_i cx cu
    simp [pcFootA, PseudoComplex.toVec, PseudoComplex.norm, PseudoComplex.smul,
      PseudoComplex.mul, PseudoComplex.conj, PseudoComplex.sub,
      PseudoComplex.add, PseudoComplex.neg, dot_apply] at hA hB hC ⊢
    ring_nf at hA hB hC ⊢
    linear_combination
      ((au * cu * delta - ax * cx * delta + 1) / 2) * hB +
        ((-au * bu * delta + ax * bx * delta - 1) / 2) * hC +
        ((-au * bu + au * cu + ax * bx - ax * cx) / 2) * hdelta

end MinkowskiMerge
