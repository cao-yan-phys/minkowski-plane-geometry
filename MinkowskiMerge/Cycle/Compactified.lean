import MinkowskiMerge.Causal
import MinkowskiMerge.Cycle.Matrix
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable section

open scoped Matrix OnePoint

abbrev CompactifiedPoint := OnePoint ℝ × OnePoint ℝ

namespace Cycle
namespace Compactified

def coordVector (z : OnePoint ℝ) : Fin 2 → ℝ :=
  z.elim ![1, 0] fun x ↦ ![x, 1]

@[simp] theorem coordVector_infty : coordVector (∞ : OnePoint ℝ) = ![1, 0] :=
  rfl

@[simp] theorem coordVector_coe (z : ℝ) :
    coordVector (z : OnePoint ℝ) = ![z, 1] :=
  rfl

def matrixEval (M : Cycle.MatrixRep) (Z : CompactifiedPoint) : ℝ :=
  coordVector Z.1 ⬝ᵥ (M *ᵥ coordVector Z.2)

def IsOn (C : Cycle) (Z : CompactifiedPoint) : Prop :=
  matrixEval C.toMatrix Z = 0

def ofPoint (P : Point) : CompactifiedPoint :=
  ((Cycle.lightconeU P : OnePoint ℝ),
    (Cycle.lightconeV P : OnePoint ℝ))

def IsBoundary (Z : CompactifiedPoint) : Prop :=
  Z.1 = ∞ ∨ Z.2 = ∞

@[simp] theorem matrixEval_ofPoint (M : Cycle.MatrixRep) (P : Point) :
    matrixEval M (ofPoint P) = Cycle.matrixEval M P := by
  rfl

@[simp] theorem isOn_ofPoint_iff (C : Cycle) (P : Point) :
    IsOn C (ofPoint P) ↔ P ∈ C := by
  rw [IsOn, matrixEval_ofPoint, Cycle.mem_iff_matrixEval]

@[simp] theorem isBoundary_ofPoint (P : Point) : ¬IsBoundary (ofPoint P) := by
  simp [IsBoundary, ofPoint]

def localGradient (M : Cycle.MatrixRep) (Z : CompactifiedPoint) : Vec :=
  Z.1.elim
    (Z.2.elim
      (M 1 0, M 0 1)
      (fun v ↦ (M 1 0 * v + M 1 1, M 0 0)))
    (fun u ↦ Z.2.elim
      (M 0 0, u * M 0 1 + M 1 1)
      (fun v ↦ (M 0 0 * v + M 0 1, u * M 0 0 + M 1 0)))

def IsFirstOrderContactAt (C D : Cycle) (Z : CompactifiedPoint) : Prop :=
  IsOn C Z ∧ IsOn D Z ∧
    br (localGradient C.toMatrix Z) (localGradient D.toMatrix Z) = 0

def IsRegularAt (C : Cycle) (Z : CompactifiedPoint) : Prop :=
  IsOn C Z ∧ localGradient C.toMatrix Z ≠ 0

def uInfinityPoint (u : ℝ) : CompactifiedPoint :=
  ((u : OnePoint ℝ), ∞)

def vInfinityPoint (v : ℝ) : CompactifiedPoint :=
  (∞, (v : OnePoint ℝ))

@[simp] theorem uInfinityPoint_isBoundary (u : ℝ) :
    IsBoundary (uInfinityPoint u) := by
  simp [IsBoundary, uInfinityPoint]

@[simp] theorem vInfinityPoint_isBoundary (v : ℝ) :
    IsBoundary (vInfinityPoint v) := by
  simp [IsBoundary, vInfinityPoint]

@[simp] theorem localGradient_uInfinityPoint (M : Cycle.MatrixRep) (u : ℝ) :
    localGradient M (uInfinityPoint u) =
      (M 0 0, u * M 0 1 + M 1 1) :=
  rfl

@[simp] theorem localGradient_vInfinityPoint (M : Cycle.MatrixRep) (v : ℝ) :
    localGradient M (vInfinityPoint v) =
      (M 1 0 * v + M 1 1, M 0 0) :=
  rfl

theorem isNull_intervalVec_iff_lightcone_eq (P Q : Point) :
    IsNull (intervalVec P Q) ↔
      Cycle.lightconeU P = Cycle.lightconeU Q ∨
      Cycle.lightconeV P = Cycle.lightconeV Q := by
  simp only [IsNull, intervalVec, vsub_eq_sub, q_apply,
    Cycle.lightconeU, Cycle.lightconeV, Vec.x_sub, Vec.t_sub]
  constructor
  · intro h
    have hfactor :
        ((Q.t - P.t) - (Q.x - P.x)) *
          ((Q.t - P.t) + (Q.x - P.x)) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hu | hv
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (hu | hv)
    · have heq : Q.t - P.t = Q.x - P.x := by
        linarith
      rw [heq]
      ring
    · have heq : Q.t - P.t = -(Q.x - P.x) := by
        linarith
      rw [heq]
      ring

end Compactified
end Cycle

end
end MinkowskiMerge
