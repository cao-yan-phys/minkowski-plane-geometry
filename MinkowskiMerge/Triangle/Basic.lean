import MinkowskiMerge.Affine
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic


set_option autoImplicit false

namespace MinkowskiMerge

@[ext]
structure Triangle where
  A : Point
  B : Point
  C : Point

namespace Triangle

def vertices (T : Triangle) : Fin 3 → Point := ![T.A, T.B, T.C]

@[simp] theorem vertices_zero (T : Triangle) : T.vertices 0 = T.A := rfl
@[simp] theorem vertices_one (T : Triangle) : T.vertices 1 = T.B := rfl
@[simp] theorem vertices_two (T : Triangle) : T.vertices 2 = T.C := rfl

def Nondegenerate (T : Triangle) : Prop := AffineIndependent ℝ T.vertices

abbrev NondegenerateTriangle := {T : Triangle // T.Nondegenerate}

def toAffineTriangle (T : Triangle) (hT : T.Nondegenerate) :
    Affine.Triangle ℝ Point where
  points := T.vertices
  independent := hT

@[simp] theorem toAffineTriangle_points (T : Triangle) (hT : T.Nondegenerate) :
    (T.toAffineTriangle hT).points = T.vertices := rfl

theorem Nondegenerate.vertices_injective {T : Triangle} (hT : T.Nondegenerate) :
    Function.Injective T.vertices := hT.injective

theorem Nondegenerate.A_ne_B {T : Triangle} (hT : T.Nondegenerate) :
    T.A ≠ T.B := by
  intro hAB
  have h01 : (0 : Fin 3) = 1 := hT.vertices_injective (by simpa using hAB)
  norm_num at h01

theorem Nondegenerate.B_ne_C {T : Triangle} (hT : T.Nondegenerate) :
    T.B ≠ T.C := by
  intro hBC
  have h12 : (1 : Fin 3) = 2 := hT.vertices_injective (by simpa using hBC)
  omega

theorem Nondegenerate.C_ne_A {T : Triangle} (hT : T.Nondegenerate) :
    T.C ≠ T.A := by
  intro hCA
  have h20 : (2 : Fin 3) = 0 := hT.vertices_injective (by simpa using hCA)
  omega

theorem Nondegenerate.pairwise_ne {T : Triangle} (hT : T.Nondegenerate) :
    T.A ≠ T.B ∧ T.B ≠ T.C ∧ T.C ≠ T.A :=
  ⟨hT.A_ne_B, hT.B_ne_C, hT.C_ne_A⟩

end Triangle

end MinkowskiMerge
