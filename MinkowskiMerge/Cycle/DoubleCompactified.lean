import MinkowskiMerge.Cycle.Compactified
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Constructions.SumProd


set_option autoImplicit false

namespace MinkowskiMerge

noncomputable section

open scoped OnePoint
open scoped Topology
open Filter

abbrev ConformalPoint := EReal × EReal

namespace Cycle
namespace DoubleCompactified

def collapseCoord (z : EReal) : OnePoint ℝ :=
  z.rec ∞ (fun x ↦ (x : OnePoint ℝ)) ∞

@[simp] theorem collapseCoord_top : collapseCoord (⊤ : EReal) = ∞ :=
  rfl

@[simp] theorem collapseCoord_bot : collapseCoord (⊥ : EReal) = ∞ :=
  rfl

@[simp] theorem collapseCoord_coe (x : ℝ) :
    collapseCoord (x : EReal) = (x : OnePoint ℝ) :=
  rfl

theorem collapseCoord_eq_infty_iff (z : EReal) :
    collapseCoord z = ∞ ↔ z = ⊤ ∨ z = ⊥ := by
  refine EReal.rec ?_ (fun x ↦ ?_) ?_ z
  · exact iff_of_true rfl (Or.inr rfl)
  · constructor
    · intro h
      exact False.elim (OnePoint.coe_ne_infty x h)
    · rintro (h | h) <;> cases h
  · exact iff_of_true rfl (Or.inl rfl)

def collapse (Z : ConformalPoint) : CompactifiedPoint :=
  (collapseCoord Z.1, collapseCoord Z.2)

def ofPoint (P : Point) : ConformalPoint :=
  ((Cycle.lightconeU P : EReal), (Cycle.lightconeV P : EReal))

@[simp] theorem collapse_ofPoint (P : Point) :
    collapse (ofPoint P) = Cycle.Compactified.ofPoint P := by
  rfl

@[simp] theorem ofPoint_first_isFinite (P : Point) :
    (ofPoint P).1 ≠ ⊤ ∧ (ofPoint P).1 ≠ ⊥ := by
  simp [ofPoint]

@[simp] theorem ofPoint_second_isFinite (P : Point) :
    (ofPoint P).2 ≠ ⊤ ∧ (ofPoint P).2 ≠ ⊥ := by
  simp [ofPoint]

def IsBoundary (Z : ConformalPoint) : Prop :=
  Z.1 = ⊤ ∨ Z.1 = ⊥ ∨ Z.2 = ⊤ ∨ Z.2 = ⊥


def uPlusBoundary : Set ConformalPoint := {Z | Z.1 = ⊤}

def uMinusBoundary : Set ConformalPoint := {Z | Z.1 = ⊥}

def vPlusBoundary : Set ConformalPoint := {Z | Z.2 = ⊤}

def vMinusBoundary : Set ConformalPoint := {Z | Z.2 = ⊥}

def boundarySet : Set ConformalPoint := {Z | IsBoundary Z}

@[simp] theorem mem_uPlusBoundary (Z : ConformalPoint) :
    Z ∈ uPlusBoundary ↔ Z.1 = ⊤ := Iff.rfl

@[simp] theorem mem_uMinusBoundary (Z : ConformalPoint) :
    Z ∈ uMinusBoundary ↔ Z.1 = ⊥ := Iff.rfl

@[simp] theorem mem_vPlusBoundary (Z : ConformalPoint) :
    Z ∈ vPlusBoundary ↔ Z.2 = ⊤ := Iff.rfl

@[simp] theorem mem_vMinusBoundary (Z : ConformalPoint) :
    Z ∈ vMinusBoundary ↔ Z.2 = ⊥ := Iff.rfl

@[simp] theorem mem_boundarySet (Z : ConformalPoint) :
    Z ∈ boundarySet ↔ IsBoundary Z := Iff.rfl

theorem isClosed_uPlusBoundary : IsClosed uPlusBoundary := by
  exact isClosed_singleton.preimage continuous_fst

theorem isClosed_uMinusBoundary : IsClosed uMinusBoundary := by
  exact isClosed_singleton.preimage continuous_fst

theorem isClosed_vPlusBoundary : IsClosed vPlusBoundary := by
  exact isClosed_singleton.preimage continuous_snd

theorem isClosed_vMinusBoundary : IsClosed vMinusBoundary := by
  exact isClosed_singleton.preimage continuous_snd

theorem isClosed_boundarySet : IsClosed boundarySet := by
  change IsClosed {Z : ConformalPoint |
    Z.1 = ⊤ ∨ Z.1 = ⊥ ∨ Z.2 = ⊤ ∨ Z.2 = ⊥}
  exact (isClosed_singleton.preimage continuous_fst).union
    ((isClosed_singleton.preimage continuous_fst).union
      ((isClosed_singleton.preimage continuous_snd).union
        (isClosed_singleton.preimage continuous_snd)))

def affineSet : Set ConformalPoint := {Z | ¬IsBoundary Z}

theorem isOpen_affineSet : IsOpen affineSet := by
  have hset : affineSet = boundarySetᶜ := by
    ext Z
    simp [affineSet, boundarySet]
  rw [hset]
  exact isClosed_boundarySet.isOpen_compl

def IsVPlusEdge (Z : ConformalPoint) : Prop :=
  Z.2 = ⊤ ∧ Z.1 ≠ ⊤ ∧ Z.1 ≠ ⊥

def IsVMinusEdge (Z : ConformalPoint) : Prop :=
  Z.2 = ⊥ ∧ Z.1 ≠ ⊤ ∧ Z.1 ≠ ⊥

def IsUPlusEdge (Z : ConformalPoint) : Prop :=
  Z.1 = ⊤ ∧ Z.2 ≠ ⊤ ∧ Z.2 ≠ ⊥

def IsUMinusEdge (Z : ConformalPoint) : Prop :=
  Z.1 = ⊥ ∧ Z.2 ≠ ⊤ ∧ Z.2 ≠ ⊥

@[simp] theorem isBoundary_ofPoint (P : Point) : ¬IsBoundary (ofPoint P) := by
  simp [IsBoundary, ofPoint]

def uPlusInfinityPoint (u : ℝ) : ConformalPoint :=
  ((u : EReal), ⊤)

def uMinusInfinityPoint (u : ℝ) : ConformalPoint :=
  ((u : EReal), ⊥)

def vPlusInfinityPoint (v : ℝ) : ConformalPoint :=
  (⊤, (v : EReal))

def vMinusInfinityPoint (v : ℝ) : ConformalPoint :=
  (⊥, (v : EReal))


theorem tendsto_uPlusInfinityPoint_atTop (u : ℝ) :
    Tendsto (fun v : ℝ => ((u : EReal), (v : EReal))) atTop
      (𝓝 (uPlusInfinityPoint u)) := by
  exact Filter.Tendsto.prodMk_nhds tendsto_const_nhds EReal.tendsto_coe_atTop

theorem tendsto_uMinusInfinityPoint_atBot (u : ℝ) :
    Tendsto (fun v : ℝ => ((u : EReal), (v : EReal))) atBot
      (𝓝 (uMinusInfinityPoint u)) := by
  exact Filter.Tendsto.prodMk_nhds tendsto_const_nhds EReal.tendsto_coe_atBot

theorem tendsto_vPlusInfinityPoint_atTop (v : ℝ) :
    Tendsto (fun u : ℝ => ((u : EReal), (v : EReal))) atTop
      (𝓝 (vPlusInfinityPoint v)) := by
  exact Filter.Tendsto.prodMk_nhds EReal.tendsto_coe_atTop tendsto_const_nhds

theorem tendsto_vMinusInfinityPoint_atBot (v : ℝ) :
    Tendsto (fun u : ℝ => ((u : EReal), (v : EReal))) atBot
      (𝓝 (vMinusInfinityPoint v)) := by
  exact Filter.Tendsto.prodMk_nhds EReal.tendsto_coe_atBot tendsto_const_nhds

@[simp] theorem isVPlusEdge_uPlusInfinityPoint (u : ℝ) :
    IsVPlusEdge (uPlusInfinityPoint u) := by
  simp [IsVPlusEdge, uPlusInfinityPoint]

@[simp] theorem isVMinusEdge_uMinusInfinityPoint (u : ℝ) :
    IsVMinusEdge (uMinusInfinityPoint u) := by
  simp [IsVMinusEdge, uMinusInfinityPoint]

@[simp] theorem isUPlusEdge_vPlusInfinityPoint (v : ℝ) :
    IsUPlusEdge (vPlusInfinityPoint v) := by
  simp [IsUPlusEdge, vPlusInfinityPoint]

@[simp] theorem isUMinusEdge_vMinusInfinityPoint (v : ℝ) :
    IsUMinusEdge (vMinusInfinityPoint v) := by
  simp [IsUMinusEdge, vMinusInfinityPoint]

@[simp] theorem collapse_uPlusInfinityPoint (u : ℝ) :
    collapse (uPlusInfinityPoint u) = Cycle.Compactified.uInfinityPoint u := by
  rfl

@[simp] theorem collapse_uMinusInfinityPoint (u : ℝ) :
    collapse (uMinusInfinityPoint u) = Cycle.Compactified.uInfinityPoint u := by
  rfl

@[simp] theorem collapse_vPlusInfinityPoint (v : ℝ) :
    collapse (vPlusInfinityPoint v) = Cycle.Compactified.vInfinityPoint v := by
  rfl

@[simp] theorem collapse_vMinusInfinityPoint (v : ℝ) :
    collapse (vMinusInfinityPoint v) = Cycle.Compactified.vInfinityPoint v := by
  rfl

@[simp] theorem isBoundary_collapse (Z : ConformalPoint) :
    Cycle.Compactified.IsBoundary (collapse Z) ↔ IsBoundary Z := by
  constructor
  · intro h
    change collapseCoord Z.1 = ∞ ∨ collapseCoord Z.2 = ∞ at h
    rcases h with h | h
    · exact Or.elim ((collapseCoord_eq_infty_iff Z.1).mp h)
        (fun hu ↦ Or.inl hu) (fun hu ↦ Or.inr (Or.inl hu))
    · exact Or.elim ((collapseCoord_eq_infty_iff Z.2).mp h)
        (fun hv ↦ Or.inr (Or.inr (Or.inl hv)))
        (fun hv ↦ Or.inr (Or.inr (Or.inr hv)))
  · intro h
    change IsBoundary Z at h
    change collapseCoord Z.1 = ∞ ∨ collapseCoord Z.2 = ∞
    rcases h with h | h | h | h
    · exact Or.inl ((collapseCoord_eq_infty_iff Z.1).mpr (Or.inl h))
    · exact Or.inl ((collapseCoord_eq_infty_iff Z.1).mpr (Or.inr h))
    · exact Or.inr ((collapseCoord_eq_infty_iff Z.2).mpr (Or.inl h))
    · exact Or.inr ((collapseCoord_eq_infty_iff Z.2).mpr (Or.inr h))

end DoubleCompactified
end Cycle

end
end MinkowskiMerge
