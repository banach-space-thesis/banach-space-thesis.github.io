import ThesisCommon.Analysis.DualLattice
import Mathlib.Order.SupClosed

/-! Dedekind completeness of the continuous real dual. Suprema of directed
order-bounded families are first constructed pointwise on the positive cone;
finite-supremum closure gives suprema of arbitrary order-bounded families. -/
noncomputable section
open Set
open scoped ThesisCommon.PositiveOperatorOrder ThesisCommon.DualLattice
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]

def dualDirectedSupPos (S : Set (E →L[ℝ] ℝ)) (x : E) (_hx : 0 ≤ x) : ℝ :=
  sSup ((fun φ : E →L[ℝ] ℝ => φ x) '' S)

theorem dualDirectedSupPos_isLUB (S : Set (E →L[ℝ] ℝ))
    (hne : S.Nonempty) (hb : BddAbove S) (x : E) (hx : 0 ≤ x) :
    IsLUB ((fun φ : E →L[ℝ] ℝ => φ x) '' S) (dualDirectedSupPos S x hx) := by
  apply isLUB_csSup (hne.image _)
  obtain ⟨R, hR⟩ := hb
  refine ⟨R x, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩
  exact hR hφ x hx

theorem dualDirectedSupPos_add (S : Set (E →L[ℝ] ℝ))
    (hne : S.Nonempty) (hb : BddAbove S) (hd : DirectedOn (· ≤ ·) S)
    (x y : E) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    dualDirectedSupPos S (x + y) (add_nonneg hx hy) =
      dualDirectedSupPos S x hx + dualDirectedSupPos S y hy := by
  have hmx := dualDirectedSupPos_isLUB S hne hb x hx
  have hmy := dualDirectedSupPos_isLUB S hne hb y hy
  have hmxy := dualDirectedSupPos_isLUB S hne hb (x + y) (add_nonneg hx hy)
  apply le_antisymm
  · apply hmxy.2
    rintro _ ⟨φ, hφ, rfl⟩
    dsimp only
    rw [map_add]
    exact add_le_add (hmx.1 ⟨φ, hφ, rfl⟩) (hmy.1 ⟨φ, hφ, rfl⟩)
  · have hinner (ψ : E →L[ℝ] ℝ) (hψ : ψ ∈ S) :
        dualDirectedSupPos S x hx + ψ y ≤
          dualDirectedSupPos S (x + y) (add_nonneg hx hy) := by
      apply le_sub_iff_add_le.mp
      apply hmx.2
      rintro _ ⟨φ, hφ, rfl⟩
      apply le_sub_iff_add_le.mpr
      obtain ⟨θ, hθ, hφθ, hψθ⟩ := hd φ hφ ψ hψ
      calc
        φ x + ψ y ≤ θ x + θ y := add_le_add (hφθ x hx) (hψθ y hy)
        _ = θ (x + y) := (map_add θ x y).symm
        _ ≤ dualDirectedSupPos S (x + y) (add_nonneg hx hy) := hmxy.1 ⟨θ, hθ, rfl⟩
    apply le_sub_iff_add_le'.mp
    apply hmy.2
    rintro _ ⟨ψ, hψ, rfl⟩
    exact le_sub_iff_add_le'.mpr (hinner ψ hψ)

theorem norm_dualDirectedSupPos_le (S : Set (E →L[ℝ] ℝ))
    (φ R : E →L[ℝ] ℝ) (hφ : φ ∈ S) (hR : R ∈ upperBounds S)
    (x : E) (hx : 0 ≤ x) :
    ‖dualDirectedSupPos S x hx‖ ≤ (‖φ‖ + ‖R‖) * ‖x‖ := by
  have hlub := dualDirectedSupPos_isLUB S ⟨φ, hφ⟩ ⟨R, hR⟩ x hx
  have hlo : φ x ≤ dualDirectedSupPos S x hx := hlub.1 ⟨φ, hφ, rfl⟩
  have hhi : dualDirectedSupPos S x hx ≤ R x := by
    apply hlub.2
    rintro _ ⟨ψ, hψ, rfl⟩
    exact hR hψ x hx
  have hφb := φ.le_opNorm x
  have hRb := R.le_opNorm x
  rw [Real.norm_eq_abs] at hφb hRb ⊢
  have hφlo := (abs_le.mp hφb).1
  have hRhi := (abs_le.mp hRb).2
  apply abs_le.mpr
  constructor <;> nlinarith [norm_nonneg φ, norm_nonneg R, norm_nonneg x]

/-- An order-bounded directed family of functionals has a supremum which
is still continuous and real linear. -/
theorem exists_dual_isLUB_of_directed (S : Set (E →L[ℝ] ℝ))
    (hne : S.Nonempty) (hb : BddAbove S) (hd : DirectedOn (· ≤ ·) S) :
    ∃ R : E →L[ℝ] ℝ, IsLUB S R := by
  obtain ⟨φ, hφ⟩ := hne
  obtain ⟨U, hU⟩ := hb
  let P := dualDirectedSupPos S
  have hadd := dualDirectedSupPos_add S ⟨φ, hφ⟩ ⟨U, hU⟩ hd
  have hC : 0 ≤ ‖φ‖ + ‖U‖ := add_nonneg (norm_nonneg φ) (norm_nonneg U)
  have hbound := norm_dualDirectedSupPos_le S φ U hφ hU
  let R := positiveConeExtension P hadd hC hbound
  have hR (x : E) (hx : 0 ≤ x) : R x = dualDirectedSupPos S x hx :=
    positiveConeExtension_apply_of_nonneg P hadd hC hbound x hx
  refine ⟨R, ?_, ?_⟩
  · intro ψ hψ x hx
    rw [hR x hx]
    exact (dualDirectedSupPos_isLUB S ⟨φ, hφ⟩ ⟨U, hU⟩ x hx).1 ⟨ψ, hψ, rfl⟩
  · intro T hT x hx
    rw [hR x hx]
    apply (dualDirectedSupPos_isLUB S ⟨φ, hφ⟩ ⟨U, hU⟩ x hx).2
    rintro _ ⟨ψ, hψ, rfl⟩
    exact hT hψ x hx

/-- Dedekind completeness, with no separability, AL, or completeness
assumption on the original normed lattice. -/
theorem exists_dual_isLUB (S : Set (E →L[ℝ] ℝ))
    (hne : S.Nonempty) (hb : BddAbove S) : ∃ R : E →L[ℝ] ℝ, IsLUB S R := by
  have hne' : (supClosure S).Nonempty := hne.mono subset_supClosure
  have hb' : BddAbove (supClosure S) := by
    change (upperBounds (supClosure S)).Nonempty
    rwa [upperBounds_supClosure]
  have hd : DirectedOn (· ≤ ·) (supClosure S) :=
    directedOn_of_sup_mem (fun {_ _} ha hb => supClosed_supClosure ha hb)
  obtain ⟨R, hR⟩ := exists_dual_isLUB_of_directed (supClosure S) hne' hb' hd
  exact ⟨R, isLUB_supClosure.mp hR⟩

def dualSupSet (S : Set (E →L[ℝ] ℝ)) : E →L[ℝ] ℝ := by
  classical
  exact if h : S.Nonempty ∧ BddAbove S then (exists_dual_isLUB S h.1 h.2).choose else 0

namespace DualLattice
scoped instance supSet : SupSet (E →L[ℝ] ℝ) := ⟨dualSupSet⟩

scoped instance conditionallyCompleteLattice : ConditionallyCompleteLattice (E →L[ℝ] ℝ) :=
  conditionallyCompleteLatticeOfLatticeOfsSup _ (fun S hb hne => by
    change IsLUB S (dualSupSet S)
    rw [dualSupSet, dif_pos ⟨hne, hb⟩]
    exact (exists_dual_isLUB S hne hb).choose_spec)
end DualLattice

end ThesisCommon
