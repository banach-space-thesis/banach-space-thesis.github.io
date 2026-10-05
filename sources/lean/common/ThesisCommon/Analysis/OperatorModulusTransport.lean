import ThesisCommon.Analysis.RieszKantorovich
import ThesisCommon.Analysis.OperatorIsometryTransport
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.Interval.Set.OrderIso

/-! The constructed real operator modulus commutes with lattice isometries.
This is the operator-lattice part of the measure-space coding reduction. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E F E' F' : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
variable [IsOrderedAddMonoid E] [HasSolidNorm E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [Lattice F]
variable [IsOrderedAddMonoid F] [HasSolidNorm F] [CompleteSpace F] [OrderClosedTopology F]
variable [NormedAddCommGroup E'] [NormedSpace ℝ E'] [Lattice E']
variable [IsOrderedAddMonoid E'] [HasSolidNorm E']
variable [NormedAddCommGroup F'] [NormedSpace ℝ F'] [Lattice F']
variable [IsOrderedAddMonoid F'] [HasSolidNorm F'] [CompleteSpace F'] [OrderClosedTopology F']

/-- Conjugation transports the actual modulus, not just its norm.
Order preservation and reflection belong to the given lattice isometries;
no modulus-transport identity is assumed. -/
theorem operatorModulus_operatorTransport
    (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    (hF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    (hE' : ∀ x y : E', 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    (hF' : ∀ x y : F', 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    (a : E ≃ₗᵢ[ℝ] E') (b : F ≃ₗᵢ[ℝ] F')
    (ha : ∀ x y, a x ≤ a y ↔ x ≤ y) (hb : ∀ x y, b x ≤ b y ↔ x ≤ y)
    (T : E →L[ℝ] F) :
    operatorModulus hE' hF' (operatorTransport a b T) =
      operatorTransport a b (operatorModulus hE hF T) := by
  let ao : E ≃o E' := { toEquiv := a.toEquiv, map_rel_iff' := fun {_ _} => ha _ _ }
  let bo : F ≃o F' := { toEquiv := b.toEquiv, map_rel_iff' := fun {_ _} => hb _ _ }
  have hpos (x : E') (hx : 0 ≤ x) :
      operatorModulus hE' hF' (operatorTransport a b T) x =
        operatorTransport a b (operatorModulus hE hF T) x := by
    have hax : 0 ≤ a.symm x := (ha 0 (a.symm x)).mp (by simpa using hx)
    have hi : a '' Icc (-(a.symm x)) (a.symm x) = Icc (-x) x := by
      have hi := ao.image_Icc (-(a.symm x)) (a.symm x)
      change a '' Icc (-(a.symm x)) (a.symm x) =
        Icc (a (-(a.symm x))) (a (a.symm x)) at hi
      simpa only [map_neg, LinearIsometryEquiv.apply_symm_apply] using hi
    have hs : b '' (T '' Icc (-(a.symm x)) (a.symm x)) =
        operatorTransport a b T '' Icc (-x) x := by
      rw [← hi]
      ext z
      constructor
      · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
        exact ⟨a g, ⟨g, hg, rfl⟩, by simp [operatorTransport_apply]⟩
      · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
        exact ⟨T g, ⟨g, hg, rfl⟩, by simp [operatorTransport_apply]⟩
    have hL := (bo.isLUB_image').mpr (operatorModulus_rieszKantorovich hE hF T _ hax)
    change IsLUB (b '' (T '' Icc (-(a.symm x)) (a.symm x)))
      (b (operatorModulus hE hF T (a.symm x))) at hL
    rw [hs] at hL
    exact (operatorModulus_rieszKantorovich hE' hF' (operatorTransport a b T) x hx).unique hL
  ext x
  calc
    operatorModulus hE' hF' (operatorTransport a b T) x =
        operatorModulus hE' hF' (operatorTransport a b T) (x⁺ - x⁻) := by rw [posPart_sub_negPart]
    _ = operatorTransport a b (operatorModulus hE hF T) (x⁺ - x⁻) := by
      rw [map_sub, map_sub, hpos _ (posPart_nonneg x), hpos _ (negPart_nonneg x)]
    _ = operatorTransport a b (operatorModulus hE hF T) x := by rw [posPart_sub_negPart]

end ThesisCommon
