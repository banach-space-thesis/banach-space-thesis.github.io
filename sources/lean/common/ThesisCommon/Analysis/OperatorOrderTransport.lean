import ThesisCommon.Analysis.OperatorIsometryTransport
import ThesisCommon.Analysis.PositiveOperatorOrder

/-! The actual cone order on bounded operators is preserved by conjugating
with order-preserving and order-reflecting linear isometry equivalences. -/
noncomputable section
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E F E' F' : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E] [IsOrderedAddMonoid E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F] [IsOrderedAddMonoid F]
variable [NormedAddCommGroup E'] [NormedSpace ℝ E'] [Lattice E'] [IsOrderedAddMonoid E']
variable [NormedAddCommGroup F'] [NormedSpace ℝ F'] [PartialOrder F'] [IsOrderedAddMonoid F']
variable (a : E ≃ₗᵢ[ℝ] E') (b : F ≃ₗᵢ[ℝ] F')

def operatorTransportOrderIso
    (ha : ∀ x y, a x ≤ a y ↔ x ≤ y) (hb : ∀ x y, b x ≤ b y ↔ x ≤ y) :
    (E →L[ℝ] F) ≃o (E' →L[ℝ] F') where
  toFun := operatorTransport a b
  invFun := operatorTransport a.symm b.symm
  left_inv := operatorTransport_symm a b
  right_inv := operatorTransport_symm a.symm b.symm
  map_rel_iff' := by
    intro S T
    constructor
    · intro h x hx
      have hax : 0 ≤ a x := by simpa only [map_zero] using (ha 0 x).mpr hx
      have hst := h (a x) hax
      change b (S (a.symm (a x))) ≤ b (T (a.symm (a x))) at hst
      simpa only [LinearIsometryEquiv.symm_apply_apply] using (hb _ _).mp hst
    · intro h x hx
      have hax : 0 ≤ a.symm x := (ha 0 (a.symm x)).mp (by simpa only [map_zero,
        LinearIsometryEquiv.apply_symm_apply] using hx)
      exact (hb _ _).mpr (h _ hax)

omit [Lattice E] [IsOrderedAddMonoid E] [PartialOrder F] [IsOrderedAddMonoid F]
  [Lattice E'] [IsOrderedAddMonoid E'] [PartialOrder F'] [IsOrderedAddMonoid F']

theorem operatorTransport_zero : operatorTransport a b 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  simp [operatorTransport_apply]

theorem operatorTransport_add (S T : E →L[ℝ] F) :
    operatorTransport a b (S + T) = operatorTransport a b S + operatorTransport a b T := by
  apply ContinuousLinearMap.ext
  intro x
  simp [operatorTransport_apply]

theorem operatorTransport_neg (T : E →L[ℝ] F) :
    operatorTransport a b (-T) = -operatorTransport a b T := by
  apply ContinuousLinearMap.ext
  intro x
  simp [operatorTransport_apply]

end ThesisCommon
