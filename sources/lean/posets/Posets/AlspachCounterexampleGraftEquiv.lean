import Posets.AlspachCounterexampleGraftSpine

/-! Explicit bijections between the algebraic disjoint-set presentation of
a graft and its compact topological model. -/

noncomputable section
open scoped OnePoint
namespace Posets
variable {K I : Type*} [TopologicalSpace K]
  (anchor : I → K) (X : I → Type*) [∀ i, TopologicalSpace (X i)]

def alspachGraftEquiv : (K ⊕ (Σ i, X i)) ≃ AlspachGraft anchor X where
  toFun := Sum.elim (alspachGraftBase anchor X) (alspachGraftSpine anchor X)
  invFun p := p.val.2.elim (.inl p.val.1) Sum.inr
  left_inv p := by cases p <;> rfl
  right_inv p := by
    rcases p with ⟨⟨k, z⟩, hp⟩
    cases z with
    | infty => rfl
    | coe z =>
        apply Subtype.ext
        exact Prod.ext (hp z rfl).symm rfl

@[simp] theorem alspachGraftEquiv_inl (k : K) :
    alspachGraftEquiv anchor X (.inl k) = alspachGraftBase anchor X k := rfl

@[simp] theorem alspachGraftEquiv_inr (z : Σ i, X i) :
    alspachGraftEquiv anchor X (.inr z) = alspachGraftSpine anchor X z := rfl

@[simp] theorem alspachGraftEquiv_symm_base (k : K) :
    (alspachGraftEquiv anchor X).symm (alspachGraftBase anchor X k) = .inl k := rfl

@[simp] theorem alspachGraftEquiv_symm_spine (z : Σ i, X i) :
    (alspachGraftEquiv anchor X).symm (alspachGraftSpine anchor X z) = .inr z := rfl

end Posets
