import ThesisCommon.Analysis.LatticeLinearIso

/-! Proposition 3.2, using the paper's literal definition of a bijective
linear lattice homomorphism. Order continuity is expressed for arbitrary
proper filters and therefore includes arbitrary directed nets. -/
noncomputable section
open Set ThesisCommon
namespace PEMS
variable {E F : Type*}
variable [AddCommGroup E] [Module ℝ E] [Lattice E] [IsOrderedAddMonoid E]
variable [AddCommGroup F] [Module ℝ F] [Lattice F] [IsOrderedAddMonoid F]

/-- The source imposes no norm, completeness, or countability hypothesis.
The order-isomorphism structure is a conclusion of the proof, not data. -/
def Proposition_3_2 (Ψ : E →ₗ[ℝ] F) : Prop :=
  IsLatticeLinearHom Ψ → Function.Bijective Ψ →
    (∀ {α : Type*} (f : α → E) (l : Filter α) (x : E),
      OrderConverges f l x → OrderConverges (fun i => Ψ (f i)) l (Ψ x)) ∧
    (∀ x, 0 ≤ x → 0 ≤ Ψ x) ∧
    ∀ x, 0 ≤ x → Ψ '' Icc 0 x = Icc 0 (Ψ x)

theorem proposition_3_2_proof (Ψ : E →ₗ[ℝ] F) : Proposition_3_2 Ψ :=
  latticeLinearIso_orderContinuous_intervalPreserving Ψ

end PEMS
