import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-! Order intervals in a dense vector sublattice are dense in the matching
intervals of its closure. Clipping the approximating vectors keeps both
the interval bound and membership in the original sublattice. -/
noncomputable section
open Set Topology
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]

theorem mem_closure_interval_inter_sublattice (P : Submodule ℝ E)
    (hinf : ∀ x ∈ P, ∀ y ∈ P, x ⊓ y ∈ P)
    (hsup : ∀ x ∈ P, ∀ y ∈ P, x ⊔ y ∈ P)
    {f g : E} (hf : 0 ≤ f) (hfP : f ∈ P)
    (hg : g ∈ Icc (-f) f) (hgP : g ∈ closure (P : Set E)) :
    g ∈ closure (Icc (-f) f ∩ (P : Set E)) := by
  let clip : E → E := fun x => (x ⊓ f) ⊔ (-f)
  have hcont : Continuous clip := (continuous_id.inf continuous_const).sup continuous_const
  have heq : clip g = g := by
    dsimp [clip]
    rw [inf_eq_left.mpr hg.2, sup_eq_left.mpr hg.1]
  have hcl : clip g ∈ closure (clip '' (P : Set E)) :=
    image_closure_subset_closure_image hcont ⟨g, hgP, rfl⟩
  rw [heq] at hcl
  apply closure_mono _ hcl
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨⟨le_sup_right, sup_le inf_le_right ?_⟩,
    hsup _ (hinf x hx f hfP) _ (P.neg_mem hfP)⟩
  exact (neg_nonpos.mpr hf).trans hf

theorem continuousLinearMap_interval_bound_of_dense_sublattice
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Preorder F] [OrderClosedTopology F]
    (T : E →L[ℝ] F) (P : Submodule ℝ E)
    (hinf : ∀ x ∈ P, ∀ y ∈ P, x ⊓ y ∈ P)
    (hsup : ∀ x ∈ P, ∀ y ∈ P, x ⊔ y ∈ P)
    {f g : E} (hf : 0 ≤ f) (hfP : f ∈ P)
    (hg : g ∈ Icc (-f) f) (hgP : g ∈ closure (P : Set E))
    {b : F} (hbound : ∀ x ∈ Icc (-f) f ∩ (P : Set E), T x ≤ b) : T g ≤ b := by
  have hcl := mem_closure_interval_inter_sublattice P hinf hsup hf hfP hg hgP
  exact closure_minimal (by intro x hx; exact hbound x hx)
    (isClosed_Iic.preimage T.continuous) hcl

end ThesisCommon
