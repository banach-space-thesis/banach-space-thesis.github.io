import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Nat

/-! Remark 4.7: the natural inclusion of an open subspace need not extend
continuously when both added points at infinity are identified. Take the open
copy of ℕ in its one-point compactification. -/

noncomputable section
open Set Topology
open scoped OnePoint
namespace Posets

/-- An explicit open embedding whose canonical one-point extension is discontinuous. -/
theorem remark_4_7_discontinuous_onePoint_extension :
    IsOpenEmbedding ((↑) : ℕ → OnePoint ℕ) ∧
      ¬ Continuous (OnePoint.map ((↑) : ℕ → OnePoint ℕ)) := by
  refine ⟨OnePoint.isOpenEmbedding_coe, ?_⟩
  intro h
  have hopen : IsOpen ({∞} : Set (OnePoint (OnePoint ℕ))) := by
    apply (OnePoint.isOpen_iff_of_mem (by simp)).mpr
    simpa using (show IsClosed (univ : Set (OnePoint ℕ)) ∧ IsCompact univ from
      ⟨isClosed_univ, isCompact_univ⟩)
  have hpre : (OnePoint.map ((↑) : ℕ → OnePoint ℕ)) ⁻¹'
      ({∞} : Set (OnePoint (OnePoint ℕ))) = {∞} := by
    ext x
    cases x <;> simp
  have hbad : IsOpen ({∞} : Set (OnePoint ℕ)) := hpre ▸ hopen.preimage h
  have hcompact : IsCompact (univ : Set ℕ) := by
    simpa using ((OnePoint.isOpen_iff_of_mem (by simp)).mp hbad).2
  exact Set.infinite_univ hcompact.finite_of_discrete

end Posets
