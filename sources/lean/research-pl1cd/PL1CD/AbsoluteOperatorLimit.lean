import PL1CD.AbsoluteRefinement
import PL1CD.HaarPartitionExpansion
import PL1CD.StrongOperatorLimits

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators

namespace PL1CD.HaarPartitions
open PL1.Walsh PL1.FiniteCoordinateKernels PL1CD.PositiveHaarOperators PL1CD.L1Order

def convergenceSubmodule (B : HaarL1 →L[ℝ] HaarL1) : Submodule ℝ HaarL1 where
  carrier := {f | ∃ g, Tendsto (fun r => absoluteOperator B (Finset.range r) f) atTop (𝓝 g)}
  zero_mem' := ⟨0, by simpa only [map_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : HaarL1)) atTop (𝓝 0))⟩
  add_mem' := by
    rintro f g ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨u + v, by simpa only [map_add] using hu.add hv⟩
  smul_mem' := by
    rintro c f ⟨u, hu⟩
    exact ⟨c • u, by simpa only [map_smul] using hu.const_smul c⟩

theorem atom_mem_convergenceSubmodule (B : HaarL1 →L[ℝ] HaarL1)
    (k : ℕ) (a : Assignments (Finset.range k)) :
    atom (Finset.range k) a ∈ convergenceSubmodule B := by
  obtain ⟨g, hg⟩ := absoluteOperator_atom_has_limit B k a
  refine ⟨g, (tendsto_add_atTop_iff_nat k).mp ?_⟩
  simpa only [Nat.add_comm] using hg

theorem dense_convergenceSubmodule (B : HaarL1 →L[ℝ] HaarL1) :
    Dense (convergenceSubmodule B : Set HaarL1) := by
  have hs : Submodule.span ℝ (Set.range (scalarCharacterLp ℝ 1)) ≤ convergenceSubmodule B := by
    apply Submodule.span_le.mpr
    rintro _ ⟨F, rfl⟩
    let k := F.sup id + 1
    have hF : F ⊆ Finset.range k := by
      intro j hj
      exact Finset.mem_range.mpr ((Finset.le_sup (f := id) hj).trans_lt (by omega))
    rw [scalarCharacter_atom_sum (Finset.range k) F hF]
    apply Submodule.sum_mem
    intro a _
    exact (convergenceSubmodule B).smul_mem _ (atom_mem_convergenceSubmodule B k a)
  exact (dense_span_scalarCharacterLp ℝ 1 (by norm_num)).mono hs

theorem exists_absoluteOperator_limit (B : HaarL1 →L[ℝ] HaarL1) :
    ∃ Q : HaarL1 →L[ℝ] HaarL1, ‖Q‖ ≤ ‖B‖ ∧ IsPositive Q ∧
      ∀ f, Tendsto (fun r => absoluteOperator B (Finset.range r) f) atTop (𝓝 (Q f)) := by
  obtain ⟨Q, hnorm, hQ⟩ := PL1CD.exists_strongLimit_of_dense
    (fun r => absoluteOperator B (Finset.range r)) ‖B‖ (norm_nonneg B)
    (fun r => norm_absoluteOperator_le B (Finset.range r))
    (convergenceSubmodule B) (dense_convergenceSubmodule B)
    (fun f ⟨g, hg⟩ => hg.cauchySeq)
  refine ⟨Q, hnorm, ?_, hQ⟩
  intro f hf
  exact nonneg_of_tendsto _ _ (fun r => absoluteOperator_positive B _ f hf) (hQ f)

end PL1CD.HaarPartitions
