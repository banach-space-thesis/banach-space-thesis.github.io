import JFA.SeparableRange
import Mathlib.Topology.Sequences

/-! Norm limits of separable-range operators still have separable range.
Consequently these operators form a closed two-sided linear ideal. -/

noncomputable section
open TopologicalSpace Filter Topology
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem hasSeparableRange_of_tendsto (Tn : ℕ → E →L[𝕜] F) (T : E →L[𝕜] F)
    (hn : ∀ n, HasSeparableRange 𝕜 E F (Tn n))
    (hlim : Tendsto Tn atTop (𝓝 T)) : HasSeparableRange 𝕜 E F T := by
  have hsep : IsSeparable (⋃ n, Set.range (Tn n)) := IsSeparable.iUnion hn
  apply hsep.closure.mono
  rintro y ⟨x, rfl⟩
  apply isClosed_closure.mem_of_tendsto
    (((ContinuousLinearMap.apply 𝕜 F x).continuous.tendsto T).comp hlim)
  exact Eventually.of_forall (fun n => subset_closure (Set.mem_iUnion.mpr ⟨n, x, rfl⟩))

theorem isClosed_separableOperators : IsClosed (separableOperators 𝕜 E) := by
  apply isSeqClosed_iff_isClosed.mp
  intro Tn T hn hlim
  exact hasSeparableRange_of_tendsto Tn T hn hlim

theorem separableOperators_closedIdeal : IsClosedOperatorIdeal 𝕜 E (separableOperators 𝕜 E) :=
  ⟨isClosed_separableOperators, hasSeparableRange_zero,
    fun _ hS _ hT => hS.add hT, fun a _ hT => hT.smul a,
    fun A _ hT => ⟨hT.comp_left A, hT.comp_right A⟩⟩

def separableRangeSubmodule : Submodule 𝕜 (E →L[𝕜] F) where
  carrier := {T | HasSeparableRange 𝕜 E F T}
  zero_mem' := hasSeparableRange_zero
  add_mem' := fun hS hT => hS.add hT
  smul_mem' := fun a _ hT => hT.smul a

end JFA
