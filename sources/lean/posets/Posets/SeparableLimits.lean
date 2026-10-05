import Posets.Definitions

/-! Lemma 6.18 uses pointwise norm convergence (the strong operator topology),
not norm convergence of the operator sequence. -/
noncomputable section
open Filter Topology TopologicalSpace
namespace Posets
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- lmm: separable-to-separable, full statement. Completeness is unnecessary. -/
def Lemma_6_18 (Sn : ℕ → E →L[𝕜] F) (S : E →L[𝕜] F) : Prop :=
  (∀ n, HasSeparableRange 𝕜 E F (Sn n)) →
  (∀ x, Tendsto (fun n => Sn n x) atTop (𝓝 (S x))) →
    HasSeparableRange 𝕜 E F S

/-- The paper's proof: the range of S lies in the closure of the countable
union of the separable ranges of Sn. -/
theorem lemma_6_18_proof (Sn : ℕ → E →L[𝕜] F) (S : E →L[𝕜] F) :
    Lemma_6_18 Sn S := by
  intro hsep hlim
  apply (IsSeparable.iUnion hsep).closure.mono
  rintro _ ⟨x, rfl⟩
  apply isClosed_closure.mem_of_tendsto (hlim x)
  exact Eventually.of_forall (fun n => subset_closure (Set.mem_iUnion.mpr ⟨n, x, rfl⟩))

end Posets
