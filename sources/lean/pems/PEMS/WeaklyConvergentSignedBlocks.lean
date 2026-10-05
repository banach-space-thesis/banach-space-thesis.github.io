import ThesisCommon.Analysis.WeaklyConvergentSignedBlocks

/-! Proposition 5.2: normalized signed successive blocks of a weakly
convergent sequence converge in norm to zero. This proves the real and
complex versions directly from weak convergence, using Mazur's theorem.
The common result does not require completeness. -/
noncomputable section
open Filter ThesisCommon
open scoped BigOperators Topology
namespace PEMS

/-- Source Proposition 5.2. The intervals are exactly `(i n, i (n+1)]`,
and `α` is a single scalar sequence shared by all blocks. -/
theorem proposition_5_2 {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {x : ℕ → E}
    (hx : ∃ l : E, Tendsto (fun n => toWeakSpace 𝕜 E (x n)) atTop
      (𝓝 (toWeakSpace 𝕜 E l))) :
    ∃ (i : ℕ → ℕ) (α : ℕ → 𝕜), StrictMono i ∧
      (∀ n, (∑ j ∈ Finset.Ioc (i n) (i (n + 1)), ‖α j‖) = 1) ∧
      Tendsto (fun n => ∑ j ∈ Finset.Ioc (i n) (i (n + 1)), α j • x j)
        atTop (𝓝 0) := by
  letI : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  letI : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower _ _ _
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  obtain ⟨l, hl⟩ := hx
  exact exists_weaklyConvergent_signed_blocks hl

end PEMS
