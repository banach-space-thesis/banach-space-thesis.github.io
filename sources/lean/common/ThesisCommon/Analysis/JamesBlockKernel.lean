import ThesisCommon.Analysis.JamesBlockEmbedding
import ThesisCommon.Analysis.JamesStepDecomposition
import ThesisCommon.Analysis.JamesInitialConvergence

/-! The closed range of block synthesis is exactly the kernel of sampling.
Surjectivity follows from concrete initial truncations and their norm convergence. -/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
  (σ : ℕ → ℕ) (hσ : StrictMono σ)

def jamesKernelBlock (x : JamesSequenceSpace 𝕜 p) (hx : ∀ n, x (σ n) = 0) (i : ℕ) :
    JamesIntervalBlock 𝕜 p (σ i) (σ (i + 1)) :=
  ⟨JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) (σ (i + 1)) x -
    JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) (σ i) x, by
    intro k hk
    simp only [JamesSequenceSpace.sub_apply, JamesSequenceSpace.initial_apply]
    rcases hk with hk | hk
    · rw [if_pos (hk.trans (hσ.monotone (by omega))), if_pos hk, sub_self]
    · by_cases he : k = σ (i + 1)
      · subst k
        simp only [hx, ite_self, sub_self]
      · have hlt : σ (i + 1) < k := lt_of_le_of_ne hk (Ne.symm he)
        have hi : σ i < σ (i + 1) := hσ (by omega)
        rw [if_neg (by omega), if_neg (by omega), sub_self]⟩

theorem jamesKernelBlock_sum (x : JamesSequenceSpace 𝕜 p) (hx : ∀ n, x (σ n) = 0)
    (N : ℕ) :
    (∑ i ∈ Finset.range N, (jamesKernelBlock p σ hσ x hx i).val) =
      JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) (σ N) x -
        JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) (σ 0) x := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    change _ + (JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) (σ (N + 1)) x -
      JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) (σ N) x) = _
    abel

theorem james_initial_mem_block_range (hzero : σ 0 = 0)
    (x : JamesSequenceSpace 𝕜 p) (hx : ∀ n, x (σ n) = 0) (N : ℕ) :
    JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) (σ N) x ∈
      Set.range (jamesBlockSynthesis (𝕜 := 𝕜) p hp σ hσ) := by
  have hinit : JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) (σ 0) x = 0 := by
    ext k
    simp only [JamesSequenceSpace.initial_apply, JamesSequenceSpace.zero_apply]
    split_ifs with hk
    · have he : k = σ 0 := by omega
      rw [he, hx]
    · rfl
  refine ⟨∑ i ∈ Finset.range N, lp.single p.val i (jamesKernelBlock p σ hσ x hx i), ?_⟩
  rw [map_sum]
  simp only [jamesBlockSynthesis_single]
  rw [jamesKernelBlock_sum, hinit, sub_zero]

theorem jamesBlockSynthesis_range_eq_ker (hzero : σ 0 = 0) :
    LinearMap.range (jamesBlockSynthesis (𝕜 := 𝕜) p hp σ hσ).toLinearMap =
      LinearMap.ker (jamesSample (𝕜 := 𝕜) p hp σ hσ).toLinearMap := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (jamesSample_mem_ker_iff p hp σ hσ _).mpr
      (jamesBlockSynthesis_endpoint p hp σ hσ y)
  · intro hx
    have hcoords := (jamesSample_mem_ker_iff p hp σ hσ x).mp hx
    exact (jamesBlockSynthesis_range_isClosed (𝕜 := 𝕜) p hp σ hσ).mem_of_tendsto
      ((JamesSequenceSpace.initial_tendsto hp x).comp hσ.tendsto_atTop)
      (Eventually.of_forall (james_initial_mem_block_range p hp σ hσ hzero x hcoords))

def jamesBlockKernelEquiv (hzero : σ 0 = 0) :
    JamesBlockSum (𝕜 := 𝕜) p σ ≃L[𝕜]
      LinearMap.ker (jamesSample (𝕜 := 𝕜) p hp σ hσ).toLinearMap :=
  ((jamesBlockSynthesis (𝕜 := 𝕜) p hp σ hσ).equivRange
    (jamesBlockSynthesis_injective p hp σ hσ)
    (jamesBlockSynthesis_range_isClosed p hp σ hσ)).trans
      (LinearIsometryEquiv.ofEq _ _
        (jamesBlockSynthesis_range_eq_ker (𝕜 := 𝕜) p hp σ hσ hzero)).toContinuousLinearEquiv

/-- A genuine decomposition into James space and the dependent lp-sum of
the finite intervals between the sampling coordinates. -/
def jamesBlockDecomposition (hzero : σ 0 = 0) :
    JamesSequenceSpace 𝕜 p ≃L[𝕜]
      JamesSequenceSpace 𝕜 p × JamesBlockSum (𝕜 := 𝕜) p σ :=
  (jamesStepDecomposition (𝕜 := 𝕜) p hp σ hσ).trans
    ((ContinuousLinearEquiv.refl 𝕜 (JamesSequenceSpace 𝕜 p)).prodCongr
      (jamesBlockKernelEquiv (𝕜 := 𝕜) p hp σ hσ hzero).symm)

end ThesisCommon
