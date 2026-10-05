import Posets.CZeroSupportedRestriction
import Posets.WolfeDisjointSynthesis
import Posets.WolfeRankedCrossMassSets
import JLMS.CZeroSumFinite

/-! Erasing a block and synthesizing all other disjoint blocks gives an
actual contraction into the supported off-band subspace. -/
noncomputable section
namespace Posets
open Set Topology TopologicalSpace
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

def cZeroSumErase (i : ℕ) : JLMS.CZeroSum 𝕜 E →L[𝕜] JLMS.CZeroSum 𝕜 E :=
  ContinuousLinearMap.id 𝕜 _ - (JLMS.CZeroSum.singleIsometry i).toContinuousLinearMap.comp
    (JLMS.CZeroSum.evalCLM i)

@[simp] theorem cZeroSumErase_apply_self (i : ℕ) (f : JLMS.CZeroSum 𝕜 E) :
    cZeroSumErase i f i = 0 := by
  change f i - JLMS.CZeroSum.single i (f i) i = 0
  rw [JLMS.CZeroSum.single_apply_self, sub_self]

theorem cZeroSumErase_apply_ne (i j : ℕ) (hji : j ≠ i) (f : JLMS.CZeroSum 𝕜 E) :
    cZeroSumErase i f j = f j := by
  change f j - JLMS.CZeroSum.single i (f i) j = f j
  rw [JLMS.CZeroSum.single_apply_ne i (f i) hji, sub_zero]

theorem norm_cZeroSumErase_le (i : ℕ) : ‖cZeroSumErase (𝕜 := 𝕜) (E := E) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply JLMS.CZeroSum.norm_le (norm_nonneg f)
  intro j
  by_cases h : j = i
  · subst j
    rw [cZeroSumErase_apply_self, norm_zero]
    exact norm_nonneg _
  · rw [cZeroSumErase_apply_ne i j h]
    exact f.norm_apply_le_norm j

variable (G : ℕ → Set K) (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
  (J : ∀ i, E i →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
  (hsupp : ∀ i f, Function.support (J i f) ⊆ G i)

theorem wolfeDisjointSynthesis_erase_support (i : ℕ) (f : JLMS.CZeroSum 𝕜 E) :
    Function.support (wolfeDisjointSynthesis G hG J hsupp (cZeroSumErase i f)) ⊆
      wolfeCrossUnion G i := by
  intro x hx
  by_contra hn
  have heval := (JLMS.evaluation x).hasSum
    (JLMS.hasSum_cZeroSumSynthesis (fun j => (J j).toContinuousLinearMap)
      (wolfe_disjoint_finite_sum_bound G hG J hsupp) (cZeroSumErase i f))
  change HasSum (fun j => J j (cZeroSumErase i f j) x)
    (wolfeDisjointSynthesis G hG J hsupp (cZeroSumErase i f) x) at heval
  have hz (j : ℕ) : J j (cZeroSumErase i f j) x = 0 := by
    by_cases hji : j = i
    · subst j
      rw [cZeroSumErase_apply_self, map_zero]
      rfl
    · by_contra hne
      exact hn ((mem_wolfeCrossUnion G i x).mpr ⟨j, hji, hsupp j _ hne⟩)
  have hzero : HasSum (fun j => J j (cZeroSumErase i f j) x) 0 := by
    simpa only [hz] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : 𝕜)) 0)
  exact hx (heval.unique hzero)

def cZeroOffBandSynthesis (i : ℕ) :
    JLMS.CZeroSum 𝕜 E →L[𝕜] cZeroSupportedOn (𝕜 := 𝕜) (wolfeCrossUnion G i) :=
  ((wolfeDisjointSynthesis G hG J hsupp).comp (cZeroSumErase i)).codRestrict
    (cZeroSupportedOn (𝕜 := 𝕜) (wolfeCrossUnion G i)) (fun f => by
      intro x hx
      by_contra hne
      exact hx (wolfeDisjointSynthesis_erase_support G hG J hsupp i f hne))

@[simp] theorem cZeroOffBandSynthesis_apply (i : ℕ) (f : JLMS.CZeroSum 𝕜 E) :
    (cZeroOffBandSynthesis G hG J hsupp i f).val =
      wolfeDisjointSynthesis G hG J hsupp (cZeroSumErase i f) := rfl

theorem norm_cZeroOffBandSynthesis_le (i : ℕ) :
    ‖cZeroOffBandSynthesis G hG J hsupp i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖wolfeDisjointSynthesis G hG J hsupp (cZeroSumErase i f)‖ ≤ 1 * ‖f‖
  rw [wolfeDisjointSynthesis_norm]
  exact ((cZeroSumErase (𝕜 := 𝕜) (E := E) i).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (norm_cZeroSumErase_le i) (norm_nonneg f))

theorem norm_offBandCompression_le
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K) (C : Compacts K) (i : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hread : ‖cZeroSupportedRead T C (wolfeCrossUnion G i)‖ ≤ ε) :
    ‖(cZeroSupportedRead T C (wolfeCrossUnion G i)).comp
      (cZeroOffBandSynthesis G hG J hsupp i)‖ ≤ ε := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  simpa only [mul_one] using mul_le_mul hread
    (norm_cZeroOffBandSynthesis_le G hG J hsupp i)
    (ContinuousLinearMap.opNorm_nonneg (cZeroOffBandSynthesis G hG J hsupp i)) hε

end Posets
