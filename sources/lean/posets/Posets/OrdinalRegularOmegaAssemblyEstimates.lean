import Posets.OrdinalRegularOmegaAssemblyInsertion

/-! A local diagonal estimate and one bound on the entire cross-block mass
produce a uniform row estimate on the actual assembled c₀ sum. -/
noncomputable section
open Set Filter Topology
namespace Posets
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1500000
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  {L : ℕ → Type*} [∀ i, TopologicalSpace (L i)] [∀ i, CompactSpace (L i)]
local instance ordinalOmegaEstimateCoordinateGroup (i : ℕ) : NormedAddCommGroup C(L i, 𝕜) := inferInstance
local instance ordinalOmegaEstimateCoordinateSpace (i : ℕ) : NormedSpace 𝕜 C(L i, 𝕜) := inferInstance
local instance ordinalOmegaEstimateSumGroup : NormedAddCommGroup (OrdinalBlockFunctionSum 𝕜 L) := inferInstance
local instance ordinalOmegaEstimateSumSpace : NormedSpace 𝕜 (OrdinalBlockFunctionSum 𝕜 L) := inferInstance
local instance ordinalOmegaEstimateDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance ordinalOmegaEstimateDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

variable (M : JLMS.AtomicDualModel 𝕜 K)
  (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
  (H : ℕ → Set K) (hH : Pairwise (fun i j => Disjoint (H i) (H j)))
  (J : ∀ i, C(L i, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
  (hsupp : ∀ i f, Function.support (J i f) ⊆ H i)
  (q : ∀ i, C(L i, K))

theorem ordinalOmega_cross_error {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∀ i x, ‖JLMS.atomicRestriction M (wolfeCrossUnion H i)
      ((JLMS.evaluation (q i x)).comp T)‖ ≤ ε)
    (f : OrdinalBlockFunctionSum 𝕜 L) (i : ℕ) (x : L i) :
    ‖T (wolfeDisjointSynthesis H hH J hsupp f) (q i x) - T (J i (f i)) (q i x)‖ ≤ ε * ‖f‖ := by
  let φ := (JLMS.evaluation (q i x)).comp T
  let g := wolfeDisjointSynthesis H hH J hsupp f - J i (f i)
  have he : φ g = T (wolfeDisjointSynthesis H hH J hsupp f) (q i x) -
      T (J i (f i)) (q i x) := by simp [φ, g]
  rw [← he, ← ordinalBand_atomic_apply_of_support M φ g
    (ordinalOmegaSynthesis_remainder_support H hH J hsupp f i)]
  exact ((JLMS.atomicRestriction M (wolfeCrossUnion H i) φ).le_opNorm g).trans
    (mul_le_mul (hmass i x) (ordinalOmegaSynthesis_remainder_norm H hH J hsupp f i)
      (norm_nonneg g) hε)

theorem ordinalOmega_assembled_row_error
    (hq : ∀ U ∈ cocompact K, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U)
    (a : ∀ i, L i → 𝕜) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hlocal : ∀ i (f : C(L i, 𝕜)) x, ‖T (J i f) (q i x) - a i x * f x‖ ≤ r * ‖f‖)
    (hcross : ∀ i x, ‖JLMS.atomicRestriction M (wolfeCrossUnion H i)
      ((JLMS.evaluation (q i x)).comp T)‖ ≤ s) :
    ∀ i x, ‖(ordinalBlockEvaluation i x).comp
      ((ordinalOmegaEscapeRead q hq).comp (T.comp (wolfeDisjointSynthesis H hH J hsupp))) -
        a i x • ordinalBlockEvaluation i x‖ ≤ r + s := by
  intro i x
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hr hs)
  intro f
  change ‖T (wolfeDisjointSynthesis H hH J hsupp f) (q i x) - a i x * f i x‖ ≤ (r + s) * ‖f‖
  have hc := ordinalOmega_cross_error M T H hH J hsupp q hs hcross f i x
  have hl := (hlocal i (f i) x).trans
    (mul_le_mul_of_nonneg_left (f.norm_apply_le_norm i) hr)
  have he : T (wolfeDisjointSynthesis H hH J hsupp f) (q i x) - a i x * f i x =
      (T (wolfeDisjointSynthesis H hH J hsupp f) (q i x) - T (J i (f i)) (q i x)) +
      (T (J i (f i)) (q i x) - a i x * f i x) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

theorem ordinalOmega_factors_of_local_and_cross_errors
    (hq : ∀ U ∈ cocompact K, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U)
    (a : ∀ i, L i → 𝕜) {d r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hgap : 3 * (r + s) < d) (hdiag : ∀ i x, d ≤ ‖a i x‖)
    (hlocal : ∀ i (f : C(L i, 𝕜)) x, ‖T (J i f) (q i x) - a i x * f x‖ ≤ r * ‖f‖)
    (hcross : ∀ i x, ‖JLMS.atomicRestriction M (wolfeCrossUnion H i)
      ((JLMS.evaluation (q i x)).comp T)‖ ≤ s) :
    ∃ R : JLMS.CZero 𝕜 K →L[𝕜] OrdinalBlockFunctionSum 𝕜 L,
      R.comp (T.comp (wolfeDisjointSynthesis H hH J hsupp)) = ContinuousLinearMap.id 𝕜 _ ∧
      ‖R‖ ≤ 1 / (d - 3 * (r + s)) := by
  obtain ⟨R, hR, hn⟩ := ordinalBlockNearDiagonal_compression_factors T
    (wolfeDisjointSynthesis H hH J hsupp) (ordinalOmegaEscapeRead q hq) a
    (add_nonneg hr hs) hgap hdiag
    (ordinalOmega_assembled_row_error M T H hH J hsupp q hq a hr hs hlocal hcross)
  refine ⟨R, hR, hn.trans ?_⟩
  exact div_le_div_of_nonneg_right (ordinalOmegaEscapeRead_norm_le q hq) (by linarith)

end Posets
