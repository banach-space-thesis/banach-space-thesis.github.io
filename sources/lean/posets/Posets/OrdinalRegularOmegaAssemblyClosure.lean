import Posets.OrdinalRegularOmegaAssemblyEstimates

/-! Actual factorization on a c₀ sum from ambient selected-leaf estimates.
The moving lower cells are used only on the leaves. Fixed continuous
function estimates are extended to their closure before reading the blocks. -/
noncomputable section
open Set Filter Topology
namespace Posets
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1500000
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  {L : ℕ → Type*} [∀ i, TopologicalSpace (L i)] [∀ i, CompactSpace (L i)]
local instance ordinalOmegaClosureCoordinateGroup (i : ℕ) : NormedAddCommGroup C(L i, 𝕜) := inferInstance
local instance ordinalOmegaClosureCoordinateSpace (i : ℕ) : NormedSpace 𝕜 C(L i, 𝕜) := inferInstance
local instance ordinalOmegaClosureSumGroup : NormedAddCommGroup (OrdinalBlockFunctionSum 𝕜 L) := inferInstance
local instance ordinalOmegaClosureSumSpace : NormedSpace 𝕜 (OrdinalBlockFunctionSum 𝕜 L) := inferInstance
local instance ordinalOmegaClosureDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance ordinalOmegaClosureDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

theorem ordinalOmega_factors_from_ambient_leaf_mass
    (M : JLMS.AtomicDualModel 𝕜 K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (H : ℕ → Set K) (hH : Pairwise (fun i j => Disjoint (H i) (H j)))
    (hHo : ∀ i, IsClopen (H i)) (hHc : ∀ i, IsCompact (H i))
    (J : ∀ i, C(L i, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
    (hsupp : ∀ i f, Function.support (J i f) ⊆ H i)
    (q : ∀ i, C(L i, K))
    (hqescape : ∀ U ∈ cocompact K, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U)
    (S : ℕ → Set K) (hq : ∀ i x, q i x ∈ closure (S i))
    (hread : ∀ i (f : C(L i, 𝕜)) x, J i f (q i x) = f x)
    (V : ℕ → K → Set K) (hVH : ∀ i y, y ∈ S i → V i y ⊆ H i)
    (hV : ∀ i y, y ∈ S i → IsClopen (V i y))
    (hcV : ∀ i y, y ∈ S i → IsCompact (V i y))
    (hconst : ∀ i y, y ∈ S i → ∀ f : C(L i, 𝕜), ∀ z ∈ V i y, J i f z = J i f y)
    {d ε : ℝ} (hε : 0 ≤ ε) (hgap : 10 * ε < d)
    (hd : ∀ i y (hy : y ∈ S i),
      d ≤ ‖T (JLMS.clopenIndicator (V i y) (hV i y hy) (hcV i y hy)) y‖)
    (hmass : ∀ i y, y ∈ S i → ‖JLMS.atomicRestriction M (H i \ V i y)
      ((JLMS.evaluation y).comp T)‖ ≤ ε)
    (hcross : ∀ i x, ‖JLMS.atomicRestriction M (wolfeCrossUnion H i)
      ((JLMS.evaluation (q i x)).comp T)‖ ≤ ε) :
    ∃ R : JLMS.CZero 𝕜 K →L[𝕜] OrdinalBlockFunctionSum 𝕜 L,
      R.comp (T.comp (wolfeDisjointSynthesis H hH J hsupp)) = ContinuousLinearMap.id 𝕜 _ ∧
      ‖R‖ ≤ 1 / (d - 10 * ε) := by
  let a : ℕ → JLMS.CZero 𝕜 K := fun i => T (JLMS.clopenIndicator (H i) (hHo i) (hHc i))
  have ha (i : ℕ) : ∀ y ∈ closure (S i), d - ε ≤ ‖a i y‖ := by
    apply closure_minimal _ (isClosed_le continuous_const (a i).continuous.norm)
    intro y hy
    exact ordinalBand_total_lower_from_cell M ((JLMS.evaluation y).comp T)
      (H i) (hHo i) (hHc i) (V i y) (hV i y hy) (hcV i y hy) (hVH i y hy)
      (hd i y hy) (hmass i y hy)
  have he (i : ℕ) (f : C(L i, 𝕜)) : ∀ y ∈ closure (S i),
      ‖T (J i f) y - a i y * J i f y‖ ≤ 2 * ε * ‖f‖ := by
    apply closure_minimal _ (isClosed_le
      ((T (J i f)).continuous.sub ((a i).continuous.mul (J i f).continuous)).norm continuous_const)
    intro y hy
    apply ordinalBand_supported_function_error M ((JLMS.evaluation y).comp T)
      (H i) (hHo i) (hHc i) (V i y) (hVH i y hy) (J i f) (J i f y)
      (hsupp i f) (hconst i y hy f) hε
    · exact le_of_eq ((J i).norm_map f)
    · exact (JLMS.norm_CZero_apply_le (J i f) y).trans (le_of_eq ((J i).norm_map f))
    · exact hmass i y hy
  obtain ⟨R, hR, hn⟩ := ordinalOmega_factors_of_local_and_cross_errors M T H hH J hsupp q
    hqescape (fun i x => a i (q i x)) (show 0 ≤ 2 * ε by positivity) hε
    (d := d - ε) (show 3 * (2 * ε + ε) < d - ε by linarith)
    (fun i x => ha i (q i x) (hq i x))
    (fun i f x => by simpa only [hread i f x] using he i f (q i x) (hq i x)) hcross
  refine ⟨R, hR, ?_⟩
  have hid : d - ε - 3 * (2 * ε + ε) = d - 10 * ε := by ring
  simpa only [hid] using hn

end Posets
