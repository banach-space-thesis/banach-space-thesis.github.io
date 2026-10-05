import Posets.OrdinalBandCompressionEstimates
import Posets.OrdinalBlockNearDiagonalInverse

/-! Reading compact blocks which approach one endpoint gives an actual c₀
map after subtracting that endpoint. In particular it reads endpoint-zero
outputs without altering any coordinate. -/
noncomputable section
open Set Filter Topology
namespace Posets
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1500000
variable {𝕜 K I : Type*} [RCLike 𝕜] [TopologicalSpace K]
  {L : I → Type*} [∀ i, TopologicalSpace (L i)] [∀ i, CompactSpace (L i)]
local instance ordinalOmegaReadCoordinateGroup (i : I) : NormedAddCommGroup C(L i, 𝕜) := inferInstance
local instance ordinalOmegaReadCoordinateSpace (i : I) : NormedSpace 𝕜 C(L i, 𝕜) := inferInstance
local instance ordinalOmegaReadSumGroup : NormedAddCommGroup (OrdinalBlockFunctionSum 𝕜 L) := inferInstance
local instance ordinalOmegaReadSumSpace : NormedSpace 𝕜 (OrdinalBlockFunctionSum 𝕜 L) := inferInstance

def ordinalOmegaReadCoordinate (q : ∀ i, C(L i, K)) (z : K)
    (f : JLMS.CZero 𝕜 K) (i : I) : C(L i, 𝕜) :=
  f.toContinuousMap.comp (q i) - ContinuousMap.const _ (f z)

@[simp] theorem ordinalOmegaReadCoordinate_apply (q : ∀ i, C(L i, K)) (z : K)
    (f : JLMS.CZero 𝕜 K) (i : I) (x : L i) :
    ordinalOmegaReadCoordinate q z f i x = f (q i x) - f z := rfl

theorem ordinalOmegaReadCoordinate_tendsto (q : ∀ i, C(L i, K)) (z : K)
    (hq : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U)
    (f : JLMS.CZero 𝕜 K) :
    Tendsto (fun i => ‖ordinalOmegaReadCoordinate q z f i‖) cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hf : Tendsto (fun y => ‖f y - f z‖) (𝓝 z) (𝓝 0) := by
    have hf0 : ContinuousAt (fun y : K => ‖f y - f z‖) z :=
      ((f.continuous.continuousAt : ContinuousAt f z).sub continuousAt_const).norm
    simpa only [ContinuousAt, sub_self, norm_zero] using hf0
  have hU : {y | ‖f y - f z‖ < ε / 2} ∈ 𝓝 z :=
    hf.eventually (eventually_lt_nhds (half_pos hε))
  filter_upwards [hq _ hU] with i hi
  have hn : ‖ordinalOmegaReadCoordinate q z f i‖ ≤ ε / 2 :=
    (ContinuousMap.norm_le _ (le_of_lt (half_pos hε))).mpr (fun x => le_of_lt (hi x))
  simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.trans_lt (half_lt_self hε)

def ordinalOmegaRead (q : ∀ i, C(L i, K)) (z : K)
    (hq : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U) :
    JLMS.CZero 𝕜 K →L[𝕜] OrdinalBlockFunctionSum 𝕜 L :=
  LinearMap.mkContinuous
    { toFun := fun f => JLMS.CZeroSum.mk (ordinalOmegaReadCoordinate q z f)
        (ordinalOmegaReadCoordinate_tendsto q z hq f)
      map_add' := by
        intro f g
        apply JLMS.CZeroSum.ext
        intro i
        ext x
        change (f (q i x) + g (q i x)) - (f z + g z) =
          (f (q i x) - f z) + (g (q i x) - g z)
        ring
      map_smul' := by
        intro c f
        apply JLMS.CZeroSum.ext
        intro i
        ext x
        change c * f (q i x) - c * f z = c * (f (q i x) - f z)
        ring }
    2 (by
      intro f
      apply JLMS.CZeroSum.norm_le (by positivity)
      intro i
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro x
      change ‖f (q i x) - f z‖ ≤ 2 * ‖f‖
      have h₁ := JLMS.norm_CZero_apply_le f (q i x)
      have h₂ := JLMS.norm_CZero_apply_le f z
      exact (norm_sub_le _ _).trans (by linarith))

@[simp] theorem ordinalOmegaRead_apply (q : ∀ i, C(L i, K)) (z : K)
    (hq : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U)
    (f : JLMS.CZero 𝕜 K) (i : I) (x : L i) :
    ordinalOmegaRead q z hq f i x = f (q i x) - f z := rfl

theorem ordinalOmegaRead_norm_le (q : ∀ i, C(L i, K)) (z : K)
    (hq : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U) :
    ‖ordinalOmegaRead (𝕜 := 𝕜) q z hq‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  apply JLMS.CZeroSum.norm_le (by positivity)
  intro i
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change ‖f (q i x) - f z‖ ≤ 2 * ‖f‖
  exact (norm_sub_le _ _).trans (by
    have := JLMS.norm_CZero_apply_le f (q i x)
    have := JLMS.norm_CZero_apply_le f z
    linarith)

end Posets




