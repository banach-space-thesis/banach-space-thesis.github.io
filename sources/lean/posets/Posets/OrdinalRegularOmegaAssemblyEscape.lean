import Posets.OrdinalRegularOmegaAssemblyRead

/-! Compact-escaping reading blocks give a contractive map into the actual
c₀ sum. This applies directly on the half-open ambient ordinal interval. -/
noncomputable section
open Set Filter Topology
namespace Posets
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1500000
variable {𝕜 K I : Type*} [RCLike 𝕜] [TopologicalSpace K]
  {L : I → Type*} [∀ i, TopologicalSpace (L i)] [∀ i, CompactSpace (L i)]
local instance ordinalOmegaEscapeCoordinateGroup (i : I) : NormedAddCommGroup C(L i, 𝕜) := inferInstance
local instance ordinalOmegaEscapeCoordinateSpace (i : I) : NormedSpace 𝕜 C(L i, 𝕜) := inferInstance
local instance ordinalOmegaEscapeSumGroup : NormedAddCommGroup (OrdinalBlockFunctionSum 𝕜 L) := inferInstance
local instance ordinalOmegaEscapeSumSpace : NormedSpace 𝕜 (OrdinalBlockFunctionSum 𝕜 L) := inferInstance

theorem ordinalOmegaEscapeRead_tendsto (q : ∀ i, C(L i, K))
    (hq : ∀ U ∈ cocompact K, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U)
    (f : JLMS.CZero 𝕜 K) :
    Tendsto (fun i => ‖f.toContinuousMap.comp (q i)‖) cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hf : Tendsto (fun y : K => ‖f y‖) (cocompact K) (𝓝 0) := by
    simpa only [norm_zero] using f.zero_at_infty'.norm
  have hU : {y | ‖f y‖ < ε / 2} ∈ cocompact K :=
    hf.eventually (eventually_lt_nhds (half_pos hε))
  filter_upwards [hq _ hU] with i hi
  have hn : ‖f.toContinuousMap.comp (q i)‖ ≤ ε / 2 :=
    (ContinuousMap.norm_le _ (le_of_lt (half_pos hε))).mpr (fun x => le_of_lt (hi x))
  simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.trans_lt (half_lt_self hε)

def ordinalOmegaEscapeRead (q : ∀ i, C(L i, K))
    (hq : ∀ U ∈ cocompact K, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U) :
    JLMS.CZero 𝕜 K →L[𝕜] OrdinalBlockFunctionSum 𝕜 L :=
  LinearMap.mkContinuous
    { toFun := fun f => JLMS.CZeroSum.mk (fun i => f.toContinuousMap.comp (q i))
        (ordinalOmegaEscapeRead_tendsto q hq f)
      map_add' := by intro f g; apply JLMS.CZeroSum.ext; intro i; rfl
      map_smul' := by intro c f; apply JLMS.CZeroSum.ext; intro i; rfl }
    1 (by
      intro f
      apply JLMS.CZeroSum.norm_le (by positivity)
      intro i
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro x
      simpa only [one_mul] using JLMS.norm_CZero_apply_le f (q i x))

@[simp] theorem ordinalOmegaEscapeRead_apply (q : ∀ i, C(L i, K))
    (hq : ∀ U ∈ cocompact K, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U)
    (f : JLMS.CZero 𝕜 K) (i : I) (x : L i) :
    ordinalOmegaEscapeRead q hq f i x = f (q i x) := rfl

theorem ordinalOmegaEscapeRead_norm_le (q : ∀ i, C(L i, K))
    (hq : ∀ U ∈ cocompact K, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U) :
    ‖ordinalOmegaEscapeRead (𝕜 := 𝕜) q hq‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  apply JLMS.CZeroSum.norm_le (by positivity)
  intro i
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  simpa only [one_mul] using JLMS.norm_CZero_apply_le f (q i x)

theorem ordinalOmega_escape_of_compact_avoidance (q : ∀ i, C(L i, K))
    (hq : ∀ C : Set K, IsCompact C → ∀ᶠ i in cofinite, ∀ x, q i x ∉ C) :
    ∀ U ∈ cocompact K, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U := by
  intro U hU
  obtain ⟨C, hC, hCU⟩ := mem_cocompact.mp hU
  filter_upwards [hq C hC] with i hi
  exact fun x => hCU (hi x)

end Posets
