import Posets.OrdinalBandCompressionEstimates
import Posets.WolfeDisjointSynthesis
import JLMS.CZeroSumFinite

/-! The actual global readback into a dependent c₀ sum. Subtracting the
common limit value makes all coordinates tend to zero; boundedness alone
would not suffice. Disjoint insertions supported away from the limit point
are read back exactly. -/
noncomputable section
namespace Posets
open Set Filter Topology
variable {𝕜 K I : Type*} [RCLike 𝕜] [TopologicalSpace K]
  {L : I → Type*} [∀ i, TopologicalSpace (L i)] [∀ i, CompactSpace (L i)]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

def centeredBandCoordinate (q : ∀ i, C(L i, K)) (z : K) (i : I) :
    JLMS.CZero 𝕜 K →L[𝕜] C(L i, 𝕜) :=
  ordinalBandRead (q i) - (JLMS.evaluation z).smulRight (ContinuousMap.const (L i) (1 : 𝕜))

@[simp] theorem centeredBandCoordinate_apply (q : ∀ i, C(L i, K)) (z : K) (i : I)
    (f : JLMS.CZero 𝕜 K) (x : L i) :
    centeredBandCoordinate q z i f x = f (q i x) - f z := by
  change f (q i x) - f z • (1 : 𝕜) = _
  simp only [smul_eq_mul, mul_one]

theorem centeredBandCoordinate_norm_le (q : ∀ i, C(L i, K)) (z : K) (i : I)
    (f : JLMS.CZero 𝕜 K) : ‖centeredBandCoordinate q z i f‖ ≤ 2 * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg f))).mpr
  intro x
  rw [centeredBandCoordinate_apply]
  exact (norm_sub_le _ _).trans (by
    nlinarith [JLMS.norm_CZero_apply_le f (q i x), JLMS.norm_CZero_apply_le f z])

theorem centeredBandCoordinate_tendsto (q : ∀ i, C(L i, K)) (z : K)
    (hq : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U)
    (f : JLMS.CZero 𝕜 K) :
    Tendsto (fun i => ‖centeredBandCoordinate q z i f‖) cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hu : {y | ‖f y - f z‖ < ε / 2} ∈ 𝓝 z := by
    simpa only [dist_eq_norm] using
      (Metric.tendsto_nhds.mp f.continuous.continuousAt (ε / 2) (half_pos hε))
  filter_upwards [hq _ hu] with i hi
  have hn : ‖centeredBandCoordinate q z i f‖ ≤ ε / 2 := by
    apply (ContinuousMap.norm_le _ (half_pos hε).le).mpr
    intro x
    simpa only [centeredBandCoordinate_apply] using (hi x).le
  simpa only [dist_zero_right, norm_norm] using hn.trans_lt (half_lt_self hε)

def convergentBandReadback (q : ∀ i, C(L i, K)) (z : K)
    (hq : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U) :
    JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZeroSum 𝕜 (fun i => C(L i, 𝕜)) :=
  ({ toFun f := JLMS.CZeroSum.mk (fun i => centeredBandCoordinate q z i f)
       (centeredBandCoordinate_tendsto q z hq f)
     map_add' f g := by
       apply JLMS.CZeroSum.ext
       intro i
       exact (centeredBandCoordinate q z i).map_add f g
     map_smul' a f := by
       apply JLMS.CZeroSum.ext
       intro i
       exact (centeredBandCoordinate q z i).map_smul a f } :
    JLMS.CZero 𝕜 K →ₗ[𝕜] JLMS.CZeroSum 𝕜 (fun i => C(L i, 𝕜))).mkContinuous 2
      (fun f => JLMS.CZeroSum.norm_le (mul_nonneg (by norm_num) (norm_nonneg f))
        (fun i => centeredBandCoordinate_norm_le q z i f))

@[simp] theorem convergentBandReadback_apply (q : ∀ i, C(L i, K)) (z : K)
    (hq : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U)
    (f : JLMS.CZero 𝕜 K) (i : I) (x : L i) :
    convergentBandReadback q z hq f i x = f (q i x) - f z :=
  centeredBandCoordinate_apply q z i f x

theorem norm_convergentBandReadback_le (q : ∀ i, C(L i, K)) (z : K)
    (hq : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U) :
    ‖convergentBandReadback (𝕜 := 𝕜) q z hq‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  exact JLMS.CZeroSum.norm_le (mul_nonneg (by norm_num) (norm_nonneg f))
    (fun i => centeredBandCoordinate_norm_le q z i f)

theorem wolfeDisjointSynthesis_apply_outside
    (G : I → Set K) (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (J : ∀ i, C(L i, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
    (hsupp : ∀ i f, Function.support (J i f) ⊆ G i)
    (f : JLMS.CZeroSum 𝕜 (fun i => C(L i, 𝕜))) (z : K) (hz : ∀ i, z ∉ G i) :
    wolfeDisjointSynthesis G hG J hsupp f z = 0 := by
  have heval := (JLMS.evaluation z).hasSum
    (JLMS.hasSum_cZeroSumSynthesis (fun i => (J i).toContinuousLinearMap)
      (wolfe_disjoint_finite_sum_bound G hG J hsupp) f)
  change HasSum (fun i => J i (f i) z) (wolfeDisjointSynthesis G hG J hsupp f z) at heval
  have hi (i : I) : J i (f i) z = 0 := by
    by_contra hn
    exact hz i (hsupp i (f i) hn)
  apply heval.unique
  simpa only [hi] using (hasSum_zero : HasSum (fun _ : I => (0 : 𝕜)) 0)

theorem convergentBandReadback_comp_synthesis
    (q : ∀ i, C(L i, K)) (z : K)
    (hq : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U)
    (G : I → Set K) (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (J : ∀ i, C(L i, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
    (hsupp : ∀ i f, Function.support (J i f) ⊆ G i)
    (hqG : ∀ i x, q i x ∈ G i) (hz : ∀ i, z ∉ G i)
    (hread : ∀ i f x, J i f (q i x) = f x) :
    (convergentBandReadback (𝕜 := 𝕜) q z hq).comp (wolfeDisjointSynthesis G hG J hsupp) =
      ContinuousLinearMap.id 𝕜 (JLMS.CZeroSum 𝕜 (fun i => C(L i, 𝕜))) := by
  apply ContinuousLinearMap.ext
  intro f
  apply JLMS.CZeroSum.ext
  intro i
  apply ContinuousMap.ext
  intro x
  change convergentBandReadback q z hq (wolfeDisjointSynthesis G hG J hsupp f) i x = f i x
  rw [convergentBandReadback_apply,
    wolfeDisjointSynthesis_apply_mem G hG J hsupp f (hqG i x),
    wolfeDisjointSynthesis_apply_outside G hG J hsupp f z hz, hread, sub_zero]

end Posets
