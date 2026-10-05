import Posets.CZeroCenteredCompression
import Posets.OrdinalBandCoordinateInverse
import JLMS.CZeroSumOperators

/-! Uniform coordinate inverses assemble on the actual c₀ sum. Cross-mass
and the endpoint row bound control the whole compression, and a Neumann
inverse corrects its error on all vectors. -/
noncomputable section
namespace Posets
open Set Filter Topology
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  {L : ℕ → Type*} [∀ i, TopologicalSpace (L i)] [∀ i, CompactSpace (L i)]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000

variable (G : ℕ → Set K) (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
  (J : ∀ i, C(L i, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
  (hsupp : ∀ i f, Function.support (J i f) ⊆ G i)

theorem wolfeDisjointSynthesis_single_coordinate (i : ℕ) (f : C(L i, 𝕜)) :
    wolfeDisjointSynthesis G hG J hsupp (JLMS.CZeroSum.single i f) = J i f := by
  classical
  have h := JLMS.hasSum_cZeroSumSynthesis (fun j => (J j).toContinuousLinearMap)
    (wolfe_disjoint_finite_sum_bound G hG J hsupp) (JLMS.CZeroSum.single i f)
  change HasSum (fun j => J j (JLMS.CZeroSum.single (𝕜 := 𝕜) (E := fun j => C(L j, 𝕜)) i f j))
    (wolfeDisjointSynthesis G hG J hsupp (JLMS.CZeroSum.single i f)) at h
  rw [← h.tsum_eq, tsum_eq_single i, JLMS.CZeroSum.single_apply_self]
  intro j hji
  change J j (JLMS.CZeroSum.single (𝕜 := 𝕜) (E := fun j => C(L j, 𝕜)) i f j) = 0
  rw [JLMS.CZeroSum.single_apply_ne (𝕜 := 𝕜) (E := fun j => C(L j, 𝕜)) i f hji,
    map_zero]

theorem wolfeDisjointSynthesis_support_union
    (f : JLMS.CZeroSum 𝕜 (fun i => C(L i, 𝕜))) :
    Function.support (wolfeDisjointSynthesis G hG J hsupp f) ⊆ ⋃ i, G i := by
  intro z hz
  by_contra hn
  exact hz (wolfeDisjointSynthesis_apply_outside G hG J hsupp f z
    (fun i hi => hn (mem_iUnion.mpr ⟨i, hi⟩)))

theorem norm_ordinalBandCompression_isometry_le
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K) (q : ∀ i, C(L i, K)) (i : ℕ) :
    ‖ordinalBandCompression T (J i).toContinuousLinearMap (q i)‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ T.opNorm_nonneg
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg T.opNorm_nonneg (norm_nonneg f))).mpr
  intro x
  exact (JLMS.norm_CZero_apply_le (T (J i f)) (q i x)).trans
    (by simpa only [LinearIsometry.norm_map] using T.le_opNorm (J i f))

def rawBandDiagonal (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (q : ∀ i, C(L i, K)) :
    JLMS.CZeroSum 𝕜 (fun i => C(L i, 𝕜)) →L[𝕜]
      JLMS.CZeroSum 𝕜 (fun i => C(L i, 𝕜)) :=
  JLMS.CZeroSum.mapCLM (fun i => ordinalBandCompression T (J i).toContinuousLinearMap (q i))
    T.opNorm_nonneg (norm_ordinalBandCompression_isometry_le J T q)

@[simp] theorem rawBandDiagonal_apply
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K) (q : ∀ i, C(L i, K))
    (f : JLMS.CZeroSum 𝕜 (fun i => C(L i, 𝕜))) (i : ℕ) (x : L i) :
    rawBandDiagonal J T q f i x = T (J i (f i)) (q i x) := rfl

theorem norm_centeredBandCompression_sub_rawDiagonal_le
    (M : JLMS.AtomicDualModel 𝕜 K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (q : ∀ i, C(L i, K)) (z : K)
    (hq : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U)
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hcross : ∀ i x, wolfeMass M (wolfeOperatorRow T (q i x)) (wolfeCrossUnion G i) ≤ ε)
    (hz : ∀ g : JLMS.CZero 𝕜 K, Function.support g ⊆ ⋃ i, G i → ‖T g z‖ ≤ η * ‖g‖) :
    ‖centeredBandCompression q z hq G hG J hsupp T - rawBandDiagonal J T q‖ ≤ ε + η := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hε hη)
  intro f
  apply JLMS.CZeroSum.norm_le (mul_nonneg (add_nonneg hε hη) (norm_nonneg f))
  intro i
  apply (ContinuousMap.norm_le _ (mul_nonneg (add_nonneg hε hη) (norm_nonneg f))).mpr
  intro x
  let g := wolfeDisjointSynthesis G hG J hsupp (cZeroSumErase i f)
  have hgs : Function.support g ⊆ wolfeCrossUnion G i :=
    wolfeDisjointSynthesis_erase_support G hG J hsupp i f
  have hgn : ‖g‖ ≤ ‖f‖ := by
    rw [show ‖g‖ = ‖cZeroSumErase i f‖ from wolfeDisjointSynthesis_norm G hG J hsupp _]
    exact ((cZeroSumErase (𝕜 := 𝕜) (E := fun i => C(L i, 𝕜)) i).le_opNorm f).trans
      ((mul_le_mul_of_nonneg_right (norm_cZeroSumErase_le i) (norm_nonneg f)).trans_eq (one_mul _))
  have hg : g = wolfeDisjointSynthesis G hG J hsupp f - J i (f i) := by
    change wolfeDisjointSynthesis G hG J hsupp (f - JLMS.CZeroSum.single i (f i)) = _
    rw [map_sub, wolfeDisjointSynthesis_single_coordinate]
  change ‖centeredBandCompression q z hq G hG J hsupp T f i x -
    rawBandDiagonal J T q f i x‖ ≤ _
  rw [centeredBandCompression_apply, rawBandDiagonal_apply]
  have he : T (wolfeDisjointSynthesis G hG J hsupp f) (q i x) -
      T (wolfeDisjointSynthesis G hG J hsupp f) z - T (J i (f i)) (q i x) =
        T g (q i x) - T (wolfeDisjointSynthesis G hG J hsupp f) z := by
    rw [hg, map_sub]
    simp only [ZeroAtInftyContinuousMap.sub_apply]
    abel
  rw [he]
  have hp := cZero_operator_apply_le_of_supported_mass M T g hgs (q i x) (hcross i x)
  have hez := hz (wolfeDisjointSynthesis G hG J hsupp f)
    (wolfeDisjointSynthesis_support_union G hG J hsupp f)
  rw [wolfeDisjointSynthesis_norm] at hez
  calc
    _ ≤ ‖T g (q i x)‖ + ‖T (wolfeDisjointSynthesis G hG J hsupp f) z‖ := norm_sub_le _ _
    _ ≤ ε * ‖f‖ + η * ‖f‖ := add_le_add
      (hp.trans (mul_le_mul_of_nonneg_left hgn hε)) hez
    _ = (ε+η) * ‖f‖ := (add_mul _ _ _).symm

theorem exists_centered_cZero_factor_of_coordinate_inverses
    (M : JLMS.AtomicDualModel 𝕜 K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (q : ∀ i, C(L i, K)) (z : K)
    (hq : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U)
    (B : ∀ i, C(L i, 𝕜) →L[𝕜] C(L i, 𝕜))
    {γ ε η : ℝ} (hγ : 0 < γ) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hgap : ε + η < γ)
    (hBn : ∀ i, ‖B i‖ ≤ 1 / γ)
    (hB : ∀ i, (B i).comp (ordinalBandCompression T (J i).toContinuousLinearMap (q i)) =
      ContinuousLinearMap.id 𝕜 C(L i, 𝕜))
    (hcross : ∀ i x, wolfeMass M (wolfeOperatorRow T (q i x)) (wolfeCrossUnion G i) ≤ ε)
    (hz : ∀ g : JLMS.CZero 𝕜 K, Function.support g ⊆ ⋃ i, G i → ‖T g z‖ ≤ η * ‖g‖) :
    ∃ R : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZeroSum 𝕜 (fun i => C(L i, 𝕜)),
      R.comp (T.comp (wolfeDisjointSynthesis G hG J hsupp)) = ContinuousLinearMap.id 𝕜 _ ∧
        ‖R‖ ≤ 2 / (γ - (ε + η)) := by
  let D := rawBandDiagonal J T q
  let Dinv := JLMS.CZeroSum.mapCLM B (one_div_pos.mpr hγ).le hBn
  have hDn : ‖Dinv‖ ≤ 1 / γ := JLMS.CZeroSum.norm_mapCLM_le B (one_div_pos.mpr hγ).le hBn
  have hDB : Dinv.comp D = ContinuousLinearMap.id 𝕜 _ := by
    apply ContinuousLinearMap.ext
    intro f
    apply JLMS.CZeroSum.ext
    intro i
    exact congrArg (fun A : C(L i, 𝕜) →L[𝕜] C(L i, 𝕜) => A (f i)) (hB i)
  obtain ⟨V, hV, hVn⟩ := wolfe_exists_left_inverse_of_approximation
    (centeredBandCompression q z hq G hG J hsupp T) D Dinv hγ (add_nonneg hε hη) hgap
    hDn hDB (norm_centeredBandCompression_sub_rawDiagonal_le G hG J hsupp M T q z hq
      hε hη hcross hz)
  refine ⟨V.comp (convergentBandReadback q z hq), ?_, ?_⟩
  · simpa only [centeredBandCompression, ContinuousLinearMap.comp_assoc] using hV
  · calc
      ‖V.comp (convergentBandReadback q z hq)‖ ≤ ‖V‖ * ‖convergentBandReadback (𝕜 := 𝕜) q z hq‖ :=
        V.opNorm_comp_le _
      _ ≤ (1 / (γ - (ε+η))) * 2 := mul_le_mul hVn
        (norm_convergentBandReadback_le q z hq)
        (ContinuousLinearMap.opNorm_nonneg _) (one_div_pos.mpr (sub_pos.mpr hgap)).le
      _ = 2 / (γ - (ε+η)) := by ring

end Posets
