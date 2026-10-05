import Posets.ConvergentBandReadback
import Posets.CZeroOffBandSynthesis
import Posets.CZeroOperatorDiagonal
import Posets.WolfePruning

/-! Atomic cross-mass control and a small endpoint row give a genuine
operator-norm estimate for the centered compression on the whole c₀ sum. -/
noncomputable section
namespace Posets
open Set Filter Topology
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  {L : ℕ → Type*} [∀ i, TopologicalSpace (L i)] [∀ i, CompactSpace (L i)]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem norm_sub_cZeroOperatorDiagonal_le_of_erase
    {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (S : JLMS.CZeroSum 𝕜 E →L[𝕜] JLMS.CZeroSum 𝕜 E)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hrow : ∀ i f, ‖S (cZeroSumErase i f) i‖ ≤ ε * ‖f‖) :
    ‖S - cZeroOperatorDiagonal S‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro f
  apply JLMS.CZeroSum.norm_le (mul_nonneg hε (norm_nonneg f))
  intro i
  have he : (S f - cZeroOperatorDiagonal S f) i = S (cZeroSumErase i f) i := by
    change S f i - S (JLMS.CZeroSum.single i (f i)) i =
      S (f - JLMS.CZeroSum.single i (f i)) i
    rw [map_sub]
    rfl
  change ‖(S f - cZeroOperatorDiagonal S f) i‖ ≤ _
  rw [he]
  exact hrow i f

theorem wolfeMass_endpoint_disjoint_tail_small
    (M : JLMS.AtomicDualModel 𝕜 K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K) (z : K)
    (G : ℕ → Set K) (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ g : JLMS.CZero 𝕜 K,
      Function.support g ⊆ ⋃ n, G (n + N) → ‖T g z‖ ≤ η * ‖g‖ := by
  obtain ⟨N, hN⟩ := wolfeMass_disjoint_tail_union_small M (wolfeOperatorRow T z) G hG hη
  exact ⟨N, fun g hg => cZero_operator_apply_le_of_supported_mass M T g hg z hN.le⟩

def centeredBandCompression
    (q : ∀ i, C(L i, K)) (z : K)
    (hq : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U)
    (G : ℕ → Set K) (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (J : ∀ i, C(L i, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
    (hsupp : ∀ i f, Function.support (J i f) ⊆ G i)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K) :
    JLMS.CZeroSum 𝕜 (fun i => C(L i, 𝕜)) →L[𝕜]
      JLMS.CZeroSum 𝕜 (fun i => C(L i, 𝕜)) :=
  (convergentBandReadback q z hq).comp (T.comp (wolfeDisjointSynthesis G hG J hsupp))

@[simp] theorem centeredBandCompression_apply
    (q : ∀ i, C(L i, K)) (z : K)
    (hq : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U)
    (G : ℕ → Set K) (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (J : ∀ i, C(L i, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
    (hsupp : ∀ i f, Function.support (J i f) ⊆ G i)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (f : JLMS.CZeroSum 𝕜 (fun i => C(L i, 𝕜))) (i : ℕ) (x : L i) :
    centeredBandCompression q z hq G hG J hsupp T f i x =
      T (wolfeDisjointSynthesis G hG J hsupp f) (q i x) -
        T (wolfeDisjointSynthesis G hG J hsupp f) z :=
  convergentBandReadback_apply q z hq _ i x

theorem norm_centeredBandCompression_sub_diagonal_le
    (M : JLMS.AtomicDualModel 𝕜 K)
    (q : ∀ i, C(L i, K)) (z : K)
    (hq : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, ∀ x, q i x ∈ U)
    (G : ℕ → Set K) (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (J : ∀ i, C(L i, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
    (hsupp : ∀ i f, Function.support (J i f) ⊆ G i)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hcross : ∀ i x, wolfeMass M (wolfeOperatorRow T (q i x)) (wolfeCrossUnion G i) ≤ ε)
    (hz : ∀ g : JLMS.CZero 𝕜 K, Function.support g ⊆ ⋃ i, G i → ‖T g z‖ ≤ η * ‖g‖) :
    ‖centeredBandCompression q z hq G hG J hsupp T -
      cZeroOperatorDiagonal (centeredBandCompression q z hq G hG J hsupp T)‖ ≤ ε + η := by
  apply norm_sub_cZeroOperatorDiagonal_le_of_erase _ (add_nonneg hε hη)
  intro i f
  apply (ContinuousMap.norm_le _ (mul_nonneg (add_nonneg hε hη) (norm_nonneg f))).mpr
  intro x
  let g := wolfeDisjointSynthesis G hG J hsupp (cZeroSumErase i f)
  have hgs : Function.support g ⊆ wolfeCrossUnion G i :=
    wolfeDisjointSynthesis_erase_support G hG J hsupp i f
  have hgu : Function.support g ⊆ ⋃ j, G j := by
    intro y hy
    obtain ⟨j, _, hj⟩ := (mem_wolfeCrossUnion G i y).mp (hgs hy)
    exact mem_iUnion.mpr ⟨j, hj⟩
  have hgn : ‖g‖ ≤ ‖f‖ := by
    rw [show ‖g‖ = ‖cZeroSumErase i f‖ from wolfeDisjointSynthesis_norm G hG J hsupp _]
    exact ((cZeroSumErase (𝕜 := 𝕜) (E := fun i => C(L i, 𝕜)) i).le_opNorm f).trans
      ((mul_le_mul_of_nonneg_right (norm_cZeroSumErase_le i) (norm_nonneg f)).trans_eq
        (one_mul _))
  rw [centeredBandCompression_apply]
  change ‖T g (q i x) - T g z‖ ≤ _
  calc
    _ ≤ ‖T g (q i x)‖ + ‖T g z‖ := norm_sub_le _ _
    _ ≤ ε * ‖g‖ + η * ‖g‖ := add_le_add
      (cZero_operator_apply_le_of_supported_mass M T g hgs (q i x) (hcross i x)) (hz g hgu)
    _ = (ε + η) * ‖g‖ := (add_mul _ _ _).symm
    _ ≤ (ε + η) * ‖f‖ := mul_le_mul_of_nonneg_left hgn (add_nonneg hε hη)

end Posets
