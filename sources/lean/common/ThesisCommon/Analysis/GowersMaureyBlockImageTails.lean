import ThesisCommon.Analysis.GowersMaureyBlockTestWeakNull
import ThesisCommon.Analysis.GowersMaureySchauderBasis
import ThesisCommon.Analysis.GowersMaureyAdjointSpreads
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! Finite-coordinate separation for images of actual block tests.
Functionals on the original subspace extend by Hahn--Banach. Thus every
bounded operator image has vanishing initial projections, and can be
approximated by genuine finite vectors beyond any prescribed cutoff. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem BlockTestSequence.tendsto_subspace_functional_zero {D : ConstructionData 𝕜}
    {Y : Submodule 𝕜 (ShiftSpace D)} (u : BlockTestSequence D Y) (φ : Y →L[𝕜] 𝕜) :
    Tendsto (fun n => φ (u.inSubspace n)) atTop (𝓝 0) := by
  obtain ⟨ψ,hψ,_⟩ := exists_extension_norm_eq Y φ
  have h := u.tendsto_functional_zero ψ
  have he (n : ℕ) : ψ (denseEmbedding D (u.vector n)) = φ (u.inSubspace n) :=
    hψ (u.inSubspace n)
  simpa only [he] using h

theorem BlockTestSequence.tendsto_operator_coordinate_zero {D : ConstructionData 𝕜}
    {Y : Submodule 𝕜 (ShiftSpace D)} (u : BlockTestSequence D Y)
    (T : Y →L[𝕜] ShiftSpace D) (i : ℕ) :
    Tendsto (fun n => completedCoordinate D i (T (u.inSubspace n))) atTop (𝓝 0) :=
  u.tendsto_subspace_functional_zero ((completedCoordinate D i).comp T)

theorem BlockTestSequence.tendsto_initialSum_operator_zero {D : ConstructionData 𝕜}
    {Y : Submodule 𝕜 (ShiftSpace D)} (u : BlockTestSequence D Y)
    (T : Y →L[𝕜] ShiftSpace D) (K : ℕ) :
    Tendsto (fun n => initialSum D K (T (u.inSubspace n))) atTop (𝓝 0) := by
  have h := tendsto_finset_sum (Finset.range K) (fun i _ =>
    (u.tendsto_operator_coordinate_zero T i).smul_const (basisVector D i))
  simpa only [zero_smul, Finset.sum_const_zero, initialSum_apply] using h

theorem exists_finite_after_approx_of_initialSum_small (D : ConstructionData 𝕜)
    (x : ShiftSpace D) (K : ℕ) {ε : ℝ} (hε : ‖initialSum D (K+1) x‖ < ε) :
    ∃ y : C00 𝕜, y ∈ afterCutoff K ∧ ‖x - denseEmbedding D y‖ < ε := by
  obtain ⟨a,ha⟩ := (denseEmbedding_denseRange D).exists_dist_lt x (sub_pos.mpr hε)
  rw [dist_eq_norm] at ha
  let y := spread (K+1) (K+1) (PreSpace.coefficients a)
  have hy : y ∈ afterCutoff K := by
    intro i hi
    have hiK : ¬ K+1 ≤ i := by omega
    simp only [y, spread_apply, if_neg hiK]
  have he : x - denseEmbedding D y = initialSum D (K+1) x +
      completedSpread D (K+1) (K+1) (x - denseEmbedding D a) := by
    rw [initialSum_eq_id_sub_tail]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub,
      completedSpread_denseEmbedding]
    change x - denseEmbedding D y = x - completedSpread D (K+1) (K+1) x +
      (completedSpread D (K+1) (K+1) x - denseEmbedding D y)
    abel
  refine ⟨y,hy,?_⟩
  rw [he]
  exact (norm_add_le _ _).trans_lt ((add_le_add_left
    (completedSpread_norm_le D (K+1) (K+1) (x - denseEmbedding D a)) _).trans_lt
    (by linarith))

theorem BlockTestSequence.eventually_finite_operator_images_after
    {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (u : BlockTestSequence D Y) {ι : Type*} (s : Finset ι)
    (T : ι → Y →L[𝕜] ShiftSpace D) (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ i ∈ s, ∃ y : C00 𝕜,
      y ∈ afterCutoff K ∧ ‖T i (u.inSubspace n) - denseEmbedding D y‖ < ε := by
  apply (eventually_all_finset s).mpr
  intro i hi
  have h := (u.tendsto_initialSum_operator_zero (T i) (K+1)).norm.eventually_lt_const
    (by simpa only [norm_zero] using hε)
  filter_upwards [h] with n hn
  exact exists_finite_after_approx_of_initialSum_small D (T i (u.inSubspace n)) K hn

end ThesisCommon.GowersMaurey
