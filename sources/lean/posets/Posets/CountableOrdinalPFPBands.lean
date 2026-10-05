import Posets.CountableOrdinalPFPRetractions
import Posets.WolfeDiagonalLimits
import Posets.WolfeOperatorRows

/-! Simultaneous small-band selection for the two actual operator rows in
T + S = I. A single finite-band argument handles both rows and preserves the
real-part diagonal dichotomy over either scalar field. Uniform full-height
subfamily selection is a separate combinatorial obligation. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

local instance countableOrdinalPFPBandsDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance countableOrdinalPFPBandsDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

theorem wolfeOperatorRow_norm_le (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (x : K) : ‖WeakDual.toStrongDual (wolfeOperatorRow T x)‖ ≤ ‖T‖ := by
  change ‖(JLMS.evaluation x).comp T‖ ≤ ‖T‖
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by
      simpa using mul_le_mul_of_nonneg_right (JLMS.norm_evaluation_le (𝕜 := 𝕜) x)
        (norm_nonneg T))

theorem wolfeOperatorRows_small_band
    (M : JLMS.AtomicDualModel 𝕜 K) (T S : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (G : ℕ → Set K) (hG : Monotone G) (x : K) {N : ℕ} {ε : ℝ}
    (hN : ‖T‖ + ‖S‖ < N * ε) :
    ∃ n < N, wolfeMass M (wolfeOperatorRow T x) (G (n+1) \ G n) < ε ∧
      wolfeMass M (wolfeOperatorRow S x) (G (n+1) \ G n) < ε := by
  obtain ⟨n, hn, hsmall⟩ := wolfe_exists_small_disjoint_mass_pair M
    (wolfeOperatorRow T x) (wolfeOperatorRow S x) _ (wolfe_nested_bands_disjoint G hG)
    ((add_le_add (wolfeOperatorRow_norm_le T x) (wolfeOperatorRow_norm_le S x)).trans_lt hN)
  refine ⟨n, hn, ?_, ?_⟩
  · exact lt_of_le_of_lt (le_add_of_nonneg_right (wolfeMass_nonneg M _ _)) hsmall
  · exact lt_of_le_of_lt (le_add_of_nonneg_left (wolfeMass_nonneg M _ _)) hsmall

theorem wolfeOperatorRows_diagonal_dichotomy
    (T S : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (hTS : T + S = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 K))
    {G : Set K} (hG : IsClopen G) (hcG : IsCompact G) {x : K} (hx : x ∈ G) :
    (1 / 2 : ℝ) ≤ RCLike.re (wolfeOperatorRow T x (JLMS.clopenIndicator G hG hcG)) ∨
      (1 / 2 : ℝ) ≤ RCLike.re (wolfeOperatorRow S x (JLMS.clopenIndicator G hG hcG)) := by
  have heq : wolfeOperatorRow T x (JLMS.clopenIndicator G hG hcG) +
      wolfeOperatorRow S x (JLMS.clopenIndicator G hG hcG) = 1 := by
    have h := congrArg (fun R : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K =>
      JLMS.evaluation x (R (JLMS.clopenIndicator G hG hcG))) hTS
    simpa [wolfeOperatorRow, hx] using h
  have hre := congrArg RCLike.re heq
  simp only [map_add, RCLike.one_re] at hre
  by_contra h
  push_neg at h
  linarith

theorem ordinalTower_operatorRows_small_band
    (θ : Ordinal.{u}) (A : ℕ → Set Ordinal.{u})
    (hA : ∀ n, IsCompact (A n)) (hmono : Antitone A) (hθ : ∀ n, θ ∈ A n)
    (M : JLMS.AtomicDualModel 𝕜 (Iic θ))
    (T S : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
    (x : Iic θ) {N : ℕ} {ε : ℝ} (hN : ‖T‖ + ‖S‖ < N * ε) :
    ∃ n < N,
      wolfeMass M (wolfeOperatorRow T x)
        (ordinalTowerCell θ (A (n+1)) (ordinalCeiling (A (n+1)) x) \
          ordinalTowerCell θ (A n) (ordinalCeiling (A n) x)) < ε ∧
      wolfeMass M (wolfeOperatorRow S x)
        (ordinalTowerCell θ (A (n+1)) (ordinalCeiling (A (n+1)) x) \
          ordinalTowerCell θ (A n) (ordinalCeiling (A n) x)) < ε :=
  wolfeOperatorRows_small_band M T S _ (ordinalTowerCells_monotone θ A hA hmono hθ x) x hN

end Posets
