import Posets.WolfePreservationNecessaryQuantileExtension
import Posets.WolfePreservationBlockJointPhaseRows

/-! The finite closed quantile graphs for the actual fixed-phase normalized
kernel. Their union contains exactly the class of good, large diagonal atoms
needed by the already proved weighted section estimate. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [CompactSpace K] [T2Space K] [LinearOrder L] [TopologicalSpace L]
  [CompactSpace L] [T2Space L]

local instance wolfePhaseQuantilesDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 L →L[𝕜] 𝕜) := inferInstance
local instance wolfePhaseQuantilesDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 L →L[𝕜] 𝕜) := inferInstance

def wolfePhaseQuantileRelation (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    (τ κ : ℝ) (hcut : ∀ a : L, IsClopen (Iic a)) (t e : ℝ) : Set (K × L) :=
  wolfeExtendedQuantileRelation (wolfeJointPhaseNormalizedRows N S f τ κ) hcut t e

theorem wolfePhaseQuantileRelation_isClosed (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    (τ : ℝ) {κ : ℝ} (hκ : 0 < κ) (hcut : ∀ a : L, IsClopen (Iic a)) (t e : ℝ) :
    IsClosed (wolfePhaseQuantileRelation N S f τ κ hcut t e) :=
  wolfeExtendedQuantileRelation_isClosed (wolfeJointPhaseGoodRows_isClosed N S f τ κ)
    _ (wolfeJointPhaseNormalizedRows_continuous N S f τ hκ) hcut t e

theorem wolfePhaseQuantileRelation_single (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    (τ κ : ℝ) (hcut : ∀ a : L, IsClopen (Iic a)) (t : ℝ) {e : ℝ} (he : 0 < e)
    (y : K) (x z : L) (hx : (y, x) ∈ wolfePhaseQuantileRelation N S f τ κ hcut t e)
    (hz : (y, z) ∈ wolfePhaseQuantileRelation N S f τ κ hcut t e) : x = z :=
  wolfeExtendedQuantileRelation_single _ hcut t he y x z hx hz

theorem wolfePhaseQuantileRelation_covers_large_atoms (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (f : JLMS.CZero 𝕜 (K × L))
    {τ κ δ e : ℝ} (hκ : 0 < κ) (hcut : ∀ a : L, IsClopen (Iic a))
    (s : Finset ℝ)
    (hgrid : ∀ a ∈ Icc (-(1 + τ)) (1 + τ),
      ∃ t ∈ s, a + τ + e < t ∧ t + e < a + δ - 2 * τ)
    (y : K) (hy : y ∈ wolfeJointPhaseGoodRows N S f τ κ) (x : L)
    (hatom : δ * ‖wolfeJointPhaseTotal S f y‖ ≤
      ‖wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y x‖) :
    y ∈ ⋃ t : s, {z | (z, x) ∈ wolfePhaseQuantileRelation N S f τ κ hcut t.val e} := by
  have hdef : ∀ z : wolfeJointPhaseGoodRows N S f τ κ,
      ‖WeakDual.toStrongDual (wolfeJointPhaseNormalizedRows N S f τ κ z)‖ -
        RCLike.re (wolfeJointPhaseNormalizedRows N S f τ κ z
          (wolfeSourceBlock univ isClopen_univ)) ≤ τ := by
    intro z
    rw [wolfeJointPhaseNormalizedRows_one N S f τ hκ z, RCLike.one_re]
    have h := wolfeJointPhaseNormalizedRows_norm_le N S f τ hκ z
    linarith
  apply wolfe_extended_quantile_grid_covers_atoms N
    (wolfeJointPhaseNormalizedRows N S f τ κ) hcut s hgrid
    (wolfeJointPhaseNormalizedRows_norm_le N S f τ hκ) hdef y hy x
  change δ ≤ ‖N.representation ((wolfeJointPhaseTotal S f y)⁻¹ •
      ((JLMS.evaluation y).comp (wolfeJointPhaseKernel S f))) x‖
  rw [map_smul]
  change δ ≤ ‖(wolfeJointPhaseTotal S f y)⁻¹ *
      wolfeAtomicCrossRow N (wolfeJointPhaseKernel S f) y x‖
  rw [norm_mul, norm_inv, ← div_eq_inv_mul]
  exact (le_div_iff₀ (hκ.trans_le hy.2)).mpr hatom

end Posets
