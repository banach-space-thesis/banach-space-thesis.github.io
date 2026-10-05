import Posets.WolfePreservationNecessaryClosedKernelAtoms

/-! Real signed masses of arbitrary atomic sets. A single global positivity
defect controls their failure of monotonicity; these estimates are used only
for the actual atomic dual representation. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 L : Type*} [RCLike 𝕜] [TopologicalSpace L] [CompactSpace L]
local instance wolfeRealMassDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 L →L[𝕜] 𝕜) := inferInstance
local instance wolfeRealMassDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 L →L[𝕜] 𝕜) := inferInstance

def wolfeRealMass (N : JLMS.AtomicDualModel 𝕜 L)
    (ν : WeakDual 𝕜 (JLMS.CZero 𝕜 L)) (D : Set L) : ℝ :=
  RCLike.re (JLMS.atomicRestriction N D (WeakDual.toStrongDual ν)
    (wolfeSourceBlock univ isClopen_univ))

theorem wolfeRealMass_clopen (N : JLMS.AtomicDualModel 𝕜 L)
    (ν : WeakDual 𝕜 (JLMS.CZero 𝕜 L)) (D : Set L) (hD : IsClopen D) :
    wolfeRealMass N ν D = RCLike.re (ν (wolfeSourceBlock D hD)) := by
  rw [wolfeRealMass, wolfeSourceBlock_restriction_one N _ D hD]
  rfl

theorem wolfeRealMass_union (N : JLMS.AtomicDualModel 𝕜 L)
    (ν : WeakDual 𝕜 (JLMS.CZero 𝕜 L)) {D E : Set L} (hd : Disjoint D E) :
    wolfeRealMass N ν (D ∪ E) = wolfeRealMass N ν D + wolfeRealMass N ν E := by
  have he : JLMS.atomicRestriction N (D ∪ E) (WeakDual.toStrongDual ν) =
      JLMS.atomicRestriction N D (WeakDual.toStrongDual ν) +
        JLMS.atomicRestriction N E (WeakDual.toStrongDual ν) := by
    apply N.representation.injective
    simp only [map_add, JLMS.atomicRestriction_coordinates]
    rw [JLMS.restrictionL1_union _ _ hd]
    rfl
  simp only [wolfeRealMass, he, ContinuousLinearMap.add_apply, map_add]

theorem wolfeRealMass_singleton (N : JLMS.AtomicDualModel 𝕜 L)
    (ν : WeakDual 𝕜 (JLMS.CZero 𝕜 L)) (x : L) :
    wolfeRealMass N ν {x} = RCLike.re (N.representation (WeakDual.toStrongDual ν) x) := by
  classical
  have h := JLMS.atomicRestriction_finset_apply N ({x} : Finset L) (WeakDual.toStrongDual ν)
    (wolfeSourceBlock univ isClopen_univ)
  simpa [wolfeRealMass, wolfeSourceBlock_apply] using congrArg RCLike.re h

theorem wolfeRealMass_abs_le (N : JLMS.AtomicDualModel 𝕜 L)
    (ν : WeakDual 𝕜 (JLMS.CZero 𝕜 L)) (D : Set L) :
    |wolfeRealMass N ν D| ≤ ‖WeakDual.toStrongDual ν‖ := by
  apply (RCLike.abs_re_le_norm _).trans
  apply ((JLMS.atomicRestriction N D (WeakDual.toStrongDual ν)).le_opNorm _).trans
  apply (mul_le_mul_of_nonneg_left (wolfeSourceBlock_norm_le univ isClopen_univ) (norm_nonneg _)).trans
  simpa only [mul_one] using wolfeMass_le_norm N ν D

theorem wolfeRealMass_lower_of_defect (N : JLMS.AtomicDualModel 𝕜 L)
    (ν : WeakDual 𝕜 (JLMS.CZero 𝕜 L)) {τ : ℝ}
    (hdefect : ‖WeakDual.toStrongDual ν‖ -
      RCLike.re (ν (wolfeSourceBlock univ isClopen_univ)) ≤ τ) (D : Set L) :
    wolfeMass N ν D - τ ≤ wolfeRealMass N ν D := by
  have h := wolfePhaseRestriction_re_lower N ν (wolfeSourceBlock univ isClopen_univ)
    (wolfeSourceBlock_norm_le univ isClopen_univ) D
  change wolfeMass N ν D - (‖WeakDual.toStrongDual ν‖ -
    RCLike.re (ν (wolfeSourceBlock univ isClopen_univ))) ≤ wolfeRealMass N ν D at h
  linarith

theorem wolfeRealMass_mono_with_defect (N : JLMS.AtomicDualModel 𝕜 L)
    (ν : WeakDual 𝕜 (JLMS.CZero 𝕜 L)) {τ : ℝ}
    (hdefect : ‖WeakDual.toStrongDual ν‖ -
      RCLike.re (ν (wolfeSourceBlock univ isClopen_univ)) ≤ τ)
    {D E : Set L} (hDE : D ⊆ E) : wolfeRealMass N ν D ≤ wolfeRealMass N ν E + τ := by
  have he : E = D ∪ (E \ D) := by ext x; aesop
  have hd : Disjoint D (E \ D) := disjoint_sdiff_right
  have h := wolfeRealMass_lower_of_defect N ν hdefect (E \ D)
  have hn := wolfeMass_nonneg N ν (E \ D)
  rw [he, wolfeRealMass_union N ν hd]
  linarith

end Posets
