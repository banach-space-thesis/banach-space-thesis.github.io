import Posets.OrdinalBlockApproximation

/-! Actual uniformly bounded block maps assemble into identity factors
when their diagonal compressions are identities and their mixed block
norms have a uniformly small finite row sum. -/

noncomputable section
open Set Filter Topology ThesisCommon
namespace Posets
attribute [local instance] Classical.typeDecidableEq
universe u v w
variable {𝕜 : Type*} [RCLike 𝕜] {I : Type u}
  {E : I → Type v} {F : I → Type w}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000

local instance blockAssemblyEGroup : NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance blockAssemblyESpace : NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance blockAssemblyFGroup : NormedAddCommGroup (JLMS.CZeroSum 𝕜 F) := inferInstance
local instance blockAssemblyFSpace : NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 F) := inferInstance

theorem blockAssembly_mapCLM_single (J : ∀ i, E i →L[𝕜] F i)
    {D : ℝ} (hD : 0 ≤ D) (hJ : ∀ i, ‖J i‖ ≤ D) (j : I) (x : E j) :
    JLMS.CZeroSum.mapCLM J hD hJ (JLMS.CZeroSum.single j x) =
      JLMS.CZeroSum.single j (J j x) := by
  apply JLMS.CZeroSum.ext
  intro i
  rw [JLMS.CZeroSum.mapCLM_apply]
  by_cases hij : i = j
  · subst i
    simp only [JLMS.CZeroSum.single_apply_self]
  · rw [JLMS.CZeroSum.single_apply_ne (𝕜 := 𝕜) (E := E) j x hij, map_zero,
      JLMS.CZeroSum.single_apply_ne (𝕜 := 𝕜) (E := F) j (J j x) hij]

theorem cZeroOperatorBlock_map_compression
    (T : JLMS.CZeroSum 𝕜 F →L[𝕜] JLMS.CZeroSum 𝕜 F)
    (R : ∀ i, F i →L[𝕜] E i) (J : ∀ i, E i →L[𝕜] F i)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : ∀ i, ‖R i‖ ≤ C) (hJ : ∀ i, ‖J i‖ ≤ D) (i j : I) :
    cZeroOperatorBlock
      ((JLMS.CZeroSum.mapCLM R hC hR).comp (T.comp (JLMS.CZeroSum.mapCLM J hD hJ))) i j =
      (R i).comp ((cZeroOperatorBlock T i j).comp (J j)) := by
  ext x
  change R i (T (JLMS.CZeroSum.mapCLM J hD hJ (JLMS.CZeroSum.single j x)) i) =
    R i (T (JLMS.CZeroSum.single j (J j x)) i)
  rw [blockAssembly_mapCLM_single]

theorem cZeroSum_factorsIdentityWith_of_block_compressions [∀ i, CompleteSpace (E i)]
    (T : JLMS.CZeroSum 𝕜 F →L[𝕜] JLMS.CZeroSum 𝕜 F)
    (R : ∀ i, F i →L[𝕜] E i) (J : ∀ i, E i →L[𝕜] F i)
    {C D ε : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hsmall : ε < 1 / 2)
    (hR : ∀ i, ‖R i‖ ≤ C) (hJ : ∀ i, ‖J i‖ ≤ D)
    (hdiag : ∀ i, (R i).comp ((cZeroOperatorBlock T i i).comp (J i)) =
      ContinuousLinearMap.id 𝕜 (E i))
    (hrow : ∀ i (s : Finset I),
      ∑ j ∈ s.erase i, ‖(R i).comp ((cZeroOperatorBlock T i j).comp (J j))‖ ≤ ε) :
    FactorsIdentityWith T (JLMS.CZeroSum 𝕜 E) (2 * (C * D)) := by
  let A := JLMS.CZeroSum.mapCLM R hC hR
  let B := JLMS.CZeroSum.mapCLM J hD hJ
  let U := A.comp (T.comp B)
  have hu : FactorsIdentityWith U (JLMS.CZeroSum 𝕜 E) 2 := by
    apply cZeroSum_factorsIdentityWith_of_offDiagonal U hε hsmall
    · intro i
      exact (cZeroOperatorBlock_map_compression T R J hC hD hR hJ i i).trans (hdiag i)
    · intro i s
      simpa only [U, A, B, cZeroOperatorBlock_map_compression] using hrow i s
  have hu' : FactorsIdentityWith ((A.comp T).comp B) (JLMS.CZeroSum 𝕜 E) 2 := by
    simpa only [U, ContinuousLinearMap.comp_assoc] using hu
  apply (hu'.of_compression A B).mono
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  exact mul_le_mul (JLMS.CZeroSum.norm_mapCLM_le R hC hR)
    (JLMS.CZeroSum.norm_mapCLM_le J hD hJ) (norm_nonneg B) hC

end Posets
