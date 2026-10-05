import Posets.WolfeMass

/-! Variation identities and inequalities for the actual atomic Wolfe mass. -/

noncomputable section
open Set
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
variable (M : JLMS.AtomicDualModel 𝕜 K)
local instance wolfeMassBoundsDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance wolfeMassBoundsDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

theorem wolfeMass_eq_tsum (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : Set K) :
    wolfeMass M μ U = ∑' x, U.indicator (fun x => ‖M.representation (WeakDual.toStrongDual μ) x‖) x := by
  classical
  rw [wolfeMass, JLMS.atomicRestriction_norm, JLMS.ellOneOn_norm_eq_tsum]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ U <;> simp [hx]

theorem wolfeMass_univ (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) :
    wolfeMass M μ univ = ‖WeakDual.toStrongDual μ‖ := by
  rw [wolfeMass_eq_tsum]
  simp only [indicator_univ, ← JLMS.ellOneOn_norm_eq_tsum, M.representation.norm_map]

theorem wolfeMass_add_le (μ ν : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : Set K) :
    wolfeMass M (μ + ν) U ≤ wolfeMass M μ U + wolfeMass M ν U := by
  simp only [wolfeMass, map_add]
  exact norm_add_le _ _

theorem wolfeMass_smul (a : 𝕜) (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : Set K) :
    wolfeMass M (a • μ) U = ‖a‖ * wolfeMass M μ U := by
  simp only [wolfeMass, map_smul, norm_smul]

theorem wolfeMass_mono (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    {U V : Set K} (hUV : U ⊆ V) : wolfeMass M μ U ≤ wolfeMass M μ V := by
  have he : V = U ∪ (V \ U) := by ext x; aesop
  have hd : Disjoint U (V \ U) := Set.disjoint_left.mpr fun _ hu hv => hv.2 hu
  rw [he, wolfeMass_union M μ hd]
  exact le_add_of_nonneg_right (wolfeMass_nonneg M μ _)

theorem wolfeMass_compl (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : Set K) :
    wolfeMass M μ U + wolfeMass M μ Uᶜ = ‖WeakDual.toStrongDual μ‖ := by
  rw [← wolfeMass_union M μ disjoint_compl_right, union_compl_self, wolfeMass_univ]

theorem wolfeMass_singleton (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (x : K) :
    wolfeMass M μ {x} = ‖M.representation (WeakDual.toStrongDual μ) x‖ := by
  classical
  rw [wolfeMass_eq_tsum]
  rw [tsum_eq_single x]
  · simp
  · intro y hy
    simp [hy]

end Posets
