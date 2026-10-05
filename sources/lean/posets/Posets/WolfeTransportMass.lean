import Posets.WolfeNorming
import Posets.SzlenkOperator
import PosetsCommon.CZeroHomeomorph

/-! Homeomorphisms preserve the actual open-set variation used by Wolfe.
The proof uses supported continuous norming functions, so it applies to any
of the proved atomic dual representations, without a compatibility assumption. -/

noncomputable section
open Set Topology ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {K L : Type*}
variable [TopologicalSpace K] [TopologicalSpace L]

def wolfeDualHomeomorph (e : K ≃ₜ L) :
    WeakDual 𝕜 (JLMS.CZero 𝕜 K) ≃ₜ WeakDual 𝕜 (JLMS.CZero 𝕜 L) where
  toFun := weakStarAdjoint (cZeroHomeomorphPull e)
  invFun := weakStarAdjoint (cZeroHomeomorphPull e.symm)
  left_inv μ := by
    apply DFunLike.ext
    intro f
    change μ (cZeroHomeomorphPull e (cZeroHomeomorphPull e.symm f)) = μ f
    congr 1
    ext x
    exact congrArg f (e.symm_apply_apply x)
  right_inv μ := by
    apply DFunLike.ext
    intro f
    change μ (cZeroHomeomorphPull e.symm (cZeroHomeomorphPull e f)) = μ f
    congr 1
    ext x
    exact congrArg f (e.apply_symm_apply x)
  continuous_toFun := weakStarAdjoint_continuous _
  continuous_invFun := weakStarAdjoint_continuous _

@[simp] theorem wolfeDualHomeomorph_apply (e : K ≃ₜ L)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (f : JLMS.CZero 𝕜 L) :
    wolfeDualHomeomorph e μ f = μ (cZeroHomeomorphPull e f) := rfl

@[simp] theorem wolfeDualHomeomorph_symm (e : K ≃ₜ L) :
    (wolfeDualHomeomorph (𝕜 := 𝕜) e).symm = wolfeDualHomeomorph e.symm := rfl

theorem cZeroHomeomorphPull_support_subset (e : K ≃ₜ L)
    (f : JLMS.CZero 𝕜 L) {U : Set K} (hf : Function.support f ⊆ e '' U) :
    Function.support (cZeroHomeomorphPull (𝕜 := 𝕜) e f) ⊆ U := by
  intro x hx
  obtain ⟨y, hy, he⟩ := hf hx
  exact e.injective he ▸ hy

variable [LocallyCompactSpace K] [LocallyCompactSpace L] [T2Space K] [T2Space L]

theorem wolfeMass_homeomorph_le (M : JLMS.AtomicDualModel 𝕜 K)
    (N : JLMS.AtomicDualModel 𝕜 L) (hL : JLMS.IsScattered L) (e : K ≃ₜ L)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {U : Set K} (hU : IsOpen U) :
    wolfeMass N (wolfeDualHomeomorph e μ) (e '' U) ≤ wolfeMass M μ U := by
  by_contra hn
  obtain ⟨f, hf, hs, hlarge⟩ := exists_supported_wolfe_norming_function N hL
    (wolfeDualHomeomorph e μ) (e.isOpenMap U hU) (lt_of_not_ge hn)
  have hp : ‖cZeroHomeomorphPull (𝕜 := 𝕜) e f‖ ≤ 1 := by
    change ‖cZeroHomeomorphIsometryEquiv (𝕜 := 𝕜) e f‖ ≤ 1
    rwa [(cZeroHomeomorphIsometryEquiv (𝕜 := 𝕜) e).norm_map]
  exact (not_lt_of_ge (norm_apply_le_wolfeMass_of_support_subset M μ
    (cZeroHomeomorphPull e f) (cZeroHomeomorphPull_support_subset e f hs) hp)) hlarge

theorem wolfeMass_homeomorph (M : JLMS.AtomicDualModel 𝕜 K)
    (N : JLMS.AtomicDualModel 𝕜 L) (hK : JLMS.IsScattered K)
    (hL : JLMS.IsScattered L) (e : K ≃ₜ L)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {U : Set K} (hU : IsOpen U) :
    wolfeMass N (wolfeDualHomeomorph e μ) (e '' U) = wolfeMass M μ U := by
  apply le_antisymm (wolfeMass_homeomorph_le M N hL e μ hU)
  have h := wolfeMass_homeomorph_le N M hK e.symm
    (wolfeDualHomeomorph e μ) (e.isOpenMap U hU)
  have hμ : wolfeDualHomeomorph e.symm (wolfeDualHomeomorph e μ) = μ :=
    (wolfeDualHomeomorph e).symm_apply_apply μ
  have hset : e.symm '' (e '' U) = U := by
    rw [← Set.image_comp]
    simpa only [Function.comp_def, e.symm_apply_apply, Set.image_id']
  simpa only [hμ, hset] using h

end Posets
