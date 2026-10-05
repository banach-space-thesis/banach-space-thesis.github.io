import Posets.TopologyStatements
import JLMS.Rudin

/-! Lemma 4.17. Rudin's proved atomic dual representation supplies countable
supports for the coordinate functionals. Their nonisolated atoms form the
exceptional set, with the stated cardinal bound. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
open scoped ZeroAtInfty Cardinal
namespace Posets

theorem not_isOpen_singleton_iff_mem_derivedSet_univ {K : Type*} [TopologicalSpace K]
    (x : K) : ¬ IsOpen ({x} : Set K) ↔ x ∈ derivedSet (Set.univ : Set K) := by
  simp only [isOpen_singleton_iff_punctured_nhds, mem_derivedSet, AccPt,
    Filter.principal_univ, inf_top_eq, neBot_iff]

/-- In an infinite scattered Hausdorff space the isolated points are infinite. -/
theorem infinite_isolated_of_scattered {K : Type*} [TopologicalSpace K] [T1Space K]
    [Infinite K] (hK : Scattered K) : Infinite (Isolated K) := by
  classical
  by_contra h
  letI : Finite (Isolated K) := not_infinite_iff_finite.mp h
  let I : Set K := {x | IsOpen ({x} : Set K)}
  letI : Finite I := ‹Finite (Isolated K)›
  have hI : I.Finite := Set.toFinite I
  have hne : Iᶜ.Nonempty := by
    by_contra hn
    have heq : I = Set.univ := by
      simpa only [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] using hn
    exact Set.infinite_univ (heq ▸ hI)
  obtain ⟨x, hx, U, hU, heq⟩ := hK Iᶜ hne
  have hopen : IsOpen ({x} : Set K) := heq ▸ (hI.isClosed.isOpen_compl.inter hU)
  exact hx hopen

variable {𝕜 : Type} [RCLike 𝕜]
variable {K : Type} [TopologicalSpace K] [T2Space K]

@[simp] theorem singletonFunction_apply (x : Isolated K) (y : K) :
    singletonFunction 𝕜 x y = if y = x.val then 1 else 0 := by
  simp [singletonFunction, Set.indicator_apply]

/-- At an isolated point the atomic coefficient is evaluation on its singleton indicator. -/
theorem atomicCoefficient_singleton (M : JLMS.AtomicDualModel 𝕜 K)
    (φ : C₀(K, 𝕜) →L[𝕜] 𝕜) (x : Isolated K) :
    M.representation φ x.val = φ (singletonFunction 𝕜 x) := by
  have h := (JLMS.atomicDual_apply_hasSum M φ (singletonFunction 𝕜 x)).tsum_eq
  rw [tsum_eq_single x.val] at h
  · simpa only [singletonFunction_apply, ite_true, mul_one] using h
  · intro y hy
    simp only [singletonFunction_apply, if_neg hy, mul_zero]

theorem lemma_4_17_proof (𝕜 : Type) [RCLike 𝕜] (K L : Type)
    [TopologicalSpace K] [TopologicalSpace L] [LocallyCompactSpace K]
    [LocallyCompactSpace L] [T2Space K] [T2Space L] [Infinite K] [Infinite L]
    (T : C₀(K, 𝕜) →L[𝕜] C₀(L, 𝕜)) : Lemma_4_17 𝕜 K L T := by
  classical
  intro hK hL
  letI : Infinite (Isolated L) := infinite_isolated_of_scattered hL
  obtain ⟨M⟩ := JLMS.exists_atomicDualModel (𝕜 := 𝕜) (K := K) hK
  let φ : Isolated L → (C₀(K, 𝕜) →L[𝕜] 𝕜) :=
    fun z => (JLMS.evaluation z.val).comp T
  let S : Isolated L → Set K := fun z => Function.support (M.representation (φ z))
  have hS (z : Isolated L) : (S z).Countable := JLMS.atomicDual_countable_support M (φ z)
  let E : Set K := derivedSet Set.univ ∩ ⋃ z : Isolated L, S z
  refine ⟨E, Set.inter_subset_left, ?_, ?_⟩
  · calc
      Cardinal.mk E ≤ Cardinal.mk (⋃ z : Isolated L, S z) :=
        Cardinal.mk_le_mk_of_subset Set.inter_subset_right
      _ ≤ Cardinal.sum (fun z : Isolated L => Cardinal.mk (S z)) := Cardinal.mk_iUnion_le_sum_mk
      _ ≤ Cardinal.sum (fun _ : Isolated L => ℵ₀) :=
        Cardinal.sum_le_sum _ _ (fun z => Cardinal.le_aleph0_iff_set_countable.mpr (hS z))
      _ = Cardinal.mk (Isolated L) := by simp
  · intro f hf z
    have hz (y : K) (hy : ¬ IsOpen ({y} : Set K)) : M.representation (φ z) y * f y = 0 := by
      by_cases ha : M.representation (φ z) y = 0
      · rw [ha, zero_mul]
      · rw [hf y ⟨(not_isOpen_singleton_iff_mem_derivedSet_univ y).mp hy,
          Set.mem_iUnion.mpr ⟨z, ha⟩⟩, mul_zero]
    have hs := JLMS.atomicDual_apply_hasSum M (φ z) f
    have hiso : HasSum (fun x : Isolated K => M.representation (φ z) x.val * f x.val) (φ z f) := by
      apply (Subtype.val_injective.hasSum_iff ?_).mpr hs
      intro y hy
      exact hz y (fun ho => hy ⟨⟨y, ho⟩, rfl⟩)
    have heq := hiso.tsum_eq.symm
    simpa only [atomicCoefficient_singleton, φ, ContinuousLinearMap.comp_apply,
      JLMS.evaluation_apply] using heq

end Posets
