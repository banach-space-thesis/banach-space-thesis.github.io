import Posets.WolfePreservationBlockMass
import Posets.WolfePositiveLimits
import Posets.WolfeNorming

/-! Open variation mass can be retained in a compact clopen subregion,
uniformly over an entire compact parameter block. This turns the genuine
continuous block regions into clopen sets without discarding source rank. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set Topology
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [LocallyCompactSpace K] [T2Space K]

theorem wolfe_exists_compact_clopen_large_mass
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {U : Set K} (hU : IsOpen U)
    {r : ℝ} (hr : r < wolfeMass M μ U) :
    ∃ H : Set K, IsClopen H ∧ IsCompact H ∧ H ⊆ U ∧ r < wolfeMass M μ H := by
  have hlarge : r < ‖JLMS.restrictionL1 U (M.representation (WeakDual.toStrongDual μ))‖ := by
    simpa only [wolfeMass, JLMS.atomicRestriction_norm] using hr
  obtain ⟨A, hAsupp, hAmass⟩ := JLMS.exists_finite_restrictionL1_mass
    (JLMS.restrictionL1 U (M.representation (WeakDual.toStrongDual μ))) hlarge
  have hAU : (A : Set K) ⊆ U := by
    intro x hx
    by_contra hxU
    exact hAsupp hx (by simp [hxU])
  have hrestrict : JLMS.restrictionL1 (A : Set K)
      (JLMS.restrictionL1 U (M.representation (WeakDual.toStrongDual μ))) =
      JLMS.restrictionL1 (A : Set K) (M.representation (WeakDual.toStrongDual μ)) := by
    ext x
    by_cases hx : x ∈ A
    · simp [hx, hAU hx]
    · simp [hx]
  rw [hrestrict, ← JLMS.atomicRestriction_norm] at hAmass
  obtain ⟨H, hH, hHc, hAH, hHU⟩ := wolfe_exists_compact_clopen_between hK
    A.finite_toSet.isCompact hU hAU
  exact ⟨H, hH, hHc, hHU, hAmass.trans_le (wolfeMass_mono M μ hAH)⟩

theorem wolfe_exists_compact_clopen_uniform_mass {P : Type*} [TopologicalSpace P]
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (μ : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (hμ : Continuous μ)
    {A : Set P} (hA : IsCompact A) {U : Set K} (hU : IsOpen U)
    {r : ℝ} (hr : ∀ x ∈ A, r < wolfeMass M (μ x) U) :
    ∃ H : Set K, IsClopen H ∧ IsCompact H ∧ H ⊆ U ∧
      ∀ x ∈ A, r < wolfeMass M (μ x) H := by
  classical
  choose H hH hHc hHU hmass using fun x : A =>
    wolfe_exists_compact_clopen_large_mass M hK (μ x) hU (hr x x.property)
  let V (x : A) : Set P := {y | r < wolfeMass M (μ y) (H x)}
  have hV (x : A) : IsOpen (V x) :=
    (isOpen_wolfeMass_gt M hK (hH x).isOpen r).preimage hμ
  have hcover : A ⊆ ⋃ x : A, V x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hmass ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover V hV hcover
  refine ⟨⋃ x ∈ s, H x, isClopen_biUnion_finset (fun x _ => hH x),
    s.isCompact_biUnion (fun x _ => hHc x),
    iUnion_subset fun x => iUnion_subset fun _ => hHU x, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
  exact hxy.trans_le (wolfeMass_mono M (μ x)
    (subset_iUnion_of_subset y (subset_iUnion_of_subset hy subset_rfl)))

end Posets
