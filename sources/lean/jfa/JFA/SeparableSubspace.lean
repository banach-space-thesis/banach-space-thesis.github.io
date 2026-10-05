import JFA.SeparableRange
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! Common separable closed subspaces and their annihilating functionals. -/

noncomputable section
open TopologicalSpace
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E X : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem exists_common_separable_subspace {I : Type*} [Countable I] (T : I → E →L[𝕜] X)
    (hT : ∀ n, HasSeparableRange 𝕜 E X (T n)) :
    ∃ Y : Submodule 𝕜 X, IsClosed (Y : Set X) ∧ IsSeparable (Y : Set X) ∧
      ∀ n x, T n x ∈ Y := by
  let Y := (Submodule.span 𝕜 (⋃ n, Set.range (T n))).topologicalClosure
  refine ⟨Y, Submodule.isClosed_topologicalClosure _, ?_, ?_⟩
  · exact ((IsSeparable.iUnion hT).span (R := 𝕜)).closure
  · intro n x
    apply Submodule.le_topologicalClosure
    exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨n, x, rfl⟩)

/-- Hahn--Banach gives a nonzero functional annihilating every proper closed
subspace. The chosen vector normalizes its value to one. -/
theorem exists_annihilator (Y : Submodule 𝕜 X) (hclosed : IsClosed (Y : Set X))
    (hproper : Y ≠ ⊤) :
    ∃ (ψ : X →L[𝕜] 𝕜) (x : X), ψ x = 1 ∧ ∀ y ∈ Y, ψ y = 0 := by
  letI : IsClosed (Y : Set X) := hclosed
  obtain ⟨x, hx⟩ : ∃ x : X, x ∉ Y := by
    by_contra h
    apply hproper
    apply top_unique
    intro x _
    by_contra hx
    exact h ⟨x, hx⟩
  have hq : (Submodule.Quotient.mk x : X ⧸ Y) ≠ 0 := by
    intro h
    exact hx ((Submodule.Quotient.mk_eq_zero Y).mp h)
  obtain ⟨f, _, hf⟩ := exists_dual_vector 𝕜 (Submodule.Quotient.mk x : X ⧸ Y) hq
  let q : X →L[𝕜] X ⧸ Y := Y.mkQ.mkContinuous 1
    (fun z => by simpa only [one_mul] using Submodule.Quotient.norm_mk_le Y z)
  let ψ : X →L[𝕜] 𝕜 := f.comp q
  have hψ : ψ x ≠ 0 := by
    change f (Submodule.Quotient.mk x) ≠ 0
    rw [hf]
    exact RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hq)
  refine ⟨ψ, (ψ x)⁻¹ • x, ?_, ?_⟩
  · simp [map_smul, hψ]
  · intro y hy
    change f (Submodule.Quotient.mk y) = 0
    rw [(Submodule.Quotient.mk_eq_zero Y).mpr hy, map_zero]

theorem exists_annihilator_of_separable (hX : ¬ SeparableSpace X)
    (Y : Submodule 𝕜 X) (hclosed : IsClosed (Y : Set X)) (hsep : IsSeparable (Y : Set X)) :
    ∃ (ψ : X →L[𝕜] 𝕜) (x : X), ψ x = 1 ∧ ∀ y ∈ Y, ψ y = 0 := by
  apply exists_annihilator Y hclosed
  intro htop
  apply hX
  rw [htop] at hsep
  exact isSeparable_univ_iff.mp hsep

theorem mem_of_all_annihilators_zero (Y : Submodule 𝕜 X)
    (hclosed : IsClosed (Y : Set X)) (x : X)
    (h : ∀ ψ : X →L[𝕜] 𝕜, (∀ y ∈ Y, ψ y = 0) → ψ x = 0) : x ∈ Y := by
  letI : IsClosed (Y : Set X) := hclosed
  by_contra hx
  have hq : (Submodule.Quotient.mk x : X ⧸ Y) ≠ 0 := by
    intro hzero
    exact hx ((Submodule.Quotient.mk_eq_zero Y).mp hzero)
  obtain ⟨f, _, hf⟩ := exists_dual_vector 𝕜 (Submodule.Quotient.mk x : X ⧸ Y) hq
  let q : X →L[𝕜] X ⧸ Y := Y.mkQ.mkContinuous 1
    (fun z => by simpa only [one_mul] using Submodule.Quotient.norm_mk_le Y z)
  have hzero := h (f.comp q) (fun y hy => by
    change f (Submodule.Quotient.mk y) = 0
    rw [(Submodule.Quotient.mk_eq_zero Y).mpr hy, map_zero])
  change f (Submodule.Quotient.mk x) = 0 at hzero
  rw [hf] at hzero
  exact (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hq)) hzero

end JFA
