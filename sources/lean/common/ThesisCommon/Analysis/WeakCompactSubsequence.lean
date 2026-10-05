import ThesisCommon.Analysis.WeakCompactCountableDual
import Mathlib.Analysis.LocallyConvex.WeakSpace

/-! Sequential extraction from actual weakly compact sets. The sequence lies
in a norm-separable closed subspace; Hahn–Banach supplies countably many
ambient dual functionals that separate its weakly compact closure. -/
noncomputable section
open Set Filter Topology TopologicalSpace
namespace ThesisCommon
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem weakCompact_firstCountable_of_separable_submodule
    (S : Submodule 𝕜 E) [SeparableSpace S]
    {K : Set (WeakSpace 𝕜 E)} (hK : IsCompact K)
    (hKS : ∀ x ∈ K, (toWeakSpace 𝕜 E).symm x ∈ S) : FirstCountableTopology K := by
  classical
  obtain ⟨D, hD, htotal⟩ := hasCountableTotalDual_of_separable 𝕜 S
  choose φ hφ hnorm using fun ψ : D => exists_extension_norm_eq S ψ.val
  letI : Countable D := hD.to_subtype
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let c : K → (D → 𝕜) := fun x ψ => φ ψ ((toWeakSpace 𝕜 E).symm x.val)
  have hc : Continuous c := by
    apply continuous_pi
    intro ψ
    exact (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip (φ ψ)).comp
      continuous_subtype_val
  have hinj : Function.Injective c := by
    intro x y hxy
    let xs : S := ⟨(toWeakSpace 𝕜 E).symm x.val, hKS x.val x.property⟩
    let ys : S := ⟨(toWeakSpace 𝕜 E).symm y.val, hKS y.val y.property⟩
    have hs : xs = ys := by
      apply sub_eq_zero.mp
      apply htotal
      intro ψ hψ
      rw [map_sub]
      rw [← hφ ⟨ψ, hψ⟩ xs, ← hφ ⟨ψ, hψ⟩ ys]
      exact sub_eq_zero.mpr (congrFun hxy ⟨ψ, hψ⟩)
    apply Subtype.ext
    apply (toWeakSpace 𝕜 E).symm.injective
    exact congrArg (fun z : S => (z : E)) hs
  exact (hc.isClosedEmbedding hinj).isEmbedding.firstCountableTopology

theorem exists_weak_subsequence_of_compactCover
    (u : ℕ → E) {K : Set (WeakSpace 𝕜 E)} (hK : IsCompact K)
    (hu : ∀ n, toWeakSpace 𝕜 E (u n) ∈ K) :
    ∃ x : E, ∃ r : ℕ → ℕ, StrictMono r ∧
      Tendsto (fun n => toWeakSpace 𝕜 E (u (r n))) atTop (𝓝 (toWeakSpace 𝕜 E x)) := by
  letI : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  letI : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower _ _ _
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars _ 𝕜 _
  let S : Submodule 𝕜 E := (Submodule.span 𝕜 (Set.range u)).topologicalClosure
  have hsep : IsSeparable (S : Set E) :=
    ((Set.countable_range u).isSeparable.span (R := 𝕜)).closure
  letI : SeparableSpace S := hsep.separableSpace
  have hSc : IsClosed (S : Set E) := Submodule.isClosed_topologicalClosure _
  have hcv : Convex ℝ (S : Set E) := (S.restrictScalars ℝ).convex
  have hSw : IsClosed (toWeakSpace 𝕜 E '' (S : Set E)) := by
    have heq := hcv.toWeakSpace_closure 𝕜
    rw [hSc.closure_eq] at heq
    rw [heq]
    exact isClosed_closure
  let L : Set (WeakSpace 𝕜 E) := K ∩ (toWeakSpace 𝕜 E '' (S : Set E))
  have hL : IsCompact L := hK.inter_right hSw
  have hLS : ∀ x ∈ L, (toWeakSpace 𝕜 E).symm x ∈ S := by
    rintro x ⟨_, y, hy, rfl⟩
    simpa only [LinearEquiv.symm_apply_apply] using hy
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  letI : FirstCountableTopology L :=
    weakCompact_firstCountable_of_separable_submodule S hL hLS
  have huL (n : ℕ) : toWeakSpace 𝕜 E (u n) ∈ L := by
    refine ⟨hu n, u n, ?_, rfl⟩
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self n))
  let v : ℕ → L := fun n => ⟨toWeakSpace 𝕜 E (u n), huL n⟩
  obtain ⟨x, r, hr, hx⟩ := CompactSpace.tendsto_subseq v
  refine ⟨(toWeakSpace 𝕜 E).symm x.val, r, hr, ?_⟩
  simpa only [Function.comp_def, v, LinearEquiv.apply_symm_apply] using
    continuous_subtype_val.tendsto x |>.comp hx

theorem exists_weak_subsequence_of_compactClosure
    (u : ℕ → E)
    (h : IsCompact (closure (toWeakSpace 𝕜 E '' Set.range u))) :
    ∃ x : E, ∃ r : ℕ → ℕ, StrictMono r ∧
      Tendsto (fun n => toWeakSpace 𝕜 E (u (r n))) atTop (𝓝 (toWeakSpace 𝕜 E x)) :=
  exists_weak_subsequence_of_compactCover u h fun n =>
    subset_closure ⟨u n, Set.mem_range_self n, rfl⟩

end ThesisCommon
