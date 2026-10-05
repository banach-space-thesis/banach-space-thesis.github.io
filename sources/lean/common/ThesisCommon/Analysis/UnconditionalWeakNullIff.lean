import ThesisCommon.Analysis.UnconditionalWeakNull
import ThesisCommon.Analysis.RCLikeEllOneSchur
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! The full equivalence between weak nullity of an unconditional basis
and absence of subsequences whose actual closed span is isomorphic to ℓ₁.
The reverse direction uses Hahn-Banach and the proved scalar Schur property. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
namespace NormalizedSchauderBasis
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (b : NormalizedSchauderBasis 𝕜 X)

theorem no_ellOne_subsequence_of_weakly_null
    (hweak : ∀ φ : X →L[𝕜] 𝕜, Tendsto (fun n => φ (b.vector n)) atTop (𝓝 0))
    (f : ℕ → ℕ) (hf : StrictMono f) :
    ¬ Nonempty (b.subsequenceSpan f ≃L[𝕜] lp (fun _ : ℕ => 𝕜) 1) := by
  rintro ⟨e⟩
  let u : ℕ → b.subsequenceSpan f := fun n =>
    ⟨b.vector (f n), Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)⟩
  have hu : ∀ φ : b.subsequenceSpan f →L[𝕜] 𝕜,
      Tendsto (fun n => φ (u n)) atTop (𝓝 0) := by
    intro φ
    obtain ⟨ψ, hψ, _⟩ := exists_extension_norm_eq (b.subsequenceSpan f) φ
    have ht := (hweak ψ).comp hf.tendsto_atTop
    simpa only [Function.comp_def, show (fun n => ψ (b.vector (f n))) = (fun n => φ (u n)) from
      funext (fun n => hψ (u n))] using ht
  have hnorm := (scalar_schur_of_equiv_ellOne e u hu).norm
  have hone (n : ℕ) : ‖u n‖ = 1 := b.norm_vector (f n)
  simp only [hone, norm_zero] at hnorm
  have hh : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hnorm
  norm_num at hh

theorem no_ellOne_subsequence_iff_weakly_null [CompleteSpace X] (hb : b.IsUnconditional) :
    (∀ f : ℕ → ℕ, StrictMono f →
      ¬ Nonempty (b.subsequenceSpan f ≃L[𝕜] lp (fun _ : ℕ => 𝕜) 1)) ↔
      ∀ φ : X →L[𝕜] 𝕜, Tendsto (fun n => φ (b.vector n)) atTop (𝓝 0) :=
  ⟨b.weakly_null_of_no_ellOne_subsequence hb, b.no_ellOne_subsequence_of_weakly_null⟩

theorem no_ellOne_subsequence_iff_rows_tendsto_zero [CompleteSpace X]
    (hb : b.IsUnconditional) :
    (∀ f : ℕ → ℕ, StrictMono f →
      ¬ Nonempty (b.subsequenceSpan f ≃L[𝕜] lp (fun _ : ℕ => 𝕜) 1)) ↔
      ∀ (T : X →L[𝕜] X) n,
        Tendsto (fun m => b.coord n (T (b.vector m))) atTop (𝓝 0) :=
  (b.no_ellOne_subsequence_iff_weakly_null hb).trans b.rows_tendsto_zero_iff_weakly_null.symm

end NormalizedSchauderBasis
end ThesisCommon
