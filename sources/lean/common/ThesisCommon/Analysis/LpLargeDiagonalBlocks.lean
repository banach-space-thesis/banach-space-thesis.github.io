import ThesisCommon.Analysis.LpSeparatedBlocks
import ThesisCommon.Analysis.HajnalFreeSet

/-! Full-cardinality selection of noninteracting triangular blocks in actual
finite-exponent sequence spaces. The combinatorial step uses the full Hajnal
theorem, including singular ambient cardinals.
-/
noncomputable section
open scoped Cardinal ENNReal
namespace ThesisCommon
universe u
variable {𝕜 Γ X : Type*} {ι : Type u} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [LinearOrder ι]

/-- Countably many earlier interactions per block and triangularity yield
a family of full cardinality with no off-diagonal interactions. The displayed
identity holds for every vector supported on its union. -/
theorem lp_exists_large_diagonal_blocks (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hι : Cardinal.aleph 1 < Cardinal.mk ι)
    (P : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p)
    (B : ι → Set Γ) (hB : Pairwise (fun α β => Disjoint (B α) (B β)))
    (htri : ∀ α, ∀ x : lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p (B α),
      ∀ γ ∉ ⋃ β ≤ α, B β, P x γ = 0)
    (hcount : ∀ α, {β : ι | β < α ∧
      ((lpCoordinateProjection (𝕜 := 𝕜) p (B β)).comp P).comp
        (lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p (B α)).subtypeL ≠ 0}.Countable) :
    ∃ H : Set ι, Cardinal.mk H = Cardinal.mk ι ∧
      (∀ α ∈ H, ∀ β ∈ H, α ≠ β →
        ((lpCoordinateProjection (𝕜 := 𝕜) p (B β)).comp P).comp
          (lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p (B α)).subtypeL = 0) ∧
      (∀ z : lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p (⋃ α ∈ H, B α),
        ∀ α ∈ H, lpCoordinateProjection (𝕜 := 𝕜) p (B α) (P z) =
          lpCoordinateProjection (𝕜 := 𝕜) p (B α)
            (P (lpCoordinateProjection (𝕜 := 𝕜) p (B α) z))) := by
  classical
  let F : ι → Set ι := fun α => {β | β < α ∧
    ((lpCoordinateProjection (𝕜 := 𝕜) p (B β)).comp P).comp
      (lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p (B α)).subtypeL ≠ 0}
  have hF (α : ι) : Cardinal.mk (F α) < Cardinal.aleph 1 :=
    (Cardinal.countable_iff_lt_aleph_one (F α)).mp (hcount α)
  obtain ⟨H, hHcard, hHfree⟩ := hajnal_free_set F (Cardinal.aleph 1)
    ((Cardinal.aleph0_le_aleph 1).trans hι.le) hι hF
  have hdiag : ∀ α ∈ H, ∀ β ∈ H, α ≠ β →
      ((lpCoordinateProjection (𝕜 := 𝕜) p (B β)).comp P).comp
        (lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p (B α)).subtypeL = 0 := by
    intro α hα β hβ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact lp_triangular_block_zero p P B hB htri hlt
    · by_contra hnzero
      exact (hHfree α hα β hβ hne).2 ⟨hgt, hnzero⟩
  exact ⟨H, hHcard, hdiag, fun z α hα =>
    lp_block_diagonal_on_supported_union p hp P B H hdiag z hα⟩

end ThesisCommon
