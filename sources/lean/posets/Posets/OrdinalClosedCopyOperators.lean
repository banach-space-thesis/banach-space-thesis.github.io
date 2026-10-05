import Posets.WolfeNearDiagonalFactorizationContinuous
import JLMS.OrdinalSpaceRetractionBounded
import ThesisCommon.Analysis.Factorization

/-! Restriction to a closed cofinal ordinal copy and ceiling extension give
actual contractive compression maps. A dominant atomic diagonal in that
compression gives identity factors with bounds independent of the ordinals. -/

noncomputable section
open Set Topology ThesisCommon JLMS
namespace Posets
universe u
variable {𝕜 : Type*} [RCLike 𝕜] {γ β : Ordinal.{u}}

theorem ordinalClosedCopy_retraction
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩) :
    (ordinalSpaceRestriction (𝕜 := 𝕜) g).comp
        (ordinalSpaceCeilingExtension g hg htop) = ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 γ) ∧
      ‖ordinalSpaceRestriction (𝕜 := 𝕜) g‖ ≤ 1 ∧
      ‖ordinalSpaceCeilingExtension (𝕜 := 𝕜) g hg htop‖ ≤ 1 := by
  refine ⟨?_, norm_ordinalSpaceRestriction_le g, norm_ordinalSpaceCeilingExtension_le g hg htop⟩
  ext f x
  exact DFunLike.congr_fun (ordinalSpaceRestriction_ceilingExtension g hg htop f) x

def ordinalClosedCopyCompression
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (T : OrdinalC 𝕜 β →L[𝕜] OrdinalC 𝕜 β) :
    JLMS.CZero 𝕜 (OrdinalInterval γ) →L[𝕜] JLMS.CZero 𝕜 (OrdinalInterval γ) :=
  wolfeContinuousCompression T (ordinalSpaceCeilingExtension g hg htop) (ordinalSpaceRestriction g)

theorem ordinalClosedCopyCompression_apply
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (T : OrdinalC 𝕜 β →L[𝕜] OrdinalC 𝕜 β)
    (f : JLMS.CZero 𝕜 (OrdinalInterval γ)) (x : OrdinalInterval γ) :
    ordinalClosedCopyCompression g hg htop T f x =
      T (ordinalSpaceCeilingExtension g hg htop
        ((compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := OrdinalInterval γ)).symm f)) (g x) := rfl

theorem ordinalClosedCopy_nearDiagonal_factors
    (M : AtomicDualModel 𝕜 (OrdinalInterval γ))
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (T : OrdinalC 𝕜 β →L[𝕜] OrdinalC 𝕜 β)
    {d ε : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < d)
    (hdiag : ∀ x, d ≤ ‖wolfeAtomicCrossRow M (ordinalClosedCopyCompression g hg htop T) x x‖)
    (hoff : ∀ x, ‖atomicRestriction M ({x}ᶜ)
      ((evaluation x).comp (ordinalClosedCopyCompression g hg htop T))‖ ≤ ε) :
    ∃ R : OrdinalC 𝕜 β →L[𝕜] OrdinalC 𝕜 γ,
      R.comp (T.comp (ordinalSpaceCeilingExtension g hg htop)) =
        ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 γ) ∧ ‖R‖ ≤ 1 / (d - 3 * ε) := by
  obtain ⟨R, hR, hn⟩ := wolfe_nearDiagonal_continuous_compression_factors M T
    (ordinalSpaceCeilingExtension g hg htop) (ordinalSpaceRestriction g) hε hgap hdiag hoff
  exact ⟨R, hR, hn.trans (div_le_div_of_nonneg_right (norm_ordinalSpaceRestriction_le g)
    (sub_pos.mpr hgap).le)⟩

theorem ordinalClosedCopy_nearDiagonal_factorsIdentityWith
    (M : AtomicDualModel 𝕜 (OrdinalInterval γ))
    (g : C(OrdinalInterval γ, OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (T : OrdinalC 𝕜 β →L[𝕜] OrdinalC 𝕜 β)
    {d ε : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < d)
    (hdiag : ∀ x, d ≤ ‖wolfeAtomicCrossRow M (ordinalClosedCopyCompression g hg htop T) x x‖)
    (hoff : ∀ x, ‖atomicRestriction M ({x}ᶜ)
      ((evaluation x).comp (ordinalClosedCopyCompression g hg htop T))‖ ≤ ε) :
    FactorsIdentityWith T (OrdinalC 𝕜 γ) (1 / (d - 3 * ε)) := by
  obtain ⟨R, hR, hn⟩ := ordinalClosedCopy_nearDiagonal_factors M g hg htop T hε hgap hdiag hoff
  refine ⟨R, ordinalSpaceCeilingExtension g hg htop, ?_, ?_⟩
  · simpa only [ContinuousLinearMap.comp_assoc] using hR
  · calc
      ‖R‖ * ‖ordinalSpaceCeilingExtension (𝕜 := 𝕜) g hg htop‖ ≤ ‖R‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_ordinalSpaceCeilingExtension_le g hg htop) (norm_nonneg R)
      _ ≤ 1 / (d - 3 * ε) := by simpa only [mul_one] using hn

end Posets
