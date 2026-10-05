import JLMS.CZeroEllOneImage
import JLMS.EllOneDualNonseparable

/-!
# The original codomain admissibility of C₀(K)

An ℓ¹ embedding would transfer isometrically on inputs to the compact image
of its coordinate functions. For scattered K this image is countable and
scattered, so its C₀ dual is separable by Rudin. Hahn–Banach would then make
the nonseparable ℓ¹ dual a continuous image of that separable dual, a
contradiction. This proves the no-ℓ¹ branch of the paper's admissibility
disjunction directly from its original hypotheses.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]

theorem cZero_not_containsEllOne (hK : IsScattered K) : ¬ContainsEllOne 𝕜 (CZero 𝕜 K) := by
  rintro ⟨J, c, hc, hlower⟩
  letI : TopologicalSpace.SeparableSpace
      (CZero 𝕜 (CZeroFamilyImage (cZeroEllOneBasisFamily J)) →L[𝕜] 𝕜) :=
    cZeroFamilyImage_dual_separable (cZeroEllOneBasisFamily J) hK
  apply not_containsEllOne_of_separable_dual (𝕜 := 𝕜)
    (X := CZero 𝕜 (CZeroFamilyImage (cZeroEllOneBasisFamily J)))
  refine ⟨cZeroEllOneImageOperator J, c, hc, ?_⟩
  intro a
  rw [norm_cZeroEllOneImageOperator_apply]
  exact hlower a

theorem cZero_admissible (hK : IsScattered K) : AdmissibleCodomain 𝕜 (CZero 𝕜 K) :=
  Or.inl (cZero_not_containsEllOne hK)

end JLMS
