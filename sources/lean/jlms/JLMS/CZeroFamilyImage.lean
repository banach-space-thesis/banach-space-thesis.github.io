import JLMS.ScatteredImages
import JLMS.ScatteredSequences
import JLMS.PointDifferenceEvaluation
import JLMS.CountableAtomicDual

/-!
# The countable compact image of a sequence of C₀ functions

Extend the functions by zero to the one-point compactification and map a
point to its sequence of values. The image is compact and second countable.
For scattered K it is also scattered, hence countable, and its C₀ dual is
separable. This encodes the topological reduction in the Asplund argument.
-/

noncomputable section

open TopologicalSpace

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]
variable (f : ℕ → CZero 𝕜 K)

def cZeroFamilyValueMap (x : OnePoint K) : ℕ → 𝕜 := fun n => extendCZeroOnePoint (f n) x

theorem continuous_cZeroFamilyValueMap : Continuous (cZeroFamilyValueMap f) :=
  continuous_pi (fun n => (extendCZeroOnePoint (f n)).continuous)

def CZeroFamilyImage := ↥(Set.range (cZeroFamilyValueMap f))

instance cZeroFamilyImageTopology : TopologicalSpace (CZeroFamilyImage f) :=
  inferInstanceAs (TopologicalSpace ↥(Set.range (cZeroFamilyValueMap f)))

instance cZeroFamilyImageT2 : T2Space (CZeroFamilyImage f) :=
  inferInstanceAs (T2Space ↥(Set.range (cZeroFamilyValueMap f)))

instance cZeroFamilyImageSecondCountable : SecondCountableTopology (CZeroFamilyImage f) :=
  inferInstanceAs (SecondCountableTopology ↥(Set.range (cZeroFamilyValueMap f)))

instance cZeroFamilyImageCompact : CompactSpace (CZeroFamilyImage f) :=
  isCompact_iff_compactSpace.mp (isCompact_range (continuous_cZeroFamilyValueMap f))

def cZeroFamilyImageMap (x : OnePoint K) : CZeroFamilyImage f :=
  ⟨cZeroFamilyValueMap f x, ⟨x, rfl⟩⟩

theorem continuous_cZeroFamilyImageMap : Continuous (cZeroFamilyImageMap f) :=
  (continuous_cZeroFamilyValueMap f).subtype_mk _

theorem cZeroFamilyImageMap_surjective : Function.Surjective (cZeroFamilyImageMap f) := by
  rintro ⟨v, x, rfl⟩
  exact ⟨x, rfl⟩

theorem scattered_cZeroFamilyImage (hK : IsScattered K) : IsScattered (CZeroFamilyImage f) :=
  scattered_continuous_surjective_image (scattered_onePoint hK) (cZeroFamilyImageMap f)
    (continuous_cZeroFamilyImageMap f) (cZeroFamilyImageMap_surjective f)

theorem countable_cZeroFamilyImage (hK : IsScattered K) : Countable (CZeroFamilyImage f) :=
  countable_of_scattered_secondCountable (scattered_cZeroFamilyImage f hK)

theorem cZeroFamilyImage_dual_separable (hK : IsScattered K) :
    SeparableSpace (CZero 𝕜 (CZeroFamilyImage f) →L[𝕜] 𝕜) := by
  letI : Countable (CZeroFamilyImage f) := countable_cZeroFamilyImage f hK
  exact cZero_dual_separable_of_countable (scattered_cZeroFamilyImage f hK)

end JLMS
