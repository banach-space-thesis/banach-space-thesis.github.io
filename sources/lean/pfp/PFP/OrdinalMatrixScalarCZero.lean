import PFP.OrdinalMatrixCZeroUncountableFactorization
import Posets.OrdinalIdealTransportRepeatedModel
import Mathlib.Logic.Denumerable

/-! Scalar c₀ has UPFP on every infinite index set, independently of the
index universe. The countable case uses a genuine reindexing; the
uncountable case uses the full-cardinality matrix selection above. -/
noncomputable section
namespace Posets.UniverseRegularMatrix
open ThesisCommon Cardinal
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096

theorem jlmsScalarCZero_infinite_hasUPFP (I : Type*) [Infinite I] :
    HasUPFP 𝕜 (JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)) := by
  classical
  rcases le_or_gt (#I) ℵ₀ with hI | hI
  · letI : Countable I := Cardinal.mk_le_aleph0_iff.mp hI
    let e : ℕ ≃ I := Classical.choice nonempty_equiv_of_countable
    exact (Posets.jlmsScalarCZero_hasUPFP (𝕜 := 𝕜)).of_equiv
      (JLMS.CZeroSum.reindex (𝕜 := 𝕜) (E := fun _ : I => 𝕜) e).symm.toContinuousLinearEquiv
  · exact ⟨2, by norm_num, uncountableScalarCZero_hasCPFP_two hI⟩

end Posets.UniverseRegularMatrix
