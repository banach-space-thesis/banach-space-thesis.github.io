/- Universe-polymorphic extension of Posets.CZeroInfiniteFactorization. Actual maps and bounds retained; paper-specific ideal statements omitted where they are not needed. -/
import LPCK.GenericCZeroUncountableFactorization
import Posets.OrdinalIdealTransportRepeatedModel
import Mathlib.Logic.Denumerable

/-! Uniform primary factorisation for scalar c₀ on every infinite index set.
The countable case is transported from the classical c₀ theorem; the
uncountable case uses the exact selected-matrix compression proved here. -/

noncomputable section
universe u
namespace LPCK.GenericOrdinal
set_option synthInstance.maxHeartbeats 200000
open Posets
open ThesisCommon Cardinal
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192

theorem jlmsScalarCZero_infinite_hasUPFP (I : Type u) [Infinite I] :
    HasUPFP 𝕜 (JLMS.CZeroSum 𝕜 (fun _ : I => 𝕜)) := by
  classical
  rcases le_or_gt (#I) ℵ₀ with hI | hI
  · letI : Countable I := Cardinal.mk_le_aleph0_iff.mp hI
    let e : ℕ ≃ I := Classical.choice nonempty_equiv_of_countable
    exact (jlmsScalarCZero_hasUPFP (𝕜 := 𝕜)).of_equiv
      (JLMS.CZeroSum.reindex (𝕜 := 𝕜) (E := fun _ : I => 𝕜) e).symm.toContinuousLinearEquiv
  · exact ⟨2, by norm_num, uncountableScalarCZero_hasCPFP_two hI⟩

end LPCK.GenericOrdinal


