import ThesisCommon.Analysis.FilterConvergenceSpace
import Mathlib.Analysis.Normed.Group.Quotient

/-! The actual quotient of bounded scalar sequences by the closed subspace
of sequences converging to zero. The norm is mathlib's quotient norm. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]

abbrev scalarCZeroSubmodule : Submodule 𝕜 (lp (fun _ : ℕ => 𝕜) ∞) :=
  filterNullSubmodule 𝕜 Filter.cofinite

instance scalarCZeroSubmodule_isClosed :
    IsClosed (scalarCZeroSubmodule 𝕜 : Set (lp (fun _ : ℕ => 𝕜) ∞)) :=
  filterNullSubmodule_isClosed Filter.cofinite

abbrev InfinityCZeroQuotient :=
  (lp (fun _ : ℕ => 𝕜) ∞) ⧸ scalarCZeroSubmodule 𝕜

instance infinityCZeroQuotient_normedAddCommGroup :
    NormedAddCommGroup (InfinityCZeroQuotient 𝕜) := inferInstance

instance infinityCZeroQuotient_normedSpace :
    NormedSpace 𝕜 (InfinityCZeroQuotient 𝕜) := inferInstance

instance infinityCZeroQuotient_completeSpace :
    CompleteSpace (InfinityCZeroQuotient 𝕜) := inferInstance

end ThesisCommon
