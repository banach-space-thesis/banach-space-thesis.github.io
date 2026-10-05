import Posets.IncidenceOperators

/-! Explicit versions of the inherited norm instances; these use exactly the
ambient operator norm. -/
noncomputable section
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜] (P : Type) [PartialOrder P]

instance (priority := 3000) oppositeIncidence_normedAddCommGroup :
    NormedAddCommGroup (oppositeIncidenceSubalgebra 𝕜 P) :=
  @Submodule.normedAddCommGroup 𝕜 (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) _ _ _
    (oppositeIncidenceSubalgebra 𝕜 P).toSubmodule

instance (priority := 3000) oppositeIncidence_seminormedAddCommGroup :
    SeminormedAddCommGroup (oppositeIncidenceSubalgebra 𝕜 P) :=
  @Submodule.seminormedAddCommGroup 𝕜 (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) _ _ _
    (oppositeIncidenceSubalgebra 𝕜 P).toSubmodule

instance (priority := 3000) oppositeIncidence_normedSpace :
    NormedSpace 𝕜 (oppositeIncidenceSubalgebra 𝕜 P) :=
  @Submodule.normedSpace 𝕜 𝕜 _ _ _ (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) _ _ _ _
    (oppositeIncidenceSubalgebra 𝕜 P).toSubmodule

instance (priority := 2000) oppositeIncidence_normedRing : NormedRing (oppositeIncidenceSubalgebra 𝕜 P) :=
  @Subalgebra.normedRing 𝕜 _ (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) _ _
    (oppositeIncidenceSubalgebra 𝕜 P)

instance (priority := 2000) oppositeIncidence_seminormedRing : SeminormedRing (oppositeIncidenceSubalgebra 𝕜 P) :=
  @Subalgebra.seminormedRing 𝕜 _ (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) _ _
    (oppositeIncidenceSubalgebra 𝕜 P)

instance (priority := 2000) oppositeIncidence_normedAlgebra : NormedAlgebra 𝕜 (oppositeIncidenceSubalgebra 𝕜 P) :=
  @Subalgebra.toNormedAlgebra 𝕜 (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) _ _ _
    (oppositeIncidenceSubalgebra 𝕜 P)

end Posets
