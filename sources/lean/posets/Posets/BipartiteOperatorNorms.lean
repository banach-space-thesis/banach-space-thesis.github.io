import Posets.BipartiteOperatorBlocks

/-! Explicit inherited structures on the actual complete bipartite incidence algebra. -/
noncomputable section
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜] (P Q : Type*)

instance (priority := 4000) bipartite_normedAddCommGroup :
    NormedAddCommGroup (BipartiteAlgebra 𝕜 P Q) :=
  @Submodule.normedAddCommGroup 𝕜 (CZeroOn 𝕜 (P ⊕ Q) →L[𝕜] CZeroOn 𝕜 (P ⊕ Q)) _ _ _
    (BipartiteAlgebra 𝕜 P Q).toSubmodule
instance (priority := 4000) bipartite_seminormedAddCommGroup :
    SeminormedAddCommGroup (BipartiteAlgebra 𝕜 P Q) :=
  @Submodule.seminormedAddCommGroup 𝕜 (CZeroOn 𝕜 (P ⊕ Q) →L[𝕜] CZeroOn 𝕜 (P ⊕ Q)) _ _ _
    (BipartiteAlgebra 𝕜 P Q).toSubmodule
instance (priority := 4000) bipartite_normedSpace :
    NormedSpace 𝕜 (BipartiteAlgebra 𝕜 P Q) :=
  @Submodule.normedSpace 𝕜 𝕜 _ _ _ (CZeroOn 𝕜 (P ⊕ Q) →L[𝕜] CZeroOn 𝕜 (P ⊕ Q)) _ _ _ _
    (BipartiteAlgebra 𝕜 P Q).toSubmodule
instance (priority := 4000) bipartite_normedRing : NormedRing (BipartiteAlgebra 𝕜 P Q) :=
  @Subalgebra.normedRing 𝕜 _ (CZeroOn 𝕜 (P ⊕ Q) →L[𝕜] CZeroOn 𝕜 (P ⊕ Q)) _ _
    (BipartiteAlgebra 𝕜 P Q)
instance (priority := 4000) bipartite_seminormedRing : SeminormedRing (BipartiteAlgebra 𝕜 P Q) :=
  @Subalgebra.seminormedRing 𝕜 _ (CZeroOn 𝕜 (P ⊕ Q) →L[𝕜] CZeroOn 𝕜 (P ⊕ Q)) _ _
    (BipartiteAlgebra 𝕜 P Q)
instance (priority := 4000) bipartite_normedAlgebra : NormedAlgebra 𝕜 (BipartiteAlgebra 𝕜 P Q) :=
  @Subalgebra.toNormedAlgebra 𝕜 (CZeroOn 𝕜 (P ⊕ Q) →L[𝕜] CZeroOn 𝕜 (P ⊕ Q)) _ _ _
    (BipartiteAlgebra 𝕜 P Q)

local instance normsCompleteBipartiteOrder : PartialOrder (P ⊕ Q) := completeBipartiteOrder
instance (priority := 5000) bipartite_mul : Mul (BipartiteAlgebra 𝕜 P Q) :=
  ⟨fun T S => ⟨T.val * S.val, incidenceOperators_mul T.property S.property⟩⟩

end Posets


