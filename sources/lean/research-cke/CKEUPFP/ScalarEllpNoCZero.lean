import CKEUPFP.ScalarLpCounting
import CKEUPFP.ScalarLpNoCZero

/-! Scalar ℓp contains no isomorphic copy of c₀ for every finite Banach
exponent. The proof uses the actual counting-measure Lp isometric embedding.
-/

noncomputable section

namespace CKEUPFP

variable {𝕜 : Type*} [RCLike 𝕜]

theorem scalarEllp_containsNoCZero (p : FiniteBanachExponent) :
    ContainsNoCZero 𝕜 (ScalarEllp 𝕜 p) :=
  containsNoCZero_scalarEllp_of_countingLp p (scalarLp_containsNoCZero p.property.2.ne)

end CKEUPFP
