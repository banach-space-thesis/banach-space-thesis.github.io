import ThesisCommon.Analysis.JamesBlockKernel
import ThesisCommon.Analysis.JamesInitialBlocks
import ThesisCommon.Analysis.LpFamilyDiagonal

/-! James space absorbs the actual lp-sum of any sequence of its finite
initial sections. No isomorphism or primariness hypothesis is assumed. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

def jamesBlockEndpoints (lengths : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => jamesBlockEndpoints lengths n + 1 + lengths n

@[simp] theorem jamesBlockEndpoints_zero (lengths : ℕ → ℕ) :
    jamesBlockEndpoints lengths 0 = 0 := rfl

@[simp] theorem jamesBlockEndpoints_succ (lengths : ℕ → ℕ) (n : ℕ) :
    jamesBlockEndpoints lengths (n + 1) = jamesBlockEndpoints lengths n + 1 + lengths n := rfl

theorem jamesBlockEndpoints_strict (lengths : ℕ → ℕ) : StrictMono (jamesBlockEndpoints lengths) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [jamesBlockEndpoints_succ]
  omega

abbrev JamesFiniteSectionSum (lengths : ℕ → ℕ) := lp (fun n => JamesInitialBlock 𝕜 p (lengths n)) p.val

def jamesFiniteSectionSumEquivBlocks (lengths : ℕ → ℕ) :
    JamesFiniteSectionSum (𝕜 := 𝕜) p lengths ≃L[𝕜]
      JamesBlockSum (𝕜 := 𝕜) p (jamesBlockEndpoints lengths) :=
  lpFamilyMapEquiv
    (fun n => jamesInitialBlockEquiv (𝕜 := 𝕜) p hp (jamesBlockEndpoints lengths n) (lengths n))
    2 1 (by norm_num) zero_le_one
    (fun n => jamesInitialBlockInsert_norm_le p hp (jamesBlockEndpoints lengths n) (lengths n))
    (fun n => jamesInitialBlockRead_norm_le p hp (jamesBlockEndpoints lengths n) (lengths n))

theorem jamesFiniteSectionSumEquivBlocks_norm_le (lengths : ℕ → ℕ) :
    ‖(jamesFiniteSectionSumEquivBlocks (𝕜 := 𝕜) p hp lengths).toContinuousLinearMap‖ ≤ 2 :=
  lpFamilyMapEquiv_norm_le _ _ _ _ _ _ _

theorem jamesFiniteSectionSumEquivBlocks_symm_norm_le (lengths : ℕ → ℕ) :
    ‖(jamesFiniteSectionSumEquivBlocks (𝕜 := 𝕜) p hp lengths).symm.toContinuousLinearMap‖ ≤ 1 :=
  lpFamilyMapEquiv_symm_norm_le _ _ _ _ _ _ _

/-- Genuine finite-section absorption for every finite exponent at least one,
over both real and complex scalars. Zero-dimensional sections are allowed. -/
def jamesFiniteSectionAbsorption (lengths : ℕ → ℕ) :
    JamesSequenceSpace 𝕜 p ≃L[𝕜]
      JamesSequenceSpace 𝕜 p × JamesFiniteSectionSum (𝕜 := 𝕜) p lengths :=
  (jamesBlockDecomposition (𝕜 := 𝕜) p hp (jamesBlockEndpoints lengths)
    (jamesBlockEndpoints_strict lengths) rfl).trans
      ((ContinuousLinearEquiv.refl 𝕜 (JamesSequenceSpace 𝕜 p)).prodCongr
        (jamesFiniteSectionSumEquivBlocks (𝕜 := 𝕜) p hp lengths).symm)

/-- The universal sum of the first n+1 James unit vectors. -/
abbrev JamesUniversalFiniteSum := JamesFiniteSectionSum (𝕜 := 𝕜) p (fun n => n + 1)

def jamesUniversalFiniteSumAbsorption : JamesSequenceSpace 𝕜 p ≃L[𝕜]
    JamesSequenceSpace 𝕜 p × JamesUniversalFiniteSum (𝕜 := 𝕜) p :=
  jamesFiniteSectionAbsorption p hp (fun n => n + 1)

end ThesisCommon
