import ThesisCommon.Analysis.JamesInitialTruncations
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Concrete finite James blocks, with the inherited variation norm. A
block is supported strictly between its two zero boundary coordinates. -/
noncomputable section
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)

def jamesIntervalSubmodule (lo hi : ℕ) : Submodule 𝕜 (JamesSequenceSpace 𝕜 p) where
  carrier := {x | ∀ n, n ≤ lo ∨ hi ≤ n → x n = 0}
  zero_mem' := by simp
  add_mem' hx hy := by intro n hn; simp only [JamesSequenceSpace.add_apply, hx n hn, hy n hn, add_zero]
  smul_mem' a x hx := by intro n hn; simp only [JamesSequenceSpace.smul_apply, hx n hn, smul_zero]

abbrev JamesIntervalBlock (lo hi : ℕ) := ↥(jamesIntervalSubmodule 𝕜 p lo hi)

instance jamesIntervalBlock_normedAddCommGroup (lo hi : ℕ) :
    NormedAddCommGroup (JamesIntervalBlock 𝕜 p lo hi) :=
  inferInstanceAs (NormedAddCommGroup ↥(jamesIntervalSubmodule 𝕜 p lo hi))

instance jamesIntervalBlock_normedSpace (lo hi : ℕ) :
    NormedSpace 𝕜 (JamesIntervalBlock 𝕜 p lo hi) :=
  inferInstanceAs (NormedSpace 𝕜 ↥(jamesIntervalSubmodule 𝕜 p lo hi))

theorem jamesIntervalSubmodule_isClosed (lo hi : ℕ) :
    IsClosed (jamesIntervalSubmodule 𝕜 p lo hi : Set (JamesSequenceSpace 𝕜 p)) := by
  change IsClosed {x : JamesSequenceSpace 𝕜 p |
    ∀ n, n ≤ lo ∨ hi ≤ n → JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) n x = 0}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun n => isClosed_iInter fun _ =>
    isClosed_eq (JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) n).continuous continuous_const

instance jamesIntervalBlock_completeSpace (lo hi : ℕ) :
    CompleteSpace (JamesIntervalBlock 𝕜 p lo hi) :=
  (jamesIntervalSubmodule_isClosed 𝕜 p lo hi).completeSpace_coe

instance jamesIntervalBlock_finiteDimensional (lo hi : ℕ) :
    FiniteDimensional 𝕜 (JamesIntervalBlock 𝕜 p lo hi) := by
  let R : JamesIntervalBlock 𝕜 p lo hi →ₗ[𝕜] (Fin hi → 𝕜) :=
    LinearMap.pi fun n => (JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) n.val).toLinearMap.comp
      (jamesIntervalSubmodule 𝕜 p lo hi).subtype
  apply FiniteDimensional.of_injective R
  intro x y hxy
  apply Subtype.ext
  apply JamesSequenceSpace.ext
  intro n
  by_cases hn : n < hi
  · exact congrFun hxy ⟨n, hn⟩
  · rw [x.property n (Or.inr (le_of_not_gt hn)), y.property n (Or.inr (le_of_not_gt hn))]

end ThesisCommon
