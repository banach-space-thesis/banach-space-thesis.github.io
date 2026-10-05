import ThesisCommon.Analysis.GowersMaureyForms
import ThesisCommon.Analysis.GowersMaureySpace
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! Actual finitely supported norming functionals on each interval. They
are obtained from Hahn--Banach on the constructed pre-space and interval
contraction, rather than postulated as a norming-set property. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def finiteDualCoefficients (D : ConstructionData 𝕜) (E : Interval)
    (φ : PreSpace D →L[𝕜] 𝕜) : C00 𝕜 :=
  ∑ n ∈ E.set, Finsupp.single n (φ (PreSpace.single n 1))

theorem finiteDualCoefficients_apply (D : ConstructionData 𝕜) (E : Interval)
    (φ : PreSpace D →L[𝕜] 𝕜) (n : ℕ) :
    finiteDualCoefficients D E φ n = if n ∈ E.set then φ (PreSpace.single n 1) else 0 := by
  classical
  simp [finiteDualCoefficients, Finsupp.finset_sum_apply, Finsupp.single_apply, eq_comm]

theorem finiteDualCoefficients_support (D : ConstructionData 𝕜) (E : Interval)
    (φ : PreSpace D →L[𝕜] 𝕜) : (finiteDualCoefficients D E φ).support ⊆ E.set := by
  classical
  intro n hn
  by_contra he
  have h := Finsupp.mem_support_iff.mp hn
  rw [finiteDualCoefficients_apply, if_neg he] at h
  exact h rfl

theorem pairing_finiteDualCoefficients (D : ConstructionData 𝕜) (E : Interval)
    (φ : PreSpace D →L[𝕜] 𝕜) (x : C00 𝕜) :
    pairing (finiteDualCoefficients D E φ) x = φ (restrict E x) := by
  have h : pairing (finiteDualCoefficients D E φ) = φ.toLinearMap.comp (restrict E) := by
    apply Finsupp.lhom_ext
    intro n c
    change pairing (finiteDualCoefficients D E φ) (Finsupp.single n c) =
      φ (restrict E (Finsupp.single n c))
    rw [pairing_single, finiteDualCoefficients_apply, restrict_single]
    split_ifs
    · have hsingle : (Finsupp.single n c : PreSpace D) = c • PreSpace.single (D := D) n 1 := by
        change Finsupp.single n c = c • (Finsupp.single n 1 : C00 𝕜)
        simp
      rw [hsingle, map_smul]
      simp only [smul_eq_mul, mul_comm]
    · simp
  exact LinearMap.congr_fun h x

theorem finiteDualCoefficients_dualUnit (D : ConstructionData 𝕜) (E : Interval)
    (φ : PreSpace D →L[𝕜] 𝕜) (hφ : ‖φ‖ ≤ 1) :
    DualUnit (implicitNorm D) (finiteDualCoefficients D E φ) := by
  intro x
  rw [pairing_finiteDualCoefficients]
  calc
    ‖φ (restrict E x)‖ ≤ ‖φ‖ * implicitNorm D (restrict E x) := φ.le_opNorm _
    _ ≤ implicitNorm D (restrict E x) := mul_le_of_le_one_left (apply_nonneg _ _) hφ
    _ ≤ implicitNorm D x := implicitNorm_restrict_le D E x

theorem exists_finite_interval_norming (D : ConstructionData 𝕜) (E : Interval) (x : C00 𝕜) :
    ∃ a : C00 𝕜, a.support ⊆ E.set ∧ DualUnit (implicitNorm D) a ∧
      pairing a x = (implicitNorm D (restrict E x) : 𝕜) := by
  obtain ⟨φ, hφ, heq⟩ := exists_dual_vector'' 𝕜 (E := PreSpace D) (restrict E x)
  refine ⟨finiteDualCoefficients D E φ, finiteDualCoefficients_support D E φ,
    finiteDualCoefficients_dualUnit D E φ hφ, ?_⟩
  rw [pairing_finiteDualCoefficients]
  exact heq

end ThesisCommon.GowersMaurey
