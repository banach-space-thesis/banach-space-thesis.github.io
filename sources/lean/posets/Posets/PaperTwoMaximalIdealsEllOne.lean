import JLMS.SignTreeLower
import JLMS.CZeroAdmissibility
import JLMS.CompactCZeroEquiv
import ThesisCommon.Analysis.MilutinCantorEmbedding
import ThesisCommon.Analysis.MilutinCantorExtension

/-! The interval space contains an actual bounded-below copy of ℓ¹, whereas
no continuous-function space on a scattered compactum does. This separates
the two summands in the Section 3 opening example over either scalar field. -/
noncomputable section
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

def paperCantorSign (n : ℕ) : C((ℕ → Bool), 𝕜) :=
  ⟨fun x => if x n then 1 else -1,
    (continuous_of_discreteTopology (f := fun b : Bool => if b then (1 : 𝕜) else -1)).comp
      (continuous_apply n)⟩

theorem paperCantorSign_norm_le (n : ℕ) : ‖paperCantorSign (𝕜 := 𝕜) n‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro x
  change ‖if x n then (1 : 𝕜) else -1‖ ≤ 1
  split <;> simp

theorem paper_interval_containsEllOne : JLMS.ContainsEllOne 𝕜 (IntervalContinuous 𝕜) := by
  obtain ⟨e, he⟩ := milutin_exists_interval_cantor_embedding
  let v (n : ℕ) := milutinCantorExtend (𝕜 := 𝕜) e he (paperCantorSign n)
  apply JLMS.containsEllOne_of_finiteSignTree v
  · intro n
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      ((mul_le_mul (norm_milutinCantorExtend_le e he) (paperCantorSign_norm_le n)
        (norm_nonneg _) zero_le_one).trans (by norm_num))
  · intro F σ
    refine ⟨ContinuousMap.evalCLM 𝕜 (e σ), ?_, ?_⟩
    · apply (ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        (fun f => by simpa using f.norm_coe_le_norm (e σ))).trans
      norm_num
    · intro n hn
      change ‖milutinCantorExtend e he (paperCantorSign n) (e σ) - _‖ ≤ _
      rw [milutinCantorExtend_on_image]
      simp [paperCantorSign]

theorem paper_containsEllOne_of_complemented
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (hE : JLMS.ContainsEllOne 𝕜 E) (A : E →L[𝕜] F) (B : F →L[𝕜] E)
    (hBA : B.comp A = ContinuousLinearMap.id 𝕜 E) : JLMS.ContainsEllOne 𝕜 F := by
  obtain ⟨J, c, hc, hJ⟩ := hE
  refine ⟨A.comp J, c / (‖B‖ + 1), div_pos hc (by positivity), ?_⟩
  intro x
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < ‖B‖ + 1)).mpr
  have hid : B (A (J x)) = J x := DFunLike.congr_fun hBA (J x)
  have hb := B.le_opNorm (A (J x))
  rw [hid] at hb
  simp only [ContinuousLinearMap.comp_apply]
  calc
    c * ‖x‖ ≤ ‖J x‖ := hJ x
    _ ≤ ‖B‖ * ‖A (J x)‖ := hb
    _ ≤ ‖A (J x)‖ * (‖B‖ + 1) := by nlinarith [norm_nonneg (A (J x))]

theorem paper_interval_not_complemented_in_scattered
    (K : Type*) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (hK : JLMS.IsScattered K) :
    ¬∃ A : IntervalContinuous 𝕜 →L[𝕜] C(K, 𝕜),
      ∃ B : C(K, 𝕜) →L[𝕜] IntervalContinuous 𝕜,
        B.comp A = ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜) := by
  rintro ⟨A, B, hBA⟩
  let e := JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := K)
  apply JLMS.cZero_not_containsEllOne (𝕜 := 𝕜) hK
  apply paper_containsEllOne_of_complemented paper_interval_containsEllOne
    (e.toContinuousLinearEquiv.toContinuousLinearMap.comp A)
    (B.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  apply ContinuousLinearMap.ext
  intro x
  simpa using DFunLike.congr_fun hBA x

end Posets
