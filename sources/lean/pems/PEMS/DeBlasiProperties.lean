import PEMS.Definitions
import ThesisCommon.Analysis.WeakEssentialNormProperties

/-! Elementary estimates for the actual De Blasi measure defined by weakly
compact approximating sets. No sequential compactness criterion is assumed. -/
noncomputable section
open Set Topology ThesisCommon
namespace PEMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem deBlasiSet_nonneg (A : Set E) : 0 ≤ deBlasiSet (𝕜 := 𝕜) A := by
  unfold deBlasiSet
  by_cases h : {ε : ℝ | 0 < ε ∧ ∃ D : Set E, IsCompact (toWeakSpace 𝕜 E '' D) ∧
    ∀ x ∈ A, ∃ y ∈ D, ‖x - y‖ ≤ ε}.Nonempty
  · exact le_csInf h (fun ε hε => hε.1.le)
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

theorem deBlasiSet_le_of_approximation (A D : Set E) {ε : ℝ} (hε : 0 < ε)
    (hD : IsCompact (toWeakSpace 𝕜 E '' D))
    (h : ∀ x ∈ A, ∃ y ∈ D, ‖x - y‖ ≤ ε) : deBlasiSet (𝕜 := 𝕜) A ≤ ε := by
  exact csInf_le ⟨0, fun _ hr => hr.1.le⟩ ⟨hε, D, hD, h⟩

theorem deBlasiSet_le_of_bound (A : Set E) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ x ∈ A, ‖x‖ ≤ R) : deBlasiSet (𝕜 := 𝕜) A ≤ R := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  apply deBlasiSet_le_of_approximation A {0} (by positivity)
  · simpa using (isCompact_singleton : IsCompact ({0} : Set (WeakSpace 𝕜 E)))
  · intro x hx
    exact ⟨0, by simp, by simpa using (h x hx).trans (by linarith : R ≤ R + δ)⟩

theorem deBlasiOperator_nonneg (T : E →L[𝕜] F) : 0 ≤ deBlasiOperator T :=
  deBlasiSet_nonneg _

theorem deBlasiOperator_le_norm_sub (T W : E →L[𝕜] F)
    (hW : IsWeaklyCompactOperator W) : deBlasiOperator T ≤ ‖T - W‖ := by
  obtain ⟨K, hK, hWK⟩ := hW
  let D : Set F := (toWeakSpace 𝕜 F) ⁻¹' K
  have hD : IsCompact (toWeakSpace 𝕜 F '' D) := by
    simpa only [D, Set.image_preimage_eq _ (toWeakSpace 𝕜 F).surjective] using hK
  apply le_of_forall_pos_le_add
  intro δ hδ
  apply deBlasiSet_le_of_approximation _ D (by positivity) hD
  rintro _ ⟨x, hx, rfl⟩
  have hx' : ‖x‖ ≤ 1 := by simpa using hx
  refine ⟨W x, hWK x hx', ?_⟩
  calc
    ‖T x - W x‖ = ‖(T - W) x‖ := rfl
    _ ≤ ‖T - W‖ * ‖x‖ := (T - W).le_opNorm x
    _ ≤ ‖T - W‖ := mul_le_of_le_one_right (norm_nonneg _) hx'
    _ ≤ ‖T - W‖ + δ := by linarith

theorem deBlasiOperator_le_weakEssentialNorm (T : E →L[𝕜] F) :
    deBlasiOperator T ≤ weakEssentialNorm T := by
  apply le_csInf
  · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, rfl⟩
  · rintro r ⟨W, hW, rfl⟩
    exact deBlasiOperator_le_norm_sub T W hW

theorem deBlasiOperator_le_norm (T : E →L[𝕜] F) : deBlasiOperator T ≤ ‖T‖ :=
  (deBlasiOperator_le_weakEssentialNorm T).trans (weakEssentialNorm_le_norm T)

theorem deBlasiOperator_eq_zero_of_weaklyCompact (T : E →L[𝕜] F)
    (hT : IsWeaklyCompactOperator T) : deBlasiOperator T = 0 := by
  apply le_antisymm _ (deBlasiOperator_nonneg T)
  simpa using deBlasiOperator_le_norm_sub T T hT

end PEMS
