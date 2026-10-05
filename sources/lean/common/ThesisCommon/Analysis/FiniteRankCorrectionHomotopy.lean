import ThesisCommon.Analysis.FiniteRankUnitClosure
import ThesisCommon.Analysis.ApproximateUnitsCorrection
import Mathlib.Topology.Connected.Clopen

/-! A connected continuous family whose members have actual closed
finite-codimensional bounded-below restrictions stays invertible up to
finite-rank correction if one member is invertible. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 X I : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [TopologicalSpace I] [PreconnectedSpace I]

theorem finiteRankInvertibleCorrection_of_connected_family
    (P : I → X →L[𝕜] X) (hP : Continuous P)
    (hlower : ∀ i, ∃ E : Submodule 𝕜 X, IsClosed (E : Set X) ∧
      FiniteDimensional 𝕜 (X ⧸ E) ∧ ∃ c : ℝ, 0<c ∧
      ∀ x : E, c*‖x.val‖ ≤ ‖P i x.val‖)
    (i₀ : I) (h₀ : IsUnit (P i₀)) :
    ∀ i, HasFiniteRankInvertibleCorrection (P i) := by
  let Q : Set I := P ⁻¹' closure {U : X →L[𝕜] X | IsUnit U}
  have hcorrect : ∀ i ∈ Q, HasFiniteRankInvertibleCorrection (P i) := by
    intro i hi
    obtain ⟨E,hE,hfd,c,hc,hb⟩ := hlower i
    letI := hfd
    letI : CompleteSpace E := hE.completeSpace_coe
    let A : E →L[𝕜] X := (P i).comp E.subtypeL
    have ha : AntilipschitzWith ⟨c⁻¹,inv_nonneg.mpr hc.le⟩ A := by
      apply A.antilipschitz_of_bound
      intro x
      have hh := mul_le_mul_of_nonneg_left (hb x) (inv_nonneg.mpr hc.le)
      simpa only [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul] using hh
    exact exists_finiteRank_invertible_correction_of_mem_closure_units
      (P i) hi E hE ha.injective (ha.isClosed_range A.uniformContinuous)
  have hcQ : IsClosed Q := isClosed_closure.preimage hP
  have hoQ : IsOpen Q := by
    rw [isOpen_iff_mem_nhds]
    intro i hi
    have hn := (isOpen_hasFiniteRankInvertibleCorrection.preimage hP).mem_nhds (hcorrect i hi)
    apply Filter.mem_of_superset hn
    intro j hj
    exact HasFiniteRankInvertibleCorrection.mem_closure_units hj
  have heq : Q = Set.univ := (show IsClopen Q from ⟨hcQ,hoQ⟩).eq_univ
    ⟨i₀,subset_closure h₀⟩
  intro i
  exact hcorrect i (heq ▸ Set.mem_univ i)

end ThesisCommon
