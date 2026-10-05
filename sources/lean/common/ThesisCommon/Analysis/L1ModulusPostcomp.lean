import ThesisCommon.Analysis.L1OperatorLattice
import ThesisCommon.Analysis.ALOrderCompleteness

/-! A bounded lattice homomorphism out of a real L1 space preserves the
operator modulus under postcomposition. The order-continuity needed here is
proved from norm convergence of directed positive suprema, not assumed. -/
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable {μ : Measure X} {ν : Measure Y} {η : Measure Z}

theorem lOne_positive_map_isLUB_image_of_directed
    (J : Lp ℝ 1 ν →L[ℝ] Lp ℝ 1 η) (hJ : 0 ≤ J)
    {s : Set (Lp ℝ 1 ν)} {f : Lp ℝ 1 ν} (hs : s.Nonempty)
    (hpos : ∀ g ∈ s, 0 ≤ g) (hdir : DirectedOn (· ≤ ·) s) (hf : IsLUB s f) :
    IsLUB (J '' s) (J f) := by
  have hbdd : BddAbove (norm '' s) := by
    refine ⟨‖f‖, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    exact norm_le_norm_of_abs_le_abs (by
      simpa only [abs_of_nonneg (hpos g hg),
        abs_of_nonneg ((hpos g hg).trans (hf.1 hg))] using hf.1 hg)
  obtain ⟨f', hf', u, hu, hlim, _⟩ := al_exists_isLUB_of_directed_norm_bdd
    (lOne_norm_add_of_nonneg ν) hs hpos hdir hbdd
  have heq : f' = f := hf'.unique hf
  rw [heq] at hlim
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact positive_operator_monotone hJ (hf.1 hg)
  · intro b hb
    exact le_of_tendsto' (J.continuous.tendsto f |>.comp hlim)
      (fun n => hb ⟨u n, hu n, rfl⟩)

/-- Every bounded lattice homomorphism between real L1 spaces intertwines
the actual operator modulus. Injectivity, finite measures, and topological
assumptions on the measure spaces are unnecessary. -/
theorem lOneOperatorModulus_postcomp
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (J : Lp ℝ 1 ν →L[ℝ] Lp ℝ 1 η)
    (habs : ∀ f, J |f| = |J f|) :
    lOneOperatorModulus (J.comp T) = J.comp (lOneOperatorModulus T) := by
  have hJpos : 0 ≤ J := by
    intro f hf
    have h := habs f
    rw [abs_of_nonneg hf] at h
    exact h.symm ▸ abs_nonneg (J f)
  have hpositive (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
      lOneOperatorModulus (J.comp T) f = J (lOneOperatorModulus T f) := by
    have heq : J '' modulusCandidates T f = modulusCandidates (J.comp T) f := by
      ext z
      constructor
      · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
        refine ⟨d, ?_⟩
        simp only [PositiveDecomposition.value, map_sum, habs,
          ContinuousLinearMap.comp_apply]
      · rintro ⟨d, rfl⟩
        refine ⟨d.value T, ⟨d, rfl⟩, ?_⟩
        simp only [PositiveDecomposition.value, map_sum, habs,
          ContinuousLinearMap.comp_apply]
    have hsup : IsLUB (modulusCandidates T f) (lOneOperatorModulus T f) := by
      rw [lOneOperatorModulus, operatorModulus_apply_of_nonneg _ _ _ f hf]
      exact operatorModulusPos_isLUB _ _ _ f hf
    have hsup' : IsLUB (modulusCandidates (J.comp T) f)
        (lOneOperatorModulus (J.comp T) f) := by
      rw [lOneOperatorModulus, operatorModulus_apply_of_nonneg _ _ _ f hf]
      exact operatorModulusPos_isLUB _ _ _ f hf
    have hmap := lOne_positive_map_isLUB_image_of_directed J hJpos
      (show (modulusCandidates T f).Nonempty from
        ⟨(PositiveDecomposition.single f hf).value T, ⟨_, rfl⟩⟩)
      (by rintro _ ⟨d, rfl⟩; exact d.value_nonneg T)
      (modulusCandidates_directed T f) hsup
    rw [heq] at hmap
    exact hsup'.unique hmap
  ext f
  have hdecomp : f = f⁺ - f⁻ := (posPart_sub_negPart f).symm
  rw [hdecomp, map_sub, ContinuousLinearMap.comp_apply, map_sub, map_sub,
    hpositive _ (posPart_nonneg _), hpositive _ (negPart_nonneg _)]

theorem abs_lOneOperator_postcomp
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (J : Lp ℝ 1 ν →L[ℝ] Lp ℝ 1 η)
    (habs : ∀ f, J |f| = |J f|) : |J.comp T| = J.comp |T| := by
  simpa only [abs_lOneOperator_eq] using lOneOperatorModulus_postcomp T J habs

end ThesisCommon
