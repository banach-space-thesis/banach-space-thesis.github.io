import ThesisCommon.Analysis.GowersMaureySpreadLaurentReduction

/-! Completion of actual finite-spread approximations in the block seminorm.
The approximation premise is explicit: its assertion for arbitrary operators
is the still separate content of the source's operator approximation lemmas.
No multiplication assertion about unilateral Laurent operators is made. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The genuine finite-spread approximation conclusion needed from Lemmas 8–9. -/
def IsFiniteSpreadApproximable (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ s : Finset (ℕ × ℕ), ∃ c : ℕ × ℕ → 𝕜,
    spaceOperatorSeminorm D
      (T - ∑ z ∈ s, c z • completedSpread D z.1 z.2) < ε

theorem IsFiniteSpreadApproximable.wiener_approximation
    {D : ConstructionData 𝕜} {T : ShiftSpace D →L[𝕜] ShiftSpace D}
    (hT : IsFiniteSpreadApproximable D T) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : WienerSequences 𝕜,
      spaceOperatorSeminorm D (T - laurentOperator D a) < ε := by
  classical
  obtain ⟨s, c, h⟩ := hT ε hε
  refine ⟨∑ z ∈ s, lp.single 1 ((z.2 : ℤ) - z.1) (c z), ?_⟩
  have he := spaceOperatorSeminorm_finite_spreads_sub_laurent D s c
  have hdiff : spaceOperatorSeminorm D
      ((T - laurentOperator D (∑ z ∈ s, lp.single 1 ((z.2 : ℤ) - z.1) (c z))) -
        (T - ∑ z ∈ s, c z • completedSpread D z.1 z.2)) = 0 := by
    convert he using 1
    congr 1
    abel
  rwa [spaceOperatorSeminorm_eq_of_sub_eq_zero D hdiff]

theorem wiener_distance_le_approximation_errors (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (a b : WienerSequences 𝕜) :
    ‖a - b‖ ≤ spaceOperatorSeminorm D (T - laurentOperator D a) +
      spaceOperatorSeminorm D (T - laurentOperator D b) := by
  rw [← spaceOperatorSeminorm_laurentOperator D (a-b), map_sub]
  have he : laurentOperator D a - laurentOperator D b =
      (T - laurentOperator D b) - (T - laurentOperator D a) := by abel
  rw [he]
  exact (map_sub_le_add (spaceOperatorSeminorm D) _ _).trans_eq (add_comm _ _)

theorem wiener_representative_unique (D : ConstructionData 𝕜)
    {T : ShiftSpace D →L[𝕜] ShiftSpace D} {a b : WienerSequences 𝕜}
    (ha : spaceOperatorSeminorm D (T - laurentOperator D a) = 0)
    (hb : spaceOperatorSeminorm D (T - laurentOperator D b) = 0) : a = b := by
  have h := wiener_distance_le_approximation_errors D T a b
  rw [ha, hb, zero_add] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

theorem wiener_representative_norm (D : ConstructionData 𝕜)
    {T : ShiftSpace D →L[𝕜] ShiftSpace D} {a : WienerSequences 𝕜}
    (ha : spaceOperatorSeminorm D (T - laurentOperator D a) = 0) :
    ‖a‖ = spaceOperatorSeminorm D T := by
  rw [spaceOperatorSeminorm_eq_of_sub_eq_zero D ha, spaceOperatorSeminorm_laurentOperator]

/-- Completeness of the literal Wiener sequence space turns arbitrary-accuracy
Laurent approximations into an exact, unique representative modulo the seminorm. -/
theorem exists_unique_wiener_representative_of_approximation
    (D : ConstructionData 𝕜) (T : ShiftSpace D →L[𝕜] ShiftSpace D)
    (hT : ∀ ε : ℝ, 0 < ε → ∃ a : WienerSequences 𝕜,
      spaceOperatorSeminorm D (T - laurentOperator D a) < ε) :
    ∃! a : WienerSequences 𝕜,
      spaceOperatorSeminorm D (T - laurentOperator D a) = 0 := by
  choose a ha using (fun n : ℕ => hT (1 / ((n : ℝ) + 1)) (by positivity))
  have hc : CauchySeq a := by
    apply cauchySeq_of_le_tendsto_0 (fun N : ℕ =>
      1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1))
    · intro n m N hn hm
      rw [dist_eq_norm]
      apply (wiener_distance_le_approximation_errors D T (a n) (a m)).trans
      apply add_le_add
      · exact (ha n).le.trans (one_div_le_one_div_of_le (by positivity)
          (by exact_mod_cast Nat.add_le_add_right hn 1))
      · exact (ha m).le.trans (one_div_le_one_div_of_le (by positivity)
          (by exact_mod_cast Nat.add_le_add_right hm 1))
    · simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.add
        tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hc
  have hlim : Tendsto (fun n => spaceOperatorSeminorm D (T - laurentOperator D (a n)))
      atTop (𝓝 (spaceOperatorSeminorm D (T - laurentOperator D b))) :=
    (spaceOperatorSeminorm_continuous D).continuousAt.tendsto.comp
      (tendsto_const_nhds.sub ((laurentOperator D).continuous.continuousAt.tendsto.comp hb))
  have hzero : spaceOperatorSeminorm D (T - laurentOperator D b) = 0 := by
    apply le_antisymm _ (apply_nonneg _ _)
    exact le_of_tendsto_of_tendsto' hlim tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n => (ha n).le)
  exact ⟨b, hzero, fun c hc => wiener_representative_unique D hc hzero⟩

theorem IsFiniteSpreadApproximable.exists_unique_wiener_representative
    {D : ConstructionData 𝕜} {T : ShiftSpace D →L[𝕜] ShiftSpace D}
    (hT : IsFiniteSpreadApproximable D T) :
    ∃! a : WienerSequences 𝕜,
      spaceOperatorSeminorm D (T - laurentOperator D a) = 0 :=
  exists_unique_wiener_representative_of_approximation D T
    (fun _ hε => hT.wiener_approximation hε)

end ThesisCommon.GowersMaurey
