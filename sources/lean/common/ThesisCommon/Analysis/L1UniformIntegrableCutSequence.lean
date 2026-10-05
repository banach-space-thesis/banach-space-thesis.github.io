import ThesisCommon.Analysis.RCLikeL1CutIdentities

/-! Quantitative consequences of uniform integrability for moving L1 cuts. -/
noncomputable section
open MeasureTheory Set Filter Topology Function
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}

theorem measure_disjoint_sequence_tendsto_zero [IsFiniteMeasure μ]
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A)) : Tendsto (fun n => μ (A n)) atTop (𝓝 0) := by
  have htail := tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint (μ := μ)
    (fun n => (hA n).nullMeasurableSet) hd
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => bot_le) (fun n => measure_mono ?_)
  exact subset_iUnion₂_of_subset n le_rfl Subset.rfl

theorem UnifIntegrable.tendsto_norm_lOneCut
    (f : ℕ → Lp 𝕜 1 μ) (hf : UnifIntegrable (fun n => (f n : X → 𝕜)) 1 μ)
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hmass : Tendsto (fun n => μ (A n)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖lpCut (A n) (hA n) (f n)‖) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (norm_nonneg _)
  · intro ε hε
    obtain ⟨δ, hδ, hcut⟩ := hf (half_pos hε)
    filter_upwards [hmass.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ))] with n hn
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcut n (A n) (hA n) hn.le)
    rw [ENNReal.toReal_ofReal (half_pos hε).le] at hh
    have hnorm : ‖lpCut (A n) (hA n) (f n)‖ ≤ ε / 2 := by
      simpa only [lpCut, Lp.norm_toLp] using hh
    linarith

theorem norm_lOne_add_of_ae_disjoint (f g : Lp 𝕜 1 μ)
    (hd : ∀ᵐ x ∂μ, f x = 0 ∨ g x = 0) : ‖f + g‖ = ‖f‖ + ‖g‖ := by
  simp only [L1.norm_eq_integral_norm]
  rw [← integral_add (L1.integrable_coeFn f).norm (L1.integrable_coeFn g).norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f g, hd] with x hx hd
  rw [hx]
  rcases hd with h | h <;> simp [h]

end ThesisCommon
