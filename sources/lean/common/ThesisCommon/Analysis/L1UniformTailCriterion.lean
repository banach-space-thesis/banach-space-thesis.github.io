import ThesisCommon.Analysis.L1TailProfiles

/-! Uniform integrability for actual L1 sequences can be checked on eventual
uniform tail bounds. Finite initial segments are handled by integrability. -/
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
namespace ThesisCommon
variable {𝕜 X I : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}

theorem uniformIntegrable_of_eventually_lOneTailMass [IsFiniteMeasure μ]
    (f : ℕ → Lp 𝕜 1 μ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ M N : ℕ, ∀ n ≥ N, lOneTailMass (f n) M ≤ ε) :
    UniformIntegrable (fun n => (f n : X → 𝕜)) 1 μ := by
  classical
  apply uniformIntegrable_of (by norm_num) (by norm_num)
    (fun n => Lp.aestronglyMeasurable (f n))
  intro ε hε
  obtain ⟨M, N, hMN⟩ := h ε hε
  have hfin : UniformIntegrable (fun n : Fin N => (f n : X → 𝕜)) 1 μ :=
    uniformIntegrable_finite (by norm_num) (by norm_num) (fun n => Lp.memLp (f n))
  obtain ⟨C, hC⟩ := hfin.spec (by norm_num) (by norm_num) hε
  let D : ℝ≥0 := max C ⟨(M : ℝ) + 1, by positivity⟩
  refine ⟨D, fun n => ?_⟩
  by_cases hn : n < N
  · have hsub : {x | D ≤ ‖f n x‖₊} ⊆ {x | C ≤ ‖f n x‖₊} :=
      fun x hx => le_trans (le_max_left C _) hx
    exact (eLpNorm_mono fun x => norm_indicator_le_of_subset hsub _ x).trans (hC ⟨n, hn⟩)
  · have hsub : {x | D ≤ ‖f n x‖₊} ⊆ lOneTailSet (f n) M := by
      intro x hx
      have hMD : (M : ℝ) + 1 ≤ (D : ℝ) := le_max_right _ _
      exact hMD.trans hx
    apply le_trans (eLpNorm_mono fun x => norm_indicator_le_of_subset hsub _ x)
    rw [eLpNorm_indicator_eq_ofReal_norm_lpCut _ (measurableSet_lOneTailSet _ _)]
    exact ENNReal.ofReal_le_ofReal (hMN n (Nat.le_of_not_lt hn))

theorem uniformIntegrable_lOne_of_unifIntegrable_norm_bounded
    (f : I → Lp 𝕜 1 μ) (h : UnifIntegrable (fun i => (f i : X → 𝕜)) 1 μ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) :
    UniformIntegrable (fun i => (f i : X → 𝕜)) 1 μ := by
  refine ⟨fun i => Lp.aestronglyMeasurable _, h, ⟨C, hC⟩, fun i => ?_⟩
  rw [← Lp.enorm_def, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (hf i)

theorem UniformIntegrable.lOne_ae_norm_le
    {f g : I → Lp 𝕜 1 μ} (hf : UniformIntegrable (fun i => (f i : X → 𝕜)) 1 μ)
    (hgf : ∀ i, ∀ᵐ x ∂μ, ‖g i x‖ ≤ ‖f i x‖) :
    UniformIntegrable (fun i => (g i : X → 𝕜)) 1 μ := by
  refine ⟨fun i => Lp.aestronglyMeasurable _, ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hs⟩ := hf.2.1 hε
    refine ⟨δ, hδ, fun i A hA hμA => ?_⟩
    apply le_trans (eLpNorm_mono_ae ?_) (hs i A hA hμA)
    filter_upwards [hgf i] with x hx
    by_cases hxA : x ∈ A <;> simp [hxA, hx]
  · obtain ⟨C, hC⟩ := hf.2.2
    exact ⟨C, fun i => (eLpNorm_mono_ae (hgf i)).trans (hC i)⟩

theorem UniformIntegrable.lOne_comp
    {J : Type*} {f : I → Lp 𝕜 1 μ}
    (hf : UniformIntegrable (fun i => (f i : X → 𝕜)) 1 μ) (r : J → I) :
    UniformIntegrable (fun j => (f (r j) : X → 𝕜)) 1 μ := by
  refine ⟨fun j => hf.1 _, ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hs⟩ := hf.2.1 hε
    exact ⟨δ, hδ, fun j => hs (r j)⟩
  · obtain ⟨C, hC⟩ := hf.2.2
    exact ⟨C, fun j => hC (r j)⟩

end ThesisCommon
