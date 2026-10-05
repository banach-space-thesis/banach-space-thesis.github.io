import ThesisCommon.Analysis.ComplexL1Coordinates

/-! A countable dense set of constant phases recovers a complex pointwise
norm bound almost everywhere. No measurability hypotheses on the functions
are needed; the hypotheses already supply the a.e. phase bounds. -/
noncomputable section
open MeasureTheory Filter Set
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem complex_norm_le_of_phase_ae {f : X → ℂ} {g : X → ℝ}
    (h : ∀ c : ℂ, ‖c‖ = 1 → ∀ᵐ x ∂μ, (c*f x).re ≤ g x) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ g x := by
  letI : SecondCountableTopology {c : ℂ // ‖c‖ = 1} :=
    TopologicalSpace.Subtype.secondCountableTopology {c : ℂ | ‖c‖ = 1}
  obtain ⟨s,hs,hd⟩ := TopologicalSpace.exists_countable_dense {c : ℂ // ‖c‖ = 1}
  have hae : ∀ c ∈ s, ∀ᵐ x ∂μ, ((c : ℂ)*f x).re ≤ g x := fun c _ => h c.val c.property
  filter_upwards [(ae_ball_iff hs).mpr hae] with x hx
  have hall : ∀ c : {c : ℂ // ‖c‖ = 1}, ((c : ℂ)*f x).re ≤ g x := by
    have hclosed : IsClosed {c : {c : ℂ // ‖c‖ = 1} | ((c : ℂ)*f x).re ≤ g x} :=
      isClosed_le (Complex.continuous_re.comp (continuous_subtype_val.mul continuous_const)) continuous_const
    have hsub := closure_minimal hx hclosed
    rw [hd.closure_eq] at hsub
    exact fun c => hsub (Set.mem_univ c)
  obtain ⟨c,hc,he⟩ := Complex.exists_norm_eq_mul_self (f x)
  have ht := hall ⟨c,hc⟩
  rw [← he] at ht
  exact ht

end ThesisCommon
