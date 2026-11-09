import BanachIsometric.LipschitzSingularCone

/-! The cone of a finite Lipschitz chain is supported on Lipschitz simplices. -/

noncomputable section
namespace BanachIsometric.SingularPrism

theorem rawLipschitzCone_preserves_lipschitz {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) : rawLipschitzCarrier V n ≤ (rawLipschitzCarrier V (n + 1)).comap (rawLipschitzCone n) := by
  conv_lhs => rw [rawLipschitzCarrier, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ, hσ, rfl⟩
  change rawLipschitzCone n (Finsupp.single σ 1) ∈ rawLipschitzCarrier V (n + 1)
  rw [rawLipschitzCone_single]
  exact Finsupp.single_mem_supported ℚ 1 (exists_lipschitz_lipschitzSingularCone n σ hσ)

end BanachIsometric.SingularPrism
