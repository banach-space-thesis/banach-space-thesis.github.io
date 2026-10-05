import ThesisCommon.Analysis.GowersMaureyImplicitNorm

/-! Global minimality of the implicit norm. The ℓ1 upper bound used in
the fixed-point construction does not restrict its minimality statement:
meeting any competing seminorm with the coefficient-mass seminorm gives
a bounded competitor. This is the lattice meet of seminorms, not the
pointwise minimum of their numerical values.
-/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem implicitNorm_le_of_closed (D : ConstructionData 𝕜)
    (p : Seminorm 𝕜 (C00 𝕜))
    (hclosed : ∀ q, NormTest D p q → q ≤ p) : implicitNorm D ≤ p := by
  apply (implicitNorm_minimal D (p ⊓ mass) inf_le_right ?_).trans inf_le_left
  intro q hq
  apply le_inf
  · obtain ⟨r, hr, hqr⟩ := normTest_mono D (show p ⊓ mass ≤ p from inf_le_left) hq
    exact hqr.trans (hclosed r hr)
  · exact normTest_le_mass D inf_le_right hq

end ThesisCommon.GowersMaurey
