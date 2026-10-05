import ThesisCommon.Analysis.GowersMaureyStandardProfiles
import ThesisCommon.Analysis.GowersMaureyConstructionProfileGap

/-! Full source Lemma 6: the actual interpolation construction belongs
to the six-condition numerical class and has the specified selected-size
and gap values. This is a numerical lemma, not an operator conclusion. -/
noncomputable section
namespace ThesisCommon.GowersMaurey.ConstructionData
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_numerical_interpolating_profile (D : ConstructionData 𝕜)
    (K : Set ℕ) (hK : K ⊆ D.specialSizes) :
    ∃ g : ℝ → ℝ, IsNumericalProfile g ∧
      (∀ x, 1 ≤ x → Real.sqrt (logarithmicWeight x) ≤ g x) ∧
      (∀ k ∈ K, g (k : ℝ) = Real.sqrt (logarithmicWeight k)) ∧
      (∀ n, D.j n ∉ K → ∀ x : ℝ,
        x ∈ Set.Icc (Real.log (D.j n : ℝ)) (Real.exp (D.j n : ℝ)) →
          g x = logarithmicWeight x) := by
  refine ⟨interpolationProfile K, interpolationProfile_isNumericalProfile K,
    (fun _ hx => interpolationProfile_ge_sqrt K hx), ?_, ?_⟩
  · intro k hk
    exact interpolationProfile_at_selected_size K (D.specialSize_pos (hK hk)) hk
  · intro n hn x hx
    exact D.interpolationProfile_eq_on_gap K hK n hn hx

end ThesisCommon.GowersMaurey.ConstructionData
