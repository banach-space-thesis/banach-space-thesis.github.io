import ThesisCommon.Analysis.GowersMaureyConstructionHullGap
import ThesisCommon.Analysis.GowersMaureyInterpolationContact
import ThesisCommon.Analysis.GowersMaureySourceTangent

/-! The actual interpolation profile agrees with f throughout the source
gap [log(j_n), exp(j_n)]. Both finite-factor and concave-envelope stages
are evaluated from their definitions; no gap equality is assumed. -/
noncomputable section
namespace ThesisCommon.GowersMaurey.ConstructionData
variable {𝕜 : Type*} [RCLike 𝕜]

theorem interpolationProfile_eq_on_gap (D : ConstructionData 𝕜)
    (K : Set ℕ) (hK : K ⊆ D.specialSizes) (n : ℕ) (hnK : D.j n ∉ K)
    {s : ℝ} (hs : s ∈ Set.Icc (Real.log (D.j n : ℝ)) (Real.exp (D.j n : ℝ))) :
    interpolationProfile K s = logarithmicWeight s := by
  let I := Set.Icc (if n = 0 then 1 else Real.log (Real.log (D.j n : ℝ)))
    (Real.exp (Real.exp (D.j n : ℝ)))
  have hs1 : 1 ≤ s := by have hh := D.log_size_large n; linarith [hs.1]
  have hsI : s ∈ I := by
    constructor
    · by_cases hn : n = 0
      · simpa only [if_pos hn] using hs1
      · simp only [if_neg hn]
        exact (Real.log_le_self (by have hh := D.log_size_large n; linarith)).trans hs.1
    · exact hs.2.trans (Real.exp_le_exp.mpr
        (le_trans (by linarith) (Real.add_one_le_exp (D.j n : ℝ))))
  apply interpolationProfile_eq_weight_of_tangent K hs1 hsI
  · intro t ht htI
    apply D.interpolationHull_eq_on_gap K hK n hnK ht ?_ htI.2
    intro hn
    simpa only [if_neg hn] using htI.1
  · intro t ht ht1
    exact logarithmicProfileTangent_ge_identity_below_one hs1 ht1
  · intro t ht htI
    have hh := D.extended_sqrtProfile_le_tangent_outside_gap hs (zero_le_one.trans ht) htI
    rw [extendedReciprocalProfile_of_one_le (by simp [logarithmicWeight_one]) ht] at hh
    exact hh

theorem odd_size_not_special (D : ConstructionData 𝕜) (m : ℕ) :
    D.j (2 * m + 1) ∉ D.specialSizes := by
  rintro ⟨i, hi⟩
  have he := D.j_strict.injective hi
  omega

theorem interpolationProfile_eq_on_odd_gap (D : ConstructionData 𝕜) (m : ℕ)
    {s : ℝ} (hs : s ∈ Set.Icc (Real.log (D.j (2 * m + 1) : ℝ))
      (Real.exp (D.j (2 * m + 1) : ℝ))) :
    interpolationProfile D.specialSizes s = logarithmicWeight s :=
  D.interpolationProfile_eq_on_gap D.specialSizes (fun _ h => h) (2 * m + 1)
    (D.odd_size_not_special m) hs

end ThesisCommon.GowersMaurey.ConstructionData
