import ThesisCommon.Analysis.GowersMaureyRationalContractions
import ThesisCommon.Analysis.GowersMaureyLogGrowth

/-! Actual code growth under arbitrarily small rational perturbations.
The scalar contractions give distinct valid appended prefixes, so the
specified coding injection itself forces their codes to tend to infinity.
This is a consequence of ConstructionData, not an additional coding axiom. -/
noncomputable section
open Filter
open scoped Topology
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

namespace ConstructionData
variable (D : ConstructionData 𝕜) {xs : List (C00 𝕜)} (hxs : CodingDomain xs)
  {a : C00 𝕜} (ha : RationalUnitSequence a) (ha0 : a ≠ 0)
  (hbefore : ∀ b ∈ xs, Before b a)
include hxs ha ha0 hbefore

theorem sigma_rational_contractions_injective :
    Function.Injective (fun n : ℕ => D.sigma (xs ++ [(codingContraction n : 𝕜) • a])) := by
  intro m n he
  have hm := codingDomain_append_rat_smul hxs ha hbefore
    (codingContraction_pos m) (codingContraction_lt_one m).le
  have hn := codingDomain_append_rat_smul hxs ha hbefore
    (codingContraction_pos n) (codingContraction_lt_one n).le
  have hp := D.sigma_injective hm hn he
  have hs := List.singleton_injective (List.append_cancel_left hp)
  have hq := smul_left_injective 𝕜 ha0 hs
  exact codingContraction_injective (Rat.cast_injective hq)

theorem sigma_rational_contractions_tendsto_atTop :
    Tendsto (fun n : ℕ => D.sigma (xs ++ [(codingContraction n : 𝕜) • a]))
      atTop atTop :=
  (D.sigma_rational_contractions_injective hxs ha ha0 hbefore).nat_tendsto_atTop

theorem sigma_rational_contractions_weight_tendsto_atTop :
    Tendsto (fun n : ℕ => logarithmicWeight (D.sigma (xs ++ [(codingContraction n : 𝕜) • a])))
      atTop atTop :=
  tendsto_logarithmicWeight_atTop.comp (tendsto_natCast_atTop_atTop.comp
    (D.sigma_rational_contractions_tendsto_atTop hxs ha ha0 hbefore))

theorem exists_large_code_rational_contraction (p : Seminorm 𝕜 (C00 𝕜))
    {ε : ℝ} (hε : 0 < ε) (M : ℕ) (B : ℝ) :
    ∃ q : ℚ, 0 < q ∧ q < 1 ∧ 1-(q : ℝ) < ε ∧
      ((q : 𝕜) • a).support = a.support ∧
      CodingDomain (xs ++ [(q : 𝕜) • a]) ∧ p ((q : 𝕜) • a - a) < ε ∧
      M < D.sigma (xs ++ [(q : 𝕜) • a]) ∧
      B < logarithmicWeight (D.sigma (xs ++ [(q : 𝕜) • a])) := by
  have hnear : ∀ᶠ n : ℕ in atTop, 1-(codingContraction n : ℝ) < ε := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_codingContraction_real
    have hz : Tendsto (fun n : ℕ => 1-(codingContraction n : ℝ)) atTop (𝓝 0) := by
      simpa only [sub_self] using h
    exact hz.eventually_lt_const hε
  have herr := (tendsto_codingContraction_seminorm_error p a).eventually_lt_const hε
  have hcode := (D.sigma_rational_contractions_tendsto_atTop hxs ha ha0 hbefore).eventually
    (eventually_gt_atTop M)
  have hweight := (D.sigma_rational_contractions_weight_tendsto_atTop hxs ha ha0 hbefore).eventually
    (eventually_gt_atTop B)
  obtain ⟨n,hn,he,hc,hw⟩ := (hnear.and (herr.and (hcode.and hweight))).exists
  exact ⟨codingContraction n, codingContraction_pos n, codingContraction_lt_one n, hn,
    support_rat_smul_of_pos a (codingContraction_pos n),
    codingDomain_append_rat_smul hxs ha hbefore (codingContraction_pos n)
      (codingContraction_lt_one n).le, he, hc, hw⟩

end ConstructionData
end ThesisCommon.GowersMaurey
