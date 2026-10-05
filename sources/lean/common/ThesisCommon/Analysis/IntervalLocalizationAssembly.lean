import ThesisCommon.Analysis.IntervalKernelCompression
import ThesisCommon.Analysis.MilutinIntervalAssembly

/-! Assembly of the diagonal-atom localization proof, with its remaining
contractive extension dependency stated at the actual operator type. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem interval_cantor_factors_four_of_contractively_extendible
    (hext : ∀ e : C(BinaryCantorSpace, UnitInterval), Function.Injective e →
      ∃ E : CantorContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜,
        ‖E‖ ≤ 1 ∧ ∀ g x, E g (e x) = g x)
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) :
    FactorsIdentityWith T (CantorContinuous 𝕜) 4 ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜) - T)
        (CantorContinuous 𝕜) 4 := by
  obtain ⟨Q, n, f, φ, hQ, hf, hinj, hlarge, hcont, hres, hφ, hφone, hφzero⟩ :=
    intervalKernel_localization_data T
  let e : C(BinaryCantorSpace, UnitInterval) := ⟨f, hf⟩
  let a : CantorContinuous 𝕜 := ⟨fun x => intervalOperatorAtom Q (f x), hcont⟩
  obtain ⟨E, hnE, hE⟩ := hext e hinj
  have hfactor : FactorsIdentityWith Q (CantorContinuous 𝕜) 4 :=
    intervalKernel_factors_four_of_extension Q n e a (fun _ => rfl) hlarge
      φ hφ hφone hφzero hres E hnE hE
  rcases hQ with rfl | rfl
  · exact Or.inl hfactor
  · exact Or.inr hfactor

theorem interval_hasCPFP_four_of_cantor_extension
    (hext : ∀ e : C(BinaryCantorSpace, UnitInterval), Function.Injective e →
      ∃ E : CantorContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜,
        ‖E‖ ≤ 1 ∧ ∀ g x, E g (e x) = g x) :
    HasCPFP 𝕜 (IntervalContinuous 𝕜) 4 := by
  obtain ⟨q, _, A, hA, hAJ⟩ := milutin_binary_cantor_regular_averaging (𝕜 := 𝕜) UnitInterval
  intro T
  rcases interval_cantor_factors_four_of_contractively_extendible hext T with h | h
  · exact Or.inl (h.target_retract_contractively A (continuousMapPullback q)
      hA.le (norm_continuousMapPullback_le q) hAJ)
  · exact Or.inr (h.target_retract_contractively A (continuousMapPullback q)
      hA.le (norm_continuousMapPullback_le q) hAJ)

end ThesisCommon
