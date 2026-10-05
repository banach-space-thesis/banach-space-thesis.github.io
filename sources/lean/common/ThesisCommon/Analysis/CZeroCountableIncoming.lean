import ThesisCommon.Analysis.CZeroArbitrarySingles
import ThesisCommon.Analysis.SublinearFibreSupport
import ThesisCommon.Analysis.CountableCoordinateSupport
import ThesisCommon.Analysis.SeparableTotalDual

/-! Incoming and outgoing support for actual arbitrary-index c0 maps.
The incoming scalar argument uses the bound one for disjoint unit fibres,
and a countable total dual set detects all vector-valued coordinate maps. -/
noncomputable section
open TopologicalSpace
open scoped ZeroAtInfty
namespace ThesisCommon
variable {𝕜 Γ X Y : Type*} [RCLike 𝕜]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem cZero_singleAt_growth (M : ℝ) (_hM : 0 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, M * 1 < n * ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (M / ε)
  exact ⟨n, by simpa only [mul_one] using (div_lt_iff₀ hε).mp hn⟩

theorem cZero_countable_incoming_fibres (htotal : HasCountableTotalDual 𝕜 Y)
    (T : C₀(Γ, X) →L[𝕜] Y) : {α | T.comp (cZeroSingleAtL α) ≠ 0}.Countable := by
  apply operator_countable_fibre_support (fun α => cZeroSingleAtL (𝕜 := 𝕜) α)
    (fun _ => 1) ?_ cZero_singleAt_growth htotal T
  intro n e x hx
  simpa only [cZeroSingleAtL_apply] using cZero_singleAt_finite_norm_bound (𝕜 := 𝕜) e x hx

def cZeroFibreRelation (T : C₀(Γ, X) →L[𝕜] C₀(Γ, X)) (α β : Γ) : Prop :=
  ((cZeroCoordinate (𝕜 := 𝕜) β).comp T).comp (cZeroSingleAtL α) ≠ 0

theorem cZeroFibreRelation_outgoing_countable [SeparableSpace X]
    (T : C₀(Γ, X) →L[𝕜] C₀(Γ, X)) (α : Γ) :
    {β | cZeroFibreRelation T α β}.Countable := by
  obtain ⟨S, hS, hT⟩ := cZero_operator_countable_support (T.comp (cZeroSingleAtL α))
  apply hS.mono
  intro β hβ
  by_contra hβS
  apply hβ
  apply ContinuousLinearMap.ext
  intro x
  change T (cZeroSingleAt α x) β = 0
  by_contra hn
  exact hβS (hT x hn)

theorem cZeroFibreRelation_incoming_countable [SeparableSpace X]
    (T : C₀(Γ, X) →L[𝕜] C₀(Γ, X)) (β : Γ) :
    {α | cZeroFibreRelation T α β}.Countable :=
  cZero_countable_incoming_fibres (hasCountableTotalDual_of_separable 𝕜 X)
    ((cZeroCoordinate β).comp T)

theorem cZeroFibreRelation_zero (T : C₀(Γ, X) →L[𝕜] C₀(Γ, X)) {α β : Γ}
    (h : ¬ cZeroFibreRelation T α β) (x : X) : T (cZeroSingleAt α x) β = 0 :=
  DFunLike.congr_fun (not_not.mp h) x

end ThesisCommon
