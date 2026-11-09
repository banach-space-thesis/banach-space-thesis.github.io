import CKEUPFP.MainStatements
import CKEUPFP.Localization
import CKEUPFP.LocalDefectMeasurable
import CKEUPFP.ContinuousFactorSelection
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Localization and continuous factor selection on a Cantor copy

This combines the Borel localization of Section 3 with the continuous bounded
factor selection of Section 2. The hypotheses concerning the actual supplied
field are explicit. In particular, this result does not assume an atom field
exists or add a substitute for the no-`c₀` argument.
-/

noncomputable section

open Set Function Topology TopologicalSpace
open scoped NNReal

namespace CKEUPFP

/-- The paper's `Fin 2` model and the `Bool` model used in the descriptive
set-theoretic selection construction carry the same product topology. -/
def cantorBoolHomeomorph : CantorSpace ≃ₜ (ℕ → Bool) :=
  Homeomorph.piCongrRight fun _ : ℕ =>
    { toEquiv := finTwoEquiv
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

variable {𝕜 K E : Type*} [RCLike 𝕜]
  [TopologicalSpace K] [PolishSpace K] [CompactSpace K] [Uncountable K]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [SeparableSpace E]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSpace E] [BorelSpace E]

/-- A uniformly bounded, pointwise Borel field with the paper's local
smallness property admits continuous factors on an embedded Cantor set inside
one open localization set. The bound on each factor is precisely `√C`.

The actual diagonal field constructed from `T` can be substituted once its
norm bound, Borel evaluations, and local smallness have been proved. -/
theorem selected_local_factors_on_cantor
    (T : C(K, E) →L[𝕜] C(K, E)) (A : K → E →L[𝕜] E)
    {M : ℝ≥0} (hbounded : ∀ t, ‖A t‖ ≤ M)
    (hBorel : ∀ x : E, Measurable (fun t => A t x))
    (η : ℝ)
    (hsmall : ∀ t : K, ∃ U : Set K,
      IsOpen U ∧ t ∈ U ∧ localDefect T A U t < η)
    {C : ℝ} (hC : HasCPFP 𝕜 E C) :
    ∃ (O : Set K) (σ : Bool) (e : CantorSpace → K)
      (L R : CantorSpace → E →L[𝕜] E),
      IsOpen O ∧ Continuous e ∧ Function.Injective e ∧
      IsStronglyContinuous (fun t => A (e t)) ∧
      IsStronglyContinuous L ∧ IsStronglyContinuous R ∧
      (∀ t, ‖L t‖ ≤ Real.sqrt C ∧ ‖R t‖ ≤ Real.sqrt C) ∧
      (∀ t, e t ∈ O ∧ localDefect T A O (e t) ≤ η) ∧
      ∀ t, ((L t).comp (factorSelectionSide σ (A (e t)))).comp (R t) =
        ContinuousLinearMap.id 𝕜 E := by
  classical
  let Ab : K → StrongOperatorBall 𝕜 E M := fun t => ⟨A t, hbounded t⟩
  have hAb : Measurable Ab := StrongOperatorBall.measurable_iff.mpr hBorel
  have hAe (f : C(K, E)) : Measurable (fun t => A t (f t)) :=
    StrongOperatorBall.measurable_apply hAb f.continuous.measurable
  have hdefect (O : Set K) : Measurable (localDefect T A O) :=
    localDefect_measurable_of_measurable_evaluation T A hAe O
  obtain ⟨O, hO, hBmeas, hBunc⟩ :=
    localDefect_localization_of_local_smallness T A η hsmall (fun O _ => hdefect O)
  obtain ⟨e₀, he₀, he₀inj, hA₀, he₀B⟩ :=
    measurable_continuous_on_cantor_subset Ab hAb hBmeas hBunc
  have hAstrong : IsStronglyContinuous (fun t => A (e₀ t)) :=
    StrongOperatorBall.continuous_iff.mp hA₀
  letI : MetricSpace (ℕ → Bool) := PiNat.metricSpace
  letI : Uncountable (ℕ → Bool) := by
    apply uncountable_iff_forall_not_surjective.mpr
    intro f hf
    obtain ⟨n, hn⟩ := hf (fun n => !(f n n))
    have hdiag := congrFun hn n
    simp at hdiag
  obtain ⟨σ, e₁, L₁, R₁, he₁, he₁inj, hL₁, hR₁, hnorm₁, hfactor₁⟩ :=
    continuous_cp_fp_factor_selection (fun t => A (e₀ t)) hAstrong
      (fun t => hbounded (e₀ t)) hC
  let q : CantorSpace → (ℕ → Bool) := cantorBoolHomeomorph
  let e : CantorSpace → K := e₀ ∘ e₁ ∘ q
  let L : CantorSpace → E →L[𝕜] E := L₁ ∘ q
  let R : CantorSpace → E →L[𝕜] E := R₁ ∘ q
  refine ⟨O, σ, e, L, R, hO,
    he₀.comp (he₁.comp cantorBoolHomeomorph.continuous),
    he₀inj.comp (he₁inj.comp cantorBoolHomeomorph.injective),
    (fun x => (hAstrong x).comp (he₁.comp cantorBoolHomeomorph.continuous)),
    (fun x => (hL₁ x).comp cantorBoolHomeomorph.continuous),
    (fun x => (hR₁ x).comp cantorBoolHomeomorph.continuous),
    (fun t => hnorm₁ (q t)), ?_, (fun t => hfactor₁ (q t))⟩
  intro t
  have ht := he₀B (Set.mem_range_self (e₁ (q t)))
  exact ⟨ht.1, ht.2.le⟩

end CKEUPFP
