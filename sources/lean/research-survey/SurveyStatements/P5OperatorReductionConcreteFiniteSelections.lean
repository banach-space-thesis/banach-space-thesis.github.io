import SurveyStatements.P5OperatorReductionConcreteOuterErrorLists
import SurveyStatements.P5OperatorReductionConcretePointMoments
import SurveyStatements.P5OperatorReductionConcreteBalanceMoments
import SurveyStatements.P5OperatorReductionConcreteEntryBirthMoments
import SurveyStatements.P5OperatorReductionOuterTraceBirthMoments
import SurveyStatements.P5OperatorReductionInnerTraceBirthMoments
import SurveyStatements.P5OperatorReductionBornPairMoments

/-! All finite selection premises are discharged for the actual mixed
operator and its two actual trace families. No analytic selection premise
is imposed on the arbitrary operator. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem concrete_inner_error_moment_tendsto_zero (p : BanachExponent)
    (hp : p.val ≠ ∞) (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (r : ℕ → ℕ) (hr : StrictMono r) (a : UniversalInnerPairRegisteredTraces p T r)
    (n : ℕ) (ho hi : Fin n → LpHaarFiniteSplit) (P : LpHaarFiniteParent)
    (v : InnerFiniteErrorIndex n) :
    Tendsto (fun m => mean (fun θ : Fin (2 ^ m) → Bool =>
      ‖concreteInnerError p T (actualNormalizedOuterTrace p T a)
        (actualNormalizedInnerTrace p T) ho hi v (candidateRefinedSplit P m θ)‖ ^ 2))
      atTop (𝓝 0) := by
  rcases v with v | v
  · exact concrete_inner_point_moment_tendsto_zero p T (ho v.val.1) (ho v.val.2) P
  rcases v with v | v
  · exact actualNormalizedInnerTrace_balance_moment_tendsto_zero p T
      (ho v.1.val.1, ho v.1.val.2) P v.2
  rcases v with v | v
  · exact born_pair_moment_tendsto_zero
      (fun J L => concreteMixedEntry p T (ho v.2) J (ho v.2) L) hi P
      (fun j => concrete_entry_inner_target_moment_tendsto_zero p T (ho v.2) (ho v.2) (hi j) P)
      (fun j => concrete_entry_inner_source_moment_tendsto_zero p T (ho v.2) (hi j) (ho v.2) P)
      v.1
  rcases v with v | v
  · exact born_pair_moment_tendsto_zero
      (fun J L => actualNormalizedOuterTrace p T a (J, L) (ho v.2).parent) hi P
      (fun j => actualNormalizedOuterTrace_birth_target_moment_tendsto_zero
        p hp T r hr a (ho v.2).parent P (hi j))
      (fun j => actualNormalizedOuterTrace_birth_source_moment_tendsto_zero
        p hp T r hr a (ho v.2).parent P (hi j)) v.1
  rcases v with v | v
  · exact born_pair_moment_tendsto_zero
      (fun J L => actualNormalizedOuterTrace p T a (J, L) ((ho v.1.2).child v.2)) hi P
      (fun j => actualNormalizedOuterTrace_birth_target_moment_tendsto_zero
        p hp T r hr a ((ho v.1.2).child v.2) P (hi j))
      (fun j => actualNormalizedOuterTrace_birth_source_moment_tendsto_zero
        p hp T r hr a ((ho v.1.2).child v.2) P (hi j)) v.1.1
  · exact born_pair_moment_tendsto_zero
      (fun J L => concreteMixedEntry p T (ho v.1.val.1) J (ho v.1.val.2) L) hi P
      (fun j => concrete_entry_inner_target_moment_tendsto_zero
        p T (ho v.1.val.1) (ho v.1.val.2) (hi j) P)
      (fun j => concrete_entry_inner_source_moment_tendsto_zero
        p T (ho v.1.val.1) (hi j) (ho v.1.val.2) P) v.2

theorem concrete_outer_error_moment_tendsto_zero (p : BanachExponent)
    (hp : p.val ≠ ∞) (hp1 : 1 < p.val)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (r : ℕ → ℕ) (hr : StrictMono r) (a : UniversalInnerPairRegisteredTraces p T r)
    (n : ℕ) (ho : Fin n → LpHaarFiniteSplit) (hi : Fin (n + 1) → LpHaarFiniteSplit)
    (P : LpHaarFiniteParent) (v : OuterFiniteErrorIndex n) :
    Tendsto (fun m => mean (fun θ : Fin (2 ^ r m) → Bool =>
      ‖concreteOuterError p T (actualNormalizedOuterTrace p T a)
        (actualNormalizedInnerTrace p T) ho hi v (candidateRefinedSplit P (r m) θ)‖ ^ 2))
      atTop (𝓝 0) := by
  rcases v with v | v
  · exact concrete_outer_point_moment_tendsto_zero p hp hp1 T r hr a
      (hi v.val.1) (hi v.val.2) P
  rcases v with v | v
  · exact (actualNormalizedOuterTrace_balance_moment_tendsto_zero p T a
      (hi v.1.val.1, hi v.1.val.2) P v.2).comp hr.tendsto_atTop
  rcases v with v | v
  · exact (born_pair_moment_tendsto_zero
      (fun I K => concreteMixedEntry p T I (hi v.2) K (hi v.2)) ho P
      (fun j => concrete_entry_outer_target_moment_tendsto_zero p T (hi v.2) (ho j) (hi v.2) P)
      (fun j => concrete_entry_outer_source_moment_tendsto_zero p hp T (ho j) (hi v.2) (hi v.2) P)
      v.1).comp hr.tendsto_atTop
  rcases v with v | v
  · exact (born_pair_moment_tendsto_zero
      (fun I K => actualNormalizedInnerTrace p T (I, K) (hi v.2).parent) ho P
      (fun j => actualNormalizedInnerTrace_birth_target_moment_tendsto_zero
        p hp hp1 T (hi v.2).parent P (ho j))
      (fun j => actualNormalizedInnerTrace_birth_source_moment_tendsto_zero
        p hp T (hi v.2).parent P (ho j)) v.1).comp hr.tendsto_atTop
  rcases v with v | v
  · exact (born_pair_moment_tendsto_zero
      (fun I K => actualNormalizedInnerTrace p T (I, K) ((hi v.1.2).child v.2)) ho P
      (fun j => actualNormalizedInnerTrace_birth_target_moment_tendsto_zero
        p hp hp1 T ((hi v.1.2).child v.2) P (ho j))
      (fun j => actualNormalizedInnerTrace_birth_source_moment_tendsto_zero
        p hp T ((hi v.1.2).child v.2) P (ho j)) v.1.1).comp hr.tendsto_atTop
  · exact (born_pair_moment_tendsto_zero
      (fun I K => concreteMixedEntry p T I (hi v.2.val.1) K (hi v.2.val.2)) ho P
      (fun j => concrete_entry_outer_target_moment_tendsto_zero
        p T (hi v.2.val.1) (ho j) (hi v.2.val.2) P)
      (fun j => concrete_entry_outer_source_moment_tendsto_zero
        p hp T (ho j) (hi v.2.val.1) (hi v.2.val.2) P) v.1).comp hr.tendsto_atTop

theorem exists_actual_concrete_inner_step (p : BanachExponent)
    (hp : p.val ≠ ∞) (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (r : ℕ → ℕ) (hr : StrictMono r) (a : UniversalInnerPairRegisteredTraces p T r)
    (δo δi : ℕ → ℕ → ℝ) (ν : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hδo : ∀ i j, 0 < δo i j) (hδi : ∀ i j, 0 < δi i j)
    (hν : ∀ i j k l, 0 < ν i j k l) (n : ℕ)
    (ho hi : Fin n → LpHaarFiniteSplit) (P : LpHaarFiniteParent) (N : ℕ) :
    ∃ S : LpHaarFiniteSplit, N ≤ S.level ∧ S.parent.set = P.set ∧
      ConcreteInnerStep p T (actualNormalizedOuterTrace p T a)
        (actualNormalizedInnerTrace p T) δo δi ν n ho hi S := by
  obtain ⟨S, k, _, hN, hP, hs⟩ := exists_concrete_inner_step_of_actual_moments p T
    (actualNormalizedOuterTrace p T a) (actualNormalizedInnerTrace p T) δo δi ν
    hδo hδi hν n ho hi P id strictMono_id N
      (concrete_inner_error_moment_tendsto_zero p hp T r hr a n ho hi P)
  exact ⟨S, hN, hP, hs⟩

theorem exists_actual_concrete_outer_step (p : BanachExponent)
    (hp : p.val ≠ ∞) (hp1 : 1 < p.val)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (r : ℕ → ℕ) (hr : StrictMono r) (a : UniversalInnerPairRegisteredTraces p T r)
    (δo δi : ℕ → ℕ → ℝ) (ν : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hδo : ∀ i j, 0 < δo i j) (hδi : ∀ i j, 0 < δi i j)
    (hν : ∀ i j k l, 0 < ν i j k l) (n : ℕ)
    (ho : Fin n → LpHaarFiniteSplit) (hi : Fin (n + 1) → LpHaarFiniteSplit)
    (P : LpHaarFiniteParent) (N : ℕ) :
    ∃ S : LpHaarFiniteSplit, N ≤ S.level ∧ S.parent.set = P.set ∧
      ConcreteOuterStep p T (actualNormalizedOuterTrace p T a)
        (actualNormalizedInnerTrace p T) δo δi ν n ho hi S := by
  obtain ⟨S, k, _, hN, hP, hs⟩ := exists_concrete_outer_step_of_actual_moments p T
    (actualNormalizedOuterTrace p T a) (actualNormalizedInnerTrace p T) δo δi ν
    hδo hδi hν n ho hi P r hr N
      (concrete_outer_error_moment_tendsto_zero p hp hp1 T r hr a n ho hi P)
  exact ⟨S, hN, hP, hs⟩

end SurveyStatements.P5OperatorReduction
