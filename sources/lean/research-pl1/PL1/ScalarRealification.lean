import PL1.SingularConvolution

/-!
# Real scalar maps for the complex construction

The canonical real inclusion and real-part maps on Haar L1 intertwine probability
convolution. Consequently a singular convolution over any RCLike scalar field cannot
factor through a real Banach space with the reviewed Radon–Nikodym property.
-/

noncomputable section
universe u

open MeasureTheory
open scoped ENNReal Topology

namespace PL1.ScalarRealification

open Walsh

variable (K : Type*) [RCLike K]

/-- Pointwise inclusion of real L1 functions in scalar-valued L1. -/
def ofRealL1 : Lp ℝ 1 haar →L[ℝ] Lp K 1 haar :=
  (@RCLike.ofRealCLM K _).compLpL 1 haar

/-- Pointwise real part on scalar-valued L1, as a real bounded linear map. -/
def reL1 : Lp K 1 haar →L[ℝ] Lp ℝ 1 haar :=
  (@RCLike.reCLM K _).compLpL 1 haar

theorem coeFn_ofRealL1 (f : Lp ℝ 1 haar) :
    ofRealL1 K f =ᵐ[haar] fun x => (f x : K) :=
  (@RCLike.ofRealCLM K _).coeFn_compLpL f

theorem coeFn_reL1 (f : Lp K 1 haar) :
    reL1 K f =ᵐ[haar] fun x => RCLike.re (f x) :=
  (@RCLike.reCLM K _).coeFn_compLpL f

theorem reL1_ofRealL1 (f : Lp ℝ 1 haar) : reL1 K (ofRealL1 K f) = f := by
  apply Lp.ext
  filter_upwards [coeFn_reL1 K (ofRealL1 K f), coeFn_ofRealL1 K f] with x hr hc
  simp only [hr, hc, RCLike.ofReal_re]

theorem ofRealL1_character (F : Finset ℕ) :
    ofRealL1 K (characterLp 1 F) = scalarCharacterLp K 1 F := by
  apply Lp.ext
  filter_upwards [coeFn_ofRealL1 K (characterLp 1 F), coeFn_characterLp 1 F,
    coeFn_scalarCharacterLp K 1 F] with x hc hr hk
  rw [hc, hr, hk]
  rfl

theorem reL1_scalarCharacter (F : Finset ℕ) :
    reL1 K (scalarCharacterLp K 1 F) = characterLp 1 F := by
  rw [← ofRealL1_character K F, reL1_ofRealL1]

/-- Taking real parts after scalar-valued convolution recovers real convolution on real inputs. -/
theorem reL1_convolution_ofRealL1 (ν : Measure Walsh.Group) [IsProbabilityMeasure ν] :
    (reL1 K).comp (((convolutionL1 (𝕜 := K) ν).restrictScalars ℝ).comp (ofRealL1 K)) =
      convolutionL1 (𝕜 := ℝ) ν := by
  apply ContinuousLinearMap.ext_on (dense_span_characterLp 1 (by norm_num))
  rintro x ⟨F, rfl⟩
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ofRealL1_character, convolutionL1_scalarCharacter, convolutionL1_character]
  rw [← RCLike.real_smul_eq_coe_smul, map_smul, reL1_scalarCharacter]

/-- A setwise density for scalar convolution on real input indicators would yield a
forbidden real density after taking real parts. -/
theorem no_setwise_density_of_null_carrier
    (ν : Measure Walsh.Group) [IsProbabilityMeasure ν] (N : Set Walsh.Group)
    (hmN : haar N = 0) (hνN : ν N ≠ 0) :
    ¬ ∃ b : Walsh.Group → Lp K 1 haar, Integrable b haar ∧
      ∀ A : Set Walsh.Group, MeasurableSet A →
        convolutionL1 ν (ofRealL1 K (RNPBridge.indicatorL1 haar A)) = ∫ x in A, b x ∂haar := by
  rintro ⟨b, hb, hrep⟩
  apply SingularConvolution.no_setwise_density_of_null_carrier ν N hmN hνN
  refine ⟨fun x => reL1 K (b x), (reL1 K).integrable_comp hb, ?_⟩
  intro A hA
  rw [(reL1 K).integral_comp_comm hb.integrableOn, ← hrep A hA]
  exact (congrArg (fun T : Lp ℝ 1 haar →L[ℝ] Lp ℝ 1 haar =>
    T (RNPBridge.indicatorL1 haar A)) (reL1_convolution_ofRealL1 K ν)).symm

/-- Scalar-valued singular convolution cannot factor through any real RNP Banach space.
Only real inputs to the scalar convolution are needed for the obstruction. -/
theorem not_RNP_of_convolution_factorization
    (ν : Measure Walsh.Group) [IsProbabilityMeasure ν] (N : Set Walsh.Group)
    (hmN : haar N = 0) (hνN : ν N ≠ 0)
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : Lp ℝ 1 haar →L[ℝ] E) (T : E →L[ℝ] Lp K 1 haar)
    (hfac : T.comp S = ((convolutionL1 (𝕜 := K) ν).restrictScalars ℝ).comp (ofRealL1 K)) :
    ¬ HasRadonNikodymProperty.{u, 0} E := by
  apply SingularConvolution.not_RNP_of_convolution_factorization ν N hmN hνN
    S ((reL1 K).comp T)
  rw [ContinuousLinearMap.comp_assoc, hfac]
  exact reL1_convolution_ofRealL1 K ν

/-- A scalar-linear factorization also obstructs the RNP of the underlying real Banach space. -/
theorem not_RNP_of_scalar_convolution_factorization
    (ν : Measure Walsh.Group) [IsProbabilityMeasure ν] (N : Set Walsh.Group)
    (hmN : haar N = 0) (hνN : ν N ≠ 0)
    {E : Type u} [NormedAddCommGroup E] [NormedSpace K E] [NormedSpace ℝ E]
    [IsScalarTower ℝ K E] [CompleteSpace E]
    (S : Lp K 1 haar →L[K] E) (T : E →L[K] Lp K 1 haar)
    (hfac : T.comp S = convolutionL1 ν) : ¬ HasRadonNikodymProperty.{u, 0} E := by
  apply not_RNP_of_convolution_factorization K ν N hmN hνN
    ((S.restrictScalars ℝ).comp (ofRealL1 K)) (T.restrictScalars ℝ)
  ext1 f
  exact congrArg (fun L : Lp K 1 haar →L[K] Lp K 1 haar => L (ofRealL1 K f)) hfac

end PL1.ScalarRealification
