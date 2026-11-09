import SurveyStatements.P5VectorPartitionTransfer

/-! Banach-valued partition transport commutes with every bounded map on
the value space. This supplies tensor identities for exterior maps. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5

variable {𝕜 α E F ι : Type*} [RCLike 𝕜] [MeasurableSpace α]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] [Fintype ι]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]

local instance vectorPartNaturalModuleRealE : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
local instance vectorPartNaturalScalarTowerE : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
local instance vectorPartNaturalNormedSpaceRealE : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
local instance vectorPartNaturalModuleRealF : Module ℝ F := RestrictScalars.module ℝ 𝕜 F
local instance vectorPartNaturalScalarTowerF : IsScalarTower ℝ 𝕜 F := RestrictScalars.isScalarTower ℝ 𝕜 F
local instance vectorPartNaturalNormedSpaceRealF : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ 𝕜 F

theorem lebesgueLpRestrict_compLpL (L : E →L[𝕜] F) (s : Set α) (f : Lp E p μ) :
    P5Support.lebesgueLpRestrict (𝕜 := 𝕜) s (L.compLpL p μ f) =
      L.compLpL p (μ.restrict s) (P5Support.lebesgueLpRestrict (𝕜 := 𝕜) s f) := by
  apply Lp.ext
  filter_upwards [P5Support.lebesgueLpRestrict_coe (𝕜 := 𝕜) s (L.compLpL p μ f),
    ae_restrict_of_ae (L.coeFn_compLpL f),
    L.coeFn_compLpL (P5Support.lebesgueLpRestrict (𝕜 := 𝕜) s f),
    P5Support.lebesgueLpRestrict_coe (𝕜 := 𝕜) s f] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

theorem finiteLpIntegral_natural (hp : p ≠ ∞) (L : E →L[𝕜] F) (f : Lp E p μ) :
    finiteLpIntegral (𝕜 := 𝕜) hp (L.compLpL p μ f) =
      L (finiteLpIntegral (𝕜 := 𝕜) hp f) := by
  rw [finiteLpIntegral_apply, finiteLpIntegral_apply,
    integral_congr_ae (L.coeFn_compLpL f)]
  exact L.integral_comp_comm ((Lp.memLp f).integrable Fact.out)

theorem compLpL_indicator (L : E →L[𝕜] F) (s : Set α)
    (hs : MeasurableSet s) (c : E) :
    L.compLpL p μ (indicatorConstLp p hs (measure_ne_top μ s) c) =
      indicatorConstLp p hs (measure_ne_top μ s) (L c) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (indicatorConstLp p hs (measure_ne_top μ s) c),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := measure_ne_top μ s) (c := c),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := measure_ne_top μ s) (c := L c)]
      with x hL hc hLc
  rw [hL, hc, hLc]
  by_cases hx : x ∈ s
  · simp [hx]
  · simp [hx]

theorem vectorLpPartitionAverage_natural (hp : p ≠ ∞)
    (L : E →L[𝕜] F) (s : Set α) (f : Lp E p μ) :
    vectorLpPartitionAverage (𝕜 := 𝕜) hp s (L.compLpL p μ f) =
      L (vectorLpPartitionAverage (𝕜 := 𝕜) hp s f) := by
  change (μ.real s : 𝕜)⁻¹ • finiteLpIntegral (𝕜 := 𝕜) hp
      (P5Support.lebesgueLpRestrict (𝕜 := 𝕜) s (L.compLpL p μ f)) =
    L ((μ.real s : 𝕜)⁻¹ • finiteLpIntegral (𝕜 := 𝕜) hp
      (P5Support.lebesgueLpRestrict (𝕜 := 𝕜) s f))
  rw [lebesgueLpRestrict_compLpL, finiteLpIntegral_natural, map_smul]

theorem vectorLpPartitionTransfer_natural (hp : p ≠ ∞) (L : E →L[𝕜] F)
    (s t : ι → Set α) (ht : ∀ i, MeasurableSet (t i)) (f : Lp E p μ) :
    vectorLpPartitionTransfer (𝕜 := 𝕜) hp s t ht (L.compLpL p μ f) =
      L.compLpL p μ (vectorLpPartitionTransfer (𝕜 := 𝕜) hp s t ht f) := by
  rw [vectorLpPartitionTransfer_apply, vectorLpPartitionTransfer_apply]
  unfold vectorLpPartitionStep
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [compLpL_indicator]
  dsimp only
  rw [vectorLpPartitionAverage_natural hp L (s i) f]

end SurveyStatements.P5
