import ThesisCommon.Analysis.ALPrincipalL1Representation
import ThesisCommon.Analysis.BooleanStoneIsoTransport

/-! A norm-content-preserving isomorphism of actual fragment algebras gives
an onto ordered linear isometry of their principal AL bands. The map is
constructed through the genuine finite Stone measures and L1 models. -/
noncomputable section
open Set MeasureTheory
namespace ThesisCommon
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  [HasSolidNorm E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [ConditionallyCompleteLattice F] [IsOrderedAddMonoid F] [IsOrderedModule ℝ F]
  [HasSolidNorm F] [CompleteSpace F]
variable (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
  (hF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
  (e : E) (f : F) [Fact (0 ≤ e)] [Fact (0 ≤ f)]
  (q : PositiveFragmentAlgebra e ≃o PositiveFragmentAlgebra f)
  (hq : ∀ a, ‖positiveFragmentValue (q a)‖ = ‖positiveFragmentValue a‖)

include hq in
theorem alFragmentIso_stone_mass (a : PositiveFragmentAlgebra e) :
    alFragmentMeasure hF f (booleanStoneSet (q a)) = alFragmentMeasure hE e (booleanStoneSet a) := by
  rw [alFragmentMeasure_apply, alFragmentMeasure_apply, hq a]

def alPrincipalBandEquivOfFragmentIso : principalBand e ≃ₗᵢ[ℝ] principalBand f :=
  (alPrincipalL1Equiv hE e).symm.trans
    ((booleanStoneLpEquiv (𝕜 := ℝ) q (alFragmentMeasure hE e) (alFragmentMeasure hF f)
      (alFragmentIso_stone_mass hE hF e f q hq)).trans (alPrincipalL1Equiv hF f))

theorem alPrincipalBandEquivOfFragmentIso_nonneg (x : principalBand e) :
    0 ≤ alPrincipalBandEquivOfFragmentIso hE hF e f q hq x ↔ 0 ≤ x := by
  change 0 ≤ alPrincipalL1Equiv hF f
    (booleanStoneLpEquiv (𝕜 := ℝ) q (alFragmentMeasure hE e) (alFragmentMeasure hF f)
      (alFragmentIso_stone_mass hE hF e f q hq) ((alPrincipalL1Equiv hE e).symm x)) ↔ 0 ≤ x
  rw [alPrincipalL1Equiv_nonneg_iff, booleanStoneLpEquiv_nonneg]
  have h := alPrincipalL1Equiv_nonneg_iff hE e ((alPrincipalL1Equiv hE e).symm x)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

def positiveFragmentInPrincipalBand (a : PositiveFragmentAlgebra e) : principalBand e :=
  ⟨positiveFragmentValue a, positiveFragmentSpan_le_principalBand e
    (Submodule.subset_span (positiveFragmentValue_isFragment a))⟩

theorem alPrincipalL1Equiv_fragment (a : PositiveFragmentAlgebra e) :
    alPrincipalL1Equiv hE e (alFragmentIndicator hE e a) = positiveFragmentInPrincipalBand e a := by
  apply Subtype.ext
  exact alFragmentL1Map_fragment hE e a

theorem alFragmentIso_stone_indicator (a : PositiveFragmentAlgebra e) :
    booleanStoneLpEquiv (𝕜 := ℝ) q (alFragmentMeasure hE e) (alFragmentMeasure hF f)
      (alFragmentIso_stone_mass hE hF e f q hq) (alFragmentIndicator hE e a) =
      alFragmentIndicator hF f (q a) := by
  let hp := measurePreserving_booleanStoneOrderMap q (alFragmentMeasure hE e)
    (alFragmentMeasure hF f) (alFragmentIso_stone_mass hE hF e f q hq)
  rw [alFragmentIndicator_eq_lOneIndicator, alFragmentIndicator_eq_lOneIndicator]
  apply Lp.ext
  filter_upwards [booleanStoneLpEquiv_coe (𝕜 := ℝ) q
      (alFragmentMeasure hE e) (alFragmentMeasure hF f)
      (alFragmentIso_stone_mass hE hF e f q hq)
      (lOneIndicator (alFragmentMeasure hE e) (booleanStoneSet a) (measurableSet_booleanStoneSet a)),
    hp.quasiMeasurePreserving.ae (lOneIndicator_coe (μ := alFragmentMeasure hE e)
      (booleanStoneSet a) (measurableSet_booleanStoneSet a)),
    lOneIndicator_coe (μ := alFragmentMeasure hF f)
      (booleanStoneSet (q a)) (measurableSet_booleanStoneSet (q a))] with p ht ha hb
  rw [ht]
  change (lOneIndicator (alFragmentMeasure hE e) (booleanStoneSet a)
    (measurableSet_booleanStoneSet a)) (booleanStoneMeasurableEquiv q p) = _
  rw [ha, hb]
  rfl

theorem alPrincipalBandEquivOfFragmentIso_fragment (a : PositiveFragmentAlgebra e) :
    alPrincipalBandEquivOfFragmentIso hE hF e f q hq (positiveFragmentInPrincipalBand e a) =
      positiveFragmentInPrincipalBand f (q a) := by
  rw [← alPrincipalL1Equiv_fragment hE e a]
  change alPrincipalL1Equiv hF f (booleanStoneLpEquiv (𝕜 := ℝ) q
    (alFragmentMeasure hE e) (alFragmentMeasure hF f) (alFragmentIso_stone_mass hE hF e f q hq)
    ((alPrincipalL1Equiv hE e).symm (alPrincipalL1Equiv hE e (alFragmentIndicator hE e a)))) = _
  rw [LinearIsometryEquiv.symm_apply_apply,
    alFragmentIso_stone_indicator hE hF e f q hq, alPrincipalL1Equiv_fragment]

theorem norm_fragment_eq_of_isometric_orderIso
    (q : PositiveFragmentAlgebra e ≃o PositiveFragmentAlgebra f) (hq : Isometry q)
    (a : PositiveFragmentAlgebra e) :
    ‖positiveFragmentValue (q a)‖ = ‖positiveFragmentValue a‖ := by
  have h := hq.dist_eq a ⊥
  change dist (positiveFragmentValue (q a)) (positiveFragmentValue (q ⊥)) =
    dist (positiveFragmentValue a) (positiveFragmentValue ⊥) at h
  simpa only [map_bot, positiveFragmentValue_bot, dist_zero_right] using h

def alPrincipalBandEquivOfIsometricFragmentIso
    (q : PositiveFragmentAlgebra e ≃o PositiveFragmentAlgebra f) (hq : Isometry q) :
    principalBand e ≃ₗᵢ[ℝ] principalBand f :=
  alPrincipalBandEquivOfFragmentIso hE hF e f q (norm_fragment_eq_of_isometric_orderIso e f q hq)

theorem alPrincipalBandEquivOfIsometricFragmentIso_nonneg
    (q : PositiveFragmentAlgebra e ≃o PositiveFragmentAlgebra f) (hq : Isometry q)
    (x : principalBand e) :
    0 ≤ alPrincipalBandEquivOfIsometricFragmentIso hE hF e f q hq x ↔ 0 ≤ x :=
  alPrincipalBandEquivOfFragmentIso_nonneg hE hF e f q
    (norm_fragment_eq_of_isometric_orderIso e f q hq) x

end ThesisCommon
