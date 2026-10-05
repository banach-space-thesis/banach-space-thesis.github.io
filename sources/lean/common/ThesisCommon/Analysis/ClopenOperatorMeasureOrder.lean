import ThesisCommon.Analysis.ClopenOperatorMeasure
import ThesisCommon.Analysis.L1OperatorLattice

/-! The actual product measure assignment preserves addition and reflects
the positive-operator order. Positivity from indicator tests is established
by L1 density, including continuity of lattice absolute value. -/
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ]

theorem lOneOperator_positive_of_indicators (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (h : ∀ (a : Set X) (ha : MeasurableSet a), 0 ≤ S (lOneIndicator μ a ha)) : 0 ≤ S := by
  have habs : ∀ f : Lp ℝ 1 μ, 0 ≤ S |f| := by
    apply Lp.induction (p := 1) (by norm_num) (fun f => 0 ≤ S |f|)
    · intro c a ha hμa
      have heq : |c • lOneIndicator μ a ha| = |c| • lOneIndicator μ a ha := by
        apply Lp.ext
        filter_upwards [Lp.coeFn_abs (c • lOneIndicator μ a ha),
          Lp.coeFn_smul c (lOneIndicator μ a ha),
          Lp.coeFn_smul |c| (lOneIndicator μ a ha),
          (Lp.coeFn_nonneg _).mpr (lOneIndicator_nonneg (μ := μ) a ha)] with x hx hc hc' hn
        rw [hx, hc, hc']
        simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hn]
      rw [Lp.simpleFunc.coe_indicatorConst, indicatorConstLp_eq_smul_lOneIndicator, heq, map_smul]
      exact smul_nonneg (abs_nonneg c) (h a ha)
    · intro f g hf hg hdisj hSf hSg
      have heq : |hf.toLp f + hg.toLp g| = |hf.toLp f| + |hg.toLp g| := by
        apply Lp.ext
        filter_upwards [Lp.coeFn_abs (hf.toLp f + hg.toLp g),
          Lp.coeFn_add (hf.toLp f) (hg.toLp g),
          Lp.coeFn_add |hf.toLp f| |hg.toLp g|,
          Lp.coeFn_abs (hf.toLp f), Lp.coeFn_abs (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
          with x hsum hab ha hb hc hfx hgx
        rw [hsum, hab, ha, Pi.add_apply, Pi.add_apply, hb, hc, hfx, hgx]
        by_cases hzero : f x = 0
        · simp [hzero]
        · have hgzero : g x = 0 := by
            by_contra hgzero
            exact Set.disjoint_left.mp hdisj hzero hgzero
          simp [hgzero]
      rw [heq, map_add]
      exact add_nonneg hSf hSg
    · exact isClosed_le continuous_const
        (S.continuous.comp (continuous_id.sup continuous_id.neg))
  intro f hf
  simpa only [abs_of_nonneg hf] using habs f

theorem lOneOperator_le_of_indicators (S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (h : ∀ (a : Set X) (ha : MeasurableSet a),
      S (lOneIndicator μ a ha) ≤ T (lOneIndicator μ a ha)) : S ≤ T := by
  have hn : 0 ≤ T - S := lOneOperator_positive_of_indicators (T - S)
    (fun a ha => sub_nonneg.mpr (h a ha))
  exact sub_nonneg.mp hn

variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y]
variable [BorelSpace X] [BorelSpace Y]

theorem clopenOperatorMeasure_zero :
    clopenOperatorMeasure (0 : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (fun _ _ => le_rfl) = 0 := by
  apply Measure.ext_prod
  intro a b ha hb
  rw [clopenOperatorMeasure_prod _ _ ha hb]
  have hzero : (fun y => (0 : Lp ℝ 1 ν) y) =ᵐ[ν.restrict b] fun _ => 0 :=
    ae_restrict_of_ae (Lp.coeFn_zero ℝ 1 ν)
  change ENNReal.ofReal (∫ y in b, (0 : Lp ℝ 1 ν) y ∂ν) = 0
  rw [integral_congr_ae hzero, integral_zero, ENNReal.ofReal_zero]

theorem clopenOperatorMeasure_add
    (S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    clopenOperatorMeasure (S + T) (add_nonneg hS hT) =
      clopenOperatorMeasure S hS + clopenOperatorMeasure T hT := by
  apply Measure.ext_prod
  intro a b ha hb
  rw [clopenOperatorMeasure_prod _ _ ha hb, Measure.add_apply,
    clopenOperatorMeasure_prod _ _ ha hb, clopenOperatorMeasure_prod _ _ ha hb]
  have hadd := ae_restrict_of_ae (μ := ν) (s := b)
    (Lp.coeFn_add (S (lOneIndicator μ a ha)) (T (lOneIndicator μ a ha)))
  change ENNReal.ofReal (∫ y in b, (S (lOneIndicator μ a ha) + T (lOneIndicator μ a ha)) y ∂ν) = _
  rw [integral_congr_ae hadd]
  dsimp only [Pi.add_apply]
  rw [integral_add (L1.integrable_coeFn _).integrableOn
    (L1.integrable_coeFn _).integrableOn]
  exact ENNReal.ofReal_add
    (integral_nonneg_of_ae (ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (hS _ (lOneIndicator_nonneg a ha)))))
    (integral_nonneg_of_ae (ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (hT _ (lOneIndicator_nonneg a ha)))))

theorem clopenOperatorMeasure_mono
    (S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T) :
    clopenOperatorMeasure S hS ≤ clopenOperatorMeasure T hT := by
  have hR : 0 ≤ T - S := sub_nonneg.mpr hST
  have hadd := clopenOperatorMeasure_add S (T - S) hS hR
  have hadd' : clopenOperatorMeasure T hT =
      clopenOperatorMeasure S hS + clopenOperatorMeasure (T - S) hR := by
    simpa only [add_sub_cancel] using hadd
  rw [hadd']
  exact Measure.le_add_right le_rfl

theorem clopenOperatorMeasure_le_iff
    (S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    clopenOperatorMeasure S hS ≤ clopenOperatorMeasure T hT ↔ S ≤ T := by
  refine ⟨?_, clopenOperatorMeasure_mono S T hS hT⟩
  intro hST
  apply lOneOperator_le_of_indicators
  intro a ha
  apply (Lp.coeFn_le _ _).mp
  apply ae_le_of_forall_setIntegral_le (L1.integrable_coeFn _) (L1.integrable_coeFn _)
  intro b hb _
  have hle := hST (a ×ˢ b)
  rw [clopenOperatorMeasure_prod _ _ ha hb, clopenOperatorMeasure_prod _ _ ha hb] at hle
  exact (ENNReal.ofReal_le_ofReal_iff
    (integral_nonneg_of_ae (ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr
      (hT _ (lOneIndicator_nonneg a ha)))))).mp hle

theorem clopenOperatorMeasure_injective
    (S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (heq : clopenOperatorMeasure S hS = clopenOperatorMeasure T hT) : S = T :=
  le_antisymm ((clopenOperatorMeasure_le_iff S T hS hT).mp heq.le)
    ((clopenOperatorMeasure_le_iff T S hT hS).mp heq.ge)

theorem clopenOperatorMeasure_eq_zero_iff
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) :
    clopenOperatorMeasure S hS = 0 ↔ S = 0 := by
  constructor
  · intro heq
    apply clopenOperatorMeasure_injective S 0 hS le_rfl
    rw [heq, clopenOperatorMeasure_zero]
  · rintro rfl
    exact clopenOperatorMeasure_zero

end ThesisCommon
