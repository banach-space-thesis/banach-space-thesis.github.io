import ThesisCommon.Analysis.OperatorAlgebraLpSelfCopies
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Actual self-similarity when a measure has a Lebesgue interval factor.
The dyadic partition and normalized affine maps act in that coordinate.
The other factor may be arbitrary and need only be s-finite. This provides
homogeneous-model geometry without assuming a measure classification. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Function
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X]
variable (μ : Measure X) [SFinite μ]

theorem product_interval_affine_measure (a : ℝ) (ha : 0 < a) :
    MeasurePreserving ((MeasurableEquiv.refl X).prodCongr (intervalLpAffineEquiv a ha))
      (μ.prod (volume.restrict (Icc (0 : ℝ) 1)))
      (ENNReal.ofReal a⁻¹ • μ.prod (volume.restrict (Ioc a (2*a)))) := by
  have h := (MeasurePreserving.id μ).prod (intervalLpAffineMeasure_restrict a ha)
  simpa only [Measure.prod_smul_right] using h

def productIntervalLpAffine (p : BanachExponent) (hp : p.val ≠ ∞)
    (a : ℝ) (ha : 0 < a) :
    Lp 𝕜 p.val (μ.prod (volume.restrict (Ioc a (2*a)))) ≃ₗᵢ[𝕜]
      Lp 𝕜 p.val (μ.prod (volume.restrict (Icc (0 : ℝ) 1))) :=
  (lebesgueLpMeasureScaleEquiv (𝕜 := 𝕜) hp (ENNReal.ofReal a⁻¹)
    (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ha)) ENNReal.ofReal_ne_top).symm.trans
      (lebesgueLpTransport
        ((MeasurableEquiv.refl X).prodCongr (intervalLpAffineEquiv a ha))
        (product_interval_affine_measure μ a ha))

theorem product_interval_dyadic_restrict (n : ℕ) :
    (μ.prod (volume.restrict (Icc (0 : ℝ) 1))).restrict
      (univ ×ˢ intervalLpDyadicBlock n) =
    μ.prod (volume.restrict (Ioc (intervalLpDyadicRadius (n+1))
      (2 * intervalLpDyadicRadius (n+1)))) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ, intervalLpDyadicBlock_measure]

def productIntervalLpSelfSimilarity (p : BanachExponent) (hp : p.val ≠ ∞) :
    Lp 𝕜 p.val (μ.prod (volume.restrict (Icc (0 : ℝ) 1))) ≃ₗᵢ[𝕜]
      lp (fun _ : ℕ => Lp 𝕜 p.val (μ.prod (volume.restrict (Icc (0 : ℝ) 1)))) p.val := by
  let A : ℕ → Set (X × ℝ) := fun n => univ ×ˢ intervalLpDyadicBlock n
  have hA (n : ℕ) : MeasurableSet (A n) := MeasurableSet.prod MeasurableSet.univ measurableSet_Ioc
  have hd : Pairwise (Disjoint on A) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro z hn hm
    exact Set.disjoint_left.mp (intervalLpDyadicBlock_disjoint hnm) hn.2 hm.2
  have hc : ∀ᵐ z ∂(μ.prod (volume.restrict (Icc (0 : ℝ) 1))), z ∈ ⋃ n, A n := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := μ)).ae
      intervalLpDyadicBlock_cover] with z hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨n, trivial, hn⟩
  exact (lebesgueLpPartitionEquiv hp A hA hd hc).trans
    (lebesgueLpCoordinateEquiv
      (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one p.property)) hp)
      (fun n => (lebesgueLpMeasureCongr (product_interval_dyadic_restrict μ n)).trans
        (productIntervalLpAffine μ p hp _ (intervalLpDyadicRadius_pos (n+1)))))

theorem exists_orthogonal_selfCopies_product_intervalLp
    (p : BanachExponent) (hp : p.val ≠ ∞) :
    ∃ J P : ℕ →
        Lp 𝕜 p.val (μ.prod (volume.restrict (Icc (0 : ℝ) 1))) →L[𝕜]
        Lp 𝕜 p.val (μ.prod (volume.restrict (Icc (0 : ℝ) 1))),
      (∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 _) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) :=
  exists_orthogonal_selfCopies_of_sequence_equiv
    (productIntervalLpSelfSimilarity (𝕜 := 𝕜) μ p hp).toContinuousLinearEquiv

end ThesisCommon
