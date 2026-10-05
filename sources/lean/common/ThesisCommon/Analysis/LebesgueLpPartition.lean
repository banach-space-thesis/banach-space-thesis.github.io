import ThesisCommon.Analysis.LebesgueLpRestrictions

/-! The norm identity for decomposing an actual Lebesgue `Lp` function along a
countable measurable partition.  No sequence-space identification is assumed. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Function Classical
namespace ThesisCommon
variable {𝕜 α E ι : Type*} [RCLike 𝕜] [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Countable ι]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

theorem lebesgueLp_norm_rpow (hp : p ≠ ∞) (f : Lp E p μ) :
    ENNReal.ofReal (‖f‖ ^ p.toReal) = ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg,
    Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f),
    eLpNorm_eq_lintegral_rpow_enorm hp0 hp, ← ENNReal.rpow_mul,
    one_div_mul_cancel (ENNReal.toReal_pos hp0 hp).ne', ENNReal.rpow_one]

theorem lebesgueLpRestrict_norm_rpow (hp : p ≠ ∞) (s : Set α) (f : Lp E p μ) :
    ENNReal.ofReal (‖lebesgueLpRestrict (𝕜 := 𝕜) s f‖ ^ p.toReal) =
      ∫⁻ x in s, ‖f x‖ₑ ^ p.toReal ∂μ := by
  rw [lebesgueLp_norm_rpow hp]
  apply lintegral_congr_ae
  filter_upwards [lebesgueLpRestrict_coe (𝕜 := 𝕜) s f] with x hx
  rw [hx]

theorem lebesgueLpPartition_enorm_rpow (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (f : Lp E p μ) :
    (∑' i, ENNReal.ofReal (‖lebesgueLpRestrict (𝕜 := 𝕜) (s i) f‖ ^ p.toReal)) =
      ENNReal.ofReal (‖f‖ ^ p.toReal) := by
  simp_rw [lebesgueLpRestrict_norm_rpow hp]
  rw [← lintegral_iUnion hs hd, Measure.restrict_eq_self_of_ae_mem hc,
    lebesgueLp_norm_rpow hp]

theorem lebesgueLpPartition_mem (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (f : Lp E p μ) :
    Memℓp (fun i => lebesgueLpRestrict (𝕜 := 𝕜) (s i) f) p := by
  apply memℓp_gen
  have h := ENNReal.summable_toReal
    (show (∑' i, ENNReal.ofReal
        (‖lebesgueLpRestrict (𝕜 := 𝕜) (s i) f‖ ^ p.toReal)) ≠ ∞ from by
      rw [lebesgueLpPartition_enorm_rpow hp s hs hd hc]
      exact ENNReal.ofReal_ne_top)
  simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using h

def lebesgueLpPartitionValue (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (f : Lp E p μ) :
    lp (fun i => Lp E p (μ.restrict (s i))) p :=
  ⟨fun i => lebesgueLpRestrict (𝕜 := 𝕜) (s i) f,
    lebesgueLpPartition_mem hp s hs hd hc f⟩

theorem lebesgueLpPartitionValue_norm (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (f : Lp E p μ) :
    ‖lebesgueLpPartitionValue (𝕜 := 𝕜) hp s hs hd hc f‖ = ‖f‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp
  apply (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp0.ne').mp
  rw [lp.norm_rpow_eq_tsum hp0]
  apply (ENNReal.ofReal_eq_ofReal_iff
    (tsum_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (norm_nonneg _) _)).mp
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    ((lp.memℓp (lebesgueLpPartitionValue (𝕜 := 𝕜) hp s hs hd hc f)).summable hp0)]
  exact lebesgueLpPartition_enorm_rpow hp s hs hd hc f

def lebesgueLpPartition (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) :
    Lp E p μ →ₗᵢ[𝕜] lp (fun i => Lp E p (μ.restrict (s i))) p where
  toFun := lebesgueLpPartitionValue (𝕜 := 𝕜) hp s hs hd hc
  map_add' f g := by
    apply lp.ext
    funext i
    exact map_add (lebesgueLpRestrict (𝕜 := 𝕜) (s i)) f g
  map_smul' c f := by
    apply lp.ext
    funext i
    exact map_smul (lebesgueLpRestrict (𝕜 := 𝕜) (s i)) c f
  norm_map' := lebesgueLpPartitionValue_norm hp s hs hd hc

theorem lebesgueLpPartition_extend (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) (i : ι) (f : Lp E p (μ.restrict (s i))) :
    lebesgueLpPartition (𝕜 := 𝕜) hp s hs hd hc
        (lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i) f) = lp.single p i f := by
  classical
  apply lp.ext
  funext j
  change lebesgueLpRestrict (𝕜 := 𝕜) (s j)
    (lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i) f) =
      (lp.single (E := fun i => Lp E p (μ.restrict (s i))) p i f) j
  by_cases hji : j = i
  · subst j
    rw [lebesgueLpRestrict_extend, lp.single_apply_self]
  · rw [lebesgueLpRestrict_extend_disjoint (hs j) (hs i) (hd hji),
      lp.single_apply_ne (E := fun i => Lp E p (μ.restrict (s i))) p i f hji]

theorem lebesgueLpPartition_surjective [CompleteSpace E]
    (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) :
    Function.Surjective (lebesgueLpPartition (𝕜 := 𝕜) (E := E) hp s hs hd hc) := by
  intro y
  let A := lebesgueLpPartition (𝕜 := 𝕜) (E := E) hp s hs hd hc
  let R := LinearMap.range A.toLinearMap
  have hclosed : IsClosed (R : Set (lp (fun i => Lp E p (μ.restrict (s i))) p)) :=
    A.isometry.isClosedEmbedding.isClosed_range
  have hsingle : ∀ i, lp.single p i (y i) ∈ R := fun i =>
    ⟨lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i) (y i),
      lebesgueLpPartition_extend hp s hs hd hc i (y i)⟩
  have hy : y ∈ R := hclosed.mem_of_tendsto (lp.hasSum_single hp y)
    (Eventually.of_forall fun t => Submodule.sum_mem R (fun i _ => hsingle i))
  exact hy

/-- Countable measurable partition decomposition as a linear isometry equivalence
between the actual measure-theoretic `Lp` and the actual sequence `lp`. -/
def lebesgueLpPartitionEquiv [CompleteSpace E]
    (hp : p ≠ ∞) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i) :
    Lp E p μ ≃ₗᵢ[𝕜] lp (fun i => Lp E p (μ.restrict (s i))) p :=
  LinearIsometryEquiv.ofSurjective (lebesgueLpPartition hp s hs hd hc)
    (lebesgueLpPartition_surjective hp s hs hd hc)

end ThesisCommon
