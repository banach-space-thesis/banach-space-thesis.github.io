import ThesisCommon.Analysis.LebesgueLpPartition

/-! Actual Lp decomposition over arbitrary, possibly uncountable, measurable
partitions. The measure-sum identity replaces a countability assumption. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Function Classical
namespace ThesisCommon
variable {𝕜 X E I : Type*} [RCLike 𝕜] [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure X}

theorem sum_restrict_eq_of_apply (s : I → Set X)
    (h : ∀ A : Set X, MeasurableSet A → μ A = ∑' i, μ (A ∩ s i)) :
    Measure.sum (fun i => μ.restrict (s i)) = μ := by
  ext A hA
  rw [Measure.sum_apply _ hA]
  simp_rw [Measure.restrict_apply hA]
  exact (h A hA).symm

theorem decomposableLpPartition_enorm_rpow (hp : p ≠ ∞) (s : I → Set X)
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ) (f : Lp E p μ) :
    (∑' i, ENNReal.ofReal (‖lebesgueLpRestrict (𝕜 := 𝕜) (s i) f‖ ^ p.toReal)) =
      ENNReal.ofReal (‖f‖ ^ p.toReal) := by
  simp_rw [lebesgueLpRestrict_norm_rpow hp]
  rw [← lintegral_sum_measure, hμ, lebesgueLp_norm_rpow hp]

theorem decomposableLpPartition_mem (hp : p ≠ ∞) (s : I → Set X)
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ) (f : Lp E p μ) :
    Memℓp (fun i => lebesgueLpRestrict (𝕜 := 𝕜) (s i) f) p := by
  apply memℓp_gen
  have h := ENNReal.summable_toReal
    (show (∑' i, ENNReal.ofReal
        (‖lebesgueLpRestrict (𝕜 := 𝕜) (s i) f‖ ^ p.toReal)) ≠ ∞ from by
      rw [decomposableLpPartition_enorm_rpow hp s hμ]
      exact ENNReal.ofReal_ne_top)
  simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using h

def decomposableLpPartitionValue (hp : p ≠ ∞) (s : I → Set X)
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ) (f : Lp E p μ) :
    lp (fun i => Lp E p (μ.restrict (s i))) p :=
  ⟨fun i => lebesgueLpRestrict (𝕜 := 𝕜) (s i) f,
    decomposableLpPartition_mem hp s hμ f⟩

theorem decomposableLpPartitionValue_norm (hp : p ≠ ∞) (s : I → Set X)
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ) (f : Lp E p μ) :
    ‖decomposableLpPartitionValue (𝕜 := 𝕜) hp s hμ f‖ = ‖f‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp
  apply (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp0.ne').mp
  rw [lp.norm_rpow_eq_tsum hp0]
  apply (ENNReal.ofReal_eq_ofReal_iff
    (tsum_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (norm_nonneg _) _)).mp
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    ((lp.memℓp (decomposableLpPartitionValue (𝕜 := 𝕜) hp s hμ f)).summable hp0)]
  exact decomposableLpPartition_enorm_rpow hp s hμ f

def decomposableLpPartition (hp : p ≠ ∞) (s : I → Set X)
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ) :
    Lp E p μ →ₗᵢ[𝕜] lp (fun i => Lp E p (μ.restrict (s i))) p where
  toFun := decomposableLpPartitionValue (𝕜 := 𝕜) hp s hμ
  map_add' f g := by
    apply lp.ext
    funext i
    exact map_add (lebesgueLpRestrict (𝕜 := 𝕜) (s i)) f g
  map_smul' c f := by
    apply lp.ext
    funext i
    exact map_smul (lebesgueLpRestrict (𝕜 := 𝕜) (s i)) c f
  norm_map' := decomposableLpPartitionValue_norm hp s hμ

theorem decomposableLpPartition_extend (hp : p ≠ ∞) (s : I → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ) (i : I)
    (f : Lp E p (μ.restrict (s i))) :
    decomposableLpPartition (𝕜 := 𝕜) hp s hμ
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

theorem decomposableLpPartition_surjective [CompleteSpace E]
    (hp : p ≠ ∞) (s : I → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ) :
    Function.Surjective (decomposableLpPartition (𝕜 := 𝕜) (E := E) hp s hμ) := by
  intro y
  let A := decomposableLpPartition (𝕜 := 𝕜) (E := E) hp s hμ
  let R := LinearMap.range A.toLinearMap
  have hclosed : IsClosed (R : Set (lp (fun i => Lp E p (μ.restrict (s i))) p)) :=
    A.isometry.isClosedEmbedding.isClosed_range
  have hsingle : ∀ i, lp.single p i (y i) ∈ R := fun i =>
    ⟨lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i) (y i),
      decomposableLpPartition_extend hp s hs hd hμ i (y i)⟩
  have hy : y ∈ R := hclosed.mem_of_tendsto (lp.hasSum_single hp y)
    (Eventually.of_forall fun t => Submodule.sum_mem R (fun i _ => hsingle i))
  exact hy

def decomposableLpPartitionEquiv [CompleteSpace E]
    (hp : p ≠ ∞) (s : I → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ) :
    Lp E p μ ≃ₗᵢ[𝕜] lp (fun i => Lp E p (μ.restrict (s i))) p :=
  LinearIsometryEquiv.ofSurjective (decomposableLpPartition hp s hμ)
    (decomposableLpPartition_surjective hp s hs hd hμ)

theorem decomposableLpPartitionEquiv_apply [CompleteSpace E]
    (hp : p ≠ ∞) (s : I → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ) (f : Lp E p μ) (i : I) :
    decomposableLpPartitionEquiv (𝕜 := 𝕜) hp s hs hd hμ f i =
      lebesgueLpRestrict (𝕜 := 𝕜) (s i) f := rfl

theorem decomposableLpPartitionEquiv_symm_single [CompleteSpace E]
    (hp : p ≠ ∞) (s : I → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ) (i : I)
    (f : Lp E p (μ.restrict (s i))) :
    (decomposableLpPartitionEquiv (𝕜 := 𝕜) hp s hs hd hμ).symm (lp.single p i f) =
      lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i) f := by
  apply (decomposableLpPartitionEquiv (𝕜 := 𝕜) hp s hs hd hμ).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (decomposableLpPartition_extend hp s hs hd hμ i f).symm

end ThesisCommon
