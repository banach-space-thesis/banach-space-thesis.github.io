import JLMS.FiniteRank
import Mathlib.Tactic

/-!
# Section 4: coordinate restrictions on ℓ¹ over an arbitrary index set

These results are independent of Rudin's theorem. They provide the actual
restriction maps to transport to C₀(K)* once its atomic representation is proved.
The index set is not assumed countable: each individual vector has countable
support and arbitrarily good finite truncations.
-/

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {I : Type*}

abbrev ellOneOn (𝕜 : Type*) [RCLike 𝕜] (I : Type*) := lp (fun _ : I => 𝕜) 1

theorem ellOneOn_summable_norm (f : ellOneOn 𝕜 I) : Summable (fun i => ‖f i‖) := by
  simpa using (lp.memℓp f).summable (by norm_num : 0 < (1 : ENNReal).toReal)

theorem ellOneOn_norm_eq_tsum (f : ellOneOn 𝕜 I) : ‖f‖ = ∑' i, ‖f i‖ := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal) f

/-- Coordinate truncation to C, before bundling as an operator. -/
def restrictL1 (C : Set I) (f : ellOneOn 𝕜 I) : ellOneOn 𝕜 I :=
  ⟨C.indicator f, by
    apply memℓp_gen
    have hnorm : (fun i => ‖C.indicator f i‖) = C.indicator (fun i => ‖f i‖) := by
      funext i
      by_cases hi : i ∈ C <;> simp only [Set.indicator_apply, hi, if_true, if_false,
        norm_zero]
    simpa only [ENNReal.toReal_one, Real.rpow_one, hnorm] using
      (ellOneOn_summable_norm f).indicator C⟩

@[simp] theorem restrictL1_apply (C : Set I) (f : ellOneOn 𝕜 I) (i : I) :
    restrictL1 C f i = if i ∈ C then f i else 0 := by
  simp [restrictL1, Set.indicator_apply]

theorem restrictL1_norm_le (C : Set I) (f : ellOneOn 𝕜 I) : ‖restrictL1 C f‖ ≤ ‖f‖ := by
  rw [ellOneOn_norm_eq_tsum, ellOneOn_norm_eq_tsum]
  apply (ellOneOn_summable_norm _).tsum_le_tsum _ (ellOneOn_summable_norm _)
  intro i
  by_cases hi : i ∈ C <;> simp [hi]

/-- The canonical coordinate projection R_C, with operator norm at most one. -/
def restrictionL1 (C : Set I) : ellOneOn 𝕜 I →L[𝕜] ellOneOn 𝕜 I :=
  ({ toFun := restrictL1 C
     map_add' := by
       intro f g
       apply lp.ext
       funext i
       by_cases hi : i ∈ C <;>
         simp only [restrictL1_apply, lp.coeFn_add, Pi.add_apply, hi, if_true, if_false,
           add_zero]
     map_smul' := by
       intro a f
       apply lp.ext
       funext i
       by_cases hi : i ∈ C <;>
         simp only [restrictL1_apply, lp.coeFn_smul, Pi.smul_apply, hi, if_true, if_false,
           RingHom.id_apply, smul_zero] } :
    ellOneOn 𝕜 I →ₗ[𝕜] ellOneOn 𝕜 I).mkContinuous 1
    (fun f => by simpa only [one_mul] using restrictL1_norm_le C f)

@[simp] theorem restrictionL1_apply (C : Set I) (f : ellOneOn 𝕜 I) :
    restrictionL1 C f = restrictL1 C f := rfl

theorem restrictionL1_norm_le (C : Set I) : ‖restrictionL1 (𝕜 := 𝕜) C‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [restrictionL1_apply, one_mul] using restrictL1_norm_le C f

@[simp] theorem restrictionL1_idempotent (C : Set I) :
    (restrictionL1 (𝕜 := 𝕜) C).comp (restrictionL1 C) = restrictionL1 C := by
  ext f i
  by_cases hi : i ∈ C <;> simp [hi]

@[simp] theorem restrictionL1_compl (C : Set I) :
    ContinuousLinearMap.id 𝕜 (ellOneOn 𝕜 I) - restrictionL1 C = restrictionL1 Cᶜ := by
  ext f i
  by_cases hi : i ∈ C <;> simp [hi]

theorem norm_id_sub_restrictionL1_le (C : Set I) :
    ‖ContinuousLinearMap.id 𝕜 (ellOneOn 𝕜 I) - restrictionL1 C‖ ≤ 1 := by
  rw [restrictionL1_compl]
  exact restrictionL1_norm_le _

theorem restrictionL1_union (C D : Set I) (hCD : Disjoint C D) :
    restrictionL1 (𝕜 := 𝕜) (C ∪ D) = restrictionL1 C + restrictionL1 D := by
  ext f i
  by_cases hiC : i ∈ C
  · have hiD : i ∉ D := fun hiD => Set.disjoint_left.mp hCD hiC hiD
    simp [hiC, hiD]
  · by_cases hiD : i ∈ D <;> simp [hiC, hiD]

/-- Disjoint coordinate pieces have additive ℓ¹ mass. -/
theorem restrictionL1_norm_union (C D : Set I) (hCD : Disjoint C D) (f : ellOneOn 𝕜 I) :
    ‖restrictionL1 (C ∪ D) f‖ = ‖restrictionL1 C f‖ + ‖restrictionL1 D f‖ := by
  simp only [ellOneOn_norm_eq_tsum]
  rw [← (ellOneOn_summable_norm (restrictionL1 C f)).tsum_add
    (ellOneOn_summable_norm (restrictionL1 D f))]
  apply tsum_congr
  intro i
  by_cases hiC : i ∈ C
  · have hiD : i ∉ D := fun hiD => Set.disjoint_left.mp hCD hiC hiD
    simp [hiC, hiD]
  · by_cases hiD : i ∈ D <;> simp [hiC, hiD]

theorem ellOneOn_countable_support (f : ellOneOn 𝕜 I) : (Function.support f).Countable := by
  have h := (ellOneOn_summable_norm f).countable_support
  simpa [Function.support] using h

/-- A finite restriction is the corresponding finite sum of point masses. -/
theorem restrictionL1_finset (s : Finset I) (f : ellOneOn 𝕜 I) :
    restrictionL1 (s : Set I) f = ∑ i ∈ s, lp.single 1 i (f i) := by
  ext i
  simp only [restrictionL1_apply, restrictL1_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_single, Finset.sum_pi_single, Finset.mem_coe]

/-- Every finite coordinate restriction has finite rank. -/
theorem restrictionL1_finiteRank (s : Finset I) :
    FiniteDimensional 𝕜 (LinearMap.range (restrictionL1 (𝕜 := 𝕜) (s : Set I)).toLinearMap) := by
  let W := Submodule.span 𝕜 ((fun i => lp.single 1 i (1 : 𝕜)) '' (s : Set I))
  letI : FiniteDimensional 𝕜 W :=
    FiniteDimensional.span_of_finite 𝕜 (s.finite_toSet.image _)
  have hle : LinearMap.range (restrictionL1 (𝕜 := 𝕜) (s : Set I)).toLinearMap ≤ W := by
    rintro y ⟨f, rfl⟩
    rw [ContinuousLinearMap.coe_coe, restrictionL1_finset]
    apply Submodule.sum_mem
    intro i hi
    have hmem : lp.single 1 i (1 : 𝕜) ∈ W :=
      Submodule.subset_span ⟨i, hi, rfl⟩
    have hsingle : (lp.single 1 i (f i) : ellOneOn 𝕜 I) =
        f i • (lp.single 1 i (1 : 𝕜) : ellOneOn 𝕜 I) := by
      simpa only [smul_eq_mul, mul_one] using
        lp.single_smul (E := fun _ : I => 𝕜) 1 i (f i) (1 : 𝕜)
    rw [hsingle]
    exact Submodule.smul_mem W _ hmem
  exact FiniteDimensional.of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective _)

theorem restrictionL1_compact (s : Finset I) :
    IsCompactOperator (restrictionL1 (𝕜 := 𝕜) (s : Set I)) :=
  isCompactOperator_of_finiteRank _ (restrictionL1_finiteRank s)

theorem restrictionL1_finset_norm (s : Finset I) (f : ellOneOn 𝕜 I) :
    ‖restrictionL1 (s : Set I) f‖ = ∑ i ∈ s, ‖f i‖ := by
  rw [restrictionL1_finset]
  simpa only [ENNReal.toReal_one, Real.rpow_one] using
    lp.norm_sum_single (by norm_num : 0 < (1 : ENNReal).toReal) (fun i => f i) s

theorem restrictionL1_norm_mono {C D : Set I} (hCD : C ⊆ D) (f : ellOneOn 𝕜 I) :
    ‖restrictionL1 C f‖ ≤ ‖restrictionL1 D f‖ := by
  simp only [ellOneOn_norm_eq_tsum]
  apply (ellOneOn_summable_norm _).tsum_le_tsum _ (ellOneOn_summable_norm _)
  intro i
  by_cases hi : i ∈ C
  · simp [hi, hCD hi]
  · simp [hi]

theorem restrictionL1_tail_eq (C : Set I) (f : ellOneOn 𝕜 I) :
    f - restrictionL1 C f = restrictionL1 Cᶜ f := by
  ext i
  by_cases hi : i ∈ C <;> simp [hi]

theorem restrictionL1_tail_norm_mono {C D : Set I} (hCD : C ⊆ D) (f : ellOneOn 𝕜 I) :
    ‖f - restrictionL1 D f‖ ≤ ‖f - restrictionL1 C f‖ := by
  rw [restrictionL1_tail_eq, restrictionL1_tail_eq]
  exact restrictionL1_norm_mono (Set.compl_subset_compl.mpr hCD) f

/-- Removing a region from a finite atomic piece loses at most the total mass
of that region. This is the quantitative invariant in Lemma 6.1. -/
theorem restrictionL1_mass_after_remove (A : Finset I) (C : Set I) (f : ellOneOn 𝕜 I) :
    ‖restrictionL1 (A : Set I) f‖ - ‖restrictionL1 C f‖ ≤
      ‖restrictionL1 (A.filter (fun i => i ∉ C) : Set I) f‖ := by
  have heq : restrictionL1 (A : Set I) f -
      restrictionL1 (A.filter (fun i => i ∉ C) : Set I) f =
      restrictionL1 ((A : Set I) ∩ C) f := by
    ext i
    by_cases hiA : i ∈ A <;> by_cases hiC : i ∈ C <;> simp [hiA, hiC]
  have hb := norm_sub_norm_le (restrictionL1 (A : Set I) f)
    (restrictionL1 (A.filter (fun i => i ∉ C) : Set I) f)
  rw [heq] at hb
  have hm := restrictionL1_norm_mono (Set.inter_subset_right : (A : Set I) ∩ C ⊆ C) f
  linarith

/-- Finite coordinate truncations approximate each ℓ¹ vector in norm. -/
theorem exists_finite_restrictionL1_tail (f : ellOneOn 𝕜 I) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset I, ‖f - restrictionL1 (s : Set I) f‖ < ε := by
  have h := lp.hasSum_single (by norm_num : (1 : ENNReal) ≠ ⊤) f
  obtain ⟨s, hs⟩ := (h.eventually (Metric.ball_mem_nhds f hε)).exists
  refine ⟨s, ?_⟩
  rw [restrictionL1_finset, ← dist_eq_norm, dist_comm]
  exact hs

/-- Any strict lower bound for the total mass is exceeded on a finite subset
of the actual support. This keeps the support requirement in the paper. -/
theorem exists_finite_restrictionL1_mass (f : ellOneOn 𝕜 I) {r : ℝ} (hr : r < ‖f‖) :
    ∃ s : Finset I, (s : Set I) ⊆ Function.support f ∧ r < ‖restrictionL1 (s : Set I) f‖ := by
  obtain ⟨s, hs⟩ := exists_finite_restrictionL1_tail f (sub_pos.mpr hr)
  let t := s.filter (fun i => f i ≠ 0)
  have heq : restrictionL1 (t : Set I) f = restrictionL1 (s : Set I) f := by
    ext i
    by_cases hi : i ∈ s <;> by_cases hfi : f i = 0 <;>
      simp [restrictionL1_apply, restrictL1_apply, t, hi, hfi]
  refine ⟨t, ?_, ?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · rw [heq]
    have hnorm := norm_sub_norm_le f (restrictionL1 (s : Set I) f)
    linarith

/-- The finite mass budget used in Lemma 5.4: disjoint coordinate sets cannot
carry more mass, in total, than the whole vector. -/
theorem sum_restrictionL1_norm_le {J : Type*} (s : Finset J) (C : J → Set I)
    (hC : Set.PairwiseDisjoint (s : Set J) C) (f : ellOneOn 𝕜 I) :
    (∑ j ∈ s, ‖restrictionL1 (C j) f‖) ≤ ‖f‖ := by
  classical
  have heq : (∑ j ∈ s, ‖restrictionL1 (C j) f‖) =
      ‖restrictionL1 (⋃ j ∈ s, C j) f‖ := by
    induction s using Finset.induction_on with
    | empty => simp [ellOneOn_norm_eq_tsum]
    | @insert j s hj ih =>
      have hd : Disjoint (C j) (⋃ k ∈ s, C k) := by
        rw [Set.disjoint_iUnion_right]
        intro k
        rw [Set.disjoint_iUnion_right]
        intro hk
        exact hC (by simp) (by simp [hk]) (by intro h; subst k; exact hj hk)
      have hu : (⋃ k ∈ insert j s, C k) = C j ∪ ⋃ k ∈ s, C k := by
        ext i
        simp
      rw [Finset.sum_insert hj, hu, restrictionL1_norm_union _ _ hd]
      rw [ih (by
        intro a ha b hb hab
        exact hC (by simp [ha]) (by simp [hb]) hab)]
  rw [heq]
  exact restrictL1_norm_le _ f

end JLMS
