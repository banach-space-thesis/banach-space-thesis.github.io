import ThesisCommon.Analysis.ContinuousMapPullback
import Mathlib.Topology.PartitionOfUnity

/-! Ditor's finite-cover averaging construction (Rosenthal, Lemma 2.11).
The domain is the actual finite topological disjoint union of the compact
covering sets. The scalar field can be real or complex. -/

noncomputable section
open Set
open scoped BigOperators
namespace ThesisCommon

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K ι : Type*} [TopologicalSpace K] [CompactSpace K]
  [Fintype ι]

abbrev MilutinCoverSpace (s : ι → Set K) := Σ i, s i

def milutinCoverMap (s : ι → Set K) : C(MilutinCoverSpace s, K) :=
  ContinuousMap.sigma (fun _ => ⟨Subtype.val, continuous_subtype_val⟩)

@[simp] theorem milutinCoverMap_apply (s : ι → Set K) (x : MilutinCoverSpace s) :
    milutinCoverMap s x = x.2.val := rfl

def milutinCoverValue (s : ι → Set K) (f : C(MilutinCoverSpace s, 𝕜))
    (i : ι) (x : K) : 𝕜 := by
  classical
  exact if hx : x ∈ s i then f ⟨i, ⟨x, hx⟩⟩ else 0

theorem milutinCoverValue_continuousOn (s : ι → Set K)
    (f : C(MilutinCoverSpace s, 𝕜)) (i : ι) :
    ContinuousOn (milutinCoverValue s f i) (s i) := by
  rw [continuousOn_iff_continuous_restrict]
  have h : Continuous (fun x : s i => f ⟨i, x⟩) :=
    f.continuous.comp continuous_sigmaMk
  change Continuous (fun x : s i => milutinCoverValue s f i x)
  convert h using 1
  funext x
  simp [milutinCoverValue]

variable (s : ι → Set K) [∀ i, CompactSpace (s i)]

theorem norm_milutinCoverValue_le (f : C(MilutinCoverSpace s, 𝕜)) (i : ι) (x : K) :
    ‖milutinCoverValue s f i x‖ ≤ ‖f‖ := by
  classical
  unfold milutinCoverValue
  split_ifs with hx
  · exact f.norm_coe_le_norm _
  · simpa using norm_nonneg f

def milutinFiniteAverageValue (ρ : PartitionOfUnity ι K)
    (hρ : ρ.IsSubordinate (fun i => interior (s i)))
    (f : C(MilutinCoverSpace s, 𝕜)) : C(K, 𝕜) where
  toFun x := ∑ i, ρ i x • milutinCoverValue s f i x
  continuous_toFun := by
    have h := hρ.continuous_finsum_smul (fun _ => isOpen_interior)
      (fun i => (milutinCoverValue_continuousOn s f i).mono interior_subset)
    simpa only [finsum_eq_sum_of_fintype] using h

theorem norm_milutinFiniteAverageValue_le (ρ : PartitionOfUnity ι K)
    (hρ : ρ.IsSubordinate (fun i => interior (s i)))
    (f : C(MilutinCoverSpace s, 𝕜)) :
    ‖milutinFiniteAverageValue s ρ hρ f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
  intro x
  calc
    ‖∑ i, ρ i x • milutinCoverValue s f i x‖
        ≤ ∑ i, ‖ρ i x • milutinCoverValue s f i x‖ := norm_sum_le _ _
    _ = ∑ i, ρ i x * ‖milutinCoverValue s f i x‖ := by
      congr 1
      funext i
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg i x)]
    _ ≤ ∑ i, ρ i x * ‖f‖ := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (norm_milutinCoverValue_le s f i x) (ρ.nonneg i x)
    _ = ‖f‖ := by
      rw [← Finset.sum_mul]
      have h : ∑ i, ρ i x = 1 := by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
      rw [h, one_mul]

def milutinFiniteAverage (ρ : PartitionOfUnity ι K)
    (hρ : ρ.IsSubordinate (fun i => interior (s i))) :
    C(MilutinCoverSpace s, 𝕜) →L[𝕜] C(K, 𝕜) :=
  LinearMap.mkContinuous
    { toFun := milutinFiniteAverageValue s ρ hρ
      map_add' := by
        intro f g
        ext x
        change (∑ i, ρ i x • milutinCoverValue s (f + g) i x) =
          (∑ i, ρ i x • milutinCoverValue s f i x) +
          (∑ i, ρ i x • milutinCoverValue s g i x)
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        unfold milutinCoverValue
        split_ifs <;> simp [smul_add]
      map_smul' := by
        intro a f
        ext x
        change (∑ i, ρ i x • milutinCoverValue s (a • f) i x) =
          a • (∑ i, ρ i x • milutinCoverValue s f i x)
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        unfold milutinCoverValue
        split_ifs <;> simp [smul_comm] }
    1 (fun f => by simpa only [one_mul] using norm_milutinFiniteAverageValue_le s ρ hρ f)

theorem norm_milutinFiniteAverage_le (ρ : PartitionOfUnity ι K)
    (hρ : ρ.IsSubordinate (fun i => interior (s i))) :
    ‖milutinFiniteAverage (𝕜 := 𝕜) s ρ hρ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem milutinFiniteAverage_comp_pullback (ρ : PartitionOfUnity ι K)
    (hρ : ρ.IsSubordinate (fun i => interior (s i))) :
    (milutinFiniteAverage (𝕜 := 𝕜) s ρ hρ).comp
      (continuousMapPullback (milutinCoverMap s)) =
      ContinuousLinearMap.id 𝕜 C(K, 𝕜) := by
  classical
  ext f x
  change (∑ i, ρ i x • milutinCoverValue s
    (continuousMapPullback (milutinCoverMap s) f) i x) = f x
  have hterm (i : ι) : ρ i x • milutinCoverValue s
      (continuousMapPullback (milutinCoverMap s) f) i x = ρ i x • f x := by
    by_cases hx : x ∈ s i
    · simp [milutinCoverValue, hx]
    · have hz : ρ i x = 0 := by
        by_contra hn
        exact hx (interior_subset (hρ i (subset_closure hn)))
      simp [hz]
  simp_rw [hterm]
  rw [← Finset.sum_smul]
  have h : ∑ i, ρ i x = 1 := by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  rw [h, one_smul]

theorem milutin_finite_cover_averaging [T2Space K]
    (hcover : ∀ x : K, ∃ i, x ∈ interior (s i)) :
    Function.Surjective (milutinCoverMap s) ∧
      ∃ A : C(MilutinCoverSpace s, 𝕜) →L[𝕜] C(K, 𝕜),
        ‖A‖ ≤ 1 ∧ A.comp (continuousMapPullback (milutinCoverMap s)) =
          ContinuousLinearMap.id 𝕜 C(K, 𝕜) := by
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i => interior (s i)) (fun _ => isOpen_interior) (by
      intro x _
      obtain ⟨i, hi⟩ := hcover x
      exact mem_iUnion.mpr ⟨i, hi⟩)
  refine ⟨?_, milutinFiniteAverage s ρ hρ, norm_milutinFiniteAverage_le s ρ hρ,
    milutinFiniteAverage_comp_pullback s ρ hρ⟩
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact ⟨⟨i, ⟨x, interior_subset hi⟩⟩, rfl⟩

/-- The exact norm-one form for nonempty compact spaces. The preceding theorem
also covers the empty-space case, where the only averaging operator has norm zero. -/
theorem milutin_finite_cover_regular_averaging [T2Space K] [Nonempty K]
    (hcover : ∀ x : K, ∃ i, x ∈ interior (s i)) :
    Function.Surjective (milutinCoverMap s) ∧
      ∃ A : C(MilutinCoverSpace s, 𝕜) →L[𝕜] C(K, 𝕜),
        ‖A‖ = 1 ∧ A.comp (continuousMapPullback (milutinCoverMap s)) =
          ContinuousLinearMap.id 𝕜 C(K, 𝕜) := by
  obtain ⟨hs, A, hA, hAJ⟩ := milutin_finite_cover_averaging (𝕜 := 𝕜) s hcover
  refine ⟨hs, A, le_antisymm hA ?_, hAJ⟩
  have h := ContinuousLinearMap.opNorm_comp_le A
    (continuousMapPullback (𝕜 := 𝕜) (milutinCoverMap s))
  rw [hAJ, ContinuousLinearMap.norm_id] at h
  apply h.trans
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (norm_continuousMapPullback_le (𝕜 := 𝕜) (milutinCoverMap s))
      (norm_nonneg A)

end ThesisCommon

