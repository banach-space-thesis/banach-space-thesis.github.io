import BanachIsometric.SingularPontryaginGradedRing
import BanachIsometric.KoszulTensorCoproduct

/-! The internal graded pieces of the Pontryagin algebra are the literal
images of the homogeneous homology groups under direct-sum insertion. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open SingularAW
open scoped DirectSum

variable (G : Type u) [TopologicalSpace G] [Monoid G] [ContinuousMul G]

def rawPontryaginDegree (n : ℕ) : Submodule ℚ (RawPontryaginAlgebra G) :=
  LinearMap.range (rawPontryaginInclusion G n)

omit [Monoid G] [ContinuousMul G] in
theorem rawPontryaginInclusion_mem_degree (n : ℕ) (a : RawHomology G n) :
    rawPontryaginInclusion G n a ∈ rawPontryaginDegree G n :=
  ⟨a, rfl⟩

omit [Monoid G] [ContinuousMul G] in
theorem rawPontryaginInclusion_injective (n : ℕ) : Function.Injective (rawPontryaginInclusion G n) := by
  intro a b h
  have he := congrArg (DirectSum.component ℚ ℕ (RawHomology G) n) h
  simpa only [rawPontryaginInclusion, DirectSum.component.lof_self] using he

instance rawPontryaginDegree_gradedMonoid : SetLike.GradedMonoid (rawPontryaginDegree G) where
  one_mem := rawPontryaginInclusion_one G ▸ rawPontryaginInclusion_mem_degree G 0 (rawPontryaginUnit G)
  mul_mem := by
    rintro p q _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    rw [rawPontryaginInclusion_mul]
    exact rawPontryaginInclusion_mem_degree G _ _

def rawPontryaginDegreeEquiv (n : ℕ) : RawHomology G n ≃ₗ[ℚ] rawPontryaginDegree G n :=
  LinearEquiv.ofBijective (rawPontryaginInclusion G n).rangeRestrict
    ⟨fun _ _ h => rawPontryaginInclusion_injective G n (congrArg Subtype.val h),
      LinearMap.range_eq_top.mp (rawPontryaginInclusion G n).range_rangeRestrict⟩

omit [Monoid G] [ContinuousMul G] in
theorem rawPontryaginDegree_isInternal : DirectSum.IsInternal (rawPontryaginDegree G) := by
  let E : RawPontryaginAlgebra G ≃ₗ[ℚ] (⨁ n, rawPontryaginDegree G n) :=
    DFinsupp.mapRange.linearEquiv (rawPontryaginDegreeEquiv G)
  have hE : (DirectSum.coeLinearMap (rawPontryaginDegree G)).comp E.toLinearMap = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro a
    change DirectSum.coeLinearMap (rawPontryaginDegree G)
      (E (rawPontryaginInclusion G n a)) = rawPontryaginInclusion G n a
    have he : E (rawPontryaginInclusion G n a) =
        DirectSum.of (fun n => rawPontryaginDegree G n) n (rawPontryaginDegreeEquiv G n a) := by
      change DFinsupp.mapRange (fun i x => rawPontryaginDegreeEquiv G i x)
        (fun i => (rawPontryaginDegreeEquiv G i).map_zero) (DFinsupp.single n a) = _
      exact DFinsupp.mapRange_single
    rw [he, DirectSum.coeLinearMap_of]
    rfl
  have h : DirectSum.coeLinearMap (rawPontryaginDegree G) = E.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := E.surjective x
    change DirectSum.coeLinearMap (rawPontryaginDegree G) (E y) = E.symm (E y)
    rw [LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun hE y
  change Function.Bijective (DirectSum.coeLinearMap (rawPontryaginDegree G))
  rw [h]
  exact E.symm.bijective

instance rawPontryaginDegree_gradedAlgebra : GradedAlgebra (rawPontryaginDegree G) :=
  (rawPontryaginDegree_isInternal G).gradedAlgebra

omit [Monoid G] [ContinuousMul G] in
theorem rawPontryaginDegree_eq_bot_of_subsingleton (n : ℕ) (h : Subsingleton (RawHomology G n)) :
    rawPontryaginDegree G n = ⊥ := by
  apply bot_unique
  rintro _ ⟨a, rfl⟩
  rw [@Subsingleton.elim (RawHomology G n) h a 0, map_zero]
  exact Submodule.zero_mem _

end BanachIsometric.SingularEZ
