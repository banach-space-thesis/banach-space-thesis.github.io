import Posets.AlspachCounterexampleMetrizable
import ThesisCommon.Analysis.ContinuousMapPullback
import Mathlib.Topology.Clopen

/-! The actual compact quotient recording membership in a clopen family.
Its coordinate functions separate points by construction. -/
noncomputable section
open Set Topology TopologicalSpace ThesisCommon
namespace Posets
variable {K ι : Type*} [TopologicalSpace K]

def wolfeClopenCode (A : ι → Set K) (x : K) (i : ι) : Bool := (A i).boolIndicator x

theorem wolfeClopenCode_continuous (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) :
    Continuous (wolfeClopenCode A) :=
  continuous_pi fun i => (continuous_boolIndicator_iff_isClopen (A i)).mpr (hA i)

def WolfeClopenQuotient (A : ι → Set K) (_hA : ∀ i, IsClopen (A i)) :=
  range (wolfeClopenCode A)

instance wolfeClopenQuotient_topology (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) :
    TopologicalSpace (WolfeClopenQuotient A hA) := inferInstanceAs (TopologicalSpace (range (wolfeClopenCode A)))

instance wolfeClopenQuotient_t2 (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) :
    T2Space (WolfeClopenQuotient A hA) := inferInstanceAs (T2Space (range (wolfeClopenCode A)))

instance wolfeClopenQuotient_compact [CompactSpace K]
    (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) : CompactSpace (WolfeClopenQuotient A hA) :=
  isCompact_iff_compactSpace.mp (isCompact_range (wolfeClopenCode_continuous A hA))

instance wolfeClopenQuotient_countable [Countable K]
    (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) : Countable (WolfeClopenQuotient A hA) :=
  (Set.countable_range (wolfeClopenCode A)).to_subtype

instance wolfeClopenQuotient_metrizable [CompactSpace K] [Countable K]
    (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) : MetrizableSpace (WolfeClopenQuotient A hA) :=
  alspach_countable_compact_metrizable _

def wolfeClopenProjection (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) :
    C(K, WolfeClopenQuotient A hA) :=
  ⟨fun x => ⟨wolfeClopenCode A x, mem_range_self x⟩,
    (wolfeClopenCode_continuous A hA).subtype_mk _⟩

theorem wolfeClopenProjection_surjective (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) :
    Function.Surjective (wolfeClopenProjection A hA) := by
  rintro ⟨q, x, rfl⟩
  exact ⟨x, rfl⟩

variable {𝕜 : Type*} [RCLike 𝕜]

def wolfeClopenCoordinate (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) (i : ι) :
    C(WolfeClopenQuotient A hA, 𝕜) :=
  ⟨fun q => if q.val i = true then 1 else 0,
    (continuous_of_discreteTopology : Continuous (fun b : Bool => if b = true then (1 : 𝕜) else 0)).comp
      ((continuous_apply i).comp continuous_subtype_val)⟩

@[simp] theorem wolfeClopenCoordinate_projection (A : ι → Set K)
    (hA : ∀ i, IsClopen (A i)) (i : ι) (x : K) :
    wolfeClopenCoordinate (𝕜 := 𝕜) A hA i (wolfeClopenProjection A hA x) =
      (A i).indicator (fun _ => 1) x := by
  classical
  change (if (A i).boolIndicator x = true then (1 : 𝕜) else 0) = _
  by_cases hx : x ∈ A i
  · simp [hx, (mem_iff_boolIndicator (A i) x).mp hx]
  · simp [hx, (notMem_iff_boolIndicator (A i) x).mp hx]

def wolfeClopenPullIsometry [CompactSpace K]
    (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) :
    C(WolfeClopenQuotient A hA, 𝕜) →ₗᵢ[𝕜] C(K, 𝕜) where
  __ := (continuousMapPullback (𝕜 := 𝕜) (wolfeClopenProjection A hA)).toLinearMap
  norm_map' f := by
    apply le_antisymm
    · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro x
      exact f.norm_coe_le_norm _
    · apply (ContinuousMap.norm_le f (norm_nonneg _)).mpr
      intro q
      obtain ⟨x, rfl⟩ := wolfeClopenProjection_surjective A hA q
      exact (continuousMapPullback (wolfeClopenProjection A hA) f).norm_coe_le_norm x

end Posets


