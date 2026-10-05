import Posets.WolfeDisjointSynthesis

/-! Disjoint top-cell quotients embed into the closed span of all their
ambient indicators. A single finite-span estimate then controls their
entire c₀ sum. -/
noncomputable section
open Set Filter Topology
namespace Posets
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
variable {𝕜 K I : Type*} [RCLike 𝕜] [TopologicalSpace K] [T2Space K]
  {ι : I → Type*}

theorem wolfeClopenTopIsometry_support
    (H : Set K) [CompactSpace H] (hH : IsClopen H)
    (A : ι₀ → Set K) (hA : ∀ i, IsClopen (A i))
    (f : C(WolfeClopenTopQuotient H A hA, 𝕜)) :
    Function.support (wolfeClopenTopIsometry (𝕜 := 𝕜) H hH A hA f) ⊆ H := by
  intro x hx
  by_contra hxH
  exact hx (wolfeClopenZeroExtend_apply_notMem H hH _ hxH)

variable (H : I → Set K) [∀ i, CompactSpace (H i)]
  (hH : ∀ i, IsClopen (H i)) (hdisj : Pairwise (fun i j => Disjoint (H i) (H j)))
  (A : ∀ i, ι i → Set K) (hA : ∀ i j, IsClopen (A i j))

local instance wolfeLaminarDisjointBlockCompact (i : I) : CompactSpace
    (WolfeClopenTopQuotient (H i) (A i) (hA i)) := inferInstance
local instance wolfeLaminarDisjointBlockGroup (i : I) : NormedAddCommGroup
    C(WolfeClopenTopQuotient (H i) (A i) (hA i), 𝕜) := inferInstance
local instance wolfeLaminarDisjointBlockSpace (i : I) : NormedSpace 𝕜
    C(WolfeClopenTopQuotient (H i) (A i) (hA i), 𝕜) := inferInstance
local instance wolfeLaminarDisjointSumGroup : NormedAddCommGroup
    (JLMS.CZeroSum 𝕜 (fun i => C(WolfeClopenTopQuotient (H i) (A i) (hA i), 𝕜))) := inferInstance
local instance wolfeLaminarDisjointSumSpace : NormedSpace 𝕜
    (JLMS.CZeroSum 𝕜 (fun i => C(WolfeClopenTopQuotient (H i) (A i) (hA i), 𝕜))) := inferInstance

def wolfeLaminarDisjointSum :
    JLMS.CZeroSum 𝕜 (fun i => C(WolfeClopenTopQuotient (H i) (A i) (hA i), 𝕜)) →ₗᵢ[𝕜]
      JLMS.CZero 𝕜 K :=
  wolfeDisjointSumIsometry H hdisj
    (fun i => wolfeClopenTopIsometry (𝕜 := 𝕜) (H i) (hH i) (A i) (hA i))
    (fun i => wolfeClopenTopIsometry_support (H i) (hH i) (A i) (hA i))

theorem wolfeLaminarDisjointSum_mem_closedSpan
    (hcA : ∀ i j, IsCompact (A i j)) (hAH : ∀ i j, A i j ⊆ H i)
    (hunit : ∀ i, ∃ j, A i j = H i)
    (hlam : ∀ i j k, A i j ⊆ A i k ∨ A i k ⊆ A i j ∨ Disjoint (A i j) (A i k))
    (f : JLMS.CZeroSum 𝕜 (fun i => C(WolfeClopenTopQuotient (H i) (A i) (hA i), 𝕜))) :
    wolfeLaminarDisjointSum (𝕜 := 𝕜) H hH hdisj A hA f ∈
      (Submodule.span 𝕜 (range (fun q : Sigma ι =>
        JLMS.clopenIndicator (𝕜 := 𝕜) (A q.1 q.2) (hA q.1 q.2) (hcA q.1 q.2)))).topologicalClosure := by
  let P := Submodule.span 𝕜 (range (fun q : Sigma ι =>
    JLMS.clopenIndicator (𝕜 := 𝕜) (A q.1 q.2) (hA q.1 q.2) (hcA q.1 q.2)))
  have hmem (i : I) : wolfeClopenTopIsometry (𝕜 := 𝕜) (H i) (hH i) (A i) (hA i) (f i) ∈
      P.topologicalClosure := by
    have hi := (wolfeClopenTopIsometry_range (𝕜 := 𝕜) (H i) (hH i) (A i) (hA i)
      (hcA i) (hAH i) (hunit i) (hlam i)).subset (mem_range_self (f i))
    apply closure_mono (s := (Submodule.span 𝕜 (range (fun j =>
      JLMS.clopenIndicator (𝕜 := 𝕜) (A i j) (hA i j) (hcA i j))) : Set (JLMS.CZero 𝕜 K))) ?_ hi
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨⟨i, j⟩, rfl⟩
  apply isClosed_closure.mem_of_tendsto
    (JLMS.hasSum_cZeroSumSynthesis
      (fun i => (wolfeClopenTopIsometry (𝕜 := 𝕜) (H i) (hH i) (A i) (hA i)).toContinuousLinearMap)
      (wolfe_disjoint_finite_sum_bound H hdisj _
        (fun i => wolfeClopenTopIsometry_support (H i) (hH i) (A i) (hA i))) f)
  exact Eventually.of_forall (fun s => P.topologicalClosure.sum_mem (fun i _ => hmem i))

theorem wolfeLaminarDisjointSum_lower_bound {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (hcA : ∀ i j, IsCompact (A i j)) (hAH : ∀ i j, A i j ⊆ H i)
    (hunit : ∀ i, ∃ j, A i j = H i)
    (hlam : ∀ i j k, A i j ⊆ A i k ∨ A i k ⊆ A i j ∨ Disjoint (A i j) (A i k))
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (c : ℝ)
    (hbound : ∀ (s : Finset (Sigma ι)) (a : Sigma ι → 𝕜),
      c * ‖∑ q ∈ s, a q • JLMS.clopenIndicator (𝕜 := 𝕜) (A q.1 q.2) (hA q.1 q.2) (hcA q.1 q.2)‖ ≤
        ‖T (∑ q ∈ s, a q • JLMS.clopenIndicator (𝕜 := 𝕜) (A q.1 q.2) (hA q.1 q.2) (hcA q.1 q.2))‖)
    (f : JLMS.CZeroSum 𝕜 (fun i => C(WolfeClopenTopQuotient (H i) (A i) (hA i), 𝕜))) :
    c * ‖f‖ ≤ ‖T (wolfeLaminarDisjointSum (𝕜 := 𝕜) H hH hdisj A hA f)‖ := by
  have h := wolfe_lower_bound_closedSpan _ T c hbound
    (wolfeLaminarDisjointSum_mem_closedSpan H hH hdisj A hA hcA hAH hunit hlam f)
  simpa only [LinearIsometry.norm_map] using h

end Posets

