import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Clopen
import Mathlib.Analysis.RCLike.Basic

/-!
# Extension by zero on clopen subsets

Extension by zero is an isometry for the supremum norm. Extensions on
pairwise disjoint clopen sets have finite-sum norm bounded by the largest
coordinate norm; this is the estimate used to synthesize a c₀ family.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [TopologicalSpace X] {s : Set X}

def clopenExtendFunction (hs : IsClopen s) (f : C(s, 𝕜)) : C(X, 𝕜) := by
  classical
  let g (x : X) := if h : x ∈ s then f ⟨x, h⟩ else 0
  refine ⟨g, continuous_iff_continuousAt.mpr (fun x => ?_)⟩
  by_cases hx : x ∈ s
  · have hc : ContinuousOn g s := continuousOn_iff_continuous_restrict.mpr (by
      convert f.continuous using 1
      funext y
      exact dif_pos y.prop)
    exact (hc x hx).continuousAt (hs.isOpen.mem_nhds hx)
  · have hc : ContinuousOn g sᶜ := continuousOn_iff_continuous_restrict.mpr (by
      have hconst : Continuous (fun _ : ↥(sᶜ : Set X) => (0 : 𝕜)) := continuous_const
      convert hconst using 1
      funext y
      exact dif_neg y.prop)
    exact (hc x hx).continuousAt (hs.isClosed.isOpen_compl.mem_nhds hx)

@[simp] theorem clopenExtendFunction_of_mem (hs : IsClopen s) (f : C(s, 𝕜))
    (x : X) (hx : x ∈ s) : clopenExtendFunction hs f x = f ⟨x, hx⟩ := by
  classical
  exact dif_pos hx

@[simp] theorem clopenExtendFunction_of_not_mem (hs : IsClopen s) (f : C(s, 𝕜))
    (x : X) (hx : x ∉ s) : clopenExtendFunction hs f x = 0 := by
  classical
  exact dif_neg hx

variable [CompactSpace X] [CompactSpace s]

def clopenFunctionExtension (hs : IsClopen s) : C(s, 𝕜) →ₗᵢ[𝕜] C(X, 𝕜) where
  toFun := clopenExtendFunction hs
  map_add' f g := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  map_smul' c f := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  norm_map' f := by
    change ‖clopenExtendFunction hs f‖ = ‖f‖
    apply le_antisymm
    · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro x
      by_cases hx : x ∈ s
      · simpa only [clopenExtendFunction_of_mem hs f x hx] using f.norm_coe_le_norm ⟨x, hx⟩
      · simp only [clopenExtendFunction_of_not_mem hs f x hx, norm_zero, norm_nonneg]
    · apply (ContinuousMap.norm_le _ (norm_nonneg (clopenExtendFunction hs f))).mpr
      intro x
      simpa only [clopenExtendFunction_of_mem hs f x.val x.prop] using
        (clopenExtendFunction hs f).norm_coe_le_norm x.val

@[simp] theorem clopenFunctionExtension_apply (hs : IsClopen s) (f : C(s, 𝕜)) (x : X) :
    clopenFunctionExtension (𝕜 := 𝕜) hs f x = clopenExtendFunction hs f x := rfl

theorem norm_sum_clopenFunctionExtensions_le {I : Type*} (s : I → Set X)
    [∀ i, CompactSpace (s i)] (hs : ∀ i, IsClopen (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (f : ∀ i, C(s i, 𝕜)) (t : Finset I) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ i ∈ t, ‖f i‖ ≤ M) :
    ‖∑ i ∈ t, clopenFunctionExtension (𝕜 := 𝕜) (hs i) (f i)‖ ≤ M := by
  classical
  apply (ContinuousMap.norm_le _ hM).mpr
  intro x
  simp only [ContinuousMap.sum_apply]
  by_cases hex : ∃ i ∈ t, x ∈ s i
  · obtain ⟨i, hi, hxi⟩ := hex
    rw [Finset.sum_eq_single i]
    · simpa only [clopenFunctionExtension_apply, clopenExtendFunction_of_mem (hs i) (f i) x hxi]
        using ((f i).norm_coe_le_norm ⟨x, hxi⟩).trans (hf i hi)
    · intro j hj hji
      have hxj : x ∉ s j := fun hxj => Set.disjoint_left.mp (hd hji) hxj hxi
      simp [hxj]
    · intro hni
      exact False.elim (hni hi)
  · have hz (i : I) (hi : i ∈ t) : clopenFunctionExtension (𝕜 := 𝕜) (hs i) (f i) x = 0 := by
      have hxi : x ∉ s i := fun hx => hex ⟨i, hi, hx⟩
      simp [hxi]
    rw [Finset.sum_eq_zero hz, norm_zero]
    exact hM

end JLMS
