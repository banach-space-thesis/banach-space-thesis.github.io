import JFA.CZeroDiscreteTensor
import JFA.CZeroProduct

/-! Currying on a discrete first factor, with vanishing at infinity in both
coordinates. The finite projection of a compact tail supplies the outer tail;
finitely many compact inner tails supply the reverse construction. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Topology Filter Set
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {D : Type*} [TopologicalSpace D] [DiscreteTopology D]
variable {L : Type*} [TopologicalSpace L] [T2Space L]

def czeroDiscreteCurry (h : C₀(D × L, 𝕜)) : C₀(D, C₀(L, 𝕜)) where
  toFun := czeroProductSlice h
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨K, hK, htail⟩ := czero_compact_tail h (ε / 2) (half_pos hε)
    apply Filter.eventually_of_mem (hK.image continuous_fst).compl_mem_cocompact
    intro d hd
    rw [dist_zero_right]
    apply lt_of_le_of_lt _ (half_lt_self hε)
    change ‖(czeroProductSlice h d).toBCF‖ ≤ ε / 2
    apply (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr
    intro l
    have hp : (d, l) ∉ K := fun hp => hd ⟨(d, l), hp, rfl⟩
    exact (htail (d, l) hp).le

@[simp] theorem czeroDiscreteCurry_apply (h : C₀(D × L, 𝕜)) (d : D) (l : L) :
    czeroDiscreteCurry h d l = h (d, l) := rfl

theorem norm_czeroDiscreteCurry (h : C₀(D × L, 𝕜)) : ‖czeroDiscreteCurry h‖ = ‖h‖ := by
  apply le_antisymm
  · change ‖(czeroDiscreteCurry h).toBCF‖ ≤ ‖h‖
    apply (BoundedContinuousFunction.norm_le (norm_nonneg h)).mpr
    intro d
    change ‖(czeroProductSlice h d).toBCF‖ ≤ ‖h‖
    apply (BoundedContinuousFunction.norm_le (norm_nonneg h)).mpr
    intro l
    exact h.toBCF.norm_coe_le_norm (d, l)
  · change ‖h.toBCF‖ ≤ ‖czeroDiscreteCurry h‖
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro p
    exact ((czeroDiscreteCurry h p.1).toBCF.norm_coe_le_norm p.2).trans
      ((czeroDiscreteCurry h).toBCF.norm_coe_le_norm p.1)

def czeroDiscreteCurryIsometry : C₀(D × L, 𝕜) →ₗᵢ[𝕜] C₀(D, C₀(L, 𝕜)) where
  toFun := czeroDiscreteCurry
  map_add' := by intro h k; ext d l; rfl
  map_smul' := by intro a h; ext d l; rfl
  norm_map' := norm_czeroDiscreteCurry

def czeroDiscreteUncurry (f : C₀(D, C₀(L, 𝕜))) : C₀(D × L, 𝕜) where
  toFun := fun p => f p.1 p.2
  continuous_toFun := BoundedContinuousFunction.continuous_eval.comp
    (((ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp f.continuous).comp continuous_fst).prodMk
      continuous_snd)
  zero_at_infty' := by
    classical
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨I, hI, hout⟩ := czero_vector_compact_tail f (ε / 2) (half_pos hε)
    let t := hI.finite_of_discrete.toFinset
    choose K hK htail using fun d : D => czero_compact_tail (f d) (ε / 2) (half_pos hε)
    let Q : Set (D × L) := ⋃ d ∈ t, ({d} : Set D) ×ˢ K d
    have hQ : IsCompact Q := t.isCompact_biUnion (fun d _ => isCompact_singleton.prod (hK d))
    apply Filter.eventually_of_mem hQ.compl_mem_cocompact
    intro p hp
    rw [dist_zero_right]
    by_cases hd : p.1 ∈ t
    · have hl : p.2 ∉ K p.1 := fun hl =>
        hp (mem_iUnion₂.mpr ⟨p.1, hd, mem_singleton _, hl⟩)
      exact (htail p.1 p.2 hl).trans (half_lt_self hε)
    · exact ((f p.1).toBCF.norm_coe_le_norm p.2).trans_lt
        ((hout p.1 (by simpa only [t, Set.Finite.mem_toFinset] using hd)).trans (half_lt_self hε))

@[simp] theorem czeroDiscreteCurry_uncurry (f : C₀(D, C₀(L, 𝕜))) :
    czeroDiscreteCurry (czeroDiscreteUncurry f) = f := by
  ext d l
  rfl

@[simp] theorem czeroDiscreteUncurry_curry (h : C₀(D × L, 𝕜)) :
    czeroDiscreteUncurry (czeroDiscreteCurry h) = h := by
  ext p
  rfl

def czeroDiscreteProductEquiv : C₀(D × L, 𝕜) ≃ₗᵢ[𝕜] C₀(D, C₀(L, 𝕜)) :=
  LinearIsometryEquiv.ofSurjective czeroDiscreteCurryIsometry
    (fun f => ⟨czeroDiscreteUncurry f, czeroDiscreteCurry_uncurry f⟩)

@[simp] theorem czeroDiscreteProductEquiv_symm_apply (f : C₀(D, C₀(L, 𝕜))) (p : D × L) :
    (czeroDiscreteProductEquiv (𝕜 := 𝕜) (D := D) (L := L)).symm f p = f p.1 p.2 := by
  have h := congrArg (fun g : C₀(D, C₀(L, 𝕜)) => g p.1 p.2)
    ((czeroDiscreteProductEquiv (𝕜 := 𝕜) (D := D) (L := L)).apply_symm_apply f)
  exact h

def czeroDiscreteTensorEquiv :
    InjectiveTensor 𝕜 C₀(D, 𝕜) C₀(L, 𝕜) ≃ₗᵢ[𝕜] C₀(D × L, 𝕜) :=
  (tensorCzeroDiscreteEquiv (𝕜 := 𝕜) (A := D) (X := C₀(L, 𝕜))).trans
    (czeroDiscreteProductEquiv (𝕜 := 𝕜) (D := D) (L := L)).symm

@[simp] theorem czeroDiscreteTensorEquiv_pure (f : C₀(D, 𝕜)) (g : C₀(L, 𝕜)) (p : D × L) :
    (czeroDiscreteTensorEquiv (𝕜 := 𝕜) (D := D) (L := L))
      (injectivePure 𝕜 C₀(D, 𝕜) C₀(L, 𝕜) f g) p = f p.1 * g p.2 := by
  change (czeroDiscreteProductEquiv (𝕜 := 𝕜) (D := D) (L := L)).symm
    ((tensorCzeroDiscreteEquiv (𝕜 := 𝕜) (A := D) (X := C₀(L, 𝕜)))
      (injectivePure 𝕜 C₀(D, 𝕜) C₀(L, 𝕜) f g)) p = _
  rw [czeroDiscreteProductEquiv_symm_apply]
  change tensorCzeroFunction (injectivePure 𝕜 C₀(D, 𝕜) C₀(L, 𝕜) f g) p.1 p.2 = _
  rw [tensorCzeroFunction_pure]
  rfl

end JFA
