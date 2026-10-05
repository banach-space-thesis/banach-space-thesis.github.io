import JFA.CZeroTopology
import Mathlib.Topology.ContinuousMap.Compact

/-! Currying for the actual C₀(M × L) spaces with compact Hausdorff M.
The compact tails supply the uniform control needed for continuity into C₀(L)
and for uniform vanishing at infinity of continuous families over M. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Topology Filter Set
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {M L : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L]

theorem czero_compact_tail {A : Type*} [TopologicalSpace A]
    (f : C₀(A, 𝕜)) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set A, IsCompact K ∧ ∀ x ∉ K, ‖f x‖ < ε := by
  obtain ⟨K, hK, hbound⟩ := mem_cocompact.mp
    (Metric.tendsto_nhds.mp (zero_at_infty f) ε hε)
  exact ⟨K, hK, fun x hx => by simpa only [dist_zero_right] using hbound hx⟩

def productSliceCocompact (m : M) : CocompactMap L (M × L) where
  toFun := fun l => (m, l)
  continuous_toFun := continuous_const.prodMk continuous_id
  cocompact_tendsto' := CocompactMap.tendsto_of_forall_preimage fun _ hK =>
    (hK.image continuous_snd).of_isClosed_subset
      (hK.isClosed.preimage (continuous_const.prodMk continuous_id))
      (fun l hl => ⟨(m, l), hl, rfl⟩)

def czeroProductSlice (h : C₀(M × L, 𝕜)) (m : M) : C₀(L, 𝕜) :=
  h.comp (productSliceCocompact m)

omit [CompactSpace M] [LocallyCompactSpace L] in
@[simp] theorem czeroProductSlice_apply (h : C₀(M × L, 𝕜)) (m : M) (l : L) :
    czeroProductSlice h m l = h (m, l) := rfl

omit [CompactSpace M] [LocallyCompactSpace L] in
theorem continuous_czeroProductSlice (h : C₀(M × L, 𝕜)) : Continuous (czeroProductSlice h) := by
  apply continuous_iff_continuousAt.mpr
  intro m₀
  apply ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly.mpr
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨K, hK, htail⟩ := czero_compact_tail h (ε / 3) (by positivity)
  let A : Set L := Prod.snd '' K
  have hA : IsCompact A := hK.image continuous_snd
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let g : C(M × A, 𝕜) :=
    ⟨fun p => h (p.1, p.2.val), h.continuous.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))⟩
  have hnear : ∀ᶠ m in 𝓝 m₀, dist (g.curry m₀) (g.curry m) < ε :=
    (Metric.tendsto_nhds.mp g.curry.continuous.continuousAt ε hε).mono
      (fun m hm => by simpa only [dist_comm] using hm)
  apply hnear.mono
  intro m hm l
  change dist (h (m₀, l)) (h (m, l)) < ε
  by_cases hl : l ∈ A
  · exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist
      (f := g.curry m₀) (g := g.curry m) ⟨l, hl⟩) hm
  · have hout (n : M) : (n, l) ∉ K := fun hnl => hl ⟨(n, l), hnl, rfl⟩
    have h₀ := htail (m₀, l) (hout m₀)
    have h₁ := htail (m, l) (hout m)
    calc
      dist (h (m₀, l)) (h (m, l)) ≤ ‖h (m₀, l)‖ + ‖h (m, l)‖ := dist_le_norm_add_norm _ _
      _ < ε / 3 + ε / 3 := add_lt_add h₀ h₁
      _ < ε := by linarith

def czeroProductCurry (h : C₀(M × L, 𝕜)) : C(M, C₀(L, 𝕜)) :=
  ⟨czeroProductSlice h, continuous_czeroProductSlice h⟩

omit [LocallyCompactSpace L] in
theorem norm_czeroProductCurry (h : C₀(M × L, 𝕜)) : ‖czeroProductCurry h‖ = ‖h‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg h)).mpr
    intro m
    change ‖(czeroProductSlice h m).toBCF‖ ≤ ‖h‖
    apply (BoundedContinuousFunction.norm_le (norm_nonneg h)).mpr
    intro l
    exact h.toBCF.norm_coe_le_norm (m, l)
  · change ‖h.toBCF‖ ≤ ‖czeroProductCurry h‖
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro p
    exact ((czeroProductCurry h p.1).toBCF.norm_coe_le_norm p.2).trans
      ((czeroProductCurry h).norm_coe_le_norm p.1)

def czeroProductCurryIsometry : C₀(M × L, 𝕜) →ₗᵢ[𝕜] C(M, C₀(L, 𝕜)) where
  toFun := czeroProductCurry
  map_add' := by intro h k; ext m l; rfl
  map_smul' := by intro a h; ext m l; rfl
  norm_map' := norm_czeroProductCurry

omit [T2Space M] [LocallyCompactSpace L] [T2Space L] in
theorem exists_uniform_czero_tail (f : C(M, C₀(L, 𝕜))) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set L, IsCompact K ∧ ∀ m l, l ∉ K → ‖f m l‖ < ε := by
  classical
  choose K hK htail using fun m => czero_compact_tail (f m) (ε / 2) (half_pos hε)
  let U : M → Set M := fun m => {n | ‖f n - f m‖ < ε / 2}
  have hopen : ∀ m, IsOpen (U m) := fun m =>
    isOpen_lt (f.continuous.sub continuous_const).norm continuous_const
  have hcover : (univ : Set M) ⊆ ⋃ m, U m := by
    intro m hm
    exact mem_iUnion.mpr ⟨m, by simpa only [U, mem_setOf_eq, sub_self, norm_zero] using half_pos hε⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  refine ⟨⋃ m ∈ t, K m, t.isCompact_biUnion (fun m hm => hK m), ?_⟩
  intro n l hl
  obtain ⟨m, hm, hn⟩ := mem_iUnion₂.mp (ht (mem_univ n))
  have hlK : l ∉ K m := fun hlm => hl (mem_iUnion₂.mpr ⟨m, hm, hlm⟩)
  have hnear : ‖f n - f m‖ < ε / 2 := hn
  calc
    ‖f n l‖ ≤ ‖f n l - f m l‖ + ‖f m l‖ := by
      simpa only [sub_add_cancel] using norm_add_le (f n l - f m l) (f m l)
    _ ≤ ‖f n - f m‖ + ‖f m l‖ := add_le_add_right ((f n - f m).toBCF.norm_coe_le_norm l) _
    _ < ε / 2 + ε / 2 := add_lt_add hnear (htail m l hlK)
    _ = ε := add_halves ε

def czeroProductUncurry (f : C(M, C₀(L, 𝕜))) : C₀(M × L, 𝕜) where
  toFun := fun p => f p.1 p.2
  continuous_toFun := BoundedContinuousFunction.continuous_eval.comp
    (((ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp f.continuous).comp continuous_fst).prodMk
      continuous_snd)
  zero_at_infty' := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨K, hK, htail⟩ := exists_uniform_czero_tail f ε hε
    apply Filter.eventually_of_mem (isCompact_univ.prod hK).compl_mem_cocompact
    intro p hp
    have hl : p.2 ∉ K := fun hl => hp ⟨mem_univ _, hl⟩
    simpa only [dist_zero_right] using htail p.1 p.2 hl

omit [T2Space M] [LocallyCompactSpace L] [T2Space L] in
@[simp] theorem czeroProductUncurry_apply (f : C(M, C₀(L, 𝕜))) (m : M) (l : L) :
    czeroProductUncurry f (m, l) = f m l := rfl

omit [LocallyCompactSpace L] in
@[simp] theorem czeroProductCurry_uncurry (f : C(M, C₀(L, 𝕜))) :
    czeroProductCurry (czeroProductUncurry f) = f := by
  ext m l
  rfl

omit [LocallyCompactSpace L] in
@[simp] theorem czeroProductUncurry_curry (h : C₀(M × L, 𝕜)) :
    czeroProductUncurry (czeroProductCurry h) = h := by
  ext p
  rfl

def czeroProductEquiv : C₀(M × L, 𝕜) ≃ₗᵢ[𝕜] C(M, C₀(L, 𝕜)) :=
  LinearIsometryEquiv.ofSurjective czeroProductCurryIsometry
    (fun f => ⟨czeroProductUncurry f, czeroProductCurry_uncurry f⟩)

omit [LocallyCompactSpace L] in
@[simp] theorem czeroProductEquiv_symm_apply (f : C(M, C₀(L, 𝕜))) (m : M) (l : L) :
    (czeroProductEquiv (𝕜 := 𝕜) (M := M) (L := L)).symm f (m, l) = f m l := by
  have h := congrArg (fun g : C(M, C₀(L, 𝕜)) => g m l)
    ((czeroProductEquiv (𝕜 := 𝕜) (M := M) (L := L)).apply_symm_apply f)
  exact h

end JFA
