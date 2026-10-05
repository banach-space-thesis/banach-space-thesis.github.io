import PosetsCommon.CZeroSum

/-! Flattening a dependent c₀ sum of c₀ sums, with the exact supremum norm.
Neither countability nor completeness of the index or coordinate spaces is needed. -/

noncomputable section
namespace ThesisCommon
open Filter Topology
open scoped ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {I : Type*} {J : I → Type*}
variable (X : ∀ i, J i → Type*) [∀ i j, NormedAddCommGroup (X i j)]
  [∀ i j, NormedSpace 𝕜 (X i j)]

theorem cZeroSum_norm_large_finite {P : Type*} {Y : P → Type*}
    [∀ p, NormedAddCommGroup (Y p)] [∀ p, NormedSpace 𝕜 (Y p)]
    (f : DependentCZeroSum 𝕜 Y) {ε : ℝ} (hε : 0 < ε) :
    {p | ¬ ‖f.val p‖ < ε}.Finite := by
  simpa only [dist_zero_right, norm_norm] using
    (mem_cofinite.mp ((Metric.tendsto_nhds.mp f.property) ε hε))

def cZeroSumFlattenValue (f : DependentCZeroSum 𝕜 (fun i => DependentCZeroSum 𝕜 (X i))) :
    DependentCZeroSum 𝕜 (fun p : Σ i, J i => X p.1 p.2) :=
  ⟨⟨fun p => (f.val p.1).val p.2, memℓp_infty ⟨‖f‖, by
    rintro _ ⟨p, rfl⟩
    exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (f.val p.1).val p.2).trans
      (lp.norm_apply_le_norm ENNReal.top_ne_zero f.val p.1)⟩⟩, by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let U := {i | ¬ ‖f.val i‖ < ε}
    let S := fun i => {j | ¬ ‖(f.val i).val j‖ < ε}
    have hU : U.Finite := cZeroSum_norm_large_finite f hε
    have hS (i) : (S i).Finite := cZeroSum_norm_large_finite (f.val i) hε
    have hf : (⋃ i ∈ U, Sigma.mk i '' S i).Finite :=
      hU.biUnion (fun i _ => (hS i).image (Sigma.mk i))
    filter_upwards [hf.compl_mem_cofinite] with p hp
    rw [dist_zero_right, norm_norm]
    by_cases hi : ‖f.val p.1‖ < ε
    · exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (f.val p.1).val p.2).trans_lt hi
    · by_contra hj
      exact hp (Set.mem_iUnion₂.mpr ⟨p.1, hi, ⟨p.2, hj, rfl⟩⟩)⟩

def cZeroSumSlice (f : DependentCZeroSum 𝕜 (fun p : Σ i, J i => X p.1 p.2)) (i : I) :
    DependentCZeroSum 𝕜 (X i) :=
  ⟨⟨fun j => f.val ⟨i, j⟩, memℓp_infty ⟨‖f‖, by
    rintro _ ⟨j, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero f.val ⟨i, j⟩⟩⟩,
    f.property.comp (show Function.Injective (Sigma.mk i : J i → Σ k, J k) from
      fun a b h => by simpa using h).tendsto_cofinite⟩

theorem cZeroSumSlice_norm_le (f : DependentCZeroSum 𝕜 (fun p : Σ i, J i => X p.1 p.2))
    (i : I) : ‖cZeroSumSlice X f i‖ ≤ ‖f‖ :=
  lp.norm_le_of_forall_le (norm_nonneg f)
    (fun j => lp.norm_apply_le_norm ENNReal.top_ne_zero f.val ⟨i, j⟩)

def cZeroSumUnflattenValue (f : DependentCZeroSum 𝕜 (fun p : Σ i, J i => X p.1 p.2)) :
    DependentCZeroSum 𝕜 (fun i => DependentCZeroSum 𝕜 (X i)) :=
  ⟨⟨cZeroSumSlice X f, memℓp_infty ⟨‖f‖, by
    rintro _ ⟨i, rfl⟩; exact cZeroSumSlice_norm_le X f i⟩⟩, by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hf := cZeroSum_norm_large_finite f (half_pos hε)
    filter_upwards [(hf.image Sigma.fst).compl_mem_cofinite] with i hi
    rw [dist_zero_right, norm_norm]
    apply lt_of_le_of_lt _ (half_lt_self hε)
    apply lp.norm_le_of_forall_le (le_of_lt (half_pos hε))
    intro j
    change ‖f.val ⟨i, j⟩‖ ≤ ε / 2
    apply le_of_lt
    by_contra hn
    exact hi ⟨⟨i, j⟩, hn, rfl⟩⟩

theorem cZeroSumFlattenValue_norm
    (f : DependentCZeroSum 𝕜 (fun i => DependentCZeroSum 𝕜 (X i))) :
    ‖cZeroSumFlattenValue X f‖ = ‖f‖ := by
  apply le_antisymm
  · apply lp.norm_le_of_forall_le (norm_nonneg f)
    intro p
    exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (f.val p.1).val p.2).trans
      (lp.norm_apply_le_norm ENNReal.top_ne_zero f.val p.1)
  · apply lp.norm_le_of_forall_le (norm_nonneg (cZeroSumFlattenValue X f))
    intro i
    apply lp.norm_le_of_forall_le (norm_nonneg (cZeroSumFlattenValue X f))
    intro j
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero (cZeroSumFlattenValue X f).val ⟨i, j⟩

def cZeroSumFlattenEquiv :
    DependentCZeroSum 𝕜 (fun i => DependentCZeroSum 𝕜 (X i)) ≃ₗᵢ[𝕜]
      DependentCZeroSum 𝕜 (fun p : Σ i, J i => X p.1 p.2) where
  toFun := cZeroSumFlattenValue X
  invFun := cZeroSumUnflattenValue X
  left_inv f := by
    apply Subtype.ext
    apply lp.ext
    funext i
    apply Subtype.ext
    apply lp.ext
    rfl
  right_inv f := by apply Subtype.ext; apply lp.ext; rfl
  map_add' f g := by apply Subtype.ext; apply lp.ext; rfl
  map_smul' a f := by apply Subtype.ext; apply lp.ext; rfl
  norm_map' := cZeroSumFlattenValue_norm X

@[simp] theorem cZeroSumFlattenEquiv_apply
    (f : DependentCZeroSum 𝕜 (fun i => DependentCZeroSum 𝕜 (X i))) (i : I) (j : J i) :
    ((cZeroSumFlattenEquiv X) f).val ⟨i, j⟩ = (f.val i).val j := rfl

@[simp] theorem cZeroSumFlattenEquiv_symm_apply
    (f : DependentCZeroSum 𝕜 (fun p : Σ i, J i => X p.1 p.2)) (i : I) (j : J i) :
    (((cZeroSumFlattenEquiv X).symm f).val i).val j = f.val ⟨i, j⟩ := rfl

end ThesisCommon
