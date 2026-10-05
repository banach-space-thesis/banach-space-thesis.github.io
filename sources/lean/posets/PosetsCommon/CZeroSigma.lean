import PosetsCommon.CZeroSum
import PosetsCommon.CZeroRestriction

noncomputable section
open Filter Topology
open scoped ZeroAtInfty ENNReal
namespace ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜] {I : Type} (K : I → Type) [∀ i, TopologicalSpace (K i)]

def sigmaSliceMap (i : I) : CocompactMap (K i) (Σ i, K i) where
  toFun := Sigma.mk i
  continuous_toFun := continuous_sigmaMk
  cocompact_tendsto' := CocompactMap.tendsto_of_forall_preimage
    (fun _ h => Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage h)

def cZeroSigmaSlice (f : C₀((Σ i, K i), 𝕜)) (i : I) : C₀(K i, 𝕜) :=
  f.comp (sigmaSliceMap K i)

theorem norm_cZeroSigmaSlice_le (f : C₀((Σ i, K i), 𝕜)) (i : I) :
    ‖cZeroSigmaSlice K f i‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    (fun x => f.toBCF.norm_coe_le_norm ⟨i, x⟩)

theorem cZeroSigmaSlice_norm_tendsto (f : C₀((Σ i, K i), 𝕜)) :
    Tendsto (fun i => ‖cZeroSigmaSlice K f i‖) cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨C, hC, hsmall⟩ := hasBasis_cocompact.mem_iff.mp
    ((Metric.tendsto_nhds.mp (zero_at_infty f)) (ε / 2) (half_pos hε))
  obtain ⟨s, t, hs, _, hst⟩ := hC.sigma_exists_finite_sigma_eq C
  filter_upwards [hs.compl_mem_cofinite] with i hi
  rw [dist_zero_right, norm_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (BoundedContinuousFunction.norm_le (le_of_lt (half_pos hε))).mpr
  intro x
  have hx : (⟨i, x⟩ : Σ i, K i) ∉ C := by
    rw [← hst]
    exact fun h => hi h.1
  exact le_of_lt (by simpa only [dist_zero_right] using hsmall hx)

def cZeroSigmaToSum (f : C₀((Σ i, K i), 𝕜)) :
    DependentCZeroSum 𝕜 (fun i => C₀(K i, 𝕜)) :=
  ⟨⟨cZeroSigmaSlice K f, memℓp_infty ⟨‖f‖, by
      rintro _ ⟨i, rfl⟩; exact norm_cZeroSigmaSlice_le K f i⟩⟩,
    cZeroSigmaSlice_norm_tendsto K f⟩

theorem norm_cZeroSigmaToSum (f : C₀((Σ i, K i), 𝕜)) : ‖cZeroSigmaToSum K f‖ = ‖f‖ := by
  apply le_antisymm
  · exact lp.norm_le_of_forall_le (norm_nonneg f) (norm_cZeroSigmaSlice_le K f)
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg (cZeroSigmaToSum K f))).mpr
    rintro ⟨i, x⟩
    exact ((cZeroSigmaSlice K f i).toBCF.norm_coe_le_norm x).trans
      (lp.norm_apply_le_norm ENNReal.top_ne_zero (cZeroSigmaToSum K f).val i)

def cZeroSigmaFromSum (f : DependentCZeroSum 𝕜 (fun i => C₀(K i, 𝕜))) :
    C₀((Σ i, K i), 𝕜) where
  toFun x := f.val x.1 x.2
  continuous_toFun := continuous_sigma_iff.mpr (fun i => (f.val i).continuous)
  zero_at_infty' := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have he := (Metric.tendsto_nhds.mp f.property) (ε / 2) (half_pos hε)
    have hs : {i | ¬ ‖f.val i‖ < ε / 2}.Finite := by
      simpa only [dist_zero_right, norm_norm] using (mem_cofinite.mp he)
    choose C hC hsmall using fun i => hasBasis_cocompact.mem_iff.mp
      ((Metric.tendsto_nhds.mp (zero_at_infty (f.val i))) ε hε)
    have hcompact : IsCompact ({i | ¬ ‖f.val i‖ < ε / 2}.sigma C) :=
      Set.isCompact_sigma hs (fun i _ => hC i)
    filter_upwards [hcompact.compl_mem_cocompact] with x hx
    rw [dist_zero_right]
    by_cases hi : ‖f.val x.1‖ < ε / 2
    · exact ((f.val x.1).toBCF.norm_coe_le_norm x.2).trans_lt (hi.trans (half_lt_self hε))
    · have hxC : x.2 ∉ C x.1 := fun h => hx ⟨hi, h⟩
      simpa only [dist_zero_right] using hsmall x.1 hxC

/-- Restriction to the components is an isometry onto the genuine dependent c₀ sum. -/
def cZeroSigmaIsometryEquiv : C₀((Σ i, K i), 𝕜) ≃ₗᵢ[𝕜]
    DependentCZeroSum 𝕜 (fun i => C₀(K i, 𝕜)) where
  toFun := cZeroSigmaToSum K
  invFun := cZeroSigmaFromSum K
  left_inv f := by ext x; rfl
  right_inv f := by apply Subtype.ext; apply lp.ext; rfl
  map_add' f g := by apply Subtype.ext; apply lp.ext; rfl
  map_smul' a f := by apply Subtype.ext; apply lp.ext; rfl
  norm_map' := norm_cZeroSigmaToSum K

end ThesisCommon
