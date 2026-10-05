import JFA.MrowkaSupport
import JFA.CZeroTensorEmbedding

/-! Reading the family-point values on a discrete product gives a genuine
discrete C₀ function. Compact subsets meet only finitely many such points,
even when the chosen subfamily is uncountable. -/

noncomputable section
open TopologicalSpace Set Filter Topology
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}
variable {D : Type*} [TopologicalSpace D] [DiscreteTopology D]
variable (S : Set 𝒜)
local instance selectedFamilyTopology : TopologicalSpace S := ⊥
local instance selectedFamilyDiscrete : DiscreteTopology S := ⟨rfl⟩

theorem mrowka_product_compact_meets_selected_family_finitely
    {K : Set (D × Mrowka 𝒜)} (hK : IsCompact K) :
    Set.Finite {q : D × S | (q.1, Sum.inr q.2.val) ∈ K} := by
  have hd : (Prod.fst '' K).Finite := (hK.image continuous_fst).finite_of_discrete
  have hA := mrowka_compact_meets_remainder_finitely (hK.image continuous_snd)
  have hS : Set.Finite ((Subtype.val : S → 𝒜) ⁻¹'
      ((Sum.inr : 𝒜 → Mrowka 𝒜) ⁻¹' (Prod.snd '' K))) :=
    hA.preimage Subtype.val_injective.injOn
  apply (hd.prod hS).subset
  intro q hq
  exact ⟨⟨(q.1, Sum.inr q.2.val), hq, rfl⟩, ⟨(q.1, Sum.inr q.2.val), hq, rfl⟩⟩

def mrowkaFamilyReadValues (f : C₀(D × Mrowka 𝒜, 𝕜)) : C₀(D × S, 𝕜) where
  toFun q := f (q.1, Sum.inr q.2.val)
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨K, hK, htail⟩ := czero_vector_compact_tail f ε hε
    rw [cocompact_eq_cofinite]
    filter_upwards [(mrowka_product_compact_meets_selected_family_finitely S hK).compl_mem_cofinite]
      with q hq
    simpa only [dist_zero_right] using htail (q.1, Sum.inr q.2.val) hq

theorem norm_mrowkaFamilyReadValues_le (f : C₀(D × Mrowka 𝒜, 𝕜)) :
    ‖mrowkaFamilyReadValues S f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro q
  exact f.toBCF.norm_coe_le_norm (q.1, Sum.inr q.2.val)

def mrowkaFamilyRead : C₀(D × Mrowka 𝒜, 𝕜) →L[𝕜] C₀(D × S, 𝕜) :=
  LinearMap.mkContinuous {
    toFun := mrowkaFamilyReadValues S
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
    1 (fun f => by simpa only [one_mul] using norm_mrowkaFamilyReadValues_le S f)

@[simp] theorem mrowkaFamilyRead_apply (f : C₀(D × Mrowka 𝒜, 𝕜)) (q : D × S) :
    mrowkaFamilyRead S f q = f (q.1, Sum.inr q.2.val) := rfl

end JFA
