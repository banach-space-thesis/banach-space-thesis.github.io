import ThesisCommon.Analysis.LpOperators
import ThesisCommon.Analysis.UniformPrimariness
import Mathlib.Topology.Sequences
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Order.Filter.Map

/-! Actual bounded sequences converging to zero along a filter, with the
inherited supremum norm. No freeness or diagonalisation hypothesis is part of
the space. Improper filters are allowed so that the trace-filter convention
in Section 6 is automatic. -/
noncomputable section
open Filter Topology
open scoped ENNReal Cardinal
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
universe u
variable (𝕜 : Type*) [RCLike 𝕜] {Γ : Type u}

/-- The genuine subspace c_F(Γ) of the actual bounded scalar families. -/
def filterNullSubmodule (F : Filter Γ) : Submodule 𝕜 (lp (fun _ : Γ => 𝕜) ∞) where
  carrier := {x | Tendsto (fun γ => x γ) F (𝓝 0)}
  zero_mem' := tendsto_const_nhds
  add_mem' hx hy := by simpa using hx.add hy
  smul_mem' c x hx := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : Γ => c) F (𝓝 c)).smul hx

abbrev FilterNullSpace (F : Filter Γ) := ↥(filterNullSubmodule 𝕜 F)

instance filterNullSpace_normedAddCommGroup (F : Filter Γ) :
    NormedAddCommGroup (FilterNullSpace 𝕜 F) :=
  inferInstanceAs (NormedAddCommGroup ↥(filterNullSubmodule 𝕜 F))

instance filterNullSpace_normedSpace (F : Filter Γ) : NormedSpace 𝕜 (FilterNullSpace 𝕜 F) :=
  inferInstanceAs (NormedSpace 𝕜 ↥(filterNullSubmodule 𝕜 F))

variable {𝕜} (F : Filter Γ)

theorem filterNullSubmodule_isClosed :
    IsClosed (filterNullSubmodule 𝕜 F : Set (lp (fun _ : Γ => 𝕜) ∞)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro s x hs hx
  change Tendsto (fun γ => x γ) F (𝓝 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hx (ε / 2) (half_pos hε)
  have hsN := hs N
  change Tendsto (fun γ => s N γ) F (𝓝 0) at hsN
  filter_upwards [Metric.tendsto_nhds.mp hsN (ε / 2) (half_pos hε)] with γ hγ
  calc
    dist (x γ) 0 ≤ dist (x γ) (s N γ) + dist (s N γ) 0 := dist_triangle _ _ _
    _ ≤ dist x (s N) + dist (s N γ) 0 := by
      apply add_le_add_right
      simpa only [dist_eq_norm, lp.coeFn_sub, Pi.sub_apply] using
        lp.norm_apply_le_norm ENNReal.top_ne_zero (x - s N) γ
    _ < ε := by have h := hN N le_rfl; rw [dist_comm] at h; linarith

instance filterNullSpace_completeSpace : CompleteSpace (FilterNullSpace 𝕜 F) :=
  (filterNullSubmodule_isClosed (𝕜 := 𝕜) F).completeSpace_coe

namespace FilterNullSpace
variable {F}

instance : CoeFun (FilterNullSpace 𝕜 F) (fun _ => Γ → 𝕜) := ⟨fun x γ => x.val γ⟩

@[ext] theorem ext {x y : FilterNullSpace 𝕜 F} (h : ∀ γ, x γ = y γ) : x = y :=
  Subtype.ext (lp.ext (funext h))

@[simp] theorem zero_apply (γ : Γ) : (0 : FilterNullSpace 𝕜 F) γ = 0 := rfl
@[simp] theorem add_apply (x y : FilterNullSpace 𝕜 F) (γ : Γ) :
    (x + y) γ = x γ + y γ := rfl
@[simp] theorem smul_apply (c : 𝕜) (x : FilterNullSpace 𝕜 F) (γ : Γ) :
    (c • x) γ = c • x γ := rfl

theorem tendsto_zero (x : FilterNullSpace 𝕜 F) : Tendsto x F (𝓝 0) := x.property

theorem norm_apply_le (x : FilterNullSpace 𝕜 F) (γ : Γ) : ‖x γ‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero x.val γ

theorem norm_le {x : FilterNullSpace 𝕜 F} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ γ, ‖x γ‖ ≤ C) : ‖x‖ ≤ C := lp.norm_le_of_forall_le hC h

/-- Multiplicative domination by a filter-null vector preserves both
boundedness and filter convergence. -/
def ofDominated (x : FilterNullSpace 𝕜 F) (f : Γ → 𝕜) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ γ, ‖f γ‖ ≤ C * ‖x γ‖) : FilterNullSpace 𝕜 F :=
  ⟨⟨f, mem_lp_of_norm_le_mul x.val f hC hf⟩, by
    change Tendsto f F (𝓝 0)
    apply squeeze_zero_norm hf
    simpa only [norm_zero, mul_zero] using tendsto_const_nhds.mul x.tendsto_zero.norm⟩

@[simp] theorem ofDominated_apply (x : FilterNullSpace 𝕜 F) (f : Γ → 𝕜)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ γ, ‖f γ‖ ≤ C * ‖x γ‖) (γ : Γ) :
    ofDominated x f hC hf γ = f γ := rfl

theorem norm_ofDominated_le (x : FilterNullSpace 𝕜 F) (f : Γ → 𝕜)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ γ, ‖f γ‖ ≤ C * ‖x γ‖) :
    ‖ofDominated x f hC hf‖ ≤ C * ‖x‖ :=
  lp_norm_le_mul_of_pointwise x.val (ofDominated x f hC hf).val hC hf

end FilterNullSpace

/-- The source's epsilon definition, with its strict sublevel sets. -/
theorem mem_filterNullSubmodule_iff (x : lp (fun _ : Γ => 𝕜) ∞) :
    x ∈ filterNullSubmodule 𝕜 F ↔
      ∀ ε : ℝ, 0 < ε → {γ | ‖x γ‖ < ε} ∈ F := by
  change Tendsto (fun γ => x γ) F (𝓝 0) ↔ _
  simp only [Metric.tendsto_nhds, dist_zero_right, Filter.Eventually]

/-- For the improper filter every bounded family belongs to c_F(Γ). -/
theorem filterNullSubmodule_bot : filterNullSubmodule 𝕜 (⊥ : Filter Γ) = ⊤ := by
  ext x
  simp [filterNullSubmodule]

/-- The closed coordinate subspace X_F(A), with its inherited supremum norm. -/
def filterSupportedSubmodule (A : Set Γ) : Submodule 𝕜 (FilterNullSpace 𝕜 F) where
  carrier := {x | ∀ γ, γ ∉ A → x γ = 0}
  zero_mem' := by simp
  add_mem' hx hy := by intro γ hγ; simp [hx γ hγ, hy γ hγ]
  smul_mem' c x hx := by intro γ hγ; simp [hx γ hγ]

abbrev FilterSupportedSpace (A : Set Γ) := ↥(filterSupportedSubmodule (𝕜 := 𝕜) F A)

instance filterSupportedSpace_normedAddCommGroup (A : Set Γ) :
    NormedAddCommGroup (FilterSupportedSpace (𝕜 := 𝕜) F A) :=
  inferInstanceAs (NormedAddCommGroup ↥(filterSupportedSubmodule (𝕜 := 𝕜) F A))

instance filterSupportedSpace_normedSpace (A : Set Γ) :
    NormedSpace 𝕜 (FilterSupportedSpace (𝕜 := 𝕜) F A) :=
  inferInstanceAs (NormedSpace 𝕜 ↥(filterSupportedSubmodule (𝕜 := 𝕜) F A))

/-- Coordinate evaluation on the actual filter-null subspace. -/
def filterCoordinate (γ : Γ) : FilterNullSpace 𝕜 F →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun x => x γ
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (fun x => by simpa using x.norm_apply_le γ)

theorem filterSupportedSubmodule_isClosed (A : Set Γ) :
    IsClosed (filterSupportedSubmodule (𝕜 := 𝕜) F A : Set (FilterNullSpace 𝕜 F)) := by
  change IsClosed {x : FilterNullSpace 𝕜 F | ∀ γ, γ ∉ A → filterCoordinate F γ x = 0}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun γ => isClosed_iInter fun _ =>
    isClosed_eq (filterCoordinate F γ).continuous continuous_const

instance filterSupportedSpace_completeSpace (A : Set Γ) :
    CompleteSpace (FilterSupportedSpace (𝕜 := 𝕜) F A) :=
  (filterSupportedSubmodule_isClosed (𝕜 := 𝕜) F A).completeSpace_coe

/-- The actual coordinate mask, not a hypothesized projection. -/
def filterCoordinateProjection (A : Set Γ) : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F :=
  LinearMap.mkContinuous
    { toFun := fun x => FilterNullSpace.ofDominated x (fun γ => if γ ∈ A then x γ else 0)
        zero_le_one (fun γ => by by_cases h : γ ∈ A <;> simp [h])
      map_add' := by intro x y; ext γ; by_cases h : γ ∈ A <;> simp [h]
      map_smul' := by intro c x; ext γ; by_cases h : γ ∈ A <;> simp [h] }
    1 (by
      intro x
      exact FilterNullSpace.norm_ofDominated_le x
        (fun γ => if γ ∈ A then x γ else 0) zero_le_one
          (fun γ => by by_cases h : γ ∈ A <;> simp [h]))

@[simp] theorem filterCoordinateProjection_apply (A : Set Γ) (x : FilterNullSpace 𝕜 F) (γ : Γ) :
    filterCoordinateProjection F A x γ = if γ ∈ A then x γ else 0 := rfl

theorem norm_filterCoordinateProjection_le (A : Set Γ) :
    ‖filterCoordinateProjection (𝕜 := 𝕜) F A‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Coordinate projection with its range explicitly restricted to X_F(A). -/
def filterProjectionTo (A : Set Γ) :
    FilterNullSpace 𝕜 F →L[𝕜] FilterSupportedSpace (𝕜 := 𝕜) F A :=
  (filterCoordinateProjection F A).codRestrict (filterSupportedSubmodule F A)
    (fun x γ hγ => by simp [hγ])

@[simp] theorem filterProjectionTo_apply (A : Set Γ) (x : FilterNullSpace 𝕜 F) :
    (filterProjectionTo F A x).val = filterCoordinateProjection F A x := rfl

/-- Every bounded multiplier acts continuously on the filter-null space. -/
def filterMultiplier (a : lp (fun _ : Γ => 𝕜) ∞) :
    FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F :=
  LinearMap.mkContinuous
    { toFun := fun x => FilterNullSpace.ofDominated x (fun γ => a γ * x γ)
        (norm_nonneg a) (fun γ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right
            (lp.norm_apply_le_norm ENNReal.top_ne_zero a γ) (norm_nonneg _))
      map_add' := by intro x y; ext γ; simp [mul_add]
      map_smul' := by intro c x; ext γ; simp [smul_eq_mul, mul_left_comm] }
    ‖a‖ (fun x => FilterNullSpace.norm_ofDominated_le x _ (norm_nonneg a) (fun γ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (lp.norm_apply_le_norm ENNReal.top_ne_zero a γ) (norm_nonneg _)))

@[simp] theorem filterMultiplier_apply (a : lp (fun _ : Γ => 𝕜) ∞)
    (x : FilterNullSpace 𝕜 F) (γ : Γ) : filterMultiplier F a x γ = a γ * x γ := rfl

theorem norm_filterMultiplier_le (a : lp (fun _ : Γ => 𝕜) ∞) :
    ‖filterMultiplier F a‖ ≤ ‖a‖ := LinearMap.mkContinuous_norm_le _ (norm_nonneg a) _

/-- The trace filter from the source. It can be improper even when F is proper. -/
def filterTrace (A : Set Γ) : Filter A := Filter.comap Subtype.val F

theorem mem_filterTrace_iff (A : Set Γ) (B : Set A) :
    B ∈ filterTrace F A ↔ (Subtype.val '' B) ∪ Aᶜ ∈ F := by
  rw [filterTrace, Filter.mem_comap']
  have heq : {γ | ∀ ⦃α : A⦄, α.val = γ → α ∈ B} = (Subtype.val '' B) ∪ Aᶜ := by
    ext γ
    constructor
    · intro h
      by_cases hγ : γ ∈ A
      · exact Or.inl ⟨⟨γ, hγ⟩, h rfl, rfl⟩
      · exact Or.inr hγ
    · rintro (⟨β, hβ, rfl⟩ | hγ) α hα
      · have : α = β := Subtype.ext hα
        simpa only [this] using hβ
      · exact False.elim (hγ (hα ▸ α.property))
  rw [heq]

/-- Co-small filters for every infinite cardinal μ, including singular μ.
Only finite unions of small complements are required for a filter. -/
def coSmallFilter (μ : Cardinal.{u}) (hμ : Cardinal.aleph0 ≤ μ) : Filter Γ where
  sets := {A | Cardinal.mk (Aᶜ : Set Γ) < μ}
  univ_sets := by simpa using (Cardinal.aleph0_pos.trans_le hμ)
  sets_of_superset := by
    intro A B hA hAB
    exact (Cardinal.mk_le_mk_of_subset (Set.compl_subset_compl.mpr hAB)).trans_lt hA
  inter_sets := by
    intro A B hA hB
    change Cardinal.mk ((A ∩ B)ᶜ : Set Γ) < μ
    rw [Set.compl_inter]
    exact (Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt hμ hA hB)

@[simp] theorem mem_coSmallFilter_iff (μ : Cardinal.{u}) (hμ : Cardinal.aleph0 ≤ μ)
    (A : Set Γ) : A ∈ coSmallFilter (Γ := Γ) μ hμ ↔ Cardinal.mk (Aᶜ : Set Γ) < μ := Iff.rfl

theorem coSmallFilter_neBot (μ : Cardinal.{u}) (hμ : Cardinal.aleph0 ≤ μ)
    (hμΓ : μ ≤ Cardinal.mk Γ) : (coSmallFilter (Γ := Γ) μ hμ).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have hempty : (∅ : Set Γ) ∈ coSmallFilter (Γ := Γ) μ hμ := h ▸ Filter.mem_bot
  have : Cardinal.mk Γ < μ := by simpa using hempty
  exact (not_lt_of_ge hμΓ) this

end ThesisCommon
