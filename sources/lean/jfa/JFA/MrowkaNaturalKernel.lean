import JFA.DisjointCZeroSynthesis
import JFA.MrowkaTopology

/-! Functions vanishing at every family point are exactly the discrete C₀
functions on the natural points. The restriction is proved null at infinity
by a finite singleton cover of each compact superlevel set. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Set Filter Topology
open scoped ZeroAtInfty
namespace JFA
set_option allowUnsafeReducibility true in
attribute [local reducible] Mrowka
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}
local instance naturalKernelTopology : TopologicalSpace (Mrowka 𝒜) := mrowkaTopology 𝒜
variable {D : Type*} [TopologicalSpace D] [DiscreteTopology D]

omit [TopologicalSpace D] [DiscreteTopology D] in
theorem mrowka_naturalPoint_injective :
    Function.Injective (fun q : D × ℕ => ((q.1, Sum.inl q.2) : D × Mrowka 𝒜)) := by
  intro q r h
  exact Prod.ext (congrArg (fun p : D × Mrowka 𝒜 => p.1) h)
    (Sum.inl.inj (congrArg (fun p : D × Mrowka 𝒜 => p.2) h))

def mrowkaNaturalKernel : Submodule 𝕜 C₀(D × Mrowka 𝒜, 𝕜) where
  carrier := {f | ∀ d A, f (d, Sum.inr A) = 0}
  zero_mem' := by
    change ∀ d A, (0 : C₀(D × Mrowka 𝒜, 𝕜)) (d, Sum.inr A) = 0
    intro d A
    rfl
  add_mem' := by intro f g hf hg d A; change f (d, Sum.inr A) + g (d, Sum.inr A) = 0; rw [hf, hg, add_zero]
  smul_mem' := by intro a f hf d A; change a • f (d, Sum.inr A) = 0; rw [hf, smul_zero]

theorem mrowka_natural_singleton_isOpen (q : D × ℕ) :
    IsOpen ({(q.1, Sum.inl q.2)} : Set (D × Mrowka 𝒜)) := by
  rw [← singleton_prod_singleton]
  exact (isOpen_discrete _).prod (mrowka_isOpen_singleton q.2)

theorem mrowka_natural_values_null (f : C₀(D × Mrowka 𝒜, 𝕜))
    (hf : ∀ d A, f (d, Sum.inr A) = 0) :
    Tendsto (fun q : D × ℕ => f (q.1, Sum.inl q.2)) (cocompact (D × ℕ)) (𝓝 0) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K, hK, htail⟩ := czero_vector_compact_tail f ε hε
  let L : Set (D × Mrowka 𝒜) := {p | ε ≤ ‖f p‖}
  have hL : IsCompact L := hK.of_isClosed_subset
    (isClosed_le continuous_const f.continuous.norm) (by
      intro p hp
      by_contra hpK
      exact (htail p hpK).not_ge hp)
  have hcover : L ⊆ ⋃ q : D × ℕ, {(q.1, Sum.inl q.2)} := by
    rintro ⟨d, p⟩ hp
    cases p with
    | inl n => exact mem_iUnion.mpr ⟨(d, n), rfl⟩
    | inr A =>
      have hbad : ε ≤ 0 := by simpa only [L, mem_setOf_eq, hf, norm_zero] using hp
      exact False.elim ((not_le_of_gt hε) hbad)
  obtain ⟨t, ht⟩ := hL.elim_finite_subcover
    (fun q : D × ℕ => {(q.1, Sum.inl q.2)}) mrowka_natural_singleton_isOpen hcover
  rw [cocompact_eq_cofinite]
  filter_upwards [t.finite_toSet.compl_mem_cofinite] with q hq
  have hsmall : ‖f (q.1, Sum.inl q.2)‖ < ε := by
    by_contra hsmall
    obtain ⟨r, hr, heq⟩ := mem_iUnion₂.mp (ht (le_of_not_gt hsmall))
    have heq' := mem_singleton_iff.mp heq
    have hqr : q = r := mrowka_naturalPoint_injective (𝒜 := 𝒜) heq'
    exact hq (hqr.symm ▸ hr)
  simpa only [dist_zero_right] using hsmall

def mrowkaNaturalReadValues (f : mrowkaNaturalKernel (𝕜 := 𝕜) (𝒜 := 𝒜) (D := D)) : C₀(D × ℕ, 𝕜) where
  toFun q := f.val (q.1, Sum.inl q.2)
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := mrowka_natural_values_null f.val f.property

theorem norm_mrowkaNaturalReadValues_le (f : mrowkaNaturalKernel (𝕜 := 𝕜) (𝒜 := 𝒜) (D := D)) :
    ‖mrowkaNaturalReadValues f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro q
  exact f.val.toBCF.norm_coe_le_norm (q.1, Sum.inl q.2)

def mrowkaNaturalRead : mrowkaNaturalKernel (𝕜 := 𝕜) (𝒜 := 𝒜) (D := D) →L[𝕜] C₀(D × ℕ, 𝕜) :=
  LinearMap.mkContinuous {
    toFun := mrowkaNaturalReadValues
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
    1 (fun f => by simpa only [one_mul] using norm_mrowkaNaturalReadValues_le f)

variable (h𝒜 : IsAlmostDisjoint 𝒜)

def mrowkaNaturalIndicator (q : D × ℕ) : C₀(D × Mrowka 𝒜, 𝕜) := by
  letI := mrowka_t2Space h𝒜
  exact JLMS.clopenIndicator {(q.1, Sum.inl q.2)}
    ⟨isClosed_singleton, mrowka_natural_singleton_isOpen q⟩ isCompact_singleton

theorem mrowkaNaturalIndicator_unit (q : D × ℕ) : ‖mrowkaNaturalIndicator (𝕜 := 𝕜) h𝒜 q‖ ≤ 1 :=
  JLMS.norm_clopenIndicator_le _ _ _

theorem mrowkaNaturalIndicator_disjoint : Pairwise fun q r : D × ℕ =>
    Disjoint (Function.support (mrowkaNaturalIndicator (𝕜 := 𝕜) h𝒜 q))
      (Function.support (mrowkaNaturalIndicator (𝕜 := 𝕜) h𝒜 r)) := by
  intro q r hqr
  have hs (q : D × ℕ) : Function.support (mrowkaNaturalIndicator (𝕜 := 𝕜) h𝒜 q) ⊆
      {(q.1, Sum.inl q.2)} := by
    intro p hp
    by_contra hpq
    exact hp (by simp only [mrowkaNaturalIndicator, JLMS.clopenIndicator_apply, if_neg hpq])
  apply Disjoint.mono (hs q) (hs r)
  apply disjoint_singleton.mpr
  intro heq
  exact hqr (mrowka_naturalPoint_injective (𝒜 := 𝒜) heq)

def mrowkaNaturalLift : C₀(D × ℕ, 𝕜) →L[𝕜] C₀(D × Mrowka 𝒜, 𝕜) :=
  disjointCzeroSynthesis (mrowkaNaturalIndicator (𝕜 := 𝕜) (D := D) h𝒜)
    (mrowkaNaturalIndicator_unit (𝕜 := 𝕜) (D := D) h𝒜)
    (mrowkaNaturalIndicator_disjoint (𝕜 := 𝕜) (D := D) h𝒜)

@[simp] theorem mrowkaNaturalLift_inl (a : C₀(D × ℕ, 𝕜)) (q : D × ℕ) :
    mrowkaNaturalLift (𝕜 := 𝕜) h𝒜 a (q.1, Sum.inl q.2) = a q := by
  classical
  apply disjointCzeroSynthesis_apply_coordinate
  intro r
  have heq : ((q.1, Sum.inl q.2) : D × Mrowka 𝒜) = (r.1, Sum.inl r.2) ↔ r = q :=
    ⟨fun h => (mrowka_naturalPoint_injective (𝒜 := 𝒜) h).symm, fun h => by cases h; rfl⟩
  simp only [mrowkaNaturalIndicator, JLMS.clopenIndicator_apply, mem_singleton_iff, heq]
  split_ifs <;> rfl

@[simp] theorem mrowkaNaturalLift_inr (a : C₀(D × ℕ, 𝕜)) (d : D) (A : 𝒜) :
    mrowkaNaturalLift (𝕜 := 𝕜) h𝒜 a (d, Sum.inr A) = 0 := by
  apply disjointCzeroSynthesis_apply_zero
  intro q
  simp only [mrowkaNaturalIndicator, JLMS.clopenIndicator_apply, mem_singleton_iff,
    Prod.mk.injEq, Sum.inr_ne_inl, and_false, if_false]

theorem mrowkaNaturalLift_read (f : mrowkaNaturalKernel (𝕜 := 𝕜) (𝒜 := 𝒜) (D := D)) :
    mrowkaNaturalLift (𝕜 := 𝕜) h𝒜 (mrowkaNaturalRead f) = f.val := by
  apply ZeroAtInftyContinuousMap.ext
  rintro ⟨d, p⟩
  cases p with
  | inl n => exact mrowkaNaturalLift_inl h𝒜 _ (d, n)
  | inr A => rw [mrowkaNaturalLift_inr, f.property]

end JFA
