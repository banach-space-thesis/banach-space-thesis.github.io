import ThesisCommon.Analysis.SequenceCoordinates

/-! Countable coordinate support, following §4 of Primariness and the Primary
Factorisation Property. Individual vectors have countable support; then take
the union over a countable dense set and use closed coordinate kernels.
The general symmetric-sum construction is not supplied by this module.
-/
noncomputable section
open scoped ENNReal ZeroAtInfty
open TopologicalSpace
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Γ X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Lemma 4.12 for actual finite-exponent ℓp sums, including arbitrary Γ.
The p=∞ case is deliberately excluded: its assertion would be false. -/
theorem lp_countable_support {p : ℝ≥0∞} (hp : p ≠ 0) (hfin : p ≠ ∞)
    (x : lp (fun _ : Γ => X) p) : (Function.support x).Countable := by
  have hpos : 0 < p.toReal := ENNReal.toReal_pos hp hfin
  have hs := ((lp.memℓp x).summable hpos).countable_support
  apply hs.mono
  intro i hi
  change ‖x i‖ ^ p.toReal ≠ 0
  exact ne_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr hi) _)

/-- Lemma 4.12 for c₀ over any discrete index set. The countable-neighbourhood
proof in mathlib is the manuscript's countable union of finite level sets. -/
theorem cZero_countable_support [TopologicalSpace Γ] [DiscreteTopology Γ]
    (x : C₀(Γ, X)) : (Function.support x).Countable := by
  have hx := zero_at_infty x
  rw [Filter.cocompact_eq_cofinite] at hx
  simpa only [ker_nhds] using hx.countable_compl_preimage_ker

/-- The dense-set argument of Lemma 4.13, abstracted only over the coordinate
maps and their continuity. Its support hypothesis must be discharged by an
actual space, as in the two specialisations below. -/
theorem separable_countable_coordinate_support
    {Y : Type*} [TopologicalSpace Y] (coord : Y → Γ → X)
    (hc : ∀ i, Continuous (fun y => coord y i))
    (hs : ∀ y, (Function.support (coord y)).Countable)
    {s : Set Y} (hsep : IsSeparable s) :
    ∃ Δ : Set Γ, Δ.Countable ∧ ∀ y ∈ s, Function.support (coord y) ⊆ Δ := by
  obtain ⟨d, hd, hsd⟩ := hsep
  let Δ := ⋃ y ∈ d, Function.support (coord y)
  refine ⟨Δ, hd.biUnion (fun y _ => hs y), ?_⟩
  intro y hy i hi
  by_contra hiΔ
  have hzero : ∀ z ∈ d, coord z i = 0 := by
    intro z hz
    by_contra hzi
    apply hiΔ
    exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, hzi⟩⟩
  have hclosed : IsClosed {z : Y | coord z i = 0} := isClosed_eq (hc i) continuous_const
  have hz : coord y i = 0 := hclosed.closure_subset_iff.mpr hzero (hsd hy)
  exact hi hz

include 𝕜 in
theorem lp_separable_countable_support {p : ℝ≥0∞} [Fact (1 ≤ p)] (hfin : p ≠ ∞)
    {s : Set (lp (fun _ : Γ => X) p)} (hsep : IsSeparable s) :
    ∃ Δ : Set Γ, Δ.Countable ∧ ∀ x ∈ s, Function.support x ⊆ Δ :=
  separable_countable_coordinate_support (fun (x : lp (fun _ : Γ => X) p) => (x : Γ → X))
    (fun i => (lpCoordinate (𝕜 := 𝕜) p i).continuous)
    (lp_countable_support (ne_of_gt (zero_lt_one.trans_le Fact.out)) hfin) hsep

include 𝕜 in
theorem cZero_separable_countable_support [TopologicalSpace Γ] [DiscreteTopology Γ]
    {s : Set C₀(Γ, X)} (hsep : IsSeparable s) :
    ∃ Δ : Set Γ, Δ.Countable ∧ ∀ x ∈ s, Function.support x ⊆ Δ :=
  separable_countable_coordinate_support (fun (x : C₀(Γ, X)) => (x : Γ → X))
    (fun i => (cZeroCoordinate (𝕜 := 𝕜) i).continuous) cZero_countable_support hsep

/-- Support reduction for operators from any separable normed space into ℓp. -/
theorem lp_operator_countable_support
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [SeparableSpace Y]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hfin : p ≠ ∞)
    (T : Y →L[𝕜] lp (fun _ : Γ => X) p) :
    ∃ Δ : Set Γ, Δ.Countable ∧ ∀ y, Function.support (T y) ⊆ Δ := by
  obtain ⟨Δ, hΔ, hT⟩ := lp_separable_countable_support (𝕜 := 𝕜) hfin
    (isSeparable_range T.continuous)
  exact ⟨Δ, hΔ, fun y => hT (T y) ⟨y, rfl⟩⟩

theorem cZero_operator_countable_support [TopologicalSpace Γ] [DiscreteTopology Γ]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [SeparableSpace Y]
    (T : Y →L[𝕜] C₀(Γ, X)) :
    ∃ Δ : Set Γ, Δ.Countable ∧ ∀ y, Function.support (T y) ⊆ Δ := by
  obtain ⟨Δ, hΔ, hT⟩ := cZero_separable_countable_support (𝕜 := 𝕜)
    (isSeparable_range T.continuous)
  exact ⟨Δ, hΔ, fun y => hT (T y) ⟨y, rfl⟩⟩

end ThesisCommon
