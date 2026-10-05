import Posets.WolfeMassBounds
import JLMS.AtomicNormingFunction

/-! Open-set variation is normed by actual supported continuous functions.
This is the function-selection step used when turning Wolfe families into
operator-preserved systems. The scalar phase construction works over ℝ and ℂ. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
variable (M : JLMS.AtomicDualModel 𝕜 K)
local instance wolfeNormingDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance wolfeNormingDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

theorem atomicRestriction_apply_of_support_subset
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (f : JLMS.CZero 𝕜 K)
    {U : Set K} (hf : Function.support f ⊆ U) :
    JLMS.atomicRestriction M U (WeakDual.toStrongDual μ) f = μ f := by
  have h := JLMS.atomicDual_apply_hasSum M (WeakDual.toStrongDual μ) f
  have hr := JLMS.atomicDual_apply_hasSum M
    (JLMS.atomicRestriction M U (WeakDual.toStrongDual μ)) f
  apply hr.unique
  apply h.congr_fun
  intro x
  rw [JLMS.atomicRestriction_coordinates]
  by_cases hx : x ∈ U
  · simp [hx]
  · have hfx : f x = 0 := by by_contra hn; exact hx (hf hn)
    simp [hx, hfx]

theorem norm_apply_le_wolfeMass_of_support_subset
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (f : JLMS.CZero 𝕜 K)
    {U : Set K} (hf : Function.support f ⊆ U) (hn : ‖f‖ ≤ 1) :
    ‖μ f‖ ≤ wolfeMass M μ U := by
  rw [← atomicRestriction_apply_of_support_subset M μ f hf]
  exact ((JLMS.atomicRestriction M U (WeakDual.toStrongDual μ)).le_opNorm f).trans
    (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hn (norm_nonneg (JLMS.atomicRestriction M U (WeakDual.toStrongDual μ))))

variable [LocallyCompactSpace K] [T2Space K]

theorem exists_supported_wolfe_norming_function (hK : JLMS.IsScattered K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {U : Set K} (hU : IsOpen U)
    {r : ℝ} (hr : r < wolfeMass M μ U) :
    ∃ f : JLMS.CZero 𝕜 K, ‖f‖ ≤ 1 ∧ Function.support f ⊆ U ∧ r < ‖μ f‖ := by
  classical
  let θ := (wolfeMass M μ U - r) / 3
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hlarge : r + θ < ‖JLMS.restrictionL1 U (M.representation (WeakDual.toStrongDual μ))‖ := by
    rw [← JLMS.atomicRestriction_norm]
    change r + θ < wolfeMass M μ U
    dsimp [θ]
    linarith
  obtain ⟨A, hAsupp, hAmass⟩ := JLMS.exists_finite_restrictionL1_mass
    (JLMS.restrictionL1 U (M.representation (WeakDual.toStrongDual μ))) hlarge
  have hAU : (A : Set K) ⊆ U := by
    intro x hx
    by_contra hxU
    exact hAsupp hx (by simp [hxU])
  have hrestrict : JLMS.restrictionL1 (A : Set K)
      (JLMS.restrictionL1 U (M.representation (WeakDual.toStrongDual μ))) =
      JLMS.restrictionL1 (A : Set K) (M.representation (WeakDual.toStrongDual μ)) := by
    ext x
    by_cases hx : x ∈ A
    · simp [hx, hAU hx]
    · simp [hx]
  rw [hrestrict, ← JLMS.atomicRestriction_norm] at hAmass
  obtain ⟨V⟩ := JLMS.exists_neighborhoodFamily hK (fun x : A => x.val) Subtype.val_injective
  obtain ⟨W, hW⟩ := JLMS.exists_neighborhoodFamily_shrink hK V hU (fun x => hAU x.property)
  obtain ⟨f, hn, hf, hnorm⟩ := JLMS.exists_supported_atomic_norming_function M hK
    (WeakDual.toStrongDual μ) A W hθ hAmass
  refine ⟨f, hn, ?_, hnorm⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hf hx)
  exact (hW i hi).2

theorem wolfeMass_gt_iff_supported_norming (hK : JLMS.IsScattered K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {U : Set K} (hU : IsOpen U) (r : ℝ) :
    r < wolfeMass M μ U ↔
      ∃ f : JLMS.CZero 𝕜 K, ‖f‖ ≤ 1 ∧ Function.support f ⊆ U ∧ r < ‖μ f‖ := by
  constructor
  · exact exists_supported_wolfe_norming_function M hK μ hU
  · rintro ⟨f, hn, hf, hr⟩
    exact hr.trans_le (norm_apply_le_wolfeMass_of_support_subset M μ f hf hn)

theorem exists_supported_wolfe_positive_norming (hK : JLMS.IsScattered K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {U : Set K} (hU : IsOpen U)
    {r : ℝ} (hr : r < wolfeMass M μ U) :
    ∃ f : JLMS.CZero 𝕜 K, ‖f‖ ≤ 1 ∧ Function.support f ⊆ U ∧ r < RCLike.re (μ f) := by
  obtain ⟨f, hn, hf, hr⟩ := exists_supported_wolfe_norming_function M hK μ hU hr
  let a : 𝕜 := JLMS.scalarPhase (μ f)
  refine ⟨a • f, ?_, ?_, ?_⟩
  · simpa only [norm_smul, a, JLMS.norm_scalarPhase, one_mul] using hn
  · intro x hx
    apply hf
    intro hzero
    apply hx
    change a * f x = 0
    rw [hzero, mul_zero]
  · have he : μ (a • f) = ((‖μ f‖ : ℝ) : 𝕜) := by
      rw [map_smul, smul_eq_mul]
      exact JLMS.scalarPhase_mul _
    simpa only [he, RCLike.ofReal_re] using hr

/-- One supported norming function works on a weak-star neighborhood of μ. -/
theorem exists_supported_wolfe_uniform_neighborhood (hK : JLMS.IsScattered K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {U : Set K} (hU : IsOpen U)
    {r : ℝ} (hr : r < wolfeMass M μ U) :
    ∃ f : JLMS.CZero 𝕜 K, ∃ V : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)),
      ‖f‖ ≤ 1 ∧ Function.support f ⊆ U ∧ IsOpen V ∧ μ ∈ V ∧
        ∀ ν ∈ V, r < RCLike.re (ν f) := by
  obtain ⟨f, hn, hf, hr⟩ := exists_supported_wolfe_positive_norming M hK μ hU hr
  refine ⟨f, {ν | r < RCLike.re (ν f)}, hn, hf, ?_, hr, fun _ hν => hν⟩
  exact isOpen_lt continuous_const (RCLike.continuous_re.comp (WeakDual.eval_continuous f))

/-- Open-set mass is lower semicontinuous in the genuine weak-star topology. -/
theorem isOpen_wolfeMass_gt (hK : JLMS.IsScattered K) {U : Set K} (hU : IsOpen U)
    (r : ℝ) : IsOpen {μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K) | r < wolfeMass M μ U} := by
  have he : {μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K) | r < wolfeMass M μ U} =
      ⋃ f : {f : JLMS.CZero 𝕜 K // ‖f‖ ≤ 1 ∧ Function.support f ⊆ U},
        {μ | r < ‖μ f.val‖} := by
    ext μ
    simp only [mem_setOf_eq, mem_iUnion]
    rw [wolfeMass_gt_iff_supported_norming M hK μ hU]
    constructor
    · rintro ⟨f, hn, hf, hr⟩; exact ⟨⟨f, hn, hf⟩, hr⟩
    · rintro ⟨f, hr⟩; exact ⟨f.val, f.property.1, f.property.2, hr⟩
  rw [he]
  exact isOpen_iUnion fun f => isOpen_lt continuous_const (WeakDual.eval_continuous f.val).norm

end Posets
