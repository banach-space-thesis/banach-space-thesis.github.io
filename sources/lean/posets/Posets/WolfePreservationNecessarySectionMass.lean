import Posets.WolfePreservationNecessaryClosedKernelAtoms

/-! Variation on a moving closed section is approximately upper
semicontinuous when the continuous measure family has a uniform positivity
defect. The defect is global; this lemma does not restrict the measure family
to a closed target subset, an operation which need not preserve continuity. -/

noncomputable section
open Set Filter Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]

local instance wolfeSectionMassDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance wolfeSectionMassDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

theorem wolfe_exists_clopen_small_outer_mass
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {D : Set K} (hD : IsClosed D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Set K, IsClopen H ∧ D ⊆ H ∧ wolfeMass M μ H < wolfeMass M μ D + ε := by
  obtain ⟨E, hE, _, hED, hmass⟩ := wolfe_exists_compact_clopen_large_mass M hK μ hD.isOpen_compl
    (show wolfeMass M μ Dᶜ - ε < wolfeMass M μ Dᶜ by linarith)
  refine ⟨Eᶜ, hE.compl, ?_, ?_⟩
  · intro x hx hxE
    exact hED hxE hx
  · have h1 := wolfeMass_compl M μ D
    have h2 := wolfeMass_compl M μ E
    linarith

theorem wolfe_closed_relation_sections_local_subset
    {R : Set (K × L)} (hR : IsClosed R) {C H : Set K}
    (hC : IsClosed C) (hH : IsOpen H) (x : L)
    (hsub : {y : K | (y, x) ∈ R ∧ y ∈ C} ⊆ H) :
    ∃ W : Set L, IsOpen W ∧ x ∈ W ∧
      ∀ z ∈ W, {y : K | (y, z) ∈ R ∧ y ∈ C} ⊆ H := by
  let E : Set (K × L) := R ∩ (Prod.fst ⁻¹' (C ∩ Hᶜ))
  have hE : IsClosed E := hR.inter ((hC.inter hH.isClosed_compl).preimage continuous_fst)
  let W := (Prod.snd '' E)ᶜ
  refine ⟨W, (hE.isCompact.image continuous_snd).isClosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨⟨y, z⟩, ⟨hyR, hyC, hyH⟩, he⟩
    have hy : (y, x) ∈ R := he ▸ hyR
    exact hyH (hsub ⟨hy, hyC⟩)
  · intro z hz y hy
    by_contra hyH
    exact hz ⟨(y, z), ⟨hy.1, hy.2, hyH⟩, rfl⟩

theorem wolfe_closed_section_mass_local_upper
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (μ : L → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (hμ : Continuous μ)
    {R : Set (K × L)} (hR : IsClosed R) {C : Set K} (hC : IsClosed C)
    {A : Set L} {η : ℝ}
    (hdefect : ∀ z ∈ A, ‖WeakDual.toStrongDual (μ z)‖ -
      RCLike.re (μ z (wolfeSourceBlock univ isClopen_univ)) ≤ η)
    (x : L) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Set L, IsOpen W ∧ x ∈ W ∧ ∀ z ∈ A ∩ W,
      wolfeMass M (μ z) {y | (y, z) ∈ R ∧ y ∈ C} <
        wolfeMass M (μ x) {y | (y, x) ∈ R ∧ y ∈ C} + η + ε := by
  let D : Set K := {y | (y, x) ∈ R ∧ y ∈ C}
  have hD : IsClosed D := (hR.preimage (continuous_id.prodMk continuous_const)).inter hC
  obtain ⟨H, hH, hDH, hmass⟩ := wolfe_exists_clopen_small_outer_mass M hK (μ x) hD (half_pos hε)
  obtain ⟨W, hW, hxW, hsub⟩ := wolfe_closed_relation_sections_local_subset hR hC hH.isOpen x hDH
  let V : Set L := {z | RCLike.re (μ z (wolfeSourceBlock H hH)) <
    RCLike.re (μ x (wolfeSourceBlock H hH)) + ε / 2}
  have hV : IsOpen V := isOpen_lt
    (RCLike.continuous_re.comp ((WeakDual.eval_continuous _).comp hμ)) continuous_const
  have hxV : x ∈ V := by dsimp [V]; linarith
  refine ⟨W ∩ V, hW.inter hV, ⟨hxW, hxV⟩, ?_⟩
  rintro z ⟨hzA, hzW, hzV⟩
  have hphase := wolfePhaseRestriction_re_lower M (μ z)
    (wolfeSourceBlock univ isClopen_univ)
    (wolfeSourceBlock_norm_le univ isClopen_univ) H
  rw [wolfeSourceBlock_restriction_one M _ H hH] at hphase
  change wolfeMass M (μ z) H - (‖WeakDual.toStrongDual (μ z)‖ -
    RCLike.re (μ z (wolfeSourceBlock univ isClopen_univ))) ≤
      RCLike.re (μ z (wolfeSourceBlock H hH)) at hphase
  have hlower := wolfeMass_mono M (μ z) (hsub z hzW)
  have hnorm : RCLike.re (μ x (wolfeSourceBlock H hH)) ≤ wolfeMass M (μ x) H :=
    (RCLike.re_le_norm _).trans (norm_apply_le_wolfeMass_of_support_subset M (μ x)
      (wolfeSourceBlock H hH) (by rw [wolfeSourceBlock_support]) (wolfeSourceBlock_norm_le H hH))
  have hd := hdefect z hzA
  change RCLike.re (μ z (wolfeSourceBlock H hH)) <
    RCLike.re (μ x (wolfeSourceBlock H hH)) + ε / 2 at hzV
  change wolfeMass M (μ z) {y | (y, z) ∈ R ∧ y ∈ C} < wolfeMass M (μ x) D + η + ε
  linarith

theorem wolfe_closed_section_mass_closure_superlevel
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (μ : L → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (hμ : Continuous μ)
    {R : Set (K × L)} (hR : IsClosed R) {C : Set K} (hC : IsClosed C)
    {A : Set L} (hA : IsClosed A) {η : ℝ}
    (hdefect : ∀ z ∈ A, ‖WeakDual.toStrongDual (μ z)‖ -
      RCLike.re (μ z (wolfeSourceBlock univ isClopen_univ)) ≤ η)
    (t : ℝ) :
    closure {z ∈ A | t ≤ wolfeMass M (μ z) {y | (y, z) ∈ R ∧ y ∈ C}} ⊆ A ∧
      ∀ x ∈ closure {z ∈ A | t ≤ wolfeMass M (μ z) {y | (y, z) ∈ R ∧ y ∈ C}},
        t - η ≤ wolfeMass M (μ x) {y | (y, x) ∈ R ∧ y ∈ C} := by
  refine ⟨closure_minimal (fun _ h => h.1) hA, ?_⟩
  intro x hx
  by_contra hn
  have hgap : 0 < t - η - wolfeMass M (μ x) {y | (y, x) ∈ R ∧ y ∈ C} := by
    push_neg at hn
    linarith
  obtain ⟨W, hW, hxW, hmass⟩ := wolfe_closed_section_mass_local_upper M hK μ hμ hR hC
    hdefect x hgap
  obtain ⟨z, hzW, hzA, hzt⟩ := mem_closure_iff.mp hx W hW hxW
  have hz := hmass z ⟨hzA, hzW⟩
  linarith

theorem wolfe_closed_section_mass_superlevel_isClosed
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (μ : L → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (hμ : Continuous μ)
    {R : Set (K × L)} (hR : IsClosed R) {C : Set K} (hC : IsClosed C)
    {A : Set L} (hA : IsClosed A)
    (hdefect : ∀ z ∈ A, ‖WeakDual.toStrongDual (μ z)‖ -
      RCLike.re (μ z (wolfeSourceBlock univ isClopen_univ)) ≤ 0)
    (t : ℝ) :
    IsClosed {z ∈ A | t ≤ wolfeMass M (μ z) {y | (y, z) ∈ R ∧ y ∈ C}} := by
  obtain ⟨hsub, hmass⟩ := wolfe_closed_section_mass_closure_superlevel M hK μ hμ hR hC hA hdefect t
  apply isClosed_of_closure_subset
  intro x hx
  exact ⟨hsub hx, by simpa using hmass x hx⟩

end Posets
