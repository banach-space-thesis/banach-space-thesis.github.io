import Posets.SzlenkIdealComposition

/-! A continuous map bounded below in norm distance reflects Szlenk bounds.
This direction needs no compactness or choice of common preimages. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 D E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup D] [NormedSpace 𝕜 D]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem image_szlenkDeriv_subset
    (f : WeakDual 𝕜 E → WeakDual 𝕜 F) (hf : Continuous f)
    {c : ℝ} (hc : 0 < c)
    (hfc : ∀ a b, c * ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ ≤
      ‖WeakDual.toStrongDual (f a) - WeakDual.toStrongDual (f b)‖)
    (ε : ℝ) (K : Set (WeakDual 𝕜 E)) :
    f '' szlenkDeriv ε K ⊆ szlenkDeriv (c * ε) (f '' K) := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
  intro U hU hxU
  obtain ⟨a, ha, b, hb, hab⟩ := hx.2 (f ⁻¹' U) (hU.preimage hf) hxU
  refine ⟨f a, ⟨⟨a, ha.1, rfl⟩, ha.2⟩, f b, ⟨⟨b, hb.1, rfl⟩, hb.2⟩, ?_⟩
  exact (mul_lt_mul_of_pos_left hab hc).trans_le (hfc a b)

theorem image_szlenkIterate_subset
    (f : WeakDual 𝕜 E → WeakDual 𝕜 F) (hf : Continuous f)
    {c : ℝ} (hc : 0 < c)
    (hfc : ∀ a b, c * ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ ≤
      ‖WeakDual.toStrongDual (f a) - WeakDual.toStrongDual (f b)‖)
    (ε : ℝ) (K : Set (WeakDual 𝕜 E)) (α : Ordinal) :
    f '' szlenkIterate ε K α ⊆ szlenkIterate (c * ε) (f '' K) α := by
  induction α using SuccOrder.limitRecOn with
  | isMin α hα =>
      obtain rfl := hα.eq_bot
      simp
  | succ α hα ih =>
      rw [szlenkIterate_succ, szlenkIterate_succ]
      exact (image_szlenkDeriv_subset f hf hc hfc ε _).trans
        (szlenkDeriv_mono _ ih)
  | isSuccLimit α hα ih =>
      rintro _ ⟨x, hx, rfl⟩
      rw [szlenkIterate_limit _ _ α hα]
      apply mem_iInter.mpr
      intro β
      exact ih β.val β.property ⟨x, szlenkIterate_antitone ε K β.property.le hx, rfl⟩

theorem HasSzlenkBound.of_image
    {K : Set (WeakDual 𝕜 E)} {α : Ordinal}
    (f : WeakDual 𝕜 E → WeakDual 𝕜 F) (hf : Continuous f)
    {c : ℝ} (hc : 0 < c)
    (hfc : ∀ a b, c * ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ ≤
      ‖WeakDual.toStrongDual (f a) - WeakDual.toStrongDual (f b)‖)
    (h : HasSzlenkBound (f '' K) α) : HasSzlenkBound K α := by
  intro ε hε
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hi := image_szlenkIterate_subset f hf hc hfc ε K α ⟨x, hx, rfl⟩
  rw [h _ (mul_pos hc hε)] at hi
  exact hi

theorem OperatorSzlenkBound.of_precomp {T : E →L[𝕜] F} {α : Ordinal}
    (U : D →L[𝕜] E) {c : ℝ} (hc : 0 < c)
    (hU : ∀ a b : WeakDual 𝕜 E,
      c * ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ ≤
        ‖WeakDual.toStrongDual (weakStarAdjoint U a) -
          WeakDual.toStrongDual (weakStarAdjoint U b)‖)
    (h : OperatorSzlenkBound (T.comp U) α) : OperatorSzlenkBound T α := by
  apply HasSzlenkBound.of_image (weakStarAdjoint U) (weakStarAdjoint_continuous U) hc hU
  simpa only [OperatorSzlenkBound, adjointUnitBall_comp] using h

end Posets
