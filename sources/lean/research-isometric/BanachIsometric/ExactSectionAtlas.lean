import BanachIsometric.ExactSectionBundle

/-!
# An actual Lipschitz atlas of exact section identifications

Every chart uses the same fixed model section. Its forward and left-inverse
operator families are constructed from the original gauge, projections and
section equivalences. The local exact maps are consequences of those geometric
inputs, rather than premises in the existence theorem.
-/

namespace BanachIsometric

open Set Filter MeasureTheory
open scoped Topology NNReal

noncomputable section

section SectionEquivalence

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

def RealSectionEquivalent (p : F → ℝ) (H J : Submodule ℝ F) : Prop :=
  ∃ e : H ≃ₗ[ℝ] J, e '' {x : H | p x.val ≤ 1} = {x : J | p x.val ≤ 1}

theorem RealSectionEquivalent.refl (p : F → ℝ) (H : Submodule ℝ F) :
    RealSectionEquivalent p H H := ⟨LinearEquiv.refl ℝ H, image_id _⟩

theorem RealSectionEquivalent.symm {p : F → ℝ} {H J : Submodule ℝ F}
    (h : RealSectionEquivalent p H J) : RealSectionEquivalent p J H := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  calc
    _ = e.symm '' (e '' {x : H | p x.val ≤ 1}) := congrArg (Set.image e.symm) he.symm
    _ = _ := e.toEquiv.symm_image_image _

theorem RealSectionEquivalent.trans {p : F → ℝ} {H J K : Submodule ℝ F}
    (h : RealSectionEquivalent p H J) (k : RealSectionEquivalent p J K) :
    RealSectionEquivalent p H K := by
  obtain ⟨e, he⟩ := h
  obtain ⟨f, hf⟩ := k
  refine ⟨e.trans f, ?_⟩
  calc
    _ = f '' (e '' {x : H | p x.val ≤ 1}) := by rw [image_image]; rfl
    _ = _ := by rw [he, hf]

end SectionEquivalence

section Atlas

variable {P E F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual forward and inverse operators, on open charts with a common
model body. The inverse is an ambient left inverse; it need not preserve
ambient vectors outside the prescribed section subspace. -/
structure ExactSectionAtlas (S : Set E) (K : Set F) (H : P → Submodule ℝ F) where
  baseSet : P → Set P
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  mem_baseSet : ∀ i, i ∈ baseSet i
  forward : P → P → E →L[ℝ] F
  inverse : P → P → F →L[ℝ] E
  forward_lipschitz : ∀ i, ∃ L : ℝ≥0, LipschitzOnWith L (forward i) (baseSet i)
  inverse_lipschitz : ∀ i, ∃ L : ℝ≥0, LipschitzOnWith L (inverse i) (baseSet i)
  left_inverse : ∀ i a, a ∈ baseSet i →
    (inverse i a).comp (forward i a) = ContinuousLinearMap.id ℝ E
  forward_valid : ∀ i a, a ∈ baseSet i →
    Function.Injective (forward i a) ∧ LinearMap.range (forward i a).toLinearMap = H a ∧
      forward i a '' S = K ∩ (H a : Set F)

end Atlas

section Construction

variable {P F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The atlas of exact section maps is constructed from the actual geometric
hypotheses. A single genuine reference section serves as the model in all
charts. Both operator families have two-point Lipschitz bounds on each chart.
-/
theorem exists_exact_section_atlas {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    {p : F → ℝ} (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1))
    (H : P → Submodule ℝ F) {L : ℝ≥0}
    (hLip : LipschitzWith L (fun a => (H a).starProjection))
    (hrank : ∀ a, Module.finrank ℝ (H a) = Module.finrank ℝ (EuclideanSpace ℝ (Fin m)))
    (a₀ : P) (hequiv : ∀ a, RealSectionEquivalent p (H a₀) (H a)) :
    ∃ R : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] F,
      LinearMap.range R.toLinearMap = H a₀ ∧
      Nonempty (ExactSectionAtlas (pulledBackGaugeBody p R) {y : F | p y ≤ 1} H) := by
  classical
  obtain ⟨R, hR⟩ := exists_linearIsometry_range_eq_submodule (H a₀) (hrank a₀)
  have hchart : ∀ i : P,
      ∃ U : Set P, ∃ KA KB : ℝ≥0,
      ∃ A : P → EuclideanSpace ℝ (Fin m) →L[ℝ] F,
      ∃ B : P → F →L[ℝ] EuclideanSpace ℝ (Fin m),
        IsOpen U ∧ i ∈ U ∧ LipschitzOnWith KA A U ∧ LipschitzOnWith KB B U ∧
          (∀ a ∈ U, (B a).comp (A a) = ContinuousLinearMap.id ℝ _) ∧
          ∀ a ∈ U, Function.Injective (A a) ∧ LinearMap.range (A a).toLinearMap = H a ∧
            A a '' pulledBackGaugeBody p R = {y : F | p y ≤ 1} ∩ (H a : Set F) := by
    intro i
    have hiEquiv : ∀ a, RealSectionEquivalent p (H i) (H a) :=
      fun a => (hequiv i).symm.trans (hequiv a)
    obtain ⟨Ri, hRi, A, U, KA, hU, hiU, hAi, hALip, hAvalid⟩ :=
      exists_lipschitz_exact_subspace_section_maps μ hp hC H hLip hrank i hiEquiv
    have hGram : (A i).adjoint.comp (A i) = ContinuousLinearMap.id ℝ _ := by
      rw [hAi]
      exact Ri.toContinuousLinearMap.norm_map_iff_adjoint_comp_self.mp Ri.norm_map
    obtain ⟨B, W, KB, hW, hiW, hWU, _, hBLip, hBA⟩ :=
      exists_lipschitz_local_leftInverse_family A i (hU.mem_nhds hiU) hALip hGram
    obtain ⟨e, he⟩ := hequiv i
    obtain ⟨d, hd⟩ := exists_frame_body_equiv_of_section_equiv p R Ri (H a₀) (H i) hR hRi e he
    let LA := (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin m)) F).flip d.toContinuousLinearMap
    let LB := (ContinuousLinearMap.compL ℝ F (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin m))) d.symm.toContinuousLinearMap
    let A' : P → EuclideanSpace ℝ (Fin m) →L[ℝ] F := fun a => (A a).comp d.toContinuousLinearMap
    let B' : P → F →L[ℝ] EuclideanSpace ℝ (Fin m) := fun a => d.symm.toContinuousLinearMap.comp (B a)
    have hA' : LipschitzOnWith (‖LA‖₊ * KA) A' W :=
      LA.lipschitz.lipschitzOnWith.comp (hALip.mono hWU) (fun _ _ => mem_univ _)
    have hB' : LipschitzOnWith (‖LB‖₊ * KB) B' W :=
      LB.lipschitz.lipschitzOnWith.comp hBLip (fun _ _ => mem_univ _)
    refine ⟨W, ‖LA‖₊ * KA, ‖LB‖₊ * KB, A', B', hW, hiW, hA', hB', ?_, ?_⟩
    · intro a ha
      apply ContinuousLinearMap.ext
      intro x
      change d.symm (B a (A a (d x))) = x
      have h := congrArg (fun T => T (d x)) (hBA a ha)
      change B a (A a (d x)) = d x at h
      rw [h]
      exact d.symm_apply_apply x
    · intro a ha
      obtain ⟨hInj, hRange, hImage⟩ := hAvalid a (hWU ha)
      refine ⟨hInj.comp d.injective, ?_, ?_⟩
      · ext y
        constructor
        · rintro ⟨x, rfl⟩
          rw [← hRange]
          exact LinearMap.mem_range_self (A a).toLinearMap (d x)
        · intro hy
          rw [← hRange] at hy
          obtain ⟨x, rfl⟩ := hy
          refine ⟨d.symm x, ?_⟩
          change A a (d (d.symm x)) = A a x
          rw [ContinuousLinearEquiv.apply_symm_apply]
      · calc
          A' a '' pulledBackGaugeBody p R = A a '' (d '' pulledBackGaugeBody p R) := by
            rw [image_image]
            rfl
          _ = A a '' pulledBackGaugeBody p Ri := by rw [hd]
          _ = {y : F | p y ≤ 1} ∩ (H a : Set F) := hImage
  choose U KA KB A B hU hmem hALip hBLip hLeft hValid using hchart
  exact ⟨R, hR, ⟨⟨U, hU, hmem, A, B, fun i => ⟨KA i, hALip i⟩,
    fun i => ⟨KB i, hBLip i⟩, hLeft, hValid⟩⟩⟩

end Construction

end
end BanachIsometric
