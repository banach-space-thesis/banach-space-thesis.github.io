import ThesisCommon.Analysis.FilterConvergenceCriteria
import Mathlib.SetTheory.Cardinal.Aleph

/-! Concrete co-small filters: coordinate self-similarity for every infinite
cardinal, and exact descriptions of the cofinite and co-countable spaces. -/
noncomputable section
open Filter Topology
open scoped ENNReal Cardinal
namespace ThesisCommon
universe u
variable {𝕜 : Type*} [RCLike 𝕜] {Γ : Type u}

theorem coSmallFilter_aleph0 :
    coSmallFilter (Γ := Γ) Cardinal.aleph0 le_rfl = Filter.cofinite := by
  ext A
  exact Cardinal.lt_aleph0_iff_set_finite

theorem mem_cofinite_filterNull_iff (x : lp (fun _ : Γ => 𝕜) ∞) :
    x ∈ filterNullSubmodule 𝕜 Filter.cofinite ↔
      ∀ ε : ℝ, 0 < ε → {γ | ε ≤ ‖x γ‖}.Finite := by
  rw [mem_filterNullSubmodule_iff]
  simp only [Filter.mem_cofinite, Set.compl_setOf, not_lt]

theorem mem_coSmallFilter_aleph_one_iff (A : Set Γ) :
    A ∈ coSmallFilter (Γ := Γ) (Cardinal.aleph 1) (Cardinal.aleph0_le_aleph 1) ↔
      Aᶜ.Countable :=
  (Cardinal.countable_iff_lt_aleph_one Aᶜ).symm

theorem mem_cocountable_filterNull_iff (x : lp (fun _ : Γ => 𝕜) ∞) :
    x ∈ filterNullSubmodule 𝕜
      (coSmallFilter (Γ := Γ) (Cardinal.aleph 1) (Cardinal.aleph0_le_aleph 1)) ↔
      (Function.support x).Countable := by
  rw [mem_filterNullSubmodule_iff]
  simp only [mem_coSmallFilter_aleph_one_iff, Set.compl_setOf, not_lt]
  constructor
  · intro h
    have hc : (⋃ n : ℕ, {γ | 1 / ((n : ℝ) + 1) ≤ ‖x γ‖}).Countable :=
      Set.countable_iUnion fun n => h _ (by positivity)
    apply hc.mono
    intro γ hγ
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hγ)
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩
  · intro h ε hε
    apply h.mono
    intro γ hγ
    exact norm_pos_iff.mp (hε.trans_le hγ)

/-- A bijection onto a subset preserves the cardinality of the missing
coordinates, exactly as required by the source's coordinate-copy definition. -/
theorem coSmallFilter_coordinateCopy (μ : Cardinal.{u}) (hμ : Cardinal.aleph0 ≤ μ)
    (C : Set Γ) (θ : Γ ≃ C) :
    IsFilterCoordinateCopy (coSmallFilter (Γ := Γ) μ hμ) C θ := by
  intro A
  have hinj : Function.Injective (fun γ => (θ γ).val) :=
    Subtype.val_injective.comp θ.injective
  have heq : (((fun γ => (θ γ).val) '' A) ∪ Cᶜ)ᶜ =
      (fun γ => (θ γ).val) '' Aᶜ := by
    ext γ
    constructor
    · intro h
      have hC : γ ∈ C := by simpa using fun hC => h (Or.inr hC)
      obtain ⟨δ, hδ⟩ := θ.surjective ⟨γ, hC⟩
      refine ⟨δ, ?_, congrArg Subtype.val hδ⟩
      intro hA
      exact h (Or.inl ⟨δ, hA, congrArg Subtype.val hδ⟩)
    · rintro ⟨δ, hδ, rfl⟩ (⟨β, hβ, heq⟩ | hC)
      · exact hδ (hinj heq ▸ hβ)
      · exact hC (θ δ).property
  change Cardinal.mk (Aᶜ : Set Γ) < μ ↔ Cardinal.mk _ < μ
  rw [heq, Cardinal.mk_image_eq hinj]

theorem coSmallFilter_largeSetSelfSimilar (μ : Cardinal.{u})
    (hμ : Cardinal.aleph0 ≤ μ) :
    IsLargeSetSelfSimilarFilter (coSmallFilter (Γ := Γ) μ hμ) := by
  intro B hB
  obtain ⟨θ⟩ := Cardinal.eq.mp hB.symm
  exact ⟨B, Set.Subset.rfl, θ, coSmallFilter_coordinateCopy μ hμ B θ⟩

end ThesisCommon
