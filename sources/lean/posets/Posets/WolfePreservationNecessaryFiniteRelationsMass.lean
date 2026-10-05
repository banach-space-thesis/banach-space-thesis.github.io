import Posets.WolfePreservationNecessarySectionMass
import ThesisCommon.Analysis.OrdinalFiniteCover

/-! A finite cover of moving closed sections has a closed colour core of
the same Cantor--Bendixson rank. Taking closures loses only the uniform
positivity defect, after the finite mass division. -/

noncomputable section
open Set Filter Topology ThesisCommon
universe u
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem wolfeMass_union_le (M : JLMS.AtomicDualModel 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U V : Set K) :
    wolfeMass M μ (U ∪ V) ≤ wolfeMass M μ U + wolfeMass M μ V := by
  have he : U ∪ V = U ∪ (V \ U) := by ext x; aesop
  rw [he, wolfeMass_union M μ (disjoint_sdiff_right)]
  exact add_le_add_left (wolfeMass_mono M μ (fun _ h => h.1)) _

theorem wolfeMass_iUnion_finite_le_sum {I : Type*} [Fintype I]
    (M : JLMS.AtomicDualModel 𝕜 K) (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (U : I → Set K) : wolfeMass M μ (⋃ i, U i) ≤ ∑ i, wolfeMass M μ (U i) := by
  classical
  have hsum (s : Finset I) :
      wolfeMass M μ (⋃ i ∈ s, U i) ≤ ∑ i ∈ s, wolfeMass M μ (U i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
        exact (wolfeMass_union_le M μ _ _).trans (add_le_add_left ih _)
  simpa using hsum Finset.univ

theorem wolfeMass_exists_large_cover {I : Type*} [Fintype I] [Nonempty I]
    (M : JLMS.AtomicDualModel 𝕜 K) (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (U : I → Set K) {d : ℝ} (hd : d ≤ wolfeMass M μ (⋃ i, U i)) :
    ∃ i, d / Fintype.card I ≤ wolfeMass M μ (U i) := by
  classical
  have hbound := hd.trans (wolfeMass_iUnion_finite_le_sum M μ U)
  by_contra hn
  push_neg at hn
  have hsum : ∑ i, wolfeMass M μ (U i) < ∑ _i : I, d / Fintype.card I := by
    apply Finset.sum_lt_sum (fun i _ => (hn i).le)
    exact ⟨Classical.choice inferInstance, Finset.mem_univ _, hn _⟩
  have he : (∑ _i : I, d / Fintype.card I) = d := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  rw [he] at hsum
  exact (not_lt_of_ge hbound) hsum

section ClosedCore
variable [TopologicalSpace L] [CompactSpace K] [CompactSpace L]
  [T2Space K] [T2Space L]

local instance wolfeFiniteRelationsMassDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance wolfeFiniteRelationsMassDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

theorem wolfe_finite_closed_relations_core {I : Type*} [Fintype I] [Nonempty I]
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (μ : L → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (hμ : Continuous μ)
    (R : I → Set (K × L)) (hR : ∀ i, IsClosed (R i))
    {A : Set L} (hA : IsClosed A) {d η : ℝ}
    (hdefect : ∀ x ∈ A, ‖WeakDual.toStrongDual (μ x)‖ -
      RCLike.re (μ x (wolfeSourceBlock univ isClopen_univ)) ≤ η)
    (hmass : ∀ x ∈ A, d ≤ wolfeMass M (μ x) (⋃ i, {y | (y, x) ∈ R i}))
    (α : Ordinal.{u}) (hrank : (ordinalDerived A α).Nonempty) :
    ∃ i : I, ∃ B : Set L, IsClosed B ∧ B ⊆ A ∧
      (ordinalDerived B α).Nonempty ∧
      ∀ x ∈ B, d / Fintype.card I - η ≤ wolfeMass M (μ x) {y | (y, x) ∈ R i} := by
  classical
  let B (i : I) := closure {x ∈ A | d / Fintype.card I ≤ wolfeMass M (μ x) {y | (y, x) ∈ R i}}
  have hclosure (i : I) : B i ⊆ A ∧ ∀ x ∈ B i,
      d / Fintype.card I - η ≤ wolfeMass M (μ x) {y | (y, x) ∈ R i} := by
    simpa only [B, mem_univ, and_true] using
      wolfe_closed_section_mass_closure_superlevel M hK μ hμ (hR i)
        isClosed_univ hA hdefect (d / Fintype.card I)
  have hcover : A = ⋃ i, B i := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := wolfeMass_exists_large_cover M (μ x) _ (hmass x hx)
      exact mem_iUnion.mpr ⟨i, subset_closure ⟨hx, hi⟩⟩
    · exact iUnion_subset fun i => (hclosure i).1
  obtain ⟨x, hx⟩ := hrank
  rw [hcover, ordinalDerived_iUnion_finite B (fun _ => isClosed_closure)] at hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact ⟨i, B i, isClosed_closure, (hclosure i).1, ⟨x, hi⟩, (hclosure i).2⟩

end ClosedCore
end Posets
