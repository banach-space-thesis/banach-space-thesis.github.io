import Posets.UltrafilterCardinality
import Posets.UltrafilterBimoduleLimits
import Posets.IdealCorrespondenceGeneral

/-! Distinct ultrafilters give distinct maximal closed ideals of scalar ℓ∞. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set Filter Topology ThesisCommon
open scoped ENNReal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

abbrev ScalarBoundedProduct (𝕜 : Type) [RCLike 𝕜] := lp (fun _ : ℕ => 𝕜) ∞

def lpUltrafilterEvaluation (U : Ultrafilter ℕ) :
    BoundedHom 𝕜 (ScalarBoundedProduct 𝕜) 𝕜 where
  toContinuousLinearMap :=
    ({ toFun := fun a => limUnder (U : Filter ℕ) (fun n => a n)
       map_add' := fun a b =>
         ((tendsto_ultrafilter_bounded U _ (lp.norm_apply_le_norm ENNReal.top_ne_zero a)).add
           (tendsto_ultrafilter_bounded U _ (lp.norm_apply_le_norm ENNReal.top_ne_zero b))).limUnder_eq
       map_smul' := fun c a =>
         ((tendsto_ultrafilter_bounded U _ (lp.norm_apply_le_norm ENNReal.top_ne_zero a)).const_smul c).limUnder_eq } :
      ScalarBoundedProduct 𝕜 →ₗ[𝕜] 𝕜).mkContinuous 1 (fun a => by
        simpa only [one_mul] using norm_ultrafilter_bounded_le U _
          (lp.norm_apply_le_norm ENNReal.top_ne_zero a))
  map_mul' a b :=
    ((tendsto_ultrafilter_bounded U _ (lp.norm_apply_le_norm ENNReal.top_ne_zero a)).mul
      (tendsto_ultrafilter_bounded U _ (lp.norm_apply_le_norm ENNReal.top_ne_zero b))).limUnder_eq

@[simp] theorem lpUltrafilterEvaluation_one (U : Ultrafilter ℕ) :
    lpUltrafilterEvaluation (𝕜 := 𝕜) U 1 = 1 := tendsto_const_nhds.limUnder_eq

theorem lpUltrafilterEvaluation_surjective (U : Ultrafilter ℕ) :
    Function.Surjective (lpUltrafilterEvaluation (𝕜 := 𝕜) U) := by
  intro c
  refine ⟨c • 1, ?_⟩
  change (lpUltrafilterEvaluation U).toContinuousLinearMap (c • 1) = c
  rw [map_smul]
  simp

/-- The kernel of a surjective scalar homomorphism is a maximal closed ideal. -/
theorem scalarHomKernel_maximal {A : Type*}
    [NormedAddCommGroup A] [NormedSpace 𝕜 A] [Mul A]
    (Φ : BoundedHom 𝕜 A 𝕜) (hsurj : Function.Surjective Φ) :
    IsMaximalClosedIdeal 𝕜 {a | Φ a = 0} := by
  have hc : IsClosedIdeal 𝕜 ({0} : Set 𝕜) := by
    refine ⟨isClosed_singleton, by simp, ?_, ?_, ?_⟩ <;> intros <;> simp_all
  refine ⟨closedIdeal_preimage Φ hc, ?_, ?_⟩
  · intro h
    obtain ⟨a, ha⟩ := hsurj 1
    have hz : a ∈ {a | Φ a = 0} := h.symm ▸ Set.mem_univ a
    exact one_ne_zero (ha.symm.trans hz)
  · intro J hJ hker
    by_cases heq : J = {a | Φ a = 0}
    · exact Or.inl heq
    · right
      have hnot : ¬ J ⊆ {a | Φ a = 0} := fun h => heq (subset_antisymm h hker)
      obtain ⟨a, ha, hΦa⟩ := Set.not_subset.mp hnot
      change Φ a ≠ 0 at hΦa
      apply Set.eq_univ_of_forall
      intro b
      let c := Φ b / Φ a
      have hdiff : b - c • a ∈ J := hker (by
        change Φ.toContinuousLinearMap (b - c • a) = 0
        rw [map_sub, map_smul]
        simp [c, hΦa])
      have hca := hJ.2.2.2.1 c a ha
      simpa only [sub_add_cancel] using hJ.2.2.1 _ hdiff _ hca

def lpIndicator (A : Set ℕ) : ScalarBoundedProduct 𝕜 :=
  ⟨fun n => if n ∈ A then 1 else 0, memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    dsimp only
    split_ifs <;> simp⟩⟩

theorem lpUltrafilterEvaluation_indicator (U : Ultrafilter ℕ) (A : Set ℕ) :
    lpUltrafilterEvaluation (𝕜 := 𝕜) U (lpIndicator A) = if A ∈ U then 1 else 0 := by
  by_cases hA : A ∈ U
  · rw [if_pos hA]
    have ht : Tendsto (fun n => (lpIndicator (𝕜 := 𝕜) A) n) (U : Filter ℕ) (𝓝 1) :=
      tendsto_const_nhds.congr' (Filter.eventually_of_mem hA (fun n hn => by
        simp [lpIndicator, hn]))
    exact ht.limUnder_eq
  · rw [if_neg hA]
    have ht : Tendsto (fun n => (lpIndicator (𝕜 := 𝕜) A) n) (U : Filter ℕ) (𝓝 0) :=
      tendsto_const_nhds.congr' (Filter.eventually_of_mem
        (Ultrafilter.compl_mem_iff_notMem.mpr hA) (fun n hn => by
          change n ∉ A at hn
          simp [lpIndicator, hn]))
    exact ht.limUnder_eq

def ultrafilterMaximalIdealEmbedding :
    Ultrafilter ℕ ↪ MaximalClosedIdeals 𝕜 (ScalarBoundedProduct 𝕜) where
  toFun U := ⟨{a | lpUltrafilterEvaluation U a = 0},
    scalarHomKernel_maximal _ (lpUltrafilterEvaluation_surjective U)⟩
  inj' := by
    intro U V h
    apply Ultrafilter.ext
    intro A
    have he := Set.ext_iff.mp (congrArg Subtype.val h) (lpIndicator (𝕜 := 𝕜) A)
    change lpUltrafilterEvaluation U (lpIndicator A) = 0 ↔
      lpUltrafilterEvaluation V (lpIndicator A) = 0 at he
    simp only [lpUltrafilterEvaluation_indicator, ite_eq_right_iff, one_ne_zero, imp_false] at he
    exact not_iff_not.mp he

def manyScalarMaximalIdealsEmbedding :
    Set (Set ℕ) ↪ MaximalClosedIdeals 𝕜 (ScalarBoundedProduct 𝕜) :=
  manyUltrafiltersEmbedding.trans ultrafilterMaximalIdealEmbedding

end Posets
