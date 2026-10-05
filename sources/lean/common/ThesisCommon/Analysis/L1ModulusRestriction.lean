import ThesisCommon.Analysis.L1OperatorCountableSup
import ThesisCommon.Analysis.ALCountableSup

/-! Countably many actual input vectors suffice to preserve the modulus of
a bounded real L1 operator under restriction. For finite input measure the
constant-one function detects equality of comparable positive operators,
so witnesses for its Riesz--Kantorovich supremum suffice. This is the
modulus-preserving enlargement step in PEMS Lemma 4.8. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable {μ : Measure X} {ν : Measure Y} {η : Measure Z}

/-- The full operator modulus on a positive input is witnessed by a countable
set of actual vectors in its order interval. No separability of either L1
space is assumed. -/
theorem lOneOperatorModulus_countable_witnesses
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
    ∃ W : Set (Lp ℝ 1 μ), W.Countable ∧ W ⊆ Icc (-f) f ∧
      IsLUB (T '' W) (lOneOperatorModulus T f) := by
  classical
  obtain ⟨c, hcsub, hcount, hc⟩ := al_countable_sup_property (lOne_norm_add_of_nonneg ν)
    (lOneOperatorModulus_rieszKantorovich T f hf)
  have hpre (y : c) : ∃ g : Lp ℝ 1 μ, g ∈ Icc (-f) f ∧ T g = y.val :=
    hcsub y.property
  choose g hg hTg using hpre
  letI : Countable c := hcount.to_subtype
  refine ⟨range g, countable_range g, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact hg y
  · have heq : T '' range g = c := by
      ext y
      constructor
      · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
        rw [hTg z]
        exact z.property
      · intro hy
        exact ⟨g ⟨y, hy⟩, mem_range_self _, hTg ⟨y, hy⟩⟩
    rwa [heq]

/-- Positive restriction always decreases the modulus. -/
theorem lOneOperatorModulus_comp_le
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (J : Lp ℝ 1 η →L[ℝ] Lp ℝ 1 μ)
    (hJ : 0 ≤ J) :
    lOneOperatorModulus (T.comp J) ≤ (lOneOperatorModulus T).comp J := by
  intro f hf
  apply lOneOperatorModulus_least (T.comp J) ((lOneOperatorModulus T).comp J) _ f hf
  intro g hg
  simpa only [ContinuousLinearMap.comp_apply, abs_of_nonneg (hJ g hg)] using
    lOneOperatorModulus_dominates T (J g)

/-- An order-reflecting embedding which preserves the constant-one vector
and contains the supremum witnesses preserves the entire operator modulus.
The domain and original input measures are finite; the output measure is
arbitrary, and zero measure spaces are included. -/
theorem lOneOperatorModulus_comp_eq_of_witnesses [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (J : Lp ℝ 1 η →L[ℝ] Lp ℝ 1 μ)
    (hJ : ∀ f g, J f ≤ J g ↔ f ≤ g)
    (hone : J (lOneIndicator η univ MeasurableSet.univ) =
      lOneIndicator μ univ MeasurableSet.univ)
    (W : Set (Lp ℝ 1 μ))
    (hW : W ⊆ Icc (-lOneIndicator μ univ MeasurableSet.univ)
      (lOneIndicator μ univ MeasurableSet.univ))
    (hsup : IsLUB (T '' W)
      (lOneOperatorModulus T (lOneIndicator μ univ MeasurableSet.univ)))
    (hrange : W ⊆ range J) :
    lOneOperatorModulus (T.comp J) = (lOneOperatorModulus T).comp J := by
  have hJpos : 0 ≤ J := by
    intro f hf
    simpa only [map_zero] using (hJ 0 f).mpr hf
  have hle := lOneOperatorModulus_comp_le T J hJpos
  apply lOneOperator_eq_of_le_of_one hle
  apply le_antisymm (hle _ (lOneIndicator_nonneg _ _))
  rw [ContinuousLinearMap.comp_apply, hone]
  apply hsup.2
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨f, hfg⟩ := hrange hg
  have hf : f ∈ Icc (-lOneIndicator η univ MeasurableSet.univ)
      (lOneIndicator η univ MeasurableSet.univ) := by
    constructor
    · apply (hJ _ _).mp
      simpa only [map_neg, hone, hfg] using (hW hg).1
    · apply (hJ _ _).mp
      simpa only [hone, hfg] using (hW hg).2
  have hb := (lOneOperatorModulus_rieszKantorovich (T.comp J)
    (lOneIndicator η univ MeasurableSet.univ) (lOneIndicator_nonneg _ _)).1
      (show (T.comp J) f ∈ (T.comp J) ''
        Icc (-lOneIndicator η univ MeasurableSet.univ)
          (lOneIndicator η univ MeasurableSet.univ) from ⟨f, hf, rfl⟩)
  simpa only [ContinuousLinearMap.comp_apply, hfg] using hb

/-- A single countable set works for every subsequent order-reflecting
restriction which contains it and preserves one. -/
theorem exists_countable_lOne_modulus_restriction_witnesses [IsFiniteMeasure μ]
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    ∃ W : Set (Lp ℝ 1 μ), W.Countable ∧
      ∀ (η : Measure Z) [IsFiniteMeasure η] (J : Lp ℝ 1 η →L[ℝ] Lp ℝ 1 μ),
        (∀ f g, J f ≤ J g ↔ f ≤ g) →
        J (lOneIndicator η univ MeasurableSet.univ) =
          lOneIndicator μ univ MeasurableSet.univ →
        W ⊆ range J →
        lOneOperatorModulus (T.comp J) = (lOneOperatorModulus T).comp J := by
  obtain ⟨W, hc, hW, hsup⟩ := lOneOperatorModulus_countable_witnesses T
    (lOneIndicator μ univ MeasurableSet.univ) (lOneIndicator_nonneg _ _)
  exact ⟨W, hc, fun η _ J hJ hone hrange =>
    lOneOperatorModulus_comp_eq_of_witnesses T J hJ hone W hW hsup hrange⟩

end ThesisCommon
