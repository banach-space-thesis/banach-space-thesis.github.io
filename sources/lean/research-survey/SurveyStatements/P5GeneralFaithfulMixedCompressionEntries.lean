import SurveyStatements.P5GeneralFaithfulMixedCompression

/-! The two genuine finite block readers expand into their signed product-Haar
coordinates, with both actual atom-cardinality denominators. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
open P5Support BiTree
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem generalMixed_compLpL_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
    (0 : E →L[𝕜] F).compLpL p unitIntervalMeasure = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  change (0 : E →L[𝕜] F).compLpL p unitIntervalMeasure f =
    (0 : Lp F p unitIntervalMeasure)
  apply Lp.ext
  filter_upwards [(0 : E →L[𝕜] F).coeFn_compLpL f,
    Lp.coeFn_zero F p unitIntervalMeasure] with x hc hz
  rw [hc, hz]
  rfl

theorem generalMixed_compLpL_sum {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (s : Finset ι) (L : ι → E →L[𝕜] F) :
    (∑ i ∈ s, L i).compLpL p unitIntervalMeasure =
      ∑ i ∈ s, (L i).compLpL p unitIntervalMeasure := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, generalMixed_compLpL_zero]
  | @insert i s hi hs =>
      rw [Finset.sum_insert hi, ContinuousLinearMap.add_compLpL,
        hs, Finset.sum_insert hi]

theorem generalMixed_compLpL_signed {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (b : Bool) (L : E →L[𝕜] F) :
    (signedValue b L).compLpL p unitIntervalMeasure =
      signedValue b (L.compLpL p unitIntervalMeasure) := by
  cases b
  · change (-L).compLpL p unitIntervalMeasure = -L.compLpL p unitIntervalMeasure
    rw [show -L = (-1 : 𝕜) • L by simp, ContinuousLinearMap.smul_compLpL]
    simp
  · rfl

theorem generalMixed_lift_block_reader (R : LpHaarFiniteSplit) :
    (R.reader 𝕜 ⟨1, le_rfl⟩).compLpL p unitIntervalMeasure =
      (R.atoms.card : 𝕜)⁻¹ • ∑ l ∈ R.atoms,
        signedValue (R.signs l)
          ((dyadicHaarCoordinate 𝕜 1 ⟨R.level, l⟩).compLpL p unitIntervalMeasure) := by
  rw [LpHaarFiniteSplit.reader, lpHaarSignedBlockReader,
    ContinuousLinearMap.smul_compLpL, generalMixed_compLpL_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [generalMixed_compLpL_signed, dyadicHaarCoordinate_eq_support]

theorem generalMixed_lift_block_reader_apply (R : LpHaarFiniteSplit)
    (f : MixedNorm 𝕜 p) :
    (R.reader 𝕜 ⟨1, le_rfl⟩).compLpL p unitIntervalMeasure f =
      (R.atoms.card : 𝕜)⁻¹ • ∑ l ∈ R.atoms,
        signedValue (R.signs l)
          ((dyadicHaarCoordinate 𝕜 1 ⟨R.level, l⟩).compLpL p unitIntervalMeasure f) := by
  let maps : MixedNorm 𝕜 p →L[𝕜] Lp 𝕜 p unitIntervalMeasure :=
    ∑ l ∈ R.atoms, signedValue (R.signs l)
      ((dyadicHaarCoordinate 𝕜 1 ⟨R.level, l⟩).compLpL p unitIntervalMeasure)
  have hsum : maps f = ∑ l ∈ R.atoms, signedValue (R.signs l)
      ((dyadicHaarCoordinate 𝕜 1 ⟨R.level, l⟩).compLpL p unitIntervalMeasure f) := by
    dsimp only [maps]
    simp only [ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro l _
    cases R.signs l <;>
      simp only [signedValue, if_true, Bool.false_eq_true, if_false,
        ContinuousLinearMap.neg_apply]
  have hreader := congrArg
    (fun L : MixedNorm 𝕜 p →L[𝕜] Lp 𝕜 p unitIntervalMeasure => L f)
    (generalMixed_lift_block_reader (𝕜 := 𝕜) (p := p) R)
  calc
    _ = ((R.atoms.card : 𝕜)⁻¹ • maps) f := hreader
    _ = (R.atoms.card : 𝕜)⁻¹ • maps f := ContinuousLinearMap.smul_apply _ _ _
    _ = _ := congrArg (fun x : Lp 𝕜 p unitIntervalMeasure => (R.atoms.card : 𝕜)⁻¹ • x) hsum

theorem faithfulMixedBlockReader_coordinate_sum
    (Fo Fi : BiTree.SignedTree) (I J : DyadicIndex) (f : MixedNorm 𝕜 p) :
    faithfulMixedBlockReader (𝕜 := 𝕜) (p := p) Fo Fi I J f =
      ((Fo.block I).atoms.card : 𝕜)⁻¹ * ((Fi.block J).atoms.card : 𝕜)⁻¹ *
        ∑ k ∈ (Fo.block I).atoms, ∑ l ∈ (Fi.block J).atoms,
          signedValue ((Fo.block I).signs k) (signedValue ((Fi.block J).signs l)
            (productHaarCoordinate 𝕜 p ⟨(Fo.block I).level, k⟩
              ⟨(Fi.block J).level, l⟩ f)) := by
  let S := Fo.block I
  let R := Fi.block J
  let v : Lp 𝕜 p unitIntervalMeasure := ∑ l ∈ R.atoms, signedValue (R.signs l)
    ((dyadicHaarCoordinate 𝕜 1 ⟨R.level, l⟩).compLpL p unitIntervalMeasure f)
  let z : 𝕜 := ∑ k ∈ S.atoms, ∑ l ∈ R.atoms, signedValue (S.signs k)
    (signedValue (R.signs l) (productHaarCoordinate 𝕜 p ⟨S.level, k⟩ ⟨R.level, l⟩ f))
  have hmatrix : S.reader 𝕜 ⟨p, Fact.out⟩ v = (S.atoms.card : 𝕜)⁻¹ * z := by
    rw [LpHaarFiniteSplit.reader, lpHaarSignedBlockReader_apply]
    congr 1
    dsimp only [z, v]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_sum]
    have hs (l : Fin (2 ^ R.level)) :
        lpHaarDyadicCoefficient 𝕜 ⟨p, Fact.out⟩ S.level k
          (signedValue (R.signs l)
            ((dyadicHaarCoordinate 𝕜 1 ⟨R.level, l⟩).compLpL p unitIntervalMeasure f)) =
        signedValue (R.signs l)
          (productHaarCoordinate 𝕜 p ⟨S.level, k⟩ ⟨R.level, l⟩ f) := by
      rw [productHaarCoordinate, ContinuousLinearMap.comp_apply,
        dyadicHaarCoordinate_eq_support (𝕜 := 𝕜) (p := p) ⟨S.level, k⟩]
      cases R.signs l <;>
        simp only [signedValue, if_true, Bool.false_eq_true, if_false, map_neg] <;> rfl
    simp_rw [hs]
    cases S.signs k <;>
      simp only [signedValue, if_true, Bool.false_eq_true, if_false, Finset.sum_neg_distrib]
  change (S.reader 𝕜 ⟨p, Fact.out⟩)
    ((R.reader 𝕜 ⟨1, le_rfl⟩).compLpL p unitIntervalMeasure f) = _
  calc
    _ = S.reader 𝕜 ⟨p, Fact.out⟩ ((R.atoms.card : 𝕜)⁻¹ • v) :=
      congrArg (fun x : Lp 𝕜 p unitIntervalMeasure => S.reader 𝕜 ⟨p, Fact.out⟩ x)
        (generalMixed_lift_block_reader_apply (𝕜 := 𝕜) (p := p) R f)
    _ = (R.atoms.card : 𝕜)⁻¹ • (S.reader 𝕜 ⟨p, Fact.out⟩ v) :=
      map_smul (S.reader 𝕜 ⟨p, Fact.out⟩) _ _
    _ = (R.atoms.card : 𝕜)⁻¹ • ((S.atoms.card : 𝕜)⁻¹ * z) :=
      congrArg (fun x : 𝕜 => (R.atoms.card : 𝕜)⁻¹ • x) hmatrix
    _ = (S.atoms.card : 𝕜)⁻¹ * (R.atoms.card : 𝕜)⁻¹ * z := by
      rw [smul_eq_mul]
      ring

end SurveyStatements.P5
