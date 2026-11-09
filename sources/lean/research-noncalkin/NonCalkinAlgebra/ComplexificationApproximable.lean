import NonCalkinAlgebra.ComplexificationOperatorIdeals
import NonCalkinAlgebra.RealOperatorIdeals

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra.BanachComplexification
universe u v
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Complexification is a bounded real-linear map on the operator spaces. -/
def mapOperator : (X →L[ℝ] Y) →L[ℝ]
    (BanachComplexification X →L[ℂ] BanachComplexification Y) :=
  LinearMap.mkContinuous
    { toFun := map X
      map_add' := by
        intro S T
        apply ContinuousLinearMap.ext
        intro f
        change (S + T).comp (toRealMap f) =
          S.comp (toRealMap f) + T.comp (toRealMap f)
        ext z
        rfl
      map_smul' := by
        intro r T
        apply ContinuousLinearMap.ext
        intro f
        change (r • T).comp (toRealMap f) = r • T.comp (toRealMap f)
        ext z
        rfl }
    1 (fun T => by
      change ‖map X T‖ ≤ 1 * ‖T‖
      rw [norm_map, one_mul])

@[simp] theorem mapOperator_apply (T : X →L[ℝ] Y) : mapOperator X T = map X T := rfl

/-- Taking a real coordinate after restricting to the embedded original
space is bounded on the full complex operator space. -/
def extractOperator (z : ℂ) :
    (BanachComplexification X →L[ℂ] BanachComplexification Y) →L[ℝ] (X →L[ℝ] Y) :=
  LinearMap.mkContinuous
    { toFun := fun U => (evaluation Y z).comp ((U.restrictScalars ℝ).comp (embedding X))
      map_add' := by intro U V; ext x; rfl
      map_smul' := by intro r U; ext x; rfl }
    ‖z‖ (fun U => by
      apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg z) (norm_nonneg U))
      intro x
      change ‖toRealMap (U (embedding X x)) z‖ ≤ _
      calc
        ‖toRealMap (U (embedding X x)) z‖ ≤ ‖U (embedding X x)‖ * ‖z‖ :=
          (toRealMap (U (embedding X x))).le_opNorm _
        _ ≤ (‖U‖ * ‖embedding X x‖) * ‖z‖ :=
          mul_le_mul_of_nonneg_right (U.le_opNorm _) (norm_nonneg z)
        _ = (‖z‖ * ‖U‖) * ‖x‖ := by rw [norm_embedding]; ring)

@[simp] theorem extractOperator_apply (z : ℂ)
    (U : BanachComplexification X →L[ℂ] BanachComplexification Y) (x : X) :
    extractOperator X z U x = toRealMap (U (embedding X x)) z := rfl

@[simp] theorem extractOperator_map (z : ℂ) (T : X →L[ℝ] Y) :
    extractOperator X z (map X T) = z.re • T := by
  ext x
  simp only [extractOperator_apply, map_embedding, embedding_apply,
    ContinuousLinearMap.smul_apply]

theorem finiteRank_extract (z : ℂ)
    (U : BanachComplexification X →L[ℂ] BanachComplexification Y)
    (hU : FiniteDimensional ℂ (LinearMap.range U.toLinearMap)) :
    extractOperator X z U ∈ realFiniteRankMaps X Y := by
  let R := LinearMap.range U.toLinearMap
  letI : FiniteDimensional ℂ R := hU
  letI : FiniteDimensional ℝ R := FiniteDimensional.trans ℝ ℂ R
  let V : R →ₗ[ℝ] Y := (evaluation Y z).toLinearMap.comp (R.subtype.restrictScalars ℝ)
  change FiniteDimensional ℝ (LinearMap.range (extractOperator X z U).toLinearMap)
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range V)
  rintro y ⟨x, rfl⟩
  exact ⟨⟨U (embedding X x), ⟨embedding X x, rfl⟩⟩, rfl⟩

/-- Passing from finite ranks to their actual norm closures proves
preservation of the approximable ideal. No approximation property is used. -/
theorem approximable_map (T : X →L[ℝ] X) (hT : T ∈ realApproximableMaps X X) :
    map X T ∈ approximableOperators (BanachComplexification X) := by
  have hmap : Set.MapsTo (mapOperator X (Y := X))
      (realFiniteRankMaps X X : Set (X →L[ℝ] X))
      (finiteRankOperators (BanachComplexification X) :
        Set (BanachComplexification X →L[ℂ] BanachComplexification X)) :=
    fun T hT => finiteRank_map X T hT
  exact hmap.closure (mapOperator X (Y := X)).continuous hT

theorem approximable_extract (z : ℂ)
    (U : BanachComplexification X →L[ℂ] BanachComplexification X)
    (hU : U ∈ approximableOperators (BanachComplexification X)) :
    extractOperator X z U ∈ realApproximableMaps X X := by
  have hmap : Set.MapsTo (extractOperator X (Y := X) z)
      (finiteRankOperators (BanachComplexification X) :
        Set (BanachComplexification X →L[ℂ] BanachComplexification X))
      (realFiniteRankMaps X X : Set (X →L[ℝ] X)) :=
    fun U hU => finiteRank_extract X z U hU
  exact hmap.closure (extractOperator X (Y := X) z).continuous hU

theorem approximable_map_iff (T : X →L[ℝ] X) :
    map X T ∈ approximableOperators (BanachComplexification X) ↔
      T ∈ realApproximableMaps X X := by
  constructor
  · intro h
    simpa only [extractOperator_map, Complex.one_re, one_smul] using
      approximable_extract X 1 (map X T) h
  · exact approximable_map X T

end NonCalkinAlgebra.BanachComplexification
