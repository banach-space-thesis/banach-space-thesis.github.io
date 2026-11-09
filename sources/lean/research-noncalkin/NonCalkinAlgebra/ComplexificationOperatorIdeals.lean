import NonCalkinAlgebra.ComplexificationCoordinates
import NonCalkinAlgebra.OperatorIdeals
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra.BanachComplexification
universe u v
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem map_decomposition (T : X →L[ℝ] Y) (f : BanachComplexification X) :
    map X T f = embedding Y (T (toRealMap f 1)) -
      Complex.I • embedding Y (T (toRealMap f Complex.I)) := by
  calc
    map X T f = fromCoordinates Y (toCoordinates Y (map X T f)) :=
      (from_to_coordinates Y _).symm
    _ = _ := by
      rw [toCoordinates_map, toCoordinates_apply]
      change embedding Y (T (toRealMap f 1)) +
        Complex.I • embedding Y (T (-toRealMap f Complex.I)) = _
      rw [map_neg, map_neg, smul_neg, sub_eq_add_neg]

/-- Real compactness is preserved by complexification on arbitrary Banach
spaces, with the actual Taylor norm. -/
theorem compact_map (T : X →L[ℝ] Y) (hT : IsCompactOperator T) :
    IsCompactOperator (map X T) := by
  have h₁ := (hT.comp_clm (evaluation X 1)).clm_comp (embedding Y)
  have h₂ := (hT.comp_clm (evaluation X Complex.I)).clm_comp (embedding Y)
  have heq : (fun f : BanachComplexification X => map X T f) =
      (fun f => embedding Y (T (toRealMap f 1)) -
        Complex.I • embedding Y (T (toRealMap f Complex.I))) :=
    funext (map_decomposition X T)
  change IsCompactOperator (fun f : BanachComplexification X => map X T f)
  rw [heq]
  exact h₁.sub (h₂.smul Complex.I)

theorem compact_of_map (T : X →L[ℝ] Y) (hT : IsCompactOperator (map X T)) :
    IsCompactOperator T := by
  have h := (hT.comp_clm (embedding X)).clm_comp (evaluation Y 1)
  have heq : (evaluation Y 1) ∘ (map X T) ∘ (embedding X) = T := by
    funext x
    simp only [Function.comp_apply, map_embedding, evaluation_apply, embedding_apply,
      Complex.one_re, one_smul]
  rw [heq] at h
  exact h

theorem compact_map_iff (T : X →L[ℝ] Y) :
    IsCompactOperator (map X T) ↔ IsCompactOperator T :=
  ⟨compact_of_map X T, compact_map X T⟩

/-- Complexifying a finite-rank real map gives a finite-rank complex map.
The proof uses a finite real basis of the actual range and its complex span. -/
theorem finiteRank_map (T : X →L[ℝ] Y)
    (hT : FiniteDimensional ℝ (LinearMap.range T.toLinearMap)) :
    FiniteDimensional ℂ (LinearMap.range (map X T).toLinearMap) := by
  classical
  letI : FiniteDimensional ℝ (LinearMap.range T.toLinearMap) := hT
  let b := Module.finBasis ℝ (LinearMap.range T.toLinearMap)
  let c : Fin (Module.finrank ℝ (LinearMap.range T.toLinearMap)) →
      BanachComplexification Y := fun j => embedding Y (b j).val
  let W : Submodule ℂ (BanachComplexification Y) := Submodule.span ℂ (Set.range c)
  letI : FiniteDimensional ℂ W :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range c)
  have hevery : ∀ r : LinearMap.range T.toLinearMap, embedding Y r.val ∈ W := by
    intro r
    let L : (LinearMap.range T.toLinearMap) →ₗ[ℝ] BanachComplexification Y :=
      (embedding Y).toLinearMap.comp (LinearMap.range T.toLinearMap).subtype
    have hsum := congrArg L (b.sum_repr r)
    simp only [map_sum, map_smul] at hsum
    change L r ∈ W.restrictScalars ℝ
    rw [← hsum]
    apply (W.restrictScalars ℝ).sum_mem
    intro j hj
    apply (W.restrictScalars ℝ).smul_mem
    exact Submodule.subset_span ⟨j, rfl⟩
  apply Submodule.finiteDimensional_of_le (S₂ := W)
  rintro y ⟨f, rfl⟩
  change map X T f ∈ W
  rw [map_decomposition]
  exact W.sub_mem (hevery ⟨T (toRealMap f 1), ⟨toRealMap f 1, rfl⟩⟩)
    (W.smul_mem Complex.I
      (hevery ⟨T (toRealMap f Complex.I), ⟨toRealMap f Complex.I, rfl⟩⟩))

theorem finiteRank_of_map (T : X →L[ℝ] Y)
    (hT : FiniteDimensional ℂ (LinearMap.range (map X T).toLinearMap)) :
    FiniteDimensional ℝ (LinearMap.range T.toLinearMap) := by
  let R := LinearMap.range (map X T).toLinearMap
  letI : FiniteDimensional ℂ R := hT
  letI : FiniteDimensional ℝ R := FiniteDimensional.trans ℝ ℂ R
  let U : R →ₗ[ℝ] Y := (evaluation Y 1).toLinearMap.comp (R.subtype.restrictScalars ℝ)
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range U)
  rintro y ⟨x, rfl⟩
  refine ⟨⟨map X T (embedding X x), ⟨embedding X x, rfl⟩⟩, ?_⟩
  change evaluation Y 1 (map X T (embedding X x)) = T x
  simp only [map_embedding, evaluation_apply, embedding_apply, Complex.one_re, one_smul]

theorem finiteRank_map_iff (T : X →L[ℝ] Y) :
    FiniteDimensional ℂ (LinearMap.range (map X T).toLinearMap) ↔
      FiniteDimensional ℝ (LinearMap.range T.toLinearMap) :=
  ⟨finiteRank_of_map X T, finiteRank_map X T⟩

end NonCalkinAlgebra.BanachComplexification
