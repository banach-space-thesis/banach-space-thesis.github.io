import NonCalkinAlgebra.TraceDiagramWeights
import NonCalkinAlgebra.TraceWeightUniqueness
import NonCalkinAlgebra.FiniteBlockTraceCoefficients
import NonCalkinAlgebra.ProductCoordinateEmbedding

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 120000

namespace NonCalkinAlgebra.TraceWeightRefinement
open NonCalkinAlgebra.FiniteBlockRefinement
open NonCalkinAlgebra.FiniteBlockRefinement.RootedBlockDiagram
open scoped Matrix.Norms.L2Operator

variable {R : Subring ℝ}

open Classical in
private theorem edge_coefficient_sum (s : State R) (z : Bool → ℂ)
    (FD : Fintype Bool) (FK : ∀ d, Fintype ((parameterEdge s).refinement.Copies d))
    (c : Bool) :
    (∑ d, ∑ k : (parameterEdge s).refinement.Copies d,
      @ite ℂ ((parameterEdge s).refinement.color d k = c) (Classical.propDecidable _) (z d) 0) =
      if s.rightWeight < s.leftWeight then
        if c then z true else z false + z true
      else
        if c then z false + z true else z false := by
  have hFD : FD = Bool.fintype := Subsingleton.elim _ _
  subst FD
  by_cases h : s.rightWeight < s.leftWeight
  · have he : parameterEdge s =
      ⟨s.subtractLeft h, leftRefinement s.leftDim s.rightDim⟩ := dif_pos h
    revert FK
    rw [he, if_pos h]
    intro FK
    let fk (d : Bool) : Fintype ((leftRefinement s.leftDim s.rightDim).Copies d) := by
      cases d
      · exact inferInstanceAs (Fintype PUnit.{1})
      · exact inferInstanceAs (Fintype Bool)
    have hFK : FK = fk := Subsingleton.elim _ _
    subst FK
    cases c <;> simp [fk, leftRefinement, Fintype.sum_bool, Fintype.sum_unique, add_comm]
  · have hR := lt_of_le_of_ne (le_of_not_gt h) s.weights_ne
    have he : parameterEdge s =
      ⟨s.subtractRight hR, rightRefinement s.leftDim s.rightDim⟩ := dif_neg h
    revert FK
    rw [he, if_neg h]
    intro FK
    let fk (d : Bool) : Fintype ((rightRefinement s.leftDim s.rightDim).Copies d) := by
      cases d
      · exact inferInstanceAs (Fintype Bool)
      · exact inferInstanceAs (Fintype PUnit.{1})
    have hFK : FK = fk := Subsingleton.elim _ _
    subst FK
    cases c <;> simp [fk, rightRefinement, Fintype.sum_bool, Fintype.sum_unique, add_comm]

universe u
variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A]
  [CStarRing A] [StarModule ℂ A]

/-- The first-stage projection has the assigned trace in any algebra
carrying compatible unital *-representations of the coordinate. -/
theorem coordinate_trace_value (s : State R) (hl : s.leftDim = 1) (hr : s.rightDim = 1)
    (g : ∀ n, Blocks ((parameterDiagram s hl hr).Row n) →⋆ₐ[ℂ] A)
    (hg : ∀ n x, g (n+1) (((parameterDiagram s hl hr).step n).hom x) = g n x)
    (σ : A →L[ℂ] ℂ) (hσ : IsNormalizedTrace σ) :
    σ (g 1 (rankOne ((parameterDiagram s hl hr).Row 1) false
      (Classical.choice inferInstance))) = (s.leftWeight : ℂ) := by
  classical
  let D := parameterDiagram s hl hr
  let row (n : ℕ) (c : D.Color n) : D.Row n c := Classical.choice inferInstance
  let L (n : ℕ) : Blocks (D.Row n) →ₗ[ℂ] ℂ := σ.toLinearMap.comp (g n).toAlgHom.toLinearMap
  have hcyc (n : ℕ) (x y : Blocks (D.Row n)) : L n (x*y) = L n (y*x) := by
    change σ (g n (x*y)) = σ (g n (y*x))
    have hxy : g n (x * y) = g n x * g n y := map_mul (g n) x y
    have hyx : g n (y * x) = g n y * g n x := map_mul (g n) y x
    rw [hxy, hyx]
    exact hσ.2 _ _
  let t (n : ℕ) (c : Bool) : ℂ := L (n+1) (rankOne (D.Row (n+1)) c (row (n+1) c))
  have hlocal (n : ℕ) (c : Bool) :
      t n c = if (parameterStates s n).rightWeight < (parameterStates s n).leftWeight then
        if c then t (n+1) true else t (n+1) false + t (n+1) true
      else
        if c then t (n+1) false + t (n+1) true else t (n+1) false := by
    have h := traceCoefficients_compatible (D.step (n+1)) (L (n+1)) (L (n+2))
      (hcyc _) (fun x => congrArg σ (hg (n+1) x)) c (row (n+1) c) (row (n+2))
    exact h.trans (edge_coefficient_sum (parameterStates s n) (t (n+1)) _ _ c)
  have hnorm : t 0 false + t 0 true = 1 := by
    have h1 := linearTrace_eq_sum (L 1) (hcyc 1) (row 1) 1
    have hleft : L 1 1 = 1 := by
      change σ (g 1 1) = 1
      rw [map_one]
      exact hσ.1
    rw [hleft] at h1
    have hcard (n : ℕ) (F : Fintype (Fin n)) : @Fintype.card (Fin n) F = n := by
      have hF : F = Fin.fintype n := Subsingleton.elim _ _
      rw [hF, Fintype.card_fin]
    have hc (c : D.Color 1) : Fintype.card (D.Row 1 c) = 1 := by
      cases c
      · exact (hcard s.leftDim _).trans hl
      · exact (hcard s.rightDim _).trans hr
    have hsum : (∑ c : D.Color 1, t 0 c) = t 0 false + t 0 true := by
      let f : Fintype Bool := localColorFintype D 1
      have hf : f = Bool.fintype := Subsingleton.elim _ _
      exact (congrArg (fun F : Fintype Bool => letI := F; ∑ c : Bool, t 0 c) hf).trans
        ((Fintype.sum_bool (t 0)).trans (add_comm _ _))
    simp only [Pi.one_apply, Matrix.trace_one, hc, Nat.cast_one, mul_one] at h1
    change (1 : ℂ) = ∑ c : D.Color 1, t 0 c at h1
    rw [hsum] at h1
    exact h1.symm
  have hbound (n : ℕ) (c : Bool) : ‖t n c‖ ≤ ‖σ‖ := by
    let p := rankOne (D.Row (n+1)) c (row (n+1) c)
    let e := g (n+1) p
    have he : e * e = e := by
      change g (n+1) p * g (n+1) p = g (n+1) p
      rw [← map_mul, rankOne_sq]
    have hes : star e = e := by
      change star (g (n+1) p) = g (n+1) p
      rw [← map_star, rankOne_star]
    have hen : ‖e‖ ≤ 1 := by
      have hn := CStarRing.norm_star_mul_self (x := e)
      rw [hes, he] at hn
      nlinarith [norm_nonneg e]
    exact (σ.le_opNorm e).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hen (norm_nonneg σ))
  let l (n : ℕ) := t n false - ((s.stages n).leftWeight : ℂ)
  let r (n : ℕ) := t n true - ((s.stages n).rightWeight : ℂ)
  have hcompatible : CompatibleWeights s l r := by
    intro n
    have hf := hlocal n false
    have ht := hlocal n true
    simp only [parameterStates_eq_stages] at hf ht
    by_cases h : (s.stages n).rightWeight < (s.stages n).leftWeight
    · simp only [if_pos h, Bool.false_eq_true, if_false, if_true] at hf ht
      simp only [if_pos h, l, r, State.stages_succ, State.step, dif_pos h,
        State.subtractLeft, Complex.ofReal_sub]
      constructor
      · rw [hf]
        ring
      · exact congrArg (fun z : ℂ => z - ((s.stages n).rightWeight : ℂ)) ht
    · simp only [if_neg h, Bool.false_eq_true, if_false, if_true] at hf ht
      simp only [if_neg h, l, r, State.stages_succ, State.step, dif_neg h,
        State.subtractRight, Complex.ofReal_sub]
      constructor
      · exact congrArg (fun z : ℂ => z - ((s.stages n).leftWeight : ℂ)) hf
      · rw [ht]
        ring
  have hzero : (s.leftDim : ℂ) * l 0 + (s.rightDim : ℂ) * r 0 = 0 := by
    have hsum : (s.leftWeight : ℂ) + (s.rightWeight : ℂ) = 1 := by
      exact_mod_cast (show s.leftWeight + s.rightWeight = 1 by simpa [hl, hr] using s.normalized)
    simp only [hl, hr, Nat.cast_one, one_mul, l, r, State.stages_zero]
    linear_combination hnorm - hsum
  have hweight (a : State R) : a.leftWeight ≤ 1 ∧ a.rightWeight ≤ 1 := by
    have hd₁ : (1 : ℝ) ≤ a.leftDim := by exact_mod_cast a.leftDim_pos
    have hd₂ : (1 : ℝ) ≤ a.rightDim := by exact_mod_cast a.rightDim_pos
    have h₁ := mul_le_mul_of_nonneg_right hd₁ a.leftWeight_pos.le
    have h₂ := mul_le_mul_of_nonneg_right hd₂ a.rightWeight_pos.le
    constructor <;> nlinarith [a.normalized, a.leftWeight_pos, a.rightWeight_pos]
  have huniform (n : ℕ) : ‖l n‖ + ‖r n‖ ≤ 2 * (‖σ‖ + 1) := by
    have hl' := norm_sub_le (t n false) ((s.stages n).leftWeight : ℂ)
    have hr' := norm_sub_le (t n true) ((s.stages n).rightWeight : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (s.stages n).leftWeight_pos] at hl'
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (s.stages n).rightWeight_pos] at hr'
    dsimp [l, r]
    linarith [hbound n false, hbound n true, (hweight (s.stages n)).1, (hweight (s.stages n)).2]
  exact sub_eq_zero.mp (compatible_difference_eq_zero s l r hcompatible hzero _ huniform 0).1

end NonCalkinAlgebra.TraceWeightRefinement
