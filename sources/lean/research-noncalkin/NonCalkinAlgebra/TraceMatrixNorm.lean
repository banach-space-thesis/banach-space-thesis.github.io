import NonCalkinAlgebra.TraceMatrixSystem
import NonCalkinAlgebra.FiniteCStarEmbedding
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TraceWeightRefinement
open scoped Matrix.Norms.L2Operator
open Matrix
variable {R : Subring ℝ}

instance finiteDimensionalStage (s : State R) : FiniteDimensional ℂ (Stage s) :=
  inferInstanceAs (FiniteDimensional ℂ (Mat s.leftDim × Mat s.rightDim))

instance cstarStage (s : State R) : CStarAlgebra (Stage s) where
  toCompleteSpace := FiniteDimensional.complete ℂ _

instance normOneStage (s : State R) : NormOneClass (Stage s) := by
  letI : Nonempty (Fin s.leftDim) := ⟨⟨0, s.leftDim_pos⟩⟩
  letI : Nonempty (Fin s.rightDim) := ⟨⟨0, s.rightDim_pos⟩⟩
  infer_instance

theorem matrix_entry_norm_le {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (i j : I) :
    ‖M i j‖ ≤ ‖M‖ := by
  let v : EuclideanSpace ℂ (I) := EuclideanSpace.single j 1
  have hv : ‖v‖ = 1 := by simp [v, EuclideanSpace.norm_single]
  have hv' : (v : I → ℂ) = Pi.single j 1 := by
    funext k
    simp [v, EuclideanSpace.single_apply, Pi.single_apply]
  let w : EuclideanSpace ℂ (I) := (EuclideanSpace.equiv (I) ℂ).symm (M *ᵥ v)
  have hw : w i = M i j := by
    change (M *ᵥ (v : I → ℂ)) i = _
    rw [hv', Matrix.mulVec_single_one]
    rfl
  have hnorm := M.l2_opNorm_mulVec v
  change ‖w‖ ≤ ‖M‖ * ‖v‖ at hnorm
  rw [hv, mul_one] at hnorm
  rw [← hw]
  exact (PiLp.norm_apply_le w i).trans hnorm

theorem norm_trace_le {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ) :
    ‖Matrix.trace M‖ ≤ (Fintype.card I : ℝ) * ‖M‖ := by
  unfold Matrix.trace
  calc
    _ ≤ ∑ i : I, ‖M i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I, ‖M‖ := Finset.sum_le_sum fun i _ => matrix_entry_norm_le M i i
    _ = _ := by simp

theorem norm_weightedTrace_le (s : State R) (x : Stage s) : ‖weightedTrace s x‖ ≤ ‖x‖ := by
  have hl : ‖x.1‖ ≤ ‖x‖ := le_max_left _ _
  have hr : ‖x.2‖ ≤ ‖x‖ := le_max_right _ _
  have hta : ‖Matrix.trace x.1‖ ≤ (s.leftDim : ℝ) * ‖x.1‖ := by
    simpa only [Fintype.card_fin] using norm_trace_le x.1
  have htb : ‖Matrix.trace x.2‖ ≤ (s.rightDim : ℝ) * ‖x.2‖ := by
    simpa only [Fintype.card_fin] using norm_trace_le x.2
  have ha : ‖Matrix.trace x.1‖ ≤ (s.leftDim : ℝ) * ‖x‖ :=
    hta.trans (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _))
  have hb : ‖Matrix.trace x.2‖ ≤ (s.rightDim : ℝ) * ‖x‖ :=
    htb.trans (mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _))
  unfold weightedTrace
  calc
    _ ≤ ‖(s.leftWeight : ℂ) * Matrix.trace x.1‖ +
        ‖(s.rightWeight : ℂ) * Matrix.trace x.2‖ := norm_add_le _ _
    _ = s.leftWeight * ‖Matrix.trace x.1‖ + s.rightWeight * ‖Matrix.trace x.2‖ := by
      simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos s.leftWeight_pos, abs_of_pos s.rightWeight_pos]
    _ ≤ s.leftWeight * ((s.leftDim : ℝ) * ‖x‖) +
        s.rightWeight * ((s.rightDim : ℝ) * ‖x‖) :=
      add_le_add (mul_le_mul_of_nonneg_left ha s.leftWeight_pos.le)
        (mul_le_mul_of_nonneg_left hb s.rightWeight_pos.le)
    _ = ‖x‖ := by
      have h : s.leftWeight * (s.leftDim : ℝ) +
          s.rightWeight * (s.rightDim : ℝ) = 1 := by
        simpa only [mul_comm] using s.normalized
      rw [← mul_assoc, ← mul_assoc, ← add_mul, h, one_mul]

theorem norm_connecting (s : State R) (i j : ℕ) (h : i ≤ j)
    (x : MatrixStage s i) : ‖connecting s i j h x‖ = ‖x‖ := by
  exact le_antisymm (NonUnitalStarAlgHom.norm_apply_le (connecting s i j h) x)
    (norm_le_starAlgHom_of_finiteDimensional (connecting s i j h)
      (connecting_injective s i j h) x)

end NonCalkinAlgebra.TraceWeightRefinement
