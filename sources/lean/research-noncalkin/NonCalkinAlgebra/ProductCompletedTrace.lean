import NonCalkinAlgebra.ProductAFAlgebra
import NonCalkinAlgebra.CompletedAFTrace
import NonCalkinAlgebra.DiagramTraceLaw
import NonCalkinAlgebra.TraceMatrixNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace NonCalkinAlgebra.FiniteBlockRefinement.RootedBlockDiagram
open NonCalkinAlgebra.FiniteBlockRefinement NonCalkinAlgebra.NormedStarDirectLimit
open UniformSpace
open scoped Matrix.Norms.L2Operator NonCalkinAlgebra.NormedStarCompletion

universe u
variable {ι : Type u} (D : ι → RootedBlockDiagram.{u})
variable (w : ∀ i n, (D i).Color n → ℝ)

abbrev stageTrace (a : Level ι) : TensorStage D a →ₗ[ℂ] ℂ :=
  weightedBlockTrace (tensorWeight D w a)

theorem stageTrace_compat (hw0 : ∀ i c, w i 0 c = 1)
    (hw : ∀ i n, UniversalWeightLaw ((D i).step n) (w i n) (w i (n+1)))
    (a b : Level ι) (hab : a ≤ b) (x : TensorStage D a) :
    stageTrace D w b (tensorConnecting D a b hab x) = stageTrace D w a x := by
  apply Refinement.weightedBlockTrace_map
  apply tensorWeight_law D w hw0
  intro i n m h
  exact (universalWeightLaw_path (D i) (w i) (hw i) n m h).law _ _ _

private theorem tensorColorZeroSubsingleton : Subsingleton (TensorColor D 0) := by
  change Subsingleton (∀ i, (D i).Color 0)
  infer_instance

private theorem tensorRowZeroSubsingleton (c : TensorColor D 0) :
    Subsingleton (TensorRow D 0 c) := by
  change Subsingleton (∀ i, (D i).Row 0 (c i))
  infer_instance

theorem stageTrace_one (hw0 : ∀ i c, w i 0 c = 1)
    (hw : ∀ i n, UniversalWeightLaw ((D i).step n) (w i n) (w i (n+1)))
    (a : Level ι) : stageTrace D w a 1 = 1 := by
  have h := stageTrace_compat D w hw0 hw 0 a (by intro i; exact Nat.zero_le _) 1
  rw [map_one] at h
  rw [h]
  letI := tensorColorZeroSubsingleton D
  letI := tensorRowZeroSubsingleton D
  change (∑ c : TensorColor D 0, (tensorWeight D w 0 c : ℂ) *
    Matrix.trace (1 : Matrix (TensorRow D 0 c) _ ℂ)) = 1
  have hc (c : TensorColor D 0) : Fintype.card (TensorRow D 0 c) = 1 := by
    letI : Unique (TensorRow D 0 c) :=
      ⟨⟨Classical.choice inferInstance⟩, fun _ => Subsingleton.elim _ _⟩
    exact Fintype.card_unique
  letI : Unique (TensorColor D 0) :=
    ⟨⟨Classical.choice inferInstance⟩, fun _ => Subsingleton.elim _ _⟩
  simp [tensorWeight, Matrix.trace_one, hc, Fintype.sum_unique]

theorem stageTrace_norm_le (hw0 : ∀ i c, w i 0 c = 1)
    (hw : ∀ i n, UniversalWeightLaw ((D i).step n) (w i n) (w i (n+1)))
    (hpos : ∀ i n c, 0 ≤ w i n c) (a : Level ι) (x : TensorStage D a) :
    ‖stageTrace D w a x‖ ≤ ‖x‖ := by
  let v := tensorWeight D w a
  have hpos' := tensorWeight_nonneg D w hpos a
  have hone := stageTrace_one D w hw0 hw a
  have hnormalize : ∑ c, v c * (Fintype.card (TensorRow D a c) : ℝ) = 1 := by
    apply Complex.ofReal_injective
    push_cast
    change (∑ c : TensorColor D a, (v c : ℂ) * Matrix.trace
      (1 : Matrix (TensorRow D a c) _ ℂ)) = 1 at hone
    simpa only [Matrix.trace_one] using hone
  change ‖∑ c : TensorColor D a, (v c : ℂ) * (x c).trace‖ ≤ ‖x‖
  calc
    _ ≤ ∑ c, ‖(v c : ℂ) * (x c).trace‖ := norm_sum_le _ _
    _ = ∑ c, v c * ‖(x c).trace‖ := by
      apply Finset.sum_congr rfl
      intro c _
      have hv : 0 ≤ v c := hpos' c
      rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
    _ ≤ ∑ c, v c * ((Fintype.card (TensorRow D a c) : ℝ) * ‖x‖) := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _ (hpos' c)
      exact (TraceWeightRefinement.norm_trace_le (x c)).trans
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm x c) (Nat.cast_nonneg _))
    _ = ‖x‖ := by simp only [← mul_assoc, ← Finset.sum_mul, hnormalize, one_mul]

variable (hw0 : ∀ i c, w i 0 c = 1)
variable (hw : ∀ i n, UniversalWeightLaw ((D i).step n) (w i n) (w i (n+1)))
variable (hpos : ∀ i n c, 0 ≤ w i n c)

def tensorTrace : TensorLimit D →L[ℂ] ℂ :=
  traceOnCompletion (tensorConnecting D) (stageTrace D w) (stageTrace_compat D w hw0 hw)
    (stageTrace_norm_le D w hw0 hw hpos)

theorem tensorTrace_normalized : IsNormalizedTrace (tensorTrace D w hw0 hw hpos) :=
  traceOnCompletion_normalized _ _ _ _ (stageTrace_one D w hw0 hw)
    (fun a => weightedBlockTrace_cyclic (tensorWeight D w a))

@[simp] theorem tensorTrace_embedding (a : Level ι) (x : TensorStage D a) :
    tensorTrace D w hw0 hw hpos (completedEmbedding (tensorConnecting D) a x) = stageTrace D w a x :=
  traceOnCompletion_of _ _ _ _ a x

include hw0 hw hpos in
theorem tensorTrace_excludes (R : Subring ℝ) (hR : ∀ i n c, w i n c ∈ R) :
    commonIdempotentTraceValues (TensorLimit D) ⊆ (fun t : ℝ => (t : ℂ)) '' (R : Set ℝ) := by
  let e := completedEmbedding (tensorConnecting D)
  let S : Set (Subalgebra ℂ (TensorLimit D)) := Set.range fun a => (e a).toAlgHom.range
  have hinj (a : Level ι) : Function.Injective (e a) :=
    (AddMonoidHomClass.isometry_of_norm (e a) (completedEmbedding_norm (tensorConnecting D) a)).injective
  refine commonIdempotentTraceValues_subset_subring S ?_ ?_ _
    (tensorTrace_normalized D w hw0 hw hpos) R ?_
  · rintro _ ⟨a, rfl⟩
    apply FiniteDimensional.of_surjective (e a).toAlgHom.rangeRestrict.toLinearMap
    rintro ⟨z, ⟨x, rfl⟩⟩
    exact ⟨x, rfl⟩
  · apply Completion.denseRange_coe.mono
    rintro _ ⟨z, rfl⟩
    obtain ⟨a, x, rfl⟩ := DirectLimit.exists_eq_mk (tensorConnecting D) z
    exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨⟨a, rfl⟩, ⟨x, rfl⟩⟩⟩
  · rintro _ ⟨a, rfl⟩ p hp
    obtain ⟨x, hx⟩ := p.property
    have hxidem : x * x = x := by
      apply hinj a
      rw [map_mul]
      change e a x = (p : TensorLimit D) at hx
      rw [hx]
      exact congrArg Subtype.val hp
    change ∃ t ∈ R, tensorTrace D w hw0 hw hpos (p : TensorLimit D) = (t : ℂ)
    rw [← hx]
    change ∃ t ∈ R, tensorTrace D w hw0 hw hpos
      (completedEmbedding (tensorConnecting D) a x) = (t : ℂ)
    rw [tensorTrace_embedding]
    exact weightedBlockTrace_idempotent _ R (tensorWeight_mem D w R hR a) x hxidem

end NonCalkinAlgebra.FiniteBlockRefinement.RootedBlockDiagram
