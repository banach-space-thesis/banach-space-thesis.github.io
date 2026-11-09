import NonCalkinAlgebra.FiniteBlockRefinement
import NonCalkinAlgebra.TraceFiniteMatrices
import NonCalkinAlgebra.TraceLocalIdempotents

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement
open Matrix
universe u

section BlockTrace
variable {C : Type u} [Fintype C] {P : C → Type u}
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]

/-- The coefficient at a summand is the trace of a rank-one idempotent in that summand. -/
def weightedBlockTrace (w : C → ℝ) : Blocks P →ₗ[ℂ] ℂ where
  toFun x := ∑ c, (w c : ℂ) * Matrix.trace (x c)
  map_add' x y := by simp [Matrix.trace_add, mul_add, Finset.sum_add_distrib]
  map_smul' z x := by
    simp only [RingHom.id_apply, Pi.smul_apply, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring

theorem weightedBlockTrace_one (w : C → ℝ)
    (h : ∑ c, w c * (Fintype.card (P c) : ℝ) = 1) :
    weightedBlockTrace (P := P) w 1 = 1 := by
  change (∑ c, (w c : ℂ) * Matrix.trace (1 : Matrix (P c) (P c) ℂ)) = _
  simp only [Matrix.trace_one]
  exact_mod_cast h

theorem weightedBlockTrace_cyclic (w : C → ℝ) (x y : Blocks P) :
    weightedBlockTrace w (x * y) = weightedBlockTrace w (y * x) := by
  change (∑ c, (w c : ℂ) * Matrix.trace (x c * y c)) =
    ∑ c, (w c : ℂ) * Matrix.trace (y c * x c)
  apply Finset.sum_congr rfl
  intro c _
  rw [Matrix.trace_mul_comm (x c) (y c)]

theorem weightedBlockTrace_idempotent (w : C → ℝ) (T : Subring ℝ)
    (hw : ∀ c, w c ∈ T) (p : Blocks P) (hp : p * p = p) :
    ∃ t ∈ T, weightedBlockTrace w p = (t : ℂ) := by
  have h (c : C) : ∃ n : ℕ, (p c).trace = n :=
    TraceFiniteMatrices.trace_idempotent (p c) (congrFun hp c)
  choose n hn using h
  refine ⟨∑ c, w c * (n c : ℝ), T.sum_mem (fun c _ => T.mul_mem (hw c) (natCast_mem T _)), ?_⟩
  change (∑ c, (w c : ℂ) * (p c).trace) = _
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, hn]

end BlockTrace

end NonCalkinAlgebra.FiniteBlockRefinement

namespace NonCalkinAlgebra
universe w
variable {A : Type w} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Exact trace-value exclusion survives passage to the norm closure of the local stages. -/
theorem commonIdempotentTraceValues_subset_subring
    (S : Set (Subalgebra ℂ A)) (hfinite : ∀ B ∈ S, FiniteDimensional ℂ B)
    (hdense : Dense (⋃ B ∈ S, (B : Set A)))
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTrace τ) (T : Subring ℝ)
    (hlocal : ∀ B ∈ S, ∀ p : B, p * p = p → ∃ t ∈ T, τ p = (t : ℂ)) :
    commonIdempotentTraceValues A ⊆ (fun t : ℝ => (t : ℂ)) '' (T : Set ℝ) := by
  rintro z ⟨e, he, hz⟩
  obtain ⟨B, hBS, p, hp, htrace⟩ :=
    exists_local_idempotent_trace_value S hfinite hdense hτ e he
  obtain ⟨t, ht, hvalue⟩ := hlocal B hBS p hp
  exact ⟨t, ht, hvalue.symm.trans (htrace.trans (hz τ hτ))⟩

end NonCalkinAlgebra
