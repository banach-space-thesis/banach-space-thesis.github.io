import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! Every nonzero two-sided ideal of bounded operators contains all rank-one
and finite-rank operators. The finite-rank decomposition uses bounded
coordinates on the actual finite-dimensional range. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem smulRight_mem_twoSidedIdeal_of_ne_bot
    (J : TwoSidedIdeal (X →L[𝕜] X)) (hJ : J ≠ ⊥) (f : X →L[𝕜] 𝕜) (z : X) :
    f.smulRight z ∈ J := by
  classical
  have hex : ∃ T : X →L[𝕜] X, T ∈ J ∧ T ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hJ
    apply le_antisymm _ bot_le
    intro T hT
    simpa only [TwoSidedIdeal.mem_bot] using hn T hT
  obtain ⟨T, hT, hT0⟩ := hex
  have hx : ∃ x : X, T x ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hT0 (ContinuousLinearMap.ext hn)
  obtain ⟨x, hx⟩ := hx
  obtain ⟨g, hg⟩ := SeparatingDual.exists_ne_zero (R := 𝕜) hx
  let ψ : X →L[𝕜] 𝕜 := (g (T x))⁻¹ • g
  have hψ : ψ (T x) = 1 := by simp [ψ, hg]
  have hmem := J.mul_mem_right ((ψ.smulRight z) * T) (f.smulRight x)
    (J.mul_mem_left (ψ.smulRight z) T hT)
  have he : (ψ.smulRight z) * T * (f.smulRight x) = f.smulRight z := by
    ext v
    change ψ (T (f v • x)) • z = f v • z
    rw [map_smul, map_smul, hψ]
    simp only [smul_eq_mul, mul_one]
  rwa [he] at hmem

theorem exists_finite_rank_one_sum (T : X →L[𝕜] X)
    [FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)] :
    ∃ n : ℕ, ∃ f : Fin n → X →L[𝕜] 𝕜, ∃ z : Fin n → X,
      T = ∑ i, (f i).smulRight (z i) := by
  let E := LinearMap.range T.toLinearMap
  let b := Module.finBasis 𝕜 E
  let f (i : Fin (Module.finrank 𝕜 E)) : X →L[𝕜] 𝕜 :=
    (b.coord i).toContinuousLinearMap.comp T.rangeRestrict
  refine ⟨Module.finrank 𝕜 E, f, (fun i => (b i).val), ?_⟩
  ext x
  have h := congrArg Subtype.val (b.sum_repr (T.rangeRestrict x))
  simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    Submodule.coe_sum, Submodule.coe_smul] using h.symm

theorem finiteRank_mem_twoSidedIdeal_of_ne_bot
    (J : TwoSidedIdeal (X →L[𝕜] X)) (hJ : J ≠ ⊥) (T : X →L[𝕜] X)
    [FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)] : T ∈ J := by
  classical
  obtain ⟨n, f, z, rfl⟩ := exists_finite_rank_one_sum T
  exact J.asIdeal.sum_mem (fun i _ => smulRight_mem_twoSidedIdeal_of_ne_bot J hJ (f i) (z i))

end ThesisCommon
