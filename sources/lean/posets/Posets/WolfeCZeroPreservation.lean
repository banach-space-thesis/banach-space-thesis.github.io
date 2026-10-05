import Posets.WolfeNorming
import Posets.WolfeFamilies
import Posets.SzlenkOperator
import JLMS.ScatteredCZeroFactorization

/-! Genuine c₀ preservation from the first Wolfe level. Disjoint positive-mass
children supply supported continuous norming functions; the proved disjoint
function factorisation then supplies a complemented copy in the range. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
variable {𝕜 K X : Type*} [RCLike 𝕜] [TopologicalSpace K]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem norm_apply_le_of_mem_adjointUnitBall (T : JLMS.CZero 𝕜 K →L[𝕜] X)
    {μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)} (hμ : μ ∈ adjointUnitBall T)
    (f : JLMS.CZero 𝕜 K) : ‖μ f‖ ≤ ‖T f‖ := by
  obtain ⟨φ, hφ, rfl⟩ := hμ
  have hn : ‖WeakDual.toStrongDual φ‖ ≤ 1 := by
    simpa only [weakStarUnitBall, mem_preimage, Metric.mem_closedBall, dist_zero_right] using hφ
  exact ((WeakDual.toStrongDual φ).le_opNorm (T f)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (norm_nonneg (T f)))

variable [LocallyCompactSpace K] [T2Space K]

theorem wolfe_disjointFunctions_of_children (M : JLMS.AtomicDualModel 𝕜 K)
    (hK : JLMS.IsScattered K) (T : JLMS.CZero 𝕜 K →L[𝕜] X)
    {ε δ : ℝ} (hδε : δ < ε) (c : ℕ → WolfeNode 𝕜 K)
    (hc : ∀ n, c n ∈ wolfeBase M ε (adjointUnitBall T))
    (hd : Pairwise (fun i j => Disjoint (c i).2 (c j).2)) :
    JLMS.UniformDisjointFunctionWitnesses T δ := by
  classical
  let γ := (δ + ε) / 2
  have hδγ : δ < γ := by dsimp [γ]; linarith
  have hγε : γ < ε := by dsimp [γ]; linarith
  have hfn (n : ℕ) : ∃ f : JLMS.CZero 𝕜 K,
      ‖f‖ ≤ 1 ∧ Function.support f ⊆ (c n).2 ∧ γ < ‖(c n).1 f‖ :=
    exists_supported_wolfe_norming_function M hK (c n).1 (hc n).2.1
      (hγε.trans_le (hc n).2.2)
  choose f hn hf hlarge using hfn
  refine ⟨γ, hδγ, f, hn, ?_, ?_⟩
  · intro i j hij
    exact (hd hij).mono (hf i) (hf j)
  · intro n
    exact (hlarge n).trans_le (norm_apply_le_of_mem_adjointUnitBall T (hc n).1 (f n))

theorem wolfe_disjointFunctions_of_successor (M : JLMS.AtomicDualModel 𝕜 K)
    (hK : JLMS.IsScattered K) (T : JLMS.CZero 𝕜 K →L[𝕜] X)
    {ε δ : ℝ} (hδε : δ < ε) (α : Ordinal.{u})
    (h : (wolfeFamily M ε (adjointUnitBall T) (succ α)).Nonempty) :
    JLMS.UniformDisjointFunctionWitnesses T δ := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨_, c, hc, hch⟩ := (mem_wolfeFamily_succ M ε (adjointUnitBall T) α p).mp hp
  exact wolfe_disjointFunctions_of_children M hK T hδε c
    (fun n => wolfeFamily_subset_base M ε (adjointUnitBall T) α (hc n)) hch.2.1

variable {L : Type*} [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L]

/-- A nonempty successor Wolfe level gives an actual quantitative c₀ identity
factorisation, for every positive threshold strictly below the mass scale. -/
theorem wolfe_cZero_factorization (M : JLMS.AtomicDualModel 𝕜 K)
    (hK : JLMS.IsScattered K) (hL : JLMS.IsScattered L)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 L)
    {ε δ : ℝ} (hδ : 0 < δ) (hδε : δ < ε) (α : Ordinal.{u})
    (h : (wolfeFamily M ε (adjointUnitBall T) (succ α)).Nonempty) :
    ∃ U : JLMS.CZero 𝕜 L →L[𝕜] JLMS.cZero 𝕜,
    ∃ V : JLMS.cZero 𝕜 →L[𝕜] JLMS.CZero 𝕜 K,
      (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (JLMS.cZero 𝕜) ∧
        ‖U‖ * ‖V‖ < 1 / δ :=
  JLMS.factorizationFromDisjointFunctions_scatteredCZero hL T δ hδ
    (wolfe_disjointFunctions_of_successor M hK T hδε α h)

end Posets
