import Posets.SzlenkOperator
import ThesisCommon.Analysis.ContinuousMapEvaluationDistance
import ThesisCommon.Analysis.OrdinalDerived

/-! Point evaluations turn Cantor--Bendixson derivatives into genuine
Szlenk derivatives. All norm distances below are strong-dual distances. -/

noncomputable section
open Set Topology ThesisCommon
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜]
    [TopologicalSpace K] [CompactSpace K] [T2Space K]

def weakStarDirac (x : K) : WeakDual 𝕜 C(K, 𝕜) :=
  StrongDual.toWeakDual (ContinuousMap.evalCLM (M := 𝕜) 𝕜 x)

theorem weakStarDirac_continuous : Continuous (weakStarDirac (𝕜 := 𝕜) (K := K)) :=
  WeakDual.continuous_of_continuous_eval (fun f => f.continuous)

theorem weakStarDirac_mem_unitBall (x : K) :
    weakStarDirac (𝕜 := 𝕜) x ∈ weakStarUnitBall 𝕜 C(K, 𝕜) := by
  change ContinuousMap.evalCLM (M := 𝕜) 𝕜 x ∈ Metric.closedBall 0 1
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    norm_continuousMap_evalCLM_le (𝕜 := 𝕜) x

theorem weakStarDirac_norm_sub {x y : K} (hxy : x ≠ y) :
    ‖WeakDual.toStrongDual (weakStarDirac (𝕜 := 𝕜) x) -
      WeakDual.toStrongDual (weakStarDirac (𝕜 := 𝕜) y)‖ = 2 :=
  norm_continuousMap_eval_sub x y hxy

theorem weakStarDirac_ordinalDerived {A : Set K} (hA : IsClosed A)
    {ε : ℝ} (hε : ε < 2) (α : Ordinal) :
    ∀ x ∈ ordinalDerived A α,
      weakStarDirac (𝕜 := 𝕜) x ∈ szlenkIterate ε (weakStarDirac '' A) α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro x hx
      rw [ordinalDerived_zero] at hx
      simpa only [szlenkIterate_zero] using
        (show weakStarDirac (𝕜 := 𝕜) x ∈ weakStarDirac '' A from ⟨x, hx, rfl⟩)
  | succ α ih =>
      intro x hx
      rw [ordinalDerived_succ] at hx
      rw [szlenkIterate_succ]
      have hxA : x ∈ ordinalDerived A α :=
        (isClosed_iff_derivedSet_subset _).mp (isClosed_ordinalDerived hA α) hx
      refine ⟨ih x hxA, ?_⟩
      intro U hU hxU
      have hpre : weakStarDirac (𝕜 := 𝕜) ⁻¹' U ∈ 𝓝 x :=
        (hU.preimage weakStarDirac_continuous).mem_nhds hxU
      obtain ⟨y, ⟨hyU, hyA⟩, hyx⟩ := (accPt_iff_nhds.mp hx) _ hpre
      refine ⟨weakStarDirac y, ⟨ih y hyA, hyU⟩,
        weakStarDirac x, ⟨ih x hxA, hxU⟩, ?_⟩
      rwa [weakStarDirac_norm_sub hyx]
  | limit α hα ih =>
      intro x hx
      rw [ordinalDerived_limit A hα] at hx
      rw [szlenkIterate_limit ε _ α hα]
      exact mem_iInter.mpr (fun β => ih β.val β.property x (mem_iInter₂.mp hx β.val β.property))

theorem weakStarDirac_mem_szlenkIterate_unitBall {α : Ordinal} {ε : ℝ} (hε : ε < 2)
    {x : K} (hx : x ∈ ordinalDerived (univ : Set K) α) :
    weakStarDirac (𝕜 := 𝕜) x ∈ szlenkIterate ε (weakStarUnitBall 𝕜 C(K, 𝕜)) α := by
  have hsub : weakStarDirac (𝕜 := 𝕜) '' (univ : Set K) ⊆ weakStarUnitBall 𝕜 C(K, 𝕜) := by
    rintro _ ⟨y, _, rfl⟩
    exact weakStarDirac_mem_unitBall y
  exact szlenkIterate_mono ε α hsub (weakStarDirac_ordinalDerived isClosed_univ hε α x hx)

theorem not_operatorSzlenkBound_id_of_ordinalDerived_nonempty {α : Ordinal}
    (hα : (ordinalDerived (univ : Set K) α).Nonempty) :
    ¬ OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 C(K, 𝕜)) α := by
  intro h
  obtain ⟨x, hx⟩ := hα
  have hd := weakStarDirac_mem_szlenkIterate_unitBall (𝕜 := 𝕜) (show (1 : ℝ) < 2 by norm_num) hx
  have he := h 1 zero_lt_one
  rw [adjointUnitBall_id] at he
  rw [he] at hd
  exact hd

end Posets
