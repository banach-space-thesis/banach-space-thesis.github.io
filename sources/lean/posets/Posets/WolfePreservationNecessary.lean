import Posets.WolfePreservationBlockJointPhaseQuantileCore
import Posets.WolfePreservationNecessaryFiniteRelations
import Posets.WolfePreservationMultiplierTransport

/-! Necessary Wolfe bounds for an actual identity factorization through an
operator on an ordinal C-space. The scale is chosen before the requested
rank. Fixed-phase quantiles reduce the support selection to finitely many
closed single-valued graphs, and compact multiplier transport returns the
result to the actual adjoint unit ball of the original operator. -/

noncomputable section
open Set Topology ThesisCommon
universe u v
namespace Posets
variable {𝕜 L X : Type*} [RCLike 𝕜] [LinearOrder L] [MetricSpace L]
  [CompactSpace L] [Countable L] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

local instance wolfeNecessaryFinalDualGroup (κ : Ordinal.{v}) :
    NormedAddCommGroup (JLMS.CZero 𝕜 (OrdinalInterval κ) →L[𝕜] 𝕜) := inferInstance
local instance wolfeNecessaryFinalDualSpace (κ : Ordinal.{v}) :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 (OrdinalInterval κ) →L[𝕜] 𝕜) := inferInstance

theorem wolfe_ordinal_factorization_necessary_omega_sq_of_scale
    {κ : Ordinal.{v}} (M : JLMS.AtomicDualModel 𝕜 (OrdinalInterval κ))
    (N : JLMS.AtomicDualModel 𝕜 L) (P : JLMS.AtomicDualModel 𝕜 (OrdinalInterval κ × L))
    (hKL : JLMS.IsScattered (OrdinalInterval κ × L))
    (hcut : ∀ a : L, IsClopen (Iic a))
    (T : JLMS.CZero 𝕜 (OrdinalInterval κ) →L[𝕜] X)
    (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 (OrdinalInterval κ))
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (hc : c ≠ 0) (hn : ‖c‖ * ‖R‖ ≤ 1)
    {A : Set L} (hA : IsClosed A)
    (hrank : (ordinalDerived A ((Ordinal.omega0 : Ordinal.{u}) ^ (2 : Ordinal))).Nonempty) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ β : Ordinal.{u}, β < Ordinal.omega0 ^ (2 : Ordinal) →
      (wolfeFamily M ε (adjointUnitBall T) β).Nonempty := by
  classical
  obtain ⟨p, s, hs, η, hη, hηcard, hcores⟩ :=
    wolfeFactorization_phase_quantile_cores_below_omega_sq M N P hKL hcut T R S hfactor c hc hn hA hrank
  letI : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  have hscard : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  let εσ : ℝ := ‖c‖ / 4 / (s.card : ℝ) - η
  have hεσ : 0 < εσ := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ hscard).mpr
    have hnorm := norm_pos_iff.mpr hc
    nlinarith
  have hC : 0 < ‖S‖ + 1 := by positivity
  refine ⟨εσ / (‖S‖ + 1), div_pos hεσ hC, ?_⟩
  intro β hβ
  have hβc : β.card ≤ Cardinal.aleph0 := by
    apply (Ordinal.card_le_card hβ.le).trans
    rw [show (2 : Ordinal.{u}) = ((2 : ℕ) : Ordinal.{u}) from rfl, Ordinal.opow_natCast,
      pow_two, Ordinal.card_mul, Ordinal.card_omega0]
    simp
  obtain ⟨B, hB, _, hrB, f, hf, hrows⟩ := hcores β hβ
  let σ := fun x : L => wolfeJointPhaseMeasure S f (wolfeFactorizationLift T R c x)
  let Q : s → Set (OrdinalInterval κ × L) := fun t =>
    wolfePhaseQuantileRelation N S f p.relative p.floor hcut t.val p.gap
  have hσ : Continuous σ := (wolfeJointPhaseMeasure_continuous S f).comp
    (wolfeFactorizationLift_continuous T R c)
  have hpositive : 0 < ‖c‖ / 4 / (Fintype.card s : ℝ) - η := by
    simpa only [Fintype.card_coe] using hεσ
  have hW := wolfe_ordinal_finite_relations_nonempty M Q
    (fun t => wolfePhaseQuantileRelation_isClosed N S f p.relative p.floor_pos hcut t.val p.gap)
    (fun t => wolfePhaseQuantileRelation_single N S f p.relative p.floor hcut t.val p.gap_pos)
    σ hσ hB (fun x hx => (hrows x hx).1) (fun x hx => (hrows x hx).2)
    hpositive hβc hrB
  have hW' : (wolfeFamily M εσ (σ '' B) β).Nonempty := by
    simpa only [Fintype.card_coe] using hW
  have hnorm : ‖wolfeJointPhaseTotal S f‖ ≤ ‖S‖ + 1 := by
    have h1 := wolfeJointCZeroOperator_bound S f
    have h2 := mul_le_mul_of_nonneg_left hf (norm_nonneg S)
    change ‖wolfeJointCZeroOperator S f‖ ≤ ‖S‖ + 1
    linarith
  have horiginal := wolfe_closed_multiplier_transport_nonempty M
    (wolfeFactorizationLift T R c) (wolfeFactorizationLift_continuous T R c)
    (wolfeJointPhaseTotal S f) hC hnorm hB εσ β hW'
  obtain ⟨z, hz⟩ := horiginal
  refine ⟨z, wolfeFamily_mono M le_rfl ?_ β hz⟩
  rintro ν ⟨x, _, rfl⟩
  exact wolfeFactorizationLift_mem_adjointUnitBall T R c hn x

theorem wolfe_ordinal_factorization_necessary_omega_sq
    {κ : Ordinal.{v}} (M : JLMS.AtomicDualModel 𝕜 (OrdinalInterval κ))
    (N : JLMS.AtomicDualModel 𝕜 L) (P : JLMS.AtomicDualModel 𝕜 (OrdinalInterval κ × L))
    (hKL : JLMS.IsScattered (OrdinalInterval κ × L))
    (hcut : ∀ a : L, IsClopen (Iic a))
    (T : JLMS.CZero 𝕜 (OrdinalInterval κ) →L[𝕜] X)
    (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 (OrdinalInterval κ))
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    {A : Set L} (hA : IsClosed A)
    (hrank : (ordinalDerived A ((Ordinal.omega0 : Ordinal.{u}) ^ (2 : Ordinal))).Nonempty) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ β : Ordinal.{u}, β < Ordinal.omega0 ^ (2 : Ordinal) →
      (wolfeFamily M ε (adjointUnitBall T) β).Nonempty := by
  obtain ⟨c, hc, hn⟩ := exists_wolfeFactorizationLift_scale R
  exact wolfe_ordinal_factorization_necessary_omega_sq_of_scale M N P hKL hcut T R S hfactor
    c hc hn hA hrank

end Posets
