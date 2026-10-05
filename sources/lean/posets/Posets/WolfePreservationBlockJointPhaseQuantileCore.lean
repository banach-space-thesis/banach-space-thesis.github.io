import Posets.WolfePreservationBlockJointPhaseParameters
import Posets.WolfePreservationNecessaryPhaseQuantiles

/-! Uniform quantile graphs and phase error are fixed before the ordinal
rank. Every rank below ω² then has a closed core carrying the same positive
lower mass on their union, for a continuous nearly-positive row family. -/

noncomputable section
open Set Topology ThesisCommon
universe u
namespace Posets
variable {𝕜 K L X : Type*} [RCLike 𝕜] [TopologicalSpace K] [LinearOrder L]
  [TopologicalSpace L] [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem wolfeFactorization_phase_quantile_cores_below_omega_sq
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (P : JLMS.AtomicDualModel 𝕜 (K × L)) (hKL : JLMS.IsScattered (K × L))
    (hcut : ∀ a : L, IsClopen (Iic a))
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (hc : c ≠ 0) (hn : ‖c‖ * ‖R‖ ≤ 1)
    {A : Set L} (hA : IsClosed A)
    (hrank : (ordinalDerived A ((Ordinal.omega0 : Ordinal.{u}) ^ (2 : Ordinal))).Nonempty) :
    ∃ p : WolfePhaseParameters ‖c‖ ‖T‖ (‖T‖ * ‖S‖),
      ∃ s : Finset ℝ, s.Nonempty ∧ ∃ η : ℝ, 0 < η ∧
        ((s.card : ℝ) + 1) * η ≤ ‖c‖ / 64 ∧
        ∀ β : Ordinal.{u}, β < Ordinal.omega0 ^ (2 : Ordinal) →
          ∃ B : Set L, IsClosed B ∧ B ⊆ A ∧ (ordinalDerived B β).Nonempty ∧
            ∃ f : JLMS.CZero 𝕜 (K × L), ‖f‖ ≤ 1 ∧ ∀ x ∈ B,
              (‖WeakDual.toStrongDual (wolfeJointPhaseMeasure S f (wolfeFactorizationLift T R c x))‖ -
                RCLike.re (wolfeJointPhaseMeasure S f (wolfeFactorizationLift T R c x)
                  (wolfeSourceBlock univ isClopen_univ)) ≤ η) ∧
              ‖c‖ / 4 ≤ wolfeMass M (wolfeJointPhaseMeasure S f (wolfeFactorizationLift T R c x))
                (⋃ t : s, {y | (y, x) ∈
                  wolfePhaseQuantileRelation N S f p.relative p.floor hcut t.val p.gap}) := by
  classical
  obtain ⟨p⟩ := wolfePhaseParameters_exists (norm_pos_iff.mpr hc)
    (norm_nonneg T) (mul_nonneg (norm_nonneg T) (norm_nonneg S))
  obtain ⟨s, hs, hgrid⟩ := wolfe_exists_finite_quantile_grid
    (show 0 ≤ 1 + p.relative by linarith [p.relative_pos]) p.quantile_gap
  obtain ⟨η, hη, hηbudget, hηcard⟩ := p.exists_error (norm_pos_iff.mpr hc) s.card
  refine ⟨p, s, hs, η, hη, hηcard, ?_⟩
  intro β hβ
  obtain ⟨B, hB, hBA, hrB, f, hf, hdef⟩ :=
    wolfeFactorizationJoint_fixed_phase_core_below_omega_sq P hKL T R S hfactor c hc hn
      hA hrank hη hβ
  refine ⟨B, hB, hBA, hrB, f, hf, ?_⟩
  intro x hx
  refine ⟨(wolfeJointPhaseMeasure_defect_le M N P S f hf _).trans (hdef x hx).2.le, ?_⟩
  apply wolfeFactorizationJoint_phase_section_lower M N P T R S hfactor c hn f hf
    p.relative_pos p.relative_le_one p.floor_pos.le p.atom_pos.le
    hηbudget p.floor_budget p.atom_budget x (hdef x hx).2.le
  intro y hy ha
  exact wolfePhaseQuantileRelation_covers_large_atoms N S f p.floor_pos hcut s hgrid y hy x ha

end Posets
