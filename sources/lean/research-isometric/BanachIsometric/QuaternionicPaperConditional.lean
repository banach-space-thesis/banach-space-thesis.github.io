import BanachIsometric.QuaternionicSeminormSimilarityTorsion
import BanachIsometric.QuaternionicCorollariesTorsion
import BanachIsometric.SeminormFamilyNormTopology

/-! The original separating-family assertion D, including the generated norm
topology and complete Hilbert conclusion, for the original right quaternionic
action. The same displayed actual compact-body topology premise suffices for
A, B, C, D and E; it is still a hypothesis, not a claimed theorem. -/

namespace BanachIsometric.Quaternionic

open Set Metric MeasureTheory
open scoped Topology Topology.Homotopy NNReal

noncomputable section

variable (hTorsion : ∀ (m : ℕ) (S : Set (EuclideanSpace ℝ (Fin m))),
  IsCompact S → closure (interior S) = S → (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S →
  ∀ k : ℕ, Even (k + 2) →
  ∀ α : HomotopyGroup (Fin (k + 2))
    (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1, IsOfFinOrder α)

include hTorsion

variable {ι X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]

theorem separating_rightSeminorm_family_collapse_of_body_even_homotopy_torsion
    (p : ι → RightSeminorm X) {n : ℕ} (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X)
    (hseparating : ∀ x : X, x ≠ 0 → ∃ i, p i x ≠ 0)
    (hsim : ∀ E F : Submodule Hᵐᵒᵖ X,
      Module.finrank Hᵐᵒᵖ E = n → Module.finrank Hᵐᵒᵖ F = n →
      ∃ T : E ≃ₗ[Hᵐᵒᵖ] F, ∀ i, ∃ c : ℝ, 0 < c ∧ ∀ x : E, p i (T x : X) = c * p i (x : X)) :
    ∃ i₀ : ι, HasHermitianSquare (p i₀ : X → ℝ) ∧
      ∀ i, (∀ x, p i x = 0) ∨ ∃ a : ℝ, 0 < a ∧ ∀ x, p i x = a * p i₀ x := by
  obtain ⟨x₀, hx₀⟩ := rank_pos_iff_exists_ne_zero.mp ((zero_le (n : Cardinal)).trans_lt hdim)
  obtain ⟨i₀, hi₀⟩ := hseparating x₀ hx₀
  obtain ⟨hp₀, hcollapse⟩ := rightSeminorm_family_collapse_of_body_even_homotopy_torsion
    hTorsion p hn hdim i₀ ⟨x₀, hi₀⟩ hsim
  exact ⟨i₀, hp₀, hcollapse⟩

variable [UniformSpace X] [IsUniformAddGroup X]

theorem separating_rightSeminorm_family_normable_of_body_even_homotopy_torsion
    (p : ι → RightSeminorm X) (hp : WithSeminorms (fun i => (p i).toRealSeminorm))
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X)
    (hseparating : ∀ x : X, x ≠ 0 → ∃ i, p i x ≠ 0)
    (hsim : ∀ E F : Submodule Hᵐᵒᵖ X,
      Module.finrank Hᵐᵒᵖ E = n → Module.finrank Hᵐᵒᵖ F = n →
      ∃ T : E ≃ₗ[Hᵐᵒᵖ] F, ∀ i, ∃ c : ℝ, 0 < c ∧ ∀ x : E, p i (T x : X) = c * p i (x : X)) :
    ∃ i₀ : ι, ∃ hdef : ∀ x : X, p i₀ x = 0 ↔ x = 0,
      HasHermitianSquare (p i₀ : X → ℝ) ∧
      HasHermitianSquare (norm : MetricGeometry.DefiniteSeminormModel (p i₀).oppositeSeminorm hdef → ℝ) ∧
      (∀ i, (∀ x, p i x = 0) ∨ ∃ a : ℝ, 0 < a ∧ ∀ x, p i x = a * p i₀ x) ∧
      (∃ e : X ≃L[Hᵐᵒᵖ] MetricGeometry.DefiniteSeminormModel (p i₀).oppositeSeminorm hdef,
        ∀ x, ‖e x‖ = p i₀ x) ∧
      (CompleteSpace X → CompleteSpace (MetricGeometry.DefiniteSeminormModel (p i₀).oppositeSeminorm hdef)) := by
  obtain ⟨i₀, hp₀, hcollapse⟩ := separating_rightSeminorm_family_collapse_of_body_even_homotopy_torsion
    hTorsion p hn hdim hseparating hsim
  have hdef : ∀ x : X, p i₀ x = 0 ↔ x = 0 := by
    obtain ⟨h, hdiag, hpos⟩ := hp₀
    intro x
    constructor
    · intro hz
      by_contra hx
      have hh := hpos x hx
      rw [hdiag] at hh
      change 0 < p i₀ x ^ 2 at hh
      rw [hz] at hh
      norm_num at hh
    · rintro rfl
      exact map_zero (p i₀).toRealSeminorm
  let M := MetricGeometry.DefiniteSeminormModel (p i₀).oppositeSeminorm hdef
  let e : X ≃ₗ[Hᵐᵒᵖ] M := MetricGeometry.toDefiniteSeminormModel (p i₀).oppositeSeminorm hdef
  have hnorm : ∀ x : X, ‖e x‖ = (p i₀).toRealSeminorm x := fun _ => rfl
  have hpM : HasHermitianSquare (norm : M → ℝ) := hp₀.pullback_injective e.symm.toLinearMap e.symm.injective
  refine ⟨i₀, hdef, hp₀, hpM, hcollapse, ?_, ?_⟩
  · exact ⟨seminormFamilyNormContinuousLinearEquiv (fun i => (p i).toRealSeminorm) hp i₀ e hnorm hcollapse, hnorm⟩
  · intro hcomplete
    letI : CompleteSpace X := hcomplete
    exact completeSpace_normModel_of_seminorm_family_collapse
      (fun i => (p i).toRealSeminorm) hp i₀ e hnorm hcollapse

end
end BanachIsometric.Quaternionic

