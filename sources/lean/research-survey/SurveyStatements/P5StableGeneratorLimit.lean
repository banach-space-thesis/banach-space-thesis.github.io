import SurveyStatements.P5DenseOperatorLimit
import Mathlib.Topology.Algebra.Module.Basic

/-! Uniformly bounded operators that stabilize on a dense generating set
have a genuine bounded strong limit. The generators need not form a basis. -/

noncomputable section
set_option autoImplicit false
open Filter Set Topology

namespace SurveyStatements.P5

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

theorem exists_operator_of_stable_generators (G : Set X)
    (hG : (Submodule.span 𝕜 G).topologicalClosure = ⊤)
    (P : ℕ → X →L[𝕜] Y) {C : ℝ} (hC : 0 ≤ C) (hP : ∀ n, ‖P n‖ ≤ C)
    (hstable : ∀ x ∈ G, ∃ N, ∀ n ≥ N, P n x = P N x) :
    ∃ A : X →L[𝕜] Y, ‖A‖ ≤ C ∧
      ∀ x, Tendsto (fun n => P n x) atTop (𝓝 (A x)) := by
  let S := Submodule.span 𝕜 G
  have hS : DenseRange S.subtypeL := by
    have hd : Dense (S : Set X) := Submodule.dense_iff_topologicalClosure_eq_top.mpr hG
    have hr : Set.range S.subtypeL = (S : Set X) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    intro x
    rw [hr]
    exact hd x
  have hlim (x : X) (hx : x ∈ S) :
      ∃ y : Y, Tendsto (fun n => P n x) atTop (𝓝 y) := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨N, hN⟩ := hstable x hx
        refine ⟨P N x, tendsto_const_nhds.congr' ?_⟩
        filter_upwards [eventually_ge_atTop N] with n hn
        exact (hN n hn).symm
    | zero =>
        exact ⟨0, by simpa only [map_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Y)) atTop (𝓝 0))⟩
    | add x y _ _ hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by simpa only [map_add] using ha.add hb⟩
    | smul c x _ hx =>
        obtain ⟨a, ha⟩ := hx
        exact ⟨c • a, by simpa only [map_smul] using ha.const_smul c⟩
  exact exists_operator_of_dense_limits S hS P hC hP (fun x => hlim x.val x.property)

end SurveyStatements.P5
