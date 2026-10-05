import ThesisCommon.Analysis.GowersMaureyFiniteFunctionalRestriction
import ThesisCommon.Analysis.GowersMaureyBlockImageTails
import ThesisCommon.Analysis.FiniteOrbitSeparation

/-! A genuine finite tail functional detecting failure of approximation by
a finite absolute-convex orbit. Hahn--Banach is applied on the completion,
then interval restriction preserves all orbit tests exactly and loses at
most twice the actual finite approximation error on the detected vector. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_finite_tail_orbit_witness (D : ConstructionData 𝕜)
    {ι : Type*} [Fintype ι] (v : ι → C00 𝕜) (z : ShiftSpace D) (K : ℕ)
    (hv : ∀ i, v i ∈ afterCutoff K) {m ε δ : ℝ} (hm : 0 < m) (hε : 0 < ε)
    (hhead : ‖initialSum D (K+1) z‖ < δ)
    (hsep : ∀ w ∈ finiteAbsoluteConvexOrbit (𝕜 := 𝕜) (fun i => denseEmbedding D (v i)) m,
      ε ≤ ‖z-w‖) :
    ∃ a : C00 𝕜, a ∈ afterCutoff K ∧ DualUnit (implicitNorm D) a ∧
      ε/2-2*δ < RCLike.re (completedPairing D a z) ∧
      ∀ i, ‖pairing a (v i)‖ ≤ ‖z‖/m := by
  classical
  letI : NormedSpace ℝ (ShiftSpace D) := NormedSpace.restrictScalars ℝ 𝕜 (ShiftSpace D)
  letI : IsScalarTower ℝ 𝕜 (ShiftSpace D) := RestrictScalars.isScalarTower ℝ 𝕜 (ShiftSpace D)
  obtain ⟨φ,hφ,hφz,hφv⟩ := exists_unit_functional_separating_finite_orbit
    (fun i => denseEmbedding D (v i)) z hm hε hsep
  obtain ⟨y,hy,hyz⟩ := exists_finite_after_approx_of_initialSum_small D z K hhead
  let B := max (y.support.sup id) (Finset.univ.sup (fun i : ι => (v i).support.sup id))
  let E : Interval := ⟨K+1,B⟩
  have hys : y.support ⊆ E.set := by
    intro j hj
    have hjK : K < j := by
      by_contra hn
      exact Finsupp.mem_support_iff.mp hj (hy j (by omega))
    exact Finset.mem_Icc.mpr ⟨by change K+1 ≤ j; omega,
      (Finset.le_sup (f := id) hj).trans (le_max_left _ _)⟩
  have hvs (i : ι) : (v i).support ⊆ E.set := by
    intro j hj
    have hjK : K < j := by
      by_contra hn
      exact Finsupp.mem_support_iff.mp hj (hv i j (by omega))
    have hup := (Finset.le_sup (f := id) hj).trans
      (Finset.le_sup (f := fun i : ι => (v i).support.sup id) (Finset.mem_univ i))
    exact Finset.mem_Icc.mpr ⟨by change K+1 ≤ j; omega,hup.trans (le_max_right _ _)⟩
  let a := finiteFunctionalRestriction D E φ
  have hau : DualUnit (implicitNorm D) a := finiteFunctionalRestriction_dualUnit D E φ hφ.le
  have haK : a ∈ afterCutoff K := by
    intro j hj
    apply Finsupp.notMem_support_iff.mp
    intro hja
    have hh := (Finset.mem_Icc.mp (finiteFunctionalRestriction_support D E φ hja)).1
    change K+1 ≤ j at hh
    omega
  have herr : ‖completedPairing D a z - φ z‖ < 2*δ :=
    (finiteFunctionalRestriction_error D E φ hφ.le z hys).trans_lt (by linarith)
  have hre := RCLike.re_le_norm (φ z - completedPairing D a z)
  rw [map_sub, norm_sub_rev] at hre
  refine ⟨a,haK,hau,by linarith,?_⟩
  intro i
  rw [show pairing a (v i) = φ (denseEmbedding D (v i)) from
    finiteFunctionalRestriction_pairing D E φ (hvs i)]
  exact hφv i

end ThesisCommon.GowersMaurey
