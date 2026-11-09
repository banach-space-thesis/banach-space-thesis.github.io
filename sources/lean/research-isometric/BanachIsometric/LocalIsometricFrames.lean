import BanachIsometric.LocalCovarianceFactor
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Lipschitz orthonormal frames for a family of orthogonal projections

For projections `proj(a)` of fixed rank and an isometric reference frame `R`, the
Gram operator is `R* proj(a) R`. Its local whitening factor corrects `proj(a) R` to
an isometric frame. Rank equality proves that the frame fills the entire
projected subspace. This is the moving-frame step of Proposition 4.2.
-/

namespace BanachIsometric

open Set Filter
open scoped Topology NNReal

noncomputable section

section BoundedComposition

variable {P E F G : Type*} [PseudoMetricSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem lipschitzOnWith_clm_comp {U : Set P}
    {A : P → F →L[ℝ] G} {B : P → E →L[ℝ] F} {KA KB MA MB : ℝ≥0}
    (hA : LipschitzOnWith KA A U) (hB : LipschitzOnWith KB B U)
    (hMA : ∀ a ∈ U, ‖A a‖ ≤ MA) (hMB : ∀ a ∈ U, ‖B a‖ ≤ MB) :
    LipschitzOnWith (MA * KB + KA * MB) (fun a ↦ (A a).comp (B a)) U := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  rw [dist_eq_norm]
  have hdec : (A a).comp (B a) - (A b).comp (B b) =
      (A a).comp (B a - B b) + (A a - A b).comp (B b) := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  have hAd : ‖A a - A b‖ ≤ KA * dist a b := by
    simpa only [dist_eq_norm] using hA.dist_le_mul a ha b hb
  have hBd : ‖B a - B b‖ ≤ KB * dist a b := by
    simpa only [dist_eq_norm] using hB.dist_le_mul a ha b hb
  calc
    ‖(A a).comp (B a) - (A b).comp (B b)‖ ≤
        ‖A a‖ * ‖B a - B b‖ + ‖A a - A b‖ * ‖B b‖ := by
      rw [hdec]
      exact (norm_add_le _ _).trans (add_le_add
        (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _))
    _ ≤ (MA : ℝ) * (KB * dist a b) + (KA * dist a b) * MB :=
      add_le_add (mul_le_mul (hMA a ha) hBd (norm_nonneg _) MA.coe_nonneg)
        (mul_le_mul hAd (hMB b hb) (norm_nonneg _) (mul_nonneg KA.coe_nonneg dist_nonneg))
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul]; ring

end BoundedComposition

section OrthogonalProjectionFrames

variable {P E F : Type*} [PseudoMetricSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Genuine locally Lipschitz isometric frames spanning the exact ranges of
a fixed-rank family of orthogonal projections. The reference frame and all
projections act on the original real inner-product spaces. -/
theorem exists_lipschitz_isometric_projection_frames
    (proj : P → F →L[ℝ] F) {L : ℝ≥0} (hprojLip : LipschitzWith L proj)
    (hprojself : ∀ a, IsSelfAdjoint (proj a)) (hprojsq : ∀ a, (proj a).comp (proj a) = proj a)
    (a₀ : P) (R : E →ₗᵢ[ℝ] F)
    (hRrange : LinearMap.range R.toLinearMap = LinearMap.range (proj a₀).toLinearMap)
    (hrank : ∀ a, Module.finrank ℝ (LinearMap.range (proj a).toLinearMap) =
      Module.finrank ℝ E) :
    ∃ J : P → E →L[ℝ] F, ∃ U : Set P, ∃ K : ℝ≥0,
      IsOpen U ∧ a₀ ∈ U ∧ J a₀ = R.toContinuousLinearMap ∧ LipschitzOnWith K J U ∧
      (∀ a ∈ U, (J a).adjoint.comp (J a) = ContinuousLinearMap.id ℝ E ∧
        LinearMap.range (J a).toLinearMap = LinearMap.range (proj a).toLinearMap) := by
  let R' := R.toContinuousLinearMap
  have hprojR : (proj a₀).comp R' = R' := by
    ext x
    have hx : R x ∈ LinearMap.range (proj a₀).toLinearMap := by
      rw [← hRrange]
      exact LinearMap.mem_range_self R.toLinearMap x
    obtain ⟨y, hy⟩ := hx
    change proj a₀ (R x) = R x
    rw [← hy]
    exact congrArg (fun A : F →L[ℝ] F ↦ A y) (hprojsq a₀)
  let A : P → E →L[ℝ] F := fun a ↦ (proj a).comp R'
  let C : P → E →L[ℝ] E := fun a ↦ R'.adjoint.comp (A a)
  let AR := (ContinuousLinearMap.compL ℝ E F F).flip R'
  let CR := (ContinuousLinearMap.compL ℝ E F E) R'.adjoint
  have hALip : LipschitzWith (‖AR‖₊ * L) A := AR.lipschitz.comp hprojLip
  have hCLip : LipschitzWith (‖CR‖₊ * (‖AR‖₊ * L)) C := CR.lipschitz.comp hALip
  have hA0 : A a₀ = R' := hprojR
  have hC0 : C a₀ = 1 := by
    change R'.adjoint.comp (A a₀) = 1
    rw [hA0]
    exact R'.norm_map_iff_adjoint_comp_self.mp R.norm_map
  have hCself : ∀ a, IsSelfAdjoint (C a) := fun a ↦ (hprojself a).adjoint_conj R'
  obtain ⟨Q, V, KQ, hV, h1V, hQ1, hQLip, _, hQwhite⟩ :=
    exists_lipschitz_local_covarianceWhitening (A := E →L[ℝ] E)
  let B : P → E →L[ℝ] E := fun a ↦ Q (C a)
  have hB0 : B a₀ = 1 := by simp only [B, hC0, hQ1]
  have hQcont : ContinuousAt Q (1 : E →L[ℝ] E) :=
    hQLip.continuousOn.continuousAt (hV.mem_nhds h1V)
  have hBcont : ContinuousAt B a₀ := by
    have hQc : ContinuousAt Q (C a₀) := by simpa only [hC0] using hQcont
    exact hQc.comp hCLip.continuous.continuousAt
  have hCv : C ⁻¹' V ∈ 𝓝 a₀ :=
    hCLip.continuous.continuousAt.preimage_mem_nhds (by simpa only [hC0] using hV.mem_nhds h1V)
  have hAball : A ⁻¹' Metric.ball R' 1 ∈ 𝓝 a₀ :=
    hALip.continuous.continuousAt.preimage_mem_nhds
      (by simpa only [hA0] using Metric.ball_mem_nhds R' zero_lt_one)
  have hBball : B ⁻¹' Metric.ball (1 : E →L[ℝ] E) 1 ∈ 𝓝 a₀ :=
    hBcont.preimage_mem_nhds (by simpa only [hB0] using (Metric.ball_mem_nhds (1 : E →L[ℝ] E) zero_lt_one))
  obtain ⟨U, hUsub, hUopen, ha₀U⟩ := mem_nhds_iff.mp (inter_mem hCv (inter_mem hAball hBball))
  have hBLip : LipschitzOnWith (KQ * (‖CR‖₊ * (‖AR‖₊ * L))) B U :=
    hQLip.comp hCLip.lipschitzOnWith (fun a ha ↦ (hUsub ha).1)
  let J : P → E →L[ℝ] F := fun a ↦ (A a).comp (B a)
  have hJGram : ∀ a ∈ U, (J a).adjoint.comp (J a) = ContinuousLinearMap.id ℝ E := by
    intro a ha
    obtain ⟨hBself, hwhite⟩ := hQwhite (C a) (hUsub ha).1 (hCself a)
    have hBself' : IsSelfAdjoint (B a) := hBself
    have hAA : (A a).adjoint.comp (A a) = C a := by
      change ((proj a).comp R').adjoint.comp ((proj a).comp R') = R'.adjoint.comp ((proj a).comp R')
      calc
        _ = R'.adjoint.comp (((proj a).comp (proj a)).comp R') := by
          simp only [ContinuousLinearMap.adjoint_comp, (hprojself a).adjoint_eq,
            ContinuousLinearMap.comp_assoc]
        _ = _ := by rw [hprojsq a]
    have hwhite' : (B a).comp ((C a).comp (B a)) = ContinuousLinearMap.id ℝ E := by
      simpa only [hBself.star_eq, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc,
        ContinuousLinearMap.one_def, B] using hwhite
    calc
      (J a).adjoint.comp (J a) =
          (B a).comp (((A a).adjoint.comp (A a)).comp (B a)) := by
        simp only [J, ContinuousLinearMap.adjoint_comp, hBself'.adjoint_eq,
          ContinuousLinearMap.comp_assoc]
      _ = _ := by rw [hAA]; exact hwhite'
  refine ⟨J, U, (‖R'‖₊ + 1) * (KQ * (‖CR‖₊ * (‖AR‖₊ * L))) +
      (‖AR‖₊ * L) * (‖(1 : E →L[ℝ] E)‖₊ + 1), hUopen, ha₀U, ?_, ?_, ?_⟩
  · simp only [J, hA0, hB0, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
    rfl
  · apply lipschitzOnWith_clm_comp hALip.lipschitzOnWith hBLip
    · intro a ha
      have hdist : dist (A a) R' < 1 := (hUsub ha).2.1
      change ‖A a‖ ≤ ‖R'‖ + 1
      exact norm_le_norm_add_const_of_dist_le hdist.le
    · intro a ha
      have hdist : dist (B a) (1 : E →L[ℝ] E) < 1 := (hUsub ha).2.2
      change ‖B a‖ ≤ ‖(1 : E →L[ℝ] E)‖ + 1
      exact norm_le_norm_add_const_of_dist_le hdist.le
  · intro a ha
    refine ⟨hJGram a ha, ?_⟩
    have hsub : LinearMap.range (J a).toLinearMap ≤ LinearMap.range (proj a).toLinearMap := by
      rintro y ⟨x, rfl⟩
      exact ⟨R' (B a x), rfl⟩
    have hnorm : ∀ x, ‖J a x‖ = ‖x‖ := (J a).norm_map_iff_adjoint_comp_self.mpr (hJGram a ha)
    let I : E →ₗᵢ[ℝ] F := { (J a).toLinearMap with norm_map' := hnorm }
    exact Submodule.eq_of_le_of_finrank_eq hsub
      ((LinearMap.finrank_range_of_inj I.injective).trans (hrank a).symm)

omit [PseudoMetricSpace P] in
/-- A reference isometric frame is constructed from equal dimensions using
orthonormal coordinates, rather than included as an extra geometric premise. -/
theorem exists_linearIsometry_range_eq_submodule (H : Submodule ℝ F)
    (hdim : Module.finrank ℝ H = Module.finrank ℝ E) :
    ∃ R : E →ₗᵢ[ℝ] F, LinearMap.range R.toLinearMap = H := by
  let bH : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ H :=
    (stdOrthonormalBasis ℝ H).reindex (finCongr hdim)
  let e : E ≃ₗᵢ[ℝ] H := (stdOrthonormalBasis ℝ E).repr.trans bH.repr.symm
  let R : E →ₗᵢ[ℝ] F := H.subtypeₗᵢ.comp e.toLinearIsometry
  refine ⟨R, ?_⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (e x).property
  · intro hy
    obtain ⟨x, hx⟩ := e.surjective (⟨y, hy⟩ : H)
    exact ⟨x, congrArg Subtype.val hx⟩

/-- Subspace-family form using the actual orthogonal projections. The only
regularity premise is Lipschitz dependence of those projections, and equal
dimensions supply the reference isometry automatically. -/
theorem exists_lipschitz_isometric_subspace_frames
    (H : P → Submodule ℝ F) {L : ℝ≥0}
    (hLip : LipschitzWith L (fun a ↦ (H a).starProjection))
    (hrank : ∀ a, Module.finrank ℝ (H a) = Module.finrank ℝ E) (a₀ : P) :
    ∃ J : P → E →L[ℝ] F, ∃ U : Set P, ∃ K : ℝ≥0,
      IsOpen U ∧ a₀ ∈ U ∧ LipschitzOnWith K J U ∧
      (∀ a ∈ U, (J a).adjoint.comp (J a) = ContinuousLinearMap.id ℝ E ∧
        LinearMap.range (J a).toLinearMap = H a) := by
  obtain ⟨R, hRrange⟩ := exists_linearIsometry_range_eq_submodule (H a₀) (hrank a₀)
  have hProjRange : ∀ a, LinearMap.range (H a).starProjection.toLinearMap = H a := by
    intro a
    exact (H a).range_starProjection
  have hRR : LinearMap.range R.toLinearMap =
      LinearMap.range (H a₀).starProjection.toLinearMap := by
    simpa only [hProjRange] using hRrange
  have hdim : ∀ a, Module.finrank ℝ (LinearMap.range (H a).starProjection.toLinearMap) =
      Module.finrank ℝ E := by
    intro a
    rw [hProjRange a]
    exact hrank a
  obtain ⟨J, U, K, hU, ha₀U, _, hJLip, hJ⟩ :=
    exists_lipschitz_isometric_projection_frames (fun a ↦ (H a).starProjection)
      hLip (fun a ↦ isSelfAdjoint_starProjection (H a))
      (fun a ↦ (H a).isIdempotentElem_starProjection) a₀ R hRR hdim
  refine ⟨J, U, K, hU, ha₀U, hJLip, ?_⟩
  simpa only [hProjRange] using hJ

end OrthogonalProjectionFrames

end

end BanachIsometric
