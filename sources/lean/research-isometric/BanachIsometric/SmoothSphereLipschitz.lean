import BanachIsometric.CompactLocalLipschitz
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Smooth fields on the original metric sphere are Lipschitz

The local stereographic charts are restrictions of actual smooth ambient
formulas, so they are locally Lipschitz for the inherited sphere metric.
A C-one map into a normed space is locally Lipschitz in these charts. Compactness
then gives a global constant. In particular smooth orthogonal-projection fields
supply the actual regularity used in the exact-section bundle construction.
-/

noncomputable section
namespace BanachIsometric

open Set Metric Filter
open scoped Topology NNReal Manifold

theorem exists_lipschitzWith_of_local_on_compact
    {P W : Type*} [PseudoMetricSpace P] [CompactSpace P] [PseudoMetricSpace W]
    (f : P → W)
    (hlocal : ∀ x, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith L f U) :
    ∃ L : ℝ≥0, LipschitzWith L f := by
  classical
  choose L U hU hLip using hlocal
  obtain ⟨s, hs⟩ := finite_cover_nhds_interior hU
  have hcover : (⋃ i : s, interior (U i.val)) = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    have hx : x ∈ ⋃ i ∈ s, interior (U i) := by rw [hs]; trivial
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
    exact ⟨⟨i, hi⟩, hx⟩
  exact exists_lipschitzWith_of_finite_open_cover f (fun i : s => interior (U i.val))
    (fun _ => isOpen_interior) hcover (fun i => L i.val)
    (fun i => (hLip i.val).mono interior_subset)

theorem exists_lipschitzOnWith_sphere_chart
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (x : sphere (0 : V) 1) :
    ∃ L : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith L (extChartAt (𝓡 n) x) U := by
  let b : (ℝ ∙ (-x.val))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere (-x))).repr
  let F : V → EuclideanSpace ℝ (Fin n) := fun y => b (stereoToFun (-x.val) y)
  have hxx : innerSL ℝ (-x.val) x.val = -1 := by
    change inner ℝ (-x.val) x.val = -1
    rw [inner_neg_left, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere x]
    norm_num
  have hStereo : ContDiffAt ℝ 1 (stereoToFun (-x.val)) x.val :=
    contDiffOn_stereoToFun.contDiffAt
      (((isOpen_ne : IsOpen {r : ℝ | r ≠ 1}).preimage
        (innerSL ℝ (-x.val)).continuous).mem_nhds (by
          change innerSL ℝ (-x.val) x.val ≠ 1
          rw [hxx]
          norm_num))
  have hF : ContDiffAt ℝ 1 F x.val := b.contDiff.contDiffAt.comp x.val hStereo
  obtain ⟨L, U, hU, hLip⟩ := hF.exists_lipschitzOnWith
  have hformula (y : sphere (0 : V) 1) : F y.val = extChartAt (𝓡 n) x y := by rfl
  refine ⟨L, Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  rw [← hformula, ← hformula]
  exact hLip.dist_le_mul y.val hy z.val hz

theorem ContMDiff.exists_lipschitzWith_sphere
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    {f : sphere (0 : V) 1 → W} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, W) 1 f) :
    ∃ L : ℝ≥0, LipschitzWith L f := by
  letI : CompactSpace (sphere (0 : V) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V) 1)
  apply exists_lipschitzWith_of_local_on_compact f
  intro x
  let e := extChartAt (𝓡 n) x
  let q := f ∘ e.symm
  have hq : ContDiffAt ℝ 1 q (e x) := by
    have h := (contMDiffAt_iff_source.mp (hf x)).contDiffWithinAt
    simpa only [modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ] using h
  obtain ⟨Lq, Uq, hUq, hqLip⟩ := hq.exists_lipschitzOnWith
  obtain ⟨Le, Ue, hUe, heLip⟩ := exists_lipschitzOnWith_sphere_chart (n := n) x
  let U := Ue ∩ e ⁻¹' Uq ∩ e.source
  have hU : U ∈ 𝓝 x := inter_mem (inter_mem hUe
    ((continuousAt_extChartAt x).preimage_mem_nhds hUq)) (extChartAt_source_mem_nhds x)
  refine ⟨Lq * Le, U, hU, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro y hy z hz
  have hyf : q (e y) = f y := congrArg f (e.left_inv hy.2)
  have hzf : q (e z) = f z := congrArg f (e.left_inv hz.2)
  rw [← hyf, ← hzf]
  calc
    dist (q (e y)) (q (e z)) ≤ (Lq : ℝ) * dist (e y) (e z) :=
      hqLip.dist_le_mul _ hy.1.2 _ hz.1.2
    _ ≤ (Lq : ℝ) * ((Le : ℝ) * dist y z) :=
      mul_le_mul_of_nonneg_left (heLip.dist_le_mul _ hy.1.1 _ hz.1.1) Lq.coe_nonneg
    _ = ((Lq * Le : ℝ≥0) : ℝ) * dist y z := by rw [NNReal.coe_mul]; ring

end BanachIsometric
