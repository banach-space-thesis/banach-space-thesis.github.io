import BanachIsometric.AffineSubdivisionCarrier
import BanachIsometric.BarycenterMesh

/-! Every actual simplex in the support of barycentric subdivision has
contracted mesh. This uses the recursive cone construction and the actual
barycenter estimate; no subdivision property is assumed. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def affineMeshCarrier (s : Set E) (D : ℝ) (n : ℕ) : Submodule ℚ (AffineRationalChains E n) :=
  Finsupp.supported ℚ ℚ {v | (∀ i, v i ∈ s) ∧ ∀ i j, dist (v i) (v j) ≤ D}

theorem affineSubdivision_single_mesh (n : ℕ) (v : Fin (n + 1) → E)
    (D : ℝ) (hD : ∀ i j, dist (v i) (v j) ≤ D) :
    affineSubdivision n (Finsupp.single v 1) ∈
      affineMeshCarrier (convexHull ℝ (Set.range v)) (barycentricMeshFactor n * D) n := by
  induction n with
  | zero =>
    apply Finsupp.single_mem_supported ℚ 1
    refine ⟨fun i => subset_convexHull ℝ _ (Set.mem_range_self i), ?_⟩
    intro i j
    have hij : i = j := Fin.ext (by omega)
    simp [hij, barycentricMeshFactor]
  | succ n ih =>
    rw [affineSubdivision_single]
    have hD0 : 0 ≤ D := by simpa only [dist_self] using hD 0 0
    let s := convexHull ℝ (Set.range v)
    let T := affineMeshCarrier s (barycentricMeshFactor n * D) n
    let P := affineMeshCarrier s (barycentricMeshFactor (n + 1) * D) (n + 1)
    have hcone : T ≤ P.comap (affineCone (affineBarycenter v) n) := by
      change Finsupp.supported ℚ ℚ _ ≤ _
      rw [Finsupp.supported_eq_span_single]
      apply Submodule.span_le.mpr
      rintro _ ⟨w, hw, rfl⟩
      change affineCone (affineBarycenter v) n (Finsupp.single w 1) ∈ P
      rw [affineCone_single]
      apply Finsupp.single_mem_supported ℚ 1
      refine ⟨?_, ?_⟩
      · intro i
        induction i using Fin.cases with
        | zero =>
          exact affineBarycenter_mem_convex (convex_convexHull ℝ _) v
            (fun i => subset_convexHull ℝ _ (Set.mem_range_self i))
        | succ i => exact hw.1 i
      · intro i j
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero =>
            simpa only [Fin.cons_zero, dist_self] using
              mul_nonneg (barycentricMeshFactor_nonneg (n + 1)) hD0
          | succ j => exact dist_affineBarycenter_convexHull_le v D hD (hw.1 j)
        | succ i =>
          induction j using Fin.cases with
          | zero =>
            simpa only [Fin.cons_succ, Fin.cons_zero, dist_comm] using
              dist_affineBarycenter_convexHull_le v D hD (hw.1 i)
          | succ j =>
            exact (hw.2 i j).trans
              (mul_le_mul_of_nonneg_right (barycentricMeshFactor_le_succ n) hD0)
    apply hcone
    rw [affineBoundary_single, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_zsmul]
    apply T.toAddSubgroup.zsmul_mem
    have hface : ∀ j k, dist ((v ∘ i.succAbove) j) ((v ∘ i.succAbove) k) ≤ D :=
      fun j k => hD _ _
    have hpiece := ih (v ∘ i.succAbove) hface
    apply Finsupp.supported_mono ?_ hpiece
    intro w hw
    refine ⟨fun j => ?_, hw.2⟩
    apply convexHull_mono (Set.range_subset_iff.mpr (fun j => Set.mem_range_self (i.succAbove j)))
    exact hw.1 j

theorem affineSubdivision_mesh {s : Set E} (hs : Convex ℝ s) (D : ℝ) (n : ℕ) :
    affineMeshCarrier s D n ≤
      (affineMeshCarrier s (barycentricMeshFactor n * D) n).comap (affineSubdivision n) := by
  rw [affineMeshCarrier, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  change affineSubdivision n (Finsupp.single v 1) ∈
    affineMeshCarrier s (barycentricMeshFactor n * D) n
  have h := affineSubdivision_single_mesh n v D hv.2
  apply Finsupp.supported_mono ?_ h
  intro w hw
  exact ⟨fun i => (convexHull_min (Set.range_subset_iff.mpr hv.1) hs) (hw.1 i), hw.2⟩

end BanachIsometric.SingularPrism
