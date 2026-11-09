import BanachIsometric.RawSmallChains
import BanachIsometric.RawSubdivisionIteration
import BanachIsometric.AffineCarrierSupport
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! Every actual finite singular chain is eventually small under literal
barycentric subdivision for any actual open cover. The proof combines the
constructed mesh contraction with the metric Lebesgue lemma on each genuine
compact standard simplex. The target space itself need not be metric. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Filter Set Metric
open scoped Topology

theorem simplexStandardVertices_dist_le_one (n : ℕ) (i j : Fin (n + 1)) :
    dist (simplexStandardVertices n i) (simplexStandardVertices n j) ≤ 1 := by
  apply (dist_pi_le_iff zero_le_one).mpr
  intro k
  simp only [simplexStandardVertices, Pi.single_apply]
  split_ifs <;> norm_num [Real.dist_eq]

theorem universalAffineSubdivisionPower_mesh (n k : ℕ) :
    (universalAffineSubdivisionPower n k).val ∈
      affineMeshCarrier (stdSimplex ℝ (Fin (n + 1))) (barycentricMeshFactor n ^ k) n := by
  have hc : Finsupp.single (simplexStandardVertices n) (1 : ℚ) ∈
      affineMeshCarrier (stdSimplex ℝ (Fin (n + 1))) 1 n :=
    Finsupp.single_mem_supported ℚ 1
      ⟨simplexStandardVertices_mem n, simplexStandardVertices_dist_le_one n⟩
  have h := affineSubdivision_iterate_mesh (convex_stdSimplex ℝ _) n k 1 hc
  simpa only [mul_one] using h

theorem rawSubdivision_power_single_small_of_ball_cover {X ι : Type*} [TopologicalSpace X]
    (U : ι → Set X) (n : ℕ) (simplex : RawSingularSimplex X n) (δ : ℝ)
    (hcover : ∀ x : Simplex n, ∃ i, ball x δ ⊆ simplex ⁻¹' U i)
    (k : ℕ) (hk : barycentricMeshFactor n ^ k < δ) :
    (rawSubdivision X n ^ k) (Finsupp.single simplex 1) ∈ rawSmallChainCarrier U n := by
  rw [rawSubdivision_power_single]
  let P : Set (Fin (n + 1) → (Fin (n + 1) → ℝ)) :=
    {v | (∀ i, v i ∈ stdSimplex ℝ (Fin (n + 1))) ∧
      ∀ i j, dist (v i) (v j) ≤ barycentricMeshFactor n ^ k}
  let Q : Set (RawSingularSimplex (Simplex n) n) :=
    {piece | ∃ i, Set.range (simplex.comp piece) ⊆ U i}
  have hu : universalSingularSubdivisionPower n k ∈ Finsupp.supported ℚ ℚ Q := by
    apply affineCarrierRealization_supported (convex_stdSimplex ℝ _) n P Q ?_
      (universalAffineSubdivisionPower n k) (universalAffineSubdivisionPower_mesh n k)
    intro v hv hvP
    obtain ⟨i, hi⟩ := hcover ⟨v 0, hv 0⟩
    refine ⟨i, ?_⟩
    rintro _ ⟨w, rfl⟩
    apply hi
    exact (dist_affineCarrierSimplex_vertex_le (convex_stdSimplex ℝ _) ⟨v, hv⟩
      (barycentricMeshFactor n ^ k) hvP.2 w 0).trans_lt hk
  exact rawChainMap_supported simplex n Q _ (fun _ h => h) hu

theorem eventually_rawSubdivision_small_single {X ι : Type*} [TopologicalSpace X]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (n : ℕ) (simplex : RawSingularSimplex X n) :
    ∀ᶠ k : ℕ in atTop,
      (rawSubdivision X n ^ k) (Finsupp.single simplex 1) ∈ rawSmallChainCarrier U n := by
  obtain ⟨δ, hδ, hδcover⟩ := lebesgue_number_lemma_of_metric
    (isCompact_univ : IsCompact (Set.univ : Set (Simplex n)))
    (fun i => (hU i).preimage simplex.continuous) (by
      intro x _
      exact Set.mem_iUnion.mpr (hcover (simplex x)))
  have hlim : Tendsto (fun k : ℕ => barycentricMeshFactor n ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (barycentricMeshFactor_nonneg n)
      (barycentricMeshFactor_lt_one n)
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with k hk
  exact rawSubdivision_power_single_small_of_ball_cover U n simplex δ
    (fun x => hδcover x (Set.mem_univ x)) k hk

theorem eventually_rawSubdivision_small_chain {X ι : Type*} [TopologicalSpace X]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (n : ℕ) (c : RawRationalChains X n) :
    ∀ᶠ k : ℕ in atTop, (rawSubdivision X n ^ k) c ∈ rawSmallChainCarrier U n := by
  classical
  induction c using Finsupp.induction_linear with
  | zero =>
    exact Filter.Eventually.of_forall (fun k => by
      simpa only [map_zero] using (rawSmallChainCarrier U n).zero_mem)
  | add c d hc hd =>
    filter_upwards [hc, hd] with k hk hl
    simpa only [map_add] using (rawSmallChainCarrier U n).add_mem hk hl
  | single simplex a =>
    filter_upwards [eventually_rawSubdivision_small_single U hU hcover n simplex] with k hk
    have ha : Finsupp.single simplex a = a • Finsupp.single simplex 1 := by simp
    rw [ha, map_smul]
    exact (rawSmallChainCarrier U n).smul_mem a hk

theorem exists_rawSubdivision_small_chain {X ι : Type*} [TopologicalSpace X]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (n : ℕ) (c : RawRationalChains X n) :
    ∃ k : ℕ, (rawSubdivision X n ^ k) c ∈ rawSmallChainCarrier U n :=
  (eventually_rawSubdivision_small_chain U hU hcover n c).exists

end BanachIsometric.SingularPrism
