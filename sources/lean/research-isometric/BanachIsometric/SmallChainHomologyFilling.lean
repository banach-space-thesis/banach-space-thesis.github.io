import BanachIsometric.SmallChainSubdivision
import BanachIsometric.SubdivisionCycleFilling
import BanachIsometric.PathConnectedZeroHomology

/-! Genuine small-chain comparison on cycles and boundaries. Every cycle
has a homologous small cycle; every small chain which bounds in the full
singular complex already bounds by an actual small chain. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {X ι : Type*} [TopologicalSpace X]

theorem exists_small_cycle_representative (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (c : RawRationalChains X (n + 1))
    (hc : rawBoundary n c = 0) :
    ∃ d : RawRationalChains X (n + 1), d ∈ rawSmallChainCarrier U (n + 1) ∧
      rawBoundary n d = 0 ∧ ∃ a : RawRationalChains X (n + 2), rawBoundary (n + 1) a = c - d := by
  obtain ⟨k, hk⟩ := exists_rawSubdivision_small_chain U hU hcover (n + 1) c
  refine ⟨(rawSubdivision X (n + 1) ^ k) c, hk, ?_, rawSubdivisionCycleFilling X n k c, ?_⟩
  · have h := LinearMap.congr_fun (rawSubdivision_boundary_power X n k) c
    simpa only [LinearMap.comp_apply, hc, map_zero] using h
  · exact rawSubdivisionCycleFilling_boundary X n k c hc

theorem exists_small_boundary_filling (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (c : RawRationalChains X (n + 1))
    (hc : c ∈ rawSmallChainCarrier U (n + 1)) (a : RawRationalChains X (n + 2))
    (ha : rawBoundary (n + 1) a = c) :
    ∃ b : RawRationalChains X (n + 2), b ∈ rawSmallChainCarrier U (n + 2) ∧
      rawBoundary (n + 1) b = c := by
  have hcycle : rawBoundary n c = 0 := by
    rw [← ha]
    exact LinearMap.congr_fun (rawBoundary_squared n) a
  obtain ⟨k, hk⟩ := exists_rawSubdivision_small_chain U hU hcover (n + 2) a
  refine ⟨rawSubdivisionCycleFilling X n k c + (rawSubdivision X (n + 2) ^ k) a,
    (rawSmallChainCarrier U (n + 2)).add_mem
      (rawSubdivisionCycleFilling_preserves_small X U n k hc) hk, ?_⟩
  rw [map_add, rawSubdivisionCycleFilling_boundary X n k c hcycle]
  have hpow := LinearMap.congr_fun (rawSubdivision_boundary_power X (n + 1) k) a
  simp only [LinearMap.comp_apply, ha] at hpow
  rw [hpow, sub_add_cancel]

theorem rawSmallChainCarrier_zero_eq_top (U : ι → Set X) (hcover : ∀ x, ∃ i, x ∈ U i) :
    rawSmallChainCarrier U 0 = ⊤ := by
  have hP : {simplex : RawSingularSimplex X 0 | ∃ i, Set.range simplex ⊆ U i} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro simplex
    obtain ⟨i, hi⟩ := hcover (simplex (stdSimplex.vertex (0 : Fin 1)))
    refine ⟨i, ?_⟩
    rintro _ ⟨w, rfl⟩
    rwa [simplexZero_eq_vertex w]
  rw [rawSmallChainCarrier, hP, Finsupp.supported_univ]

theorem exists_small_zero_boundary_filling (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (c : RawRationalChains X 0) (a : RawRationalChains X 1)
    (ha : rawBoundary 0 a = c) :
    ∃ b : RawRationalChains X 1, b ∈ rawSmallChainCarrier U 1 ∧ rawBoundary 0 b = c := by
  obtain ⟨k, hk⟩ := exists_rawSubdivision_small_chain U hU hcover 1 a
  refine ⟨(rawSubdivision X 1 ^ k) a, hk, ?_⟩
  have h := LinearMap.congr_fun (rawSubdivision_boundary_power X 0 k) a
  simp only [LinearMap.comp_apply, ha] at h
  rw [h, rawSubdivision_zero]
  change ((1 : Module.End ℚ (RawRationalChains X 0)) ^ k) c = c
  simp only [one_pow, Module.End.one_apply]

end BanachIsometric.SingularPrism
