import BanachIsometric.RawSmallPositiveHomology

/-! The actual small-chain inclusion also induces the degree-zero
singular-homology equivalence. Every zero-simplex lies in a cover member,
and subdivision preserves its endpoints while making its boundary filling
small. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {X ι : Type*} [TopologicalSpace X] (U : ι → Set X)

def RawSmallZeroHomology : Type _ :=
  RawSmallCoordinates U 0 ⧸ LinearMap.range (rawSmallCoordinateBoundary U 0)

instance : AddCommGroup (RawSmallZeroHomology U) :=
  inferInstanceAs (AddCommGroup (RawSmallCoordinates U 0 ⧸ LinearMap.range (rawSmallCoordinateBoundary U 0)))

instance : Module ℚ (RawSmallZeroHomology U) :=
  inferInstanceAs (Module ℚ (RawSmallCoordinates U 0 ⧸ LinearMap.range (rawSmallCoordinateBoundary U 0)))

def rawSmallZeroHomologyInclusion : RawSmallZeroHomology U →ₗ[ℚ] RawZeroHomology X :=
  (LinearMap.range (rawSmallCoordinateBoundary U 0)).mapQ
    (LinearMap.range (rawBoundary (X := X) 0)) (rawSmallCoordinateInclusion U 0) (by
      rintro _ ⟨a, rfl⟩
      exact ⟨rawSmallCoordinateInclusion U 1 a, rawSmallCoordinateInclusion_boundary_apply U 0 a⟩)

theorem rawSmallZeroCoordinateInclusion_reflects_boundaries (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (c : RawSmallCoordinates U 0)
    (hc : rawSmallCoordinateInclusion U 0 c ∈ LinearMap.range (rawBoundary (X := X) 0)) :
    c ∈ LinearMap.range (rawSmallCoordinateBoundary U 0) := by
  obtain ⟨a, ha⟩ := hc
  obtain ⟨b, hb, he⟩ := exists_small_zero_boundary_filling U hU hcover
    (rawSmallCoordinateInclusion U 0 c) a ha
  obtain ⟨d, hd⟩ := exists_rawSmallCoordinates_of_mem U 1 b hb
  refine ⟨d, rawSmallCoordinateInclusion_injective U 0 ?_⟩
  rw [← rawSmallCoordinateInclusion_boundary_apply, hd, he]

theorem rawSmallZeroHomologyInclusion_injective (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    Function.Injective (rawSmallZeroHomologyInclusion U) := by
  intro q r he
  induction q using Submodule.Quotient.induction_on with
  | H c =>
    induction r using Submodule.Quotient.induction_on with
    | H d =>
      change (Submodule.Quotient.mk (rawSmallCoordinateInclusion U 0 c) : RawZeroHomology X) =
        Submodule.Quotient.mk (rawSmallCoordinateInclusion U 0 d) at he
      apply (Submodule.Quotient.eq _).mpr
      apply rawSmallZeroCoordinateInclusion_reflects_boundaries U hU hcover
      rw [map_sub]
      exact (Submodule.Quotient.eq _).mp he

theorem rawSmallZeroHomologyInclusion_surjective (hcover : ∀ x, ∃ i, x ∈ U i) :
    Function.Surjective (rawSmallZeroHomologyInclusion U) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H c =>
    have hc : c ∈ rawSmallChainCarrier U 0 := by
      simp [rawSmallChainCarrier_zero_eq_top U hcover]
    obtain ⟨d, hd⟩ := exists_rawSmallCoordinates_of_mem U 0 c hc
    refine ⟨Submodule.Quotient.mk d, ?_⟩
    change (Submodule.Quotient.mk (rawSmallCoordinateInclusion U 0 d) : RawZeroHomology X) =
      Submodule.Quotient.mk c
    rw [hd]

def rawSmallZeroHomologyEquiv (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    RawSmallZeroHomology U ≃ₗ[ℚ] RawZeroHomology X :=
  LinearEquiv.ofBijective (rawSmallZeroHomologyInclusion U)
    ⟨rawSmallZeroHomologyInclusion_injective U hU hcover,
      rawSmallZeroHomologyInclusion_surjective U hcover⟩

end BanachIsometric.SingularPrism
