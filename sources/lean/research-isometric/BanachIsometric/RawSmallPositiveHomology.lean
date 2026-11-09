import BanachIsometric.RawSmallChainInclusion
import BanachIsometric.SmallChainHomologyFilling

/-! Inclusion of the literal small-chain complex induces an equivalence on
positive rational singular homology for every open cover. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {X ι : Type*} [TopologicalSpace X] (U : ι → Set X)

def rawSmallCycles (n : ℕ) : Submodule ℚ (RawSmallCoordinates U (n + 1)) :=
  LinearMap.ker (rawSmallCoordinateBoundary U n)

def rawSmallBoundaryCycle (n : ℕ) : RawSmallCoordinates U (n + 2) →ₗ[ℚ] rawSmallCycles U n :=
  (rawSmallCoordinateBoundary U (n + 1)).codRestrict (rawSmallCycles U n)
    (fun c => LinearMap.congr_fun (rawSmallCoordinateBoundary_squared U n) c)

def rawSmallBoundaries (n : ℕ) : Submodule ℚ (rawSmallCycles U n) :=
  LinearMap.range (rawSmallBoundaryCycle U n)

def RawSmallPositiveHomology (n : ℕ) : Type _ := rawSmallCycles U n ⧸ rawSmallBoundaries U n

instance (n : ℕ) : AddCommGroup (RawSmallPositiveHomology U n) :=
  inferInstanceAs (AddCommGroup (rawSmallCycles U n ⧸ rawSmallBoundaries U n))

instance (n : ℕ) : Module ℚ (RawSmallPositiveHomology U n) :=
  inferInstanceAs (Module ℚ (rawSmallCycles U n ⧸ rawSmallBoundaries U n))

def rawSmallCyclesInclusion (n : ℕ) : rawSmallCycles U n →ₗ[ℚ] rawCycles X n :=
  ((rawSmallCoordinateInclusion U (n + 1)).comp (rawSmallCycles U n).subtype).codRestrict
    (rawCycles X n) (by
      intro c
      have hc : rawSmallCoordinateBoundary U n c.val = 0 := c.property
      change rawBoundary n (rawSmallCoordinateInclusion U (n + 1) c.val) = 0
      rw [rawSmallCoordinateInclusion_boundary_apply, hc, map_zero])

theorem rawSmallCyclesInclusion_preserves_boundaries (n : ℕ) :
    rawSmallBoundaries U n ≤ (rawBoundaries X n).comap (rawSmallCyclesInclusion U n) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨rawSmallCoordinateInclusion U (n + 2) a,
    Subtype.ext (rawSmallCoordinateInclusion_boundary_apply U (n + 1) a)⟩

def rawSmallPositiveHomologyInclusion (n : ℕ) :
    RawSmallPositiveHomology U n →ₗ[ℚ] RawPositiveHomology X n :=
  (rawSmallBoundaries U n).mapQ (rawBoundaries X n) (rawSmallCyclesInclusion U n)
    (rawSmallCyclesInclusion_preserves_boundaries U n)

theorem rawSmallCyclesInclusion_reflects_boundaries (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (c : rawSmallCycles U n)
    (hc : rawSmallCyclesInclusion U n c ∈ rawBoundaries X n) : c ∈ rawSmallBoundaries U n := by
  obtain ⟨a, ha⟩ := hc
  have h : rawBoundary (n + 1) a = rawSmallCoordinateInclusion U (n + 1) c.val :=
    congrArg Subtype.val ha
  obtain ⟨b, hb, he⟩ := exists_small_boundary_filling U hU hcover n
    (rawSmallCoordinateInclusion U (n + 1) c.val) (rawSmallCoordinateInclusion_mem U (n + 1) c.val) a h
  obtain ⟨d, hd⟩ := exists_rawSmallCoordinates_of_mem U (n + 2) b hb
  refine ⟨d, Subtype.ext ?_⟩
  apply rawSmallCoordinateInclusion_injective U (n + 1)
  change rawSmallCoordinateInclusion U (n + 1) (rawSmallCoordinateBoundary U (n + 1) d) =
    rawSmallCoordinateInclusion U (n + 1) c.val
  rw [← rawSmallCoordinateInclusion_boundary_apply, hd, he]

theorem rawSmallPositiveHomologyInclusion_injective (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) :
    Function.Injective (rawSmallPositiveHomologyInclusion U n) := by
  intro q r he
  induction q using Submodule.Quotient.induction_on with
  | H c =>
    induction r using Submodule.Quotient.induction_on with
    | H d =>
      change Submodule.Quotient.mk (rawSmallCyclesInclusion U n c) =
        Submodule.Quotient.mk (rawSmallCyclesInclusion U n d) at he
      apply (Submodule.Quotient.eq _).mpr
      apply rawSmallCyclesInclusion_reflects_boundaries U hU hcover n
      rw [map_sub]
      exact (Submodule.Quotient.eq _).mp he

theorem rawSmallPositiveHomologyInclusion_surjective (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) :
    Function.Surjective (rawSmallPositiveHomologyInclusion U n) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H c =>
    obtain ⟨d, hd, hd0, a, ha⟩ := exists_small_cycle_representative U hU hcover n c.val c.property
    obtain ⟨e, he⟩ := exists_rawSmallCoordinates_of_mem U (n + 1) d hd
    have he0 : rawSmallCoordinateBoundary U n e = 0 := by
      apply rawSmallCoordinateInclusion_injective U n
      rw [← rawSmallCoordinateInclusion_boundary_apply, he, hd0, map_zero]
    let v : rawSmallCycles U n := ⟨e, he0⟩
    refine ⟨Submodule.Quotient.mk v, ?_⟩
    change Submodule.Quotient.mk (rawSmallCyclesInclusion U n v) = Submodule.Quotient.mk c
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨-a, Subtype.ext ?_⟩
    change rawBoundary (n + 1) (-a) = rawSmallCoordinateInclusion U (n + 1) e - c.val
    rw [map_neg, ha, he]
    abel

def rawSmallPositiveHomologyEquiv (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) : RawSmallPositiveHomology U n ≃ₗ[ℚ] RawPositiveHomology X n :=
  LinearEquiv.ofBijective (rawSmallPositiveHomologyInclusion U n)
    ⟨rawSmallPositiveHomologyInclusion_injective U hU hcover n,
      rawSmallPositiveHomologyInclusion_surjective U hU hcover n⟩

end BanachIsometric.SingularPrism
