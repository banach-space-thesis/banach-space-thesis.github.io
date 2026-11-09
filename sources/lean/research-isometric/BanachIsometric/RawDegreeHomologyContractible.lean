import BanachIsometric.RawDegreeHomology
import BanachIsometric.ConvexSingularAcyclicity
import BanachIsometric.ContractibleZeroHomology

/-! Rational homology of contractible spaces, indexed by actual degree. -/

noncomputable section
namespace BanachIsometric.SingularPrism

theorem rawDegreeHomology_subsingleton_succ_of_contractible
    (X : Type*) [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) :
    Subsingleton (RawDegreeHomology X (n + 1)) :=
  rawPositiveHomology_contractible X n

theorem rawDegreeHomology_finiteDimensional_of_contractible
    (X : Type*) [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) :
    FiniteDimensional ℚ (RawDegreeHomology X n) := by
  cases n with
  | zero =>
      change FiniteDimensional ℚ (RawZeroHomology X)
      exact FiniteDimensional.of_injective (rawZeroHomologyContractibleEquiv X).toLinearMap
        (rawZeroHomologyContractibleEquiv X).injective
  | succ n =>
      letI := rawDegreeHomology_subsingleton_succ_of_contractible X n
      infer_instance

end BanachIsometric.SingularPrism
