import PFP.GowersMaureyNamedStatements
import PFP.GowersMaureyConditionalProofs
import ThesisCommon.Analysis.GowersMaureyFullConsequences

/-! All six original conclusions of Example 7.1, on the actual constructed
complex shift space and on its fixed named choice. The approximation theorem
is proved in the shared library; no representation or ideal premise remains. -/
noncomputable section
namespace PFP
open ThesisCommon ThesisCommon.GowersMaurey

theorem example_7_1 (D : ConstructionData ℂ) : Example_7_1 D :=
  example_7_1_of_finiteSpreadApproximation D (finiteSpreadApproximable D)

theorem example_7_1_named : Example_7_1_named :=
  example_7_1_named_iff.mpr (example_7_1 (chosenConstructionData ℂ))

theorem example_7_1_all_constructions : Example_7_1_all_constructions :=
  ⟨gowersMaureyConstructionExists, example_7_1⟩

end PFP
