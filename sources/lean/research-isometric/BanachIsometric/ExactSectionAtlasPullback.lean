import BanachIsometric.ExactSectionAtlas

/-! The actual exact-operator atlas pulls back along an actual Lipschitz
base map. All chart operators, inverse identities and exact body images
are retained literally by composition. -/

noncomputable section
namespace BanachIsometric.ExactSectionAtlas
open Set
open scoped NNReal

variable {A P E F : Type*} [PseudoMetricSpace A] [PseudoMetricSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : P → Submodule ℝ F}

def pullback (Z : ExactSectionAtlas S K H) (φ : A → P) {L : ℝ≥0}
    (hφ : LipschitzWith L φ) : ExactSectionAtlas S K (fun a => H (φ a)) where
  baseSet i := φ ⁻¹' Z.baseSet (φ i)
  isOpen_baseSet i := (Z.isOpen_baseSet (φ i)).preimage hφ.continuous
  mem_baseSet i := Z.mem_baseSet (φ i)
  forward i a := Z.forward (φ i) (φ a)
  inverse i a := Z.inverse (φ i) (φ a)
  forward_lipschitz i := by
    obtain ⟨C, hC⟩ := Z.forward_lipschitz (φ i)
    exact ⟨C * L, hC.comp hφ.lipschitzOnWith (fun _ ha => ha)⟩
  inverse_lipschitz i := by
    obtain ⟨C, hC⟩ := Z.inverse_lipschitz (φ i)
    exact ⟨C * L, hC.comp hφ.lipschitzOnWith (fun _ ha => ha)⟩
  left_inverse i a ha := Z.left_inverse (φ i) (φ a) ha
  forward_valid i a ha := Z.forward_valid (φ i) (φ a) ha

end BanachIsometric.ExactSectionAtlas
