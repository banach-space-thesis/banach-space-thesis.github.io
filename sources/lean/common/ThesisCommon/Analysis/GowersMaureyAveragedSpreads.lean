import ThesisCommon.Analysis.GowersMaureyAdjointSpreads

/-! The source averaged-functional classes are preserved by actual tail
spreads, including their adjoints. The witnesses are the spread images of
the original successive dual-unit family, with unchanged averaging size. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem AveragedFunctional.spread {D : ConstructionData 𝕜} {k : ℕ} {a : C00 𝕜}
    (ha : AveragedFunctional (implicitNorm D) k a) (m n : ℕ) :
    AveragedFunctional (implicitNorm D) k (GowersMaurey.spread m n a) := by
  obtain ⟨hk, z, hz, hu, he⟩ := ha
  refine ⟨hk, (fun i => GowersMaurey.spread m n (z i)),
    successive_spread hz m n, (fun i => (hu i).spread m n), ?_⟩
  simp only [he, RCLike.real_smul_eq_coe_smul (K := 𝕜), map_smul, map_sum]

theorem AveragedFunctional.spread_pairing {D : ConstructionData 𝕜}
    {k : ℕ} {a : C00 𝕜} (ha : AveragedFunctional (implicitNorm D) k a)
    (m n : ℕ) :
    AveragedFunctional (implicitNorm D) k (GowersMaurey.spread n m a) ∧
      ∀ x : C00 𝕜, pairing a (GowersMaurey.spread m n x) =
        pairing (GowersMaurey.spread n m a) x :=
  ⟨ha.spread n m, fun x => (pairing_spread_left n m a x).symm⟩

end ThesisCommon.GowersMaurey
