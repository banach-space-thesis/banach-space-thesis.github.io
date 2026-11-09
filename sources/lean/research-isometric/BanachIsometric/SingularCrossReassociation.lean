import BanachIsometric.SingularCrossAssociativity

/-! Reassociation formulas at any supplied total degrees. The inverse
formula uses the actual inverse of the geometric product associator. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

open SingularAW

variable (X Y Z : Type u) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def awProductUnassoc : C(X × (Y × Z), (X × Y) × Z) :=
  ⟨fun z => ((z.1, z.2.1), z.2.2),
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)⟩

theorem rawFullHomologyMap_apply_comp {A B D : Type u}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace D]
    (f : C(A, B)) (g : C(B, D)) (n : ℕ) (a : RawHomology A n) :
    rawFullHomologyMap (g.comp f) n a = rawFullHomologyMap g n (rawFullHomologyMap f n a) :=
  LinearMap.congr_fun (rawFullHomologyMap_comp f g n) a

theorem rawHomologyCross_reassociate {n p q r k l : ℕ}
    (h₁ : p + q = k) (h₂ : k + r = n) (h₃ : q + r = l) (h₄ : p + l = n)
    (a : RawHomology X p) (b : RawHomology Y q) (c : RawHomology Z r) :
    rawFullHomologyMap awProductAssoc n (rawHomologyCross (X × Y) Z h₂ (rawHomologyCross X Y h₁ a b) c) =
      rawHomologyCross X (Y × Z) h₄ a (rawHomologyCross Y Z h₃ b c) := by
  subst k
  subst l
  exact rawHomologyCross_associativity X Y Z h₂ a b c

theorem rawHomologyCross_unassociate {n p q r k l : ℕ}
    (h₁ : p + q = k) (h₂ : k + r = n) (h₃ : q + r = l) (h₄ : p + l = n)
    (a : RawHomology X p) (b : RawHomology Y q) (c : RawHomology Z r) :
    rawFullHomologyMap (awProductUnassoc X Y Z) n
      (rawHomologyCross X (Y × Z) h₄ a (rawHomologyCross Y Z h₃ b c)) =
        rawHomologyCross (X × Y) Z h₂ (rawHomologyCross X Y h₁ a b) c := by
  rw [← rawHomologyCross_reassociate X Y Z h₁ h₂ h₃ h₄ a b c,
    ← rawFullHomologyMap_apply_comp,
    show (awProductUnassoc X Y Z).comp awProductAssoc = ContinuousMap.id ((X × Y) × Z) from rfl,
    rawFullHomologyMap_id, LinearMap.id_apply]

end BanachIsometric.SingularEZ
