import BanachIsometric.MetricBallKernelRigidity

/-! A definite seminorm defines a genuine norm on an explicit algebraic
copy of the original space. No topology or metric on the original is replaced.
The scalar ring may be noncommutative; only NormSMulClass is installed there. -/

namespace BanachIsometric.MetricGeometry

noncomputable section

variable {R X : Type*} [SeminormedRing R] [AddCommGroup X] [Module R X]

def DefiniteSeminormModel (p : Seminorm R X) (_hdef : ∀ x, p x = 0 ↔ x = 0) : Type _ := X

instance (p : Seminorm R X) (hdef : ∀ x, p x = 0 ↔ x = 0) :
    AddCommGroup (DefiniteSeminormModel p hdef) := inferInstanceAs (AddCommGroup X)

instance (p : Seminorm R X) (hdef : ∀ x, p x = 0 ↔ x = 0) :
    Module R (DefiniteSeminormModel p hdef) := inferInstanceAs (Module R X)

instance (p : Seminorm R X) (hdef : ∀ x, p x = 0 ↔ x = 0) :
    NormedAddCommGroup (DefiniteSeminormModel p hdef) :=
  AddGroupNorm.toNormedAddCommGroup
    { p.toAddGroupSeminorm with eq_zero_of_map_eq_zero' := fun x hx => (hdef x).mp hx }

instance (p : Seminorm R X) (hdef : ∀ x, p x = 0 ↔ x = 0) :
    NormSMulClass R (DefiniteSeminormModel p hdef) where
  norm_smul a x := map_smul_eq_mul p a (x : X)

theorem norm_definiteSeminormModel (p : Seminorm R X) (hdef : ∀ x, p x = 0 ↔ x = 0)
    (x : DefiniteSeminormModel p hdef) : ‖x‖ = p (x : X) := rfl

def toDefiniteSeminormModel (p : Seminorm R X) (hdef : ∀ x, p x = 0 ↔ x = 0) :
    X ≃ₗ[R] DefiniteSeminormModel p hdef := LinearEquiv.refl R X

end
end BanachIsometric.MetricGeometry
