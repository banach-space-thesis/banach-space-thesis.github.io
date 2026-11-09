import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! The concrete free rational module functor, with no additional monoidal
structure required. Objects and maps are literal Finsupps and mapDomain. -/

namespace BanachIsometric

open CategoryTheory

noncomputable def rationalFreeModule : Type ⥤ ModuleCat ℚ where
  obj X := ModuleCat.of ℚ (X →₀ ℚ)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain ℚ ℚ f)
  map_id := by intro X; ext : 1; exact Finsupp.lmapDomain_id ℚ ℚ
  map_comp := by intros; ext : 1; exact Finsupp.lmapDomain_comp ℚ ℚ _ _

theorem rationalFreeModule_map_single {X Y : Type} (f : X → Y) (x : X) (c : ℚ) :
    rationalFreeModule.map f (Finsupp.single x c) = Finsupp.single (f x) c :=
  Finsupp.mapDomain_single

end BanachIsometric
