module
/- Modified for Lean 4.34.1 and current mathlib compatibility.
See vendor/HamSandwich/README.md and source-lock.json for provenance and changes. -/
public import HamSandwich.SphereOddDegree.AlgebraicTopology.HomotopyToChainHomotopy
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

@[expose] public section

-- Local compatibility adapter: replace the old prism backport with installed mathlib.
open CategoryTheory AlgebraicTopology
namespace SphereOddDegree
noncomputable def singularChainHomotopyOfHomotopy
    {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : ContinuousMap.Homotopy f.hom g.hom) :
    Homotopy (singularChainℤ.map f) (singularChainℤ.map g) :=
  TopCat.Homotopy.singularChainComplexFunctorObjMap H (ModuleCat.of ℤ ℤ)
noncomputable def singularChainHomotopyOfHomotopyModule
    (R : Type) [CommRing R] (Mod : ModuleCat.{0} R)
    {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : ContinuousMap.Homotopy f.hom g.hom) :
    Homotopy (((singularChainComplexFunctor (ModuleCat.{0} R)).obj Mod).map f)
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj Mod).map g) :=
  TopCat.Homotopy.singularChainComplexFunctorObjMap H Mod
end SphereOddDegree
#print axioms SphereOddDegree.singularChainHomotopyOfHomotopy
#print axioms SphereOddDegree.singularChainHomotopyOfHomotopyModule
