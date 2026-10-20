module
public import HamSandwich.SphereOddDegree.SphereModTwoHomologyVanishing
public import HamSandwich.SphereOddDegree.RPnFiltrationCofiber
public import HamSandwich.SphereOddDegree.AlgebraicTopology.InducedOnRPCohomology
public import HamSandwich.SphereOddDegree.AlgebraicTopology.H1ClassifierZMod2
public import Mathlib

@[expose] public section

/-!
# Homology notation for spheres and real projective spaces

This file provides short names for the mod-two homology modules used in the
dimension-vanishing argument for real projective space.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace SphereOddDegree

/-- Mod-two singular homology of `RPⁿ`, packaged as a `ModuleCat (ZMod 2)`. -/
abbrev rpHomologyZMod2 (n k : Nat) : ModuleCat.{0} (ZMod 2) :=
  homologyZMod2 (TopCat.of (RP n)) k

/-- Mod-two singular homology of `Sⁿ`, packaged as a `ModuleCat (ZMod 2)`. -/
abbrev sphereHomologyZMod2 (n k : Nat) : ModuleCat.{0} (ZMod 2) :=
  homologyZMod2 (TopCat.of (Sphere n)) k

end SphereOddDegree
