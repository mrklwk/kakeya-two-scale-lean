module
/- Modified for Lean 4.34.1 and current mathlib compatibility.
See vendor/HamSandwich/README.md and source-lock.json for provenance and changes. -/
public import HamSandwich.SphereOddDegree.AlgebraicTopology.HomotopyInvarianceWrappers
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

@[expose] public section

/-!
# Homotopy invariance of singular homology — conditional packaging

This file states the **strongest homotopy-invariance theorem the project can prove
today** and packages it cleanly for downstream topological-degree work.

Pinned Mathlib (`v4.28.0`, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`)
contains *no* homotopy invariance of singular homology and *no* complete prism
operator. The project has built:

* the **consumer** `singularHomologyMap_eq_of_singularChainHomotopy`
  (`HomotopyToChainHomotopy.lean`): a chain homotopy between singular chain maps
  yields equal maps on singular homology;
* the **topological / simplicial-set half** of the prism (`PrismOperator.lean`):
  the singular cylinder `cylinder H : Sing X ⨯ Δ[1] ⟶ Sing Y` of a topological
  homotopy, with the two endpoint identities `cylinder_sect_zero/one`.

The one genuinely missing keystone is the *algebraic* prism (simplicial homotopy
⇒ chain homotopy on alternating-face-map complexes). Rather than fake an
unconditional theorem, this file isolates that exact missing piece as a single,
named hypothesis — `SingularPrismOperator` — and proves homotopy invariance
**conditionally on it**, in every form later code needs:

* `singularHomologyMap_eq_of_homotopy` — from a topological homotopy of `TopCat`
  maps;
* `singularHomologyMap_eq_of_homotopic` — from the `Homotopic` relation;
* `singularHomologyMap_eq_of_homotopic_continuousMap` — the `C(X, Y)` interface;
* `singularHomologyFunctor_map_eq_of_homotopic` — the raw functor form.

The hypothesis `SingularPrismOperator` is **exactly** the still-missing prism
operator (it is implied by it, and it would deliver full unconditional homotopy
invariance the moment the algebraic prism is constructed). No unconditional
homotopy-invariance statement is asserted.

We work at integer coefficients (`ModuleCat.{0} ℤ`), the case relevant to the
topological degree of sphere maps.
-/

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

/-- **The prism-operator hypothesis** (the still-missing keystone).

A `SingularPrismOperator` is the assertion that every topological homotopy
between two `TopCat` maps gives rise to a chain homotopy of the induced integral
singular chain maps. This is precisely the classical prism operator
`P_n : C_n(X) → C_{n+1}(Y)` with `∂P + P∂ = g_# − f_#`, the one ingredient of
homotopy invariance of singular homology still absent from pinned Mathlib (the
topological half is built in `PrismOperator.lean` as `cylinder`).

It is phrased as a `Prop` (using `Nonempty` of the chain-homotopy data) so it can
be assumed cleanly as a hypothesis; this suffices for every homology-level
*equality* below, which are propositions. -/
def SingularPrismOperator : Prop :=
  ∀ {X Y : TopCat.{0}} {f g : X ⟶ Y},
    ContinuousMap.Homotopy f.hom g.hom →
      Nonempty (Homotopy (singularChainℤ.map f) (singularChainℤ.map g))

/-- **Conditional homotopy invariance (topological homotopy form).**

Assuming the prism operator, a topological homotopy between two `TopCat` maps
`f, g : X ⟶ Y` induces equal maps on the `n`-th integral singular homology. -/
theorem singularHomologyMap_eq_of_homotopy
    (prism : SingularPrismOperator)
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ) :
    (singularHomologyℤ n).map f = (singularHomologyℤ n).map g := by
  obtain ⟨ch⟩ := prism H
  exact singularHomologyMap_eq_of_singularChainHomotopy ch n

/-- **Conditional homotopy invariance (`Homotopic` form).**

Assuming the prism operator, homotopic `TopCat` maps `f, g : X ⟶ Y` (i.e.
`ContinuousMap.Homotopic f.hom g.hom`) induce equal maps on the `n`-th integral
singular homology. -/
theorem singularHomologyMap_eq_of_homotopic
    (prism : SingularPrismOperator)
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : ContinuousMap.Homotopic f.hom g.hom) (n : ℕ) :
    (singularHomologyℤ n).map f = (singularHomologyℤ n).map g := by
  obtain ⟨H⟩ := h
  exact singularHomologyMap_eq_of_homotopy prism H n

/-- **Conditional homotopy invariance (`C(X, Y)` interface).**

Assuming the prism operator, two homotopic continuous maps `f, g : C(X, Y)`
between topological spaces underlying `TopCat` objects induce equal maps on the
`n`-th integral singular homology (after the canonical `TopCat.ofHom`). -/
theorem singularHomologyMap_eq_of_homotopic_continuousMap
    (prism : SingularPrismOperator)
    {X Y : TopCat.{0}} {f g : C(X, Y)}
    (h : ContinuousMap.Homotopic f g) (n : ℕ) :
    (singularHomologyℤ n).map (TopCat.ofHom f)
      = (singularHomologyℤ n).map (TopCat.ofHom g) :=
  singularHomologyMap_eq_of_homotopic prism h n

/-- **Conditional homotopy invariance (raw functor form).**

The same statement as `singularHomologyMap_eq_of_homotopic`, written directly in
terms of `AlgebraicTopology.singularHomologyFunctor`, for callers that prefer the
unfolded functor. -/
theorem singularHomologyFunctor_map_eq_of_homotopic
    (prism : SingularPrismOperator)
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : ContinuousMap.Homotopic f.hom g.hom) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).map f
      = ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).map g :=
  singularHomologyMap_eq_of_homotopic prism h n

end SphereOddDegree
