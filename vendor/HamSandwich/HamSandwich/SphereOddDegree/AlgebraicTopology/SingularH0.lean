module
/- Modified for Lean 4.34.1 and current mathlib compatibility.
See vendor/HamSandwich/README.md and source-lock.json for provenance and changes. -/
public import HamSandwich.SphereOddDegree.AlgebraicTopology.SubChainSubspaceBridge
public import HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionCone

@[expose] public section

/-!
# Zeroth singular homology of path-connected spaces

We build the classical computation `H₀(X; ℤ) ≅ ℤ` for a nonempty path-connected
space `X`, via the augmentation `ε : C₀(X) → ℤ` (sum of coefficients).  The key
geometric input is that for points joined by a path, the difference of the two
`0`-simplices is a boundary (`chainGenerator_sub_mem_range_of_path`).
-/

open CategoryTheory AlgebraicTopology Limits
open SphereOddDegree.AffineBarycentricSubdivision

noncomputable section
namespace SphereOddDegree

variable {X : TopCat.{0}}

/-- The `0`-simplex of `X` sitting at the point `x`. -/
noncomputable def pointSimplex (X : TopCat.{0}) (x : X) : singularSimplices X 0 :=
  continuousMapAsSingularSimplex X 0 (ContinuousMap.const (Delta 0) x)

/-- The singular `1`-simplex of `X` obtained from a path, by reparametrising the
standard `1`-simplex `Δ¹` as the unit interval. -/
noncomputable def pathSimplex {a b : X} (p : Path a b) : singularSimplices X 1 :=
  continuousMapAsSingularSimplex X 1
    (p.toContinuousMap.comp
      (⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩ :
        C(Delta 1, unitInterval)))

/-
The boundary of the path `1`-simplex is the difference of its endpoint
`0`-simplices.
-/
theorem boundary_pathSimplex {a b : X} (p : Path a b) :
    (singularBoundary ℤ X 0).hom (chainGenerator ℤ X 1 (pathSimplex p))
      = chainGenerator ℤ X 0 (pointSimplex X b) - chainGenerator ℤ X 0 (pointSimplex X a) := by
  have hf (k : Fin 2) :
      AlexanderWhitney.faceSimplex X 0 k (pathSimplex p) =
        pointSimplex X (if k = 0 then b else a) := by
    apply singularSimplices_ext
    rw [faceSimplex_continuousMap]
    ext x
    simp only [pathSimplex, pointSimplex, singularSimplexAsContinuousMap,
      continuousMapAsSingularSimplex, Equiv.apply_symm_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, Homeomorph.symm_apply_apply, ContinuousMap.const_apply]
    fin_cases k
    · have h : stdSimplexHomeomorphUnitInterval (cofaceTop 0 0 x) = 1 := by
        apply Subtype.ext
        change (cofaceTop 0 0 x).val 1 = 1
        have hs := (cofaceTop 0 0 x).property.2
        rw [Fin.sum_univ_two] at hs
        have hz := cofaceTop_apply_base 0 0 x
        change (cofaceTop 0 0 x).val 0 = 0 at hz
        rw [hz, zero_add] at hs
        exact hs
      simp [h]
    · have h : stdSimplexHomeomorphUnitInterval (cofaceTop 0 1 x) = 0 := by
        apply Subtype.ext
        exact cofaceTop_apply_base 0 1 x
      simp [h]
  simp [singularBoundary_chainGenerator_formula, Fin.sum_univ_two, hf, sub_eq_add_neg]

/-- For points joined by a path, the difference of the corresponding `0`-simplex
generators is a boundary. -/
theorem chainGenerator_sub_mem_range_of_path {a b : X} (p : Path a b) :
    chainGenerator ℤ X 0 (pointSimplex X b) - chainGenerator ℤ X 0 (pointSimplex X a)
      ∈ LinearMap.range (singularBoundary ℤ X 0).hom :=
  ⟨chainGenerator ℤ X 1 (pathSimplex p), boundary_pathSimplex p⟩

/-
For points in the same (path-)connected space, the difference of their
`0`-simplex generators is a boundary.
-/
theorem chainGenerator_sub_mem_range [PathConnectedSpace X] (σ τ : singularSimplices X 0) :
    chainGenerator ℤ X 0 σ - chainGenerator ℤ X 0 τ
      ∈ LinearMap.range (singularBoundary ℤ X 0).hom := by
        have h_simplices : ∃ a b : X, σ = pointSimplex X a ∧ τ = pointSimplex X b := by
          refine' ⟨ _, _, _, _ ⟩;
          exact ( singularSimplexAsContinuousMap X 0 σ ) ( stdSimplex.vertex 0 );
          exact ( singularSimplexAsContinuousMap X 0 τ ) ( stdSimplex.vertex 0 );
          · apply singularSimplices_ext;
            ext x;
            simp only [pointSimplex, singularSimplexAsContinuousMap,
              continuousMapAsSingularSimplex, Equiv.apply_symm_apply,
              ContinuousMap.comp_apply, ContinuousMap.coe_mk,
              Homeomorph.symm_apply_apply, ContinuousMap.const_apply]
            exact congrArg (singularSimplexAsContinuousMap X 0 σ)
              (delta0_subsingleton x (stdSimplex.vertex 0))
          · apply singularSimplices_ext;
            exact ContinuousMap.ext fun x => by rw [ show x = stdSimplex.vertex 0 from delta0_subsingleton _ _ ] ; rfl;
        obtain ⟨ a, b, rfl, rfl ⟩ := h_simplices;
        have := chainGenerator_sub_mem_range_of_path ( PathConnectedSpace.somePath b a ) ; aesop;

/-! ## The augmentation -/

/-- The augmentation `ε : C₀(X; ℤ) → ℤ` summing the coefficients (each `0`-simplex
generator maps to `1`). -/
noncomputable def aug (X : TopCat.{0}) : singularChainGroup ℤ X 0 ⟶ ModuleCat.of ℤ ℤ :=
  Limits.Sigma.desc (fun _ => 𝟙 (ModuleCat.of ℤ ℤ))

@[simp] theorem aug_generator (σ : singularSimplices X 0) :
    (aug X).hom (chainGenerator ℤ X 0 σ) = 1 := by
  change ((Sigma.ι (fun _ : singularSimplices X 0 => ModuleCat.of ℤ ℤ) σ ≫ aug X).hom 1) = 1
  rw [aug, Sigma.ι_comp_desc]
  rfl

theorem aug_boundary (c : singularChainGroup ℤ X 1) :
    (aug X).hom ((singularBoundary ℤ X 0).hom c) = 0 := by
      refine' Submodule.span_induction _ _ _ _ ( show c ∈ Submodule.span ℤ ( Set.range ( fun τ : singularSimplices X 1 => chainGenerator ℤ X 1 τ ) ) from _ );
      · rw [chainGenerator_span_top]
        exact Submodule.mem_top
      · intro x hx
        obtain ⟨τ, rfl⟩ := hx
        have h_sum : (aug X).hom ((singularBoundary ℤ X 0).hom (chainGenerator ℤ X 1 τ)) = 0 := by
          rw [ singularBoundary_chainGenerator_formula ] ; simp +decide [ Fin.sum_univ_two ] ;
          rw [ aug_generator, aug_generator ] ; norm_num
        exact h_sum;
      · aesop;
      · aesop;
      · simp +contextual [ map_smul ]

/-
Every `0`-chain is, modulo boundaries, `ε(c)` copies of a fixed basepoint
`0`-simplex.
-/
theorem sub_aug_smul_basept_mem_range [PathConnectedSpace X] (b : X)
    (c : singularChainGroup ℤ X 0) :
    c - (aug X).hom c • chainGenerator ℤ X 0 (pointSimplex X b)
      ∈ LinearMap.range (singularBoundary ℤ X 0).hom := by
        -- Work additively: the basis chains generate the chain group as an additive
        -- subgroup, so we may induct over `AddSubgroup.closure`, avoiding the
        -- scalar-action instance diamond on the `ModuleCat ℤ` carrier.
        have h_span : c ∈ AddSubgroup.closure (Set.range (chainGenerator ℤ X 0)) := by
          have hc0 : c ∈ Submodule.span ℤ (Set.range (chainGenerator ℤ X 0)) := by
            rw [chainGenerator_span_top]; exact Submodule.mem_top
          induction hc0 using Submodule.span_induction with
          | mem y hy => exact AddSubgroup.subset_closure hy
          | zero => exact zero_mem _
          | add p q _ _ hp hq => exact add_mem hp hq
          | smul r a _ ha => convert zsmul_mem ha r using 1; exact int_smul_eq_zsmul _ r a
        induction h_span using AddSubgroup.closure_induction with
        | mem c hc =>
            obtain ⟨σ, rfl⟩ := hc
            rw [aug_generator, one_zsmul]
            exact chainGenerator_sub_mem_range σ (pointSimplex X b)
        | zero => simp
        | add x y _ _ hx hy =>
            have h : x + y - (aug X).hom (x + y) • chainGenerator ℤ X 0 (pointSimplex X b)
                = (x - (aug X).hom x • chainGenerator ℤ X 0 (pointSimplex X b))
                  + (y - (aug X).hom y • chainGenerator ℤ X 0 (pointSimplex X b)) := by
              rw [map_add, add_zsmul]; abel
            rw [h]; exact Submodule.add_mem _ hx hy
        | neg x _ hx =>
            have h : -x - (aug X).hom (-x) • chainGenerator ℤ X 0 (pointSimplex X b)
                = -(x - (aug X).hom x • chainGenerator ℤ X 0 (pointSimplex X b)) := by
              rw [map_neg, neg_zsmul]; abel
            rw [h]; exact Submodule.neg_mem _ hx

end SphereOddDegree