module
/- Modified for Lean 4.34.1 and current mathlib compatibility.
See vendor/HamSandwich/README.md and source-lock.json for provenance and changes. -/
public import HamSandwich.SphereOddDegree.AlgebraicTopology.SingularH0PathConnected
public import HamSandwich.SphereOddDegree.AlgebraicTopology.SubChainSubspaceBridge
public import HamSandwich.SphereOddDegree.AlgebraicTopology.SingularHomologyFunctorAPI
public import Mathlib

@[expose] public section

/-!
# Zeroth singular homology of path-connected spaces, general coefficients

General-coefficient (`R : CommRing`) version of the augmentation computation
`H₀(X; R) ≅ R` for nonempty path-connected `X`, mirroring the integral
development in `SingularH0.lean` / `SingularH0PathConnected.lean`. The mod-two
instance is the case `R = ZMod 2`, used for `H₁(Sⁿ; F₂) = 0`.

The point-simplex `pointSimplex` and path-simplex `pathSimplex` are
coefficient-independent, so they are reused from `SingularH0.lean`.
-/

open CategoryTheory AlgebraicTopology Limits
open SphereOddDegree.AffineBarycentricSubdivision

noncomputable section
namespace SphereOddDegree
namespace H0Gen

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-- The augmentation `ε : C₀(X; R) → R` summing the coefficients. -/
noncomputable def aug (R : Type) [CommRing R] (X : TopCat.{0}) :
    singularChainGroup R X 0 ⟶ ModuleCat.of R R :=
  Limits.Sigma.desc (fun _ => 𝟙 (ModuleCat.of R R))

@[simp] theorem aug_generator (σ : singularSimplices X 0) :
    (aug R X).hom (chainGenerator R X 0 σ) = 1 := by
  change ((Sigma.ι (fun _ : singularSimplices X 0 => ModuleCat.of R R) σ ≫ aug R X).hom 1) = 1
  rw [aug, Sigma.ι_comp_desc]
  rfl

theorem boundary_pathSimplex {a b : X} (p : Path a b) :
    (singularBoundary R X 0).hom (chainGenerator R X 1 (pathSimplex p))
      = chainGenerator R X 0 (pointSimplex X b) - chainGenerator R X 0 (pointSimplex X a) := by
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

theorem chainGenerator_sub_mem_range_of_path {a b : X} (p : Path a b) :
    chainGenerator R X 0 (pointSimplex X b) - chainGenerator R X 0 (pointSimplex X a)
      ∈ LinearMap.range (singularBoundary R X 0).hom :=
  ⟨chainGenerator R X 1 (pathSimplex p), boundary_pathSimplex p⟩

theorem chainGenerator_sub_mem_range [PathConnectedSpace X] (σ τ : singularSimplices X 0) :
    chainGenerator R X 0 σ - chainGenerator R X 0 τ
      ∈ LinearMap.range (singularBoundary R X 0).hom := by
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
        have := chainGenerator_sub_mem_range_of_path (R := R) ( PathConnectedSpace.somePath b a ) ; aesop;

theorem aug_boundary (c : singularChainGroup R X 1) :
    (aug R X).hom ((singularBoundary R X 0).hom c) = 0 := by
  have h_ind : ∀ c : singularChainGroup R X 1, (aug R X).hom ((singularBoundary R X 0).hom c) = 0 := by
    intro c
    have h_c : c ∈ Submodule.span R (Set.range (fun τ : singularSimplices X 1 => chainGenerator R X 1 τ)) := by
      convert Submodule.mem_top ( x := c );
      ext; simp [chainGenerator_span_top]
    refine' Submodule.span_induction _ _ _ _ h_c <;> simp_all +decide [ Submodule.mem_span ];
    intro τ; rw [ singularBoundary_chainGenerator_formula ] ; simp +decide [ Fin.sum_univ_two, aug_generator ] ;
    rw [ aug_generator, aug_generator, add_neg_cancel ];
  exact h_ind c

theorem sub_aug_smul_basept_mem_range [PathConnectedSpace X] (b : X)
    (c : singularChainGroup R X 0) :
    c - (aug R X).hom c • chainGenerator R X 0 (pointSimplex X b)
      ∈ LinearMap.range (singularBoundary R X 0).hom := by
  have h_span : c ∈ Submodule.span R (Set.range (chainGenerator R X 0)) := by
    rw [chainGenerator_span_top]; exact Submodule.mem_top
  induction' h_span using Submodule.span_induction with c hc c₁ c₂ hc₁ hc₂ c hc ih;
  · obtain ⟨ σ, rfl ⟩ := hc;
    have := chainGenerator_sub_mem_range ( R := R ) σ ( pointSimplex X b );
    convert this using 1 ; simp +decide [ aug_generator ];
    erw [ H0Gen.aug_generator ] ; norm_num;
  · simp +decide [ ModuleCat.Hom.hom ];
  · convert Submodule.add_mem _ c hc using 1 ; simp +decide [ add_smul, sub_add_sub_comm ];
  · rename_i k hk;
    obtain ⟨ y, hy ⟩ := hk; use ih • y; simp +decide [ hy, mul_assoc, mul_left_comm, mul_comm ] ;
    simp +decide [ mul_assoc, mul_left_comm, smul_sub, smul_smul ]

theorem prev_zero : (ComplexShape.down ℕ).prev 0 = 1 := by simp [ComplexShape.prev]

theorem aug_comp_boundary_eq_zero (Y : TopCat.{0}) :
    (singularChainComplex R Y).d 1 0 ≫ aug R Y = 0 := by
  ext c;
  exact aug_boundary c

/-- The augmentation descended to degree-0 homology `H₀(Y; R) → R`. -/
def H0aug (R : Type) [CommRing R] (Y : TopCat.{0}) :
    (singularChainComplex R Y).homology 0 ⟶ ModuleCat.of R R :=
  (singularChainComplex R Y).homologyι 0 ≫
    (singularChainComplex R Y).descOpcycles (aug R Y) 1 prev_zero (aug_comp_boundary_eq_zero Y)

theorem H0aug_natural {Y Z : TopCat.{0}} (f : Y ⟶ Z) :
    HomologicalComplex.homologyMap
        (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map f) 0
        ≫ H0aug R Z
      = H0aug R Y := by
  unfold H0aug;
  have h_comm : (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map f).f 0 ≫ aug R Z = aug R Y := by
    simp +decide [ CategoryTheory.Category.assoc, singularChainComplexFunctor, aug ];
    simp +decide [ CategoryTheory.Functor.map, _root_.SSet.chainComplexFunctor ];
    ext; simp +decide [ CategoryTheory.Functor.map, _root_.SSet.chainComplexFunctor ] ;
  simp +decide [ ← h_comm, ← CategoryTheory.Category.assoc, HomologicalComplex.homologyι, HomologicalComplex.descOpcycles ];
  simp +decide [ HomologicalComplex.sc, HomologicalComplex.homologyι ];
  erw [ CategoryTheory.ShortComplex.homologyι_naturality_assoc ];
  simp +decide [ HomologicalComplex.shortComplexFunctor, HomologicalComplex.descOpcycles ]

instance isIso_homologyι_zero (Y : TopCat.{0}) :
    IsIso ((singularChainComplex R Y).homologyι 0) :=
  HomologicalComplex.isIso_homologyι (singularChainComplex R Y) 0 ((ComplexShape.down ℕ).next 0)
    rfl ((singularChainComplex R Y).shape _ _ (by simp [ComplexShape.next]))

theorem isIso_descOpcycles_aug (Y : TopCat.{0}) [Nonempty Y] [PathConnectedSpace Y] :
    IsIso ((singularChainComplex R Y).descOpcycles (aug R Y) 1 prev_zero
      (aug_comp_boundary_eq_zero Y)) := by
  have h_bijective : Function.Bijective (HomologicalComplex.descOpcycles (singularChainComplex R Y) (aug R Y) 1 prev_zero (aug_comp_boundary_eq_zero Y)).hom := by
    constructor;
    · intro x y hxy
      obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective ( singularChainComplex R Y |>.pOpcycles 0 )).mp ( by infer_instance ) x
      obtain ⟨d, hd⟩ := (ModuleCat.epi_iff_surjective ( singularChainComplex R Y |>.pOpcycles 0 )).mp ( by infer_instance ) y
      have haug : (aug R Y).hom c = (aug R Y).hom d := by
        have hc' := congrArg (fun f => f.hom c)
          (HomologicalComplex.p_descOpcycles (singularChainComplex R Y)
            (aug R Y) 1 prev_zero (aug_comp_boundary_eq_zero Y))
        have hd' := congrArg (fun f => f.hom d)
          (HomologicalComplex.p_descOpcycles (singularChainComplex R Y)
            (aug R Y) 1 prev_zero (aug_comp_boundary_eq_zero Y))
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hc] at hc'
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hd] at hd'
        exact hc'.symm.trans (hxy.trans hd')
      have h_diff : c - d ∈ LinearMap.range (singularBoundary R Y 0).hom := by
        have := sub_aug_smul_basept_mem_range ( R := R ) ( Classical.arbitrary Y ) ( c - d ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
      have h_zero : (singularChainComplex R Y |>.pOpcycles 0) c = (singularChainComplex R Y |>.pOpcycles 0) d := by
        obtain ⟨ e, he ⟩ := h_diff; simp_all +decide [ sub_eq_iff_eq_add ] ;
        have h_zero : (singularChainComplex R Y |>.pOpcycles 0) (c - d) = 0 := by
          convert congr_arg ( fun x => ( singularChainComplex R Y |>.pOpcycles 0 ) x ) he.symm using 1 ; simp +decide [ ← CategoryTheory.comp_apply, singularBoundary ] ;
        simp_all +decide [ sub_eq_iff_eq_add ]
      simp_all +decide [ Function.Injective ];
    · intro r
      use (singularChainComplex R Y).pOpcycles 0 (r • chainGenerator R Y 0 (pointSimplex Y (Classical.arbitrary Y)));
      convert congr_arg ( fun f => f ( r • chainGenerator R Y 0 ( pointSimplex Y ( Classical.arbitrary Y ) ) ) ) ( HomologicalComplex.p_descOpcycles ( singularChainComplex R Y ) ( aug R Y ) 1 prev_zero ( by simp [ aug_comp_boundary_eq_zero ] ) ) using 1 ; simp +decide [ aug_generator ];
      erw [ H0Gen.aug_generator ] ; aesop;
  convert ( ConcreteCategory.isIso_iff_bijective _ ).mpr h_bijective

/-- **The augmentation is an isomorphism on `H₀` of a nonempty path-connected
space.** -/
instance isIso_H0aug (Y : TopCat.{0}) [Nonempty Y] [PathConnectedSpace Y] :
    IsIso (H0aug R Y) := by
  have := isIso_descOpcycles_aug (R := R) Y
  unfold H0aug
  infer_instance

/-- The subspace augmentation on `H₀` of a subordinate-chain complex. -/
def subH0aug (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X) :
    (subChainComplex R X S).homology 0 ⟶ ModuleCat.of R R :=
  (subspaceHomologyIso S 0).hom ≫ H0aug R (TopCat.of S)

instance isIso_subH0aug (X : TopCat.{0}) (S : Set X) [Nonempty S] [PathConnectedSpace S] :
    IsIso (subH0aug R X S) := by
  unfold subH0aug
  infer_instance

theorem subChainCorestrict_inclusion_square (X : TopCat.{0}) (S T : Set X) (h : S ⊆ T) :
    subChainCorestrict R X S ≫ subChainInclusion S T h
      = ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
          (setInclusionTopCat X S T h) ≫ subChainCorestrict R X T := by
  ext n c
  apply Subtype.ext
  change (singularChainMap R (sInclusion S) n).hom c =
    (singularChainMap R (sInclusion T) n).hom
      ((singularChainMap R (setInclusionTopCat X S T h) n).hom c)
  have hc := singularChainMap_comp R (setInclusionTopCat X S T h) (sInclusion T) n
  exact congrArg (fun f => f.hom c) hc

theorem subH0aug_natural_inclusion (X : TopCat.{0}) (S T : Set X) (h : S ⊆ T) :
    HomologicalComplex.homologyMap (subChainInclusion S T h) 0 ≫ subH0aug R X T
      = subH0aug R X S := by
  have hs := congrArg (fun f => HomologicalComplex.homologyMap f 0)
    (subChainCorestrict_inclusion_square (R := R) X S T h)
  simp only [HomologicalComplex.homologyMap_comp] at hs
  unfold subH0aug
  simp only [subspaceHomologyIso, Iso.symm_hom,
    Functor.mapIso_inv, asIso_inv, Functor.map_inv]
  change HomologicalComplex.homologyMap (subChainInclusion S T h) 0 ≫
      (inv (HomologicalComplex.homologyMap (subChainCorestrict R X T) 0) ≫ H0aug R (TopCat.of T)) =
    inv (HomologicalComplex.homologyMap (subChainCorestrict R X S) 0) ≫ H0aug R (TopCat.of S)
  rw [← Category.assoc, ← CategoryTheory.cancel_epi
    (HomologicalComplex.homologyMap (subChainCorestrict R X S) 0)]
  simp only [← Category.assoc]
  rw [hs]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  exact H0aug_natural (setInclusionTopCat X S T h)

end H0Gen
end SphereOddDegree