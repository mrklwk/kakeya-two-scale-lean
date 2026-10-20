module
public import KakeyaTwoScale.FrozenLocalPhysical

@[expose] public section

open Set Metric MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

/-- All represented old varieties receive actual constructed local seeds.
The common orientation set depends only on dimensions. Every incoming record
and tuple is inherited from the same frozen state; no local seed is a premise. -/
theorem exists_frozen_buffered_local_seeds (b c : ℕ) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin b ⊕ Fin c)),
    ∀ {J s k A Lh B depth : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
      (W : FrozenGeometryState (b+c) k T C O)
      (Y₀ : Finset T) (cube : T → C) (tube : T → Fin k → O)
      (cubes : Finset C) (Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c)))
      (P : W.Grain → Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
      (D : ℕ → ℕ),
      (∀ g ∈ W.grains cube, ∀ i, (P g i).totalDegree ≤ J) →
      (∀ g ∈ W.grains cube, ∀ x, rectangularPolynomialMap (P g) x=0 →
        (fderiv ℝ (rectangularPolynomialMap (P g)) x).range=⊤) →
      (∀ j < s, 2^j < (D j+1)^b) → 2 ≤ s →
      (∀ y ∈ W.tuples, cube y ∈ cubes) →
      (∀ q ∈ cubes, MeasurableSet (Q q)) → (∀ q ∈ cubes, volume (Q q) ≠ ⊤) →
      (∀ q ∈ cubes, 0 < volume.real (Q q)) → (∀ q ∈ cubes, IsPreconnected (Q q)) →
      ∀ (alpha η r δ R : ℝ), 0 < alpha → alpha ≤ 1 → 0 < δ → 2*δ < r →
      η+2*(η+r) ≤ R*δ → 0 ≤ (R+1)*δ →
      ∀ (tag : C → EuclideanSpace ℝ (Fin b ⊕ Fin c)),
      (∀ y ∈ W.tuples, rectangularPolynomialMap (P (W.grain (cube y))) (tag (cube y))=0) →
      (∀ q ∈ W.tuples.image cube, ∀ x ∈ Q q, dist x (tag q) < η) →
      (∀ g ∈ W.grains cube,
        Real.log (tupleCubeMass (W.grainTuples cube g) cube (W.grainCubes cube g) alpha) /
          (-Real.log ((2:ℝ)/2^s)) < depth) →
      0 < k → W.Valid Y₀ cube tube (fun q => physicalCoordinateCube (Q q)) δ →
      (∀ j, W.height j ≤ Lh) → (W.tuples.card:ℝ) ≤ (2:ℝ)^B →
      ∀ (center : C → EuclideanSpace ℝ (Fin (b+c))),
      (∀ q ∈ cubes, ∀ x ∈ physicalCoordinateCube (Q q), dist x (center q) ≤ (A:ℝ)*δ) →
      ∀ g ∈ W.grains cube,
        S.Nonempty ∧ Nonempty (ActualBufferedStageSeed (J:=J) (s:=s) (A:=A) (Lh:=Lh) (B:=B) (depth:=depth)
          (P g) D S (W.grainTuples cube g) cube tube (W.grainCubes cube g) Q
          (W.localPhysical cube g δ) alpha δ R) := by
  classical
  obtain ⟨S,hS⟩ := exists_actual_buffered_cube_forest b c
  refine ⟨S,?_⟩
  intro J s k A Lh B depth T C O instT instC W Y₀ cube tube cubes Q P D
    hdeg hreg hd hs hc hQ hf hpos hconn alpha η r δ R hp hp1 hδ hgap hR hR0
    tag htag hnear hdepth hk hv hh hbound center hdiam g hg
  have hsub : W.grainCubes cube g ⊆ cubes := by
    intro q hq
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
    exact hc y ((W.grainTuples_subset cube g) hy)
  have htag' : ∀ q ∈ W.grainCubes cube g, rectangularPolynomialMap (P g) (tag q)=0 := by
    intro q hq
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
    have hy' := Finset.mem_filter.mp hy
    simpa only [hy'.2] using htag y hy'.1
  have hcard : ((W.grainTuples cube g).card:ℝ) ≤ (2:ℝ)^B :=
    (show ((W.grainTuples cube g).card:ℝ) ≤ W.tuples.card by
      exact_mod_cast Finset.card_le_card (W.grainTuples_subset cube g)).trans hbound
  let root := W.grainCubes cube g
  let Y := W.grainTuples cube g
  have hr : root.Nonempty := (W.grainTuples_nonempty cube hg).image cube
  have hactive : ∀ q ∈ root, 1 ≤ ParentLevel.capacity Y cube q :=
    fun q hq => W.grainCubes_active cube hq
  have htotal : ownedCubeMass (bufferedTupleWeight Y cube alpha) root =
      tupleCubeMass Y cube root alpha := by
    apply Finset.sum_congr rfl
    intro q hq
    exact max_eq_right (Real.one_le_rpow (by exact_mod_cast hactive q hq) hp.le)
  have hradius : 0 < r := by linarith
  obtain ⟨forest⟩ := hS (P g) (hdeg g hg) (hreg g hg) D hd hs root hr Q
    (bufferedTupleWeight Y cube alpha)
    (fun q hq => hQ q (hsub hq)) (fun q hq => hf q (hsub hq))
    (fun q hq => hpos q (hsub hq)) (fun q hq => hconn q (hsub hq))
    (fun q => le_max_left _ _) tag htag' η r hradius
    (fun q hq => hnear q (Finset.image_subset_image (W.grainTuples_subset cube g) hq))
    depth (by simpa only [htotal] using hdepth g hg)
  have hn : S.Nonempty := ⟨(forest.node root (Finset.Subset.refl _) hr).data.orientation,
    (forest.node root (Finset.Subset.refl _) hr).data.orientation_mem⟩
  refine ⟨hn,?_⟩
  exact exists_seed_of_actual_buffered_forest (A:=A) (Lh:=Lh) (B:=B)
    (P g) (hdeg g hg) D S Y cube tube root hr Q alpha η r δ R hp hp1 hδ hradius
    hgap hR hR0 hactive (fun q hq => hconn q (hsub hq)) forest hk
    (W.localPhysical cube g δ) (W.localPhysical_valid Y₀ cube tube _ g hδ hv hh)
    hcard center (fun q hq => hdiam q (hsub hq))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_frozen_buffered_local_seeds
