module
public import KakeyaTwoScale.TransverseCoordinateGrid
public import KakeyaTwoScale.ActualPolynomialArchive

@[expose] public section

open Set
open scoped ContDiff
noncomputable section
namespace KakeyaTwoScale

/-- Actual rank rules out grid intersections beyond the remaining dimension. -/
theorem coordinateGridRegular_dimension_le
    {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {d : ℕ}
    (f : E→F) (g : Fin d→E→ℝ) (c : F) (h : ℝ) (theta : Fin d→ℝ)
    (S : Finset (Fin d)) (hgrid : coordinateGridRegular f g c h theta S)
    (J : Finset (Fin d)) (hJ : J⊆S) (z : Fin d→ℤ) (x : E)
    (hx : f x=c) (hxg : ∀ j∈J, g j x=theta j+z j*h) :
    Module.finrank ℝ F+J.card≤Module.finrank ℝ E := by
  have hr := hgrid J hJ z x hx hxg
  have hd := LinearMap.finrank_le_finrank_of_surjective (LinearMap.range_eq_top.mp hr)
  simpa using hd

/-- Every globally regular polynomial zero set admits a translated coordinate
grid whose faces above its codimension budget miss the actual zero set. The
mesh and center are arbitrary; no quantitative lower bound on minors is used. -/
theorem regular_polynomial_transverse_grid {d s : ℕ}
    (P : Fin s→MvPolynomial (Fin d) ℝ)
    (hreg : ∀ x, rectangularPolynomialMap P x=0 →
      (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤)
    (center : EuclideanSpace ℝ (Fin d)) (h : ℝ) (hh : 0<h) :
    ∃ theta : Fin d→ℝ, (∀ j, theta j∈Ioo 0 h) ∧
      coordinateGridRegular (rectangularPolynomialMap P)
        (fun j x => x j-center j) 0 h theta Finset.univ ∧
      ∀ (J : Finset (Fin d)) (z : Fin d→ℤ) (x : EuclideanSpace ℝ (Fin d)),
        rectangularPolynomialMap P x=0 →
        (∀ j∈J, x j=center j+theta j+z j*h) → s+J.card≤d := by
  have hg (j : Fin d) : ContDiff ℝ ∞
      (fun x : EuclideanSpace ℝ (Fin d) => x j-center j) :=
    (contDiff_piLp_apply (𝕜 := ℝ) (p := (2 : ENNReal)) (i := j)).sub contDiff_const
  obtain ⟨theta,ht,hgrid⟩ := exists_transverse_coordinate_grid
    (rectangularPolynomialMap P) (fun j x => x j-center j) 0
    (rectangularPolynomialMap_contDiff P ∞) hg hreg h hh Finset.univ
  refine ⟨theta,fun j => ht j (Finset.mem_univ j),hgrid,?_⟩
  intro J z x hx hxg
  have hb := coordinateGridRegular_dimension_le _ _ _ _ _ _ hgrid J
    (Finset.subset_univ J) z x hx (fun j hj => by have := hxg j hj; linarith)
  simpa using hb

namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O}
    {P U : ℝ} {fuel : ℕ}

/-- The grid construction applies to ORIGINAL archive equations, whose rank
is proved by the archive. Zero-padded capture equations are not used here. -/
theorem polynomialSnapshot_transverse_grid
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (S : PolynomialArchiveSnapshot k T C O) (hS : S∈H.polynomialSnapshots)
    (g : S.state.Grain) (hg : g∈S.state.grains I.cube)
    (center : EuclideanSpace ℝ (Fin S.dimension)) (h : ℝ) (hh : 0<h) :
    ∃ theta : Fin S.dimension→ℝ, (∀ j, theta j∈Ioo 0 h) ∧
      coordinateGridRegular (rectangularPolynomialMap (S.equations g))
        (fun j x => x j-center j) 0 h theta Finset.univ ∧
      ∀ (J : Finset (Fin S.dimension)) (z : Fin S.dimension→ℤ)
        (x : EuclideanSpace ℝ (Fin S.dimension)),
        x∈S.zeroSet g → (∀ j∈J, x j=center j+theta j+z j*h) →
        S.codimension+J.card≤S.dimension :=
  regular_polynomial_transverse_grid (S.equations g)
    ((H.polynomialSnapshots_sound S hS).2.1 g hg) center h hh

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.coordinateGridRegular_dimension_le
#print axioms KakeyaTwoScale.regular_polynomial_transverse_grid
#print axioms KakeyaTwoScale.ActualBufferedArchive.polynomialSnapshot_transverse_grid
