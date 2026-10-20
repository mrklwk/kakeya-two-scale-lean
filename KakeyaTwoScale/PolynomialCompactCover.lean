module
public import KakeyaTwoScale.OccupiedGridCubeCount
public import KakeyaTwoScale.GridIntegerBank

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- A uniform finite ball cover of an actual regular polynomial zero set in a
closed ball. All grid choices, terminal faces, components, labels and finite
cube counts are constructed from the original equations and their rank. -/
theorem regular_polynomial_compact_cover {d s D : ℕ}
    (P : Fin s→MvPolynomial (Fin d) ℝ) (hP : ∀ j, (P j).totalDegree≤D)
    (hreg : ∀ x, rectangularPolynomialMap P x=0 →
      (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤)
    (a : EuclideanSpace ℝ (Fin d)) (R : ℝ) (hR : 0≤R) (h : ℝ) (hh : 0<h) :
    ∃ centers : Finset (EuclideanSpace ℝ (Fin d)),
      {x | rectangularPolynomialMap P x=0} ∩ closedBall a R ⊆
        ⋃ c∈centers, ball c ((d+2)*h) ∧
      centers.card≤(2^d*(gridLabelBank (⌈R/h⌉₊+2)).card^(d-s))*((4*max D 1+5)^d*2^d) := by
  classical
  obtain ⟨theta,htheta,_,hgrid⟩ := regular_polynomial_transverse_grid P hreg a h hh
  let N := ⌈R/h⌉₊+2
  let A := (gridIndexBank d N).filter (fun k => ∃ x : EuclideanSpace ℝ (Fin d),
    rectangularPolynomialMap P x=0 ∧ x∈closedGridFace a.ofLp theta h k (fun _=>none) ∧
      x∈closedBall a R)
  have hocc (k) (hk : k∈A) : ∃ x : EuclideanSpace ℝ (Fin d),
      rectangularPolynomialMap P x=0 ∧ x∈closedGridFace a.ofLp theta h k (fun _=>none) ∧
        x∈closedBall a R := (Finset.mem_filter.mp hk).2
  have hcount := occupied_grid_cubes_card_le P hP a theta h hh
    (fun J z x hx hp => hgrid J z x hx (fun j hj => hp j hj)) R hR A hocc
    (gridLabelBank N) (gridLabelBank_nonempty N)
    (fun k hk => gridLabelBank_mem_of_cube k (Finset.mem_filter.mp hk).1)
  have hw (k : A) : ∃ x : EuclideanSpace ℝ (Fin d), rectangularPolynomialMap P x=0 ∧
      x∈closedGridFace a.ofLp theta h k (fun _=>none) ∧ x∈closedBall a R := hocc k k.property
  choose w hw using hw
  let centers := Finset.univ.image w
  refine ⟨centers,?_,?_⟩
  · intro x hx
    let k := coordinateGridIndex a.ofLp theta h x
    have hxk : x∈closedGridFace a.ofLp theta h k (fun _=>none) := mem_grid_cube_floor _ _ _ hh x
    have hkB : k∈gridIndexBank d N := by
      apply (mem_gridIndexBank k).mpr
      intro j
      have hb := occupied_cube_integer_bound a theta h htheta hh R k x hxk hx.2 j
      exact_mod_cast hb
    have hkA : k∈A := Finset.mem_filter.mpr ⟨hkB,x,hx.1,hxk,hx.2⟩
    let ka : A := ⟨k,hkA⟩
    apply mem_iUnion₂.mpr
    refine ⟨w ka,Finset.mem_image.mpr ⟨ka,Finset.mem_univ _,rfl⟩,?_⟩
    have hd := closed_grid_cube_diameter a.ofLp theta h hh.le k x (w ka) hxk (hw ka).2.1
    change dist x (w ka)<(d+2)*h
    nlinarith
  · have hc : centers.card≤A.card := by
      have hb := Finset.card_image_le (s := Finset.univ) (f := w)
      simpa only [Finset.card_univ,Fintype.card_coe] using hb
    exact hc.trans hcount

end KakeyaTwoScale
#print axioms KakeyaTwoScale.regular_polynomial_compact_cover
