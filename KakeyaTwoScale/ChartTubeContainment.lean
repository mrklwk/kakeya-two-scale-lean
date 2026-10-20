module
public import KakeyaTwoScale.EuclideanCharts
public import KakeyaTwoScale.HeightRescaling

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

def chartIntercept {n : ℕ} (i : Fin (n+1)) (b u : EuclideanSpace ℝ (Fin (n+1)))
    (s : ℝ) : Fin n → ℝ := fun j => b (i.succAbove j)+(s-b i)*chartSlope i u j

/-- Exact reconstruction of the axis in the chosen, height-rescaled chart. -/
theorem chart_axis_identity {n : ℕ} (i : Fin (n+1)) (b u : EuclideanSpace ℝ (Fin (n+1)))
    (hui : u i ≠ 0) (s L t : ℝ) :
    euclideanSplit i (b+((s+L*t-b i)/u i) • u) =
      (s+L*t,segmentPoint (chartIntercept i b u s) (L • chartSlope i u) t) := by
  apply Prod.ext
  · dsimp [euclideanSplit]
    field_simp
    ring
  · funext j
    simp only [euclideanSplit,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,
      segmentPoint,chartIntercept,chartSlope,Pi.add_apply,Pi.smul_apply]
    field_simp
    ring

/-- The selected common height interval gives actual segment parameters. -/
theorem chart_parameter_mem {a v s L t : ℝ} (hv : 0 < v) (hL : 0 ≤ L)
    (hlo : a ≤ s) (hhi : s+L ≤ a+v) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (s+L*t-a)/v ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · apply div_nonneg _ hv.le
    nlinarith [ht.1]
  · apply (div_le_iff₀ hv).mpr
    nlinarith [ht.2]

/-- Strict containment in actual open Euclidean tubes. The graph-tube radius
rho may be closed; the strict dimensional radius margin ensures containment. -/
theorem chart_graph_inside_euclideanTube {n : ℕ} (i : Fin (n+1))
    (b u : EuclideanSpace ℝ (Fin (n+1))) {s L r rho : ℝ}
    (hui : 0 < u i) (hL : 0 ≤ L) (hrho : 0 ≤ rho) (hmargin : (n+2:ℝ)*rho < r)
    (hlo : b i ≤ s) (hhi : s+L ≤ b i+u i) :
    horizontalTube (chartIntercept i b u s) (L • chartSlope i u) rho ⊆
      (fun p => euclideanUnsplit i (heightAffine s L p)) ⁻¹' euclideanTube b u r := by
  intro p hp
  let tau := (s+L*p.1-b i)/u i
  have htau := chart_parameter_mem hui hL hlo hhi hp.1
  refine ⟨tau,htau,?_⟩
  let y := b+tau • u
  let x := euclideanUnsplit i (heightAffine s L p)
  have hy := chart_axis_identity i b u hui.ne' s L p.1
  have hx := euclideanSplit_unsplit i (heightAffine s L p)
  have hcoord : ∀ j, |(x-y) j| ≤ rho := by
    refine (Fin.forall_iff_succAbove i (P:=fun j => |(x-y) j| ≤ rho)).mpr ?_
    constructor
    · have hx' := congrArg Prod.fst hx
      have hy' := congrArg Prod.fst hy
      change x i=s+L*p.1 at hx'
      change y i=s+L*p.1 at hy'
      simpa [PiLp.sub_apply,hx',hy'] using hrho
    · intro j
      have hx' := congrFun (congrArg Prod.snd hx) j
      have hy' := congrFun (congrArg Prod.snd hy) j
      change x (i.succAbove j)=p.2 j at hx'
      change y (i.succAbove j)=
        segmentPoint (chartIntercept i b u s) (L • chartSlope i u) p.1 j at hy'
      have hh := (dist_le_pi_dist p.2
        (segmentPoint (chartIntercept i b u s) (L • chartSlope i u) p.1) j).trans hp.2
      simpa only [PiLp.sub_apply,hx',hy',Real.dist_eq] using hh
  have hh := euclidean_norm_of_coordinate_bound (x-y) rho hrho hcoord
  exact (show dist x y ≤ (n+2:ℝ)*rho by rwa [dist_eq_norm]).trans_lt hmargin

end KakeyaTwoScale
#print axioms KakeyaTwoScale.chart_axis_identity
#print axioms KakeyaTwoScale.chart_parameter_mem
#print axioms KakeyaTwoScale.chart_graph_inside_euclideanTube
