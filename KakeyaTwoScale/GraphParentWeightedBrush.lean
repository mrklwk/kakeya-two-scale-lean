module
public import KakeyaTwoScale.GraphParentCapsule
public import KakeyaTwoScale.VariableWeightedBrush

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

theorem graph_base_norm {n : ℕ} (i : Fin (n+1)) (b : Fin n → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hb : ‖b‖ ≤ R) :
    ‖euclideanUnsplit i (0,b)‖ ≤ (n+2:ℝ)*R := by
  apply euclidean_norm_of_coordinate_bound _ _ hR
  apply (Fin.forall_iff_succAbove i (P:=fun j => |euclideanUnsplit i (0,b) j| ≤ R)).mpr
  constructor
  · simpa [unsplit_height] using hR
  · intro j
    rw [unsplit_horizontal]
    have hh : |b j| ≤ ‖b‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm b j
    exact hh.trans hb

/-- Source-facing graph-parent brush. Horizontal closed-sup parents and their
original high-overlap capture are converted internally to capsules about the
exact finite graph axes. All constants precede the dyadic scale. -/
theorem graph_parent_weighted_brush (n k : ℕ) (R eta B C : ℝ) (shift : ℕ)
    (hR : 0 ≤ R) (heta : 0 < eta) (hB : 0 < B) (hC : 0 ≤ C)
    (hD : 4*(n+2:ℝ)+1 ≤ (2:ℝ)^shift) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, shift+1 ≤ q →
      ∀ {J : Type*} (G S : Finset J), S ⊆ G →
      ∀ (b v : J → Fin n → ℝ) (w : J → ℝ),
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖v j‖ ≤ R) → (∀ j ∈ G, 0 ≤ w j) →
      ∀ i : Fin (n+1),
      (∀ e : EuclideanSpace ℝ (Fin (n+1)), ‖e‖=1 →
        (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (graphUnitDirection i (v j)) e| ≤
          (2:ℝ)^shift*dyadicRadius q), w j) ≤ B) →
      ∀ (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))))
        (p : ℝ × (Fin n → ℝ)) (M : ℝ),
      Module.finrank ℝ H=k+1 → 0 ≤ M →
      (∀ j ∈ S, p ∈ horizontalTube (b j) (v j) (4*dyadicRadius q)) →
      (∀ j ∈ S, planeAngle H (graphUnitDirection i (v j)) ≤ C*dyadicRadius q) →
      (∀ j ∈ S, eta*(dyadicRadius q)^n ≤ volume.real
        (horizontalTube (b j) (v j) (4*dyadicRadius q) ∩
          {x | M ≤ weightedOverlap G (fun j => horizontalTube (b j) (v j) (4*dyadicRadius q)) w x})) →
      c*(dyadicRadius q)^n*((dyadicRadius q)^(k+1))^theta*M*(∑ j ∈ S, w j) ≤
        (q:ℝ)*volume.real (⋃ j ∈ G, euclideanTube (euclideanUnsplit i (0,b j))
          (euclideanUnsplit i (1,v j)) ((2:ℝ)^shift*dyadicRadius q)) := by
  let D : ℝ := (2:ℝ)^shift
  let L : ℝ := (n+2:ℝ)*(R+1)
  let lam := eta/(3*L*(2*(n+3:ℝ))^n*D^n)
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hL : 1 ≤ L := by dsimp [L]; have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; nlinarith
  have hlam : 0 < lam := by
    have hLp : 0 < L := by linarith
    dsimp [lam]
    positivity
  obtain ⟨c,hc,hbrush⟩ := scaled_variable_weighted_brush n k ((n+2:ℝ)*R) lam B C L
    (by positivity) hlam hB hC hL
  refine ⟨c,hc,?_⟩
  intro q hq J G S hSG b v w hb hv hw i hcap H p M hdim hM hp ha hcapture
  let r := dyadicRadius q
  let bb := fun j => euclideanUnsplit i (0,b j)
  let uu := fun j => graphUnitDirection i (v j)
  let ell := fun j => ‖euclideanUnsplit i (1,v j)‖
  have hr : 0 < r := Real.exp_pos _
  have hwidth : D*r ≤ 1/2 := by
    dsimp [D,r]
    rw [dyadicRadius_enlarge shift q (by omega)]
    exact dyadicRadius_le_half (by omega)
  have haxis (j) : ell j • uu j=euclideanUnsplit i (1,v j) := NormedSpace.norm_smul_normalize _
  have hlen (j) (hj : j ∈ G) : 1 ≤ ell j ∧ ell j ≤ L :=
    ⟨(graph_axis_length i (v j) R hR (hv j hj)).1,(graph_axis_length i (v j) R hR (hv j hj)).2.1⟩
  have hpoint (j) (hj : j ∈ S) : euclideanUnsplit i p ∈ euclideanTube (bb j) (ell j • uu j) (D*r) := by
    rw [haxis]
    exact horizontal_parent_subset_capsule_width i (b j) (v j) r D hr hD ⟨p,hp j hj,rfl⟩
  have hcaptured (j) (hj : j ∈ S) : lam*volume.real (euclideanTube (bb j) (ell j • uu j) (D*r)) ≤
      volume.real (euclideanTube (bb j) (ell j • uu j) (D*r) ∩
        tubeHighSet G bb (fun j => ell j • uu j) w (D*r) M) := by
    simp_rw [haxis]
    exact graph_parent_relative_capture i G b v w hw r M D L eta hr hD hwidth hL heta.le j
      (hlen j (hSG hj)).2 (hcapture j hj)
  have hh := hbrush shift q hq G S hSG bb uu ell w hlen
    (fun j hj => graph_base_norm i (b j) R hR (hb j hj))
    (fun j _ => graphUnitDirection_norm i (v j)) hw hcap H (euclideanUnsplit i p) M
    hdim hM hpoint ha hcaptured
  simpa only [haxis] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.graph_base_norm
#print axioms KakeyaTwoScale.graph_parent_weighted_brush
