module
public import KakeyaTwoScale.BroadGreedyTuples
public import KakeyaTwoScale.GramRecursion

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Every actually constructed tuple has the quantitative Gram-volume
lower bound, with the first unit vector contributing exactly one. -/
theorem broadGreedyTuples_wedge_lower {n N : ℕ}
    (G : Finset (Fin N)) (u : Fin N → EuclideanSpace ℝ (Fin n))
    (eta : ℝ) (heta : 0≤eta) (hu : ∀ j∈G, ‖u j‖=1)
    (m : ℕ) (f : Fin (m+1) → Fin N) (hf : f∈broadGreedyTuples G u eta m) :
    eta^m≤tupleWedgeVolume (fun i => u (f i)) := by
  induction m with
  | zero =>
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hf
    rw [tupleWedgeVolume_singleton,hu j hj,pow_zero]
  | succ m ih =>
    obtain ⟨g,hg,hf⟩ := Finset.mem_biUnion.mp hf
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hf
    have he : (fun i => u (Fin.cons (α:=fun _ : Fin (m+2) => Fin N) j g i))=
        Fin.cons (α:=fun _ : Fin (m+2) => EuclideanSpace ℝ (Fin n)) (u j) (fun i => u (g i)) := by
      funext i
      refine Fin.cases ?_ (fun l => ?_) i <;> simp
    rw [he,pow_succ]
    exact tupleWedgeVolume_cons_lower (fun i => u (g i)) (u j) (eta^m) eta heta
      (ih g hg) (Finset.mem_filter.mp hj).2

/-- Explicit positive broad coefficient, uniform over radius and family. -/
def broadCoefficient (m : ℕ) (B : ℝ) : ℝ :=
  ((1/2:ℝ)^m)^((1:ℝ)/(m+1))* (2/Real.pi)^((m:ℝ)/B)

theorem broadCoefficient_pos (m : ℕ) (B : ℝ) : 0<broadCoefficient m B := by
  unfold broadCoefficient
  positivity

/-- The source's actual non-narrow finite incident family supplies the
pointwise multilinear lower bound. No good-tuple/count/wedge premises remain. -/
theorem broad_multilinear_pointwise {n N m : ℕ}
    (G : Finset (Fin N)) (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n)))
    (rho B : ℝ) (hrho : 0<rho) (hB : 0<B) (hkn : m+1≤n)
    (hu : ∀ j∈G, ‖u j‖=1)
    (hbroad : ∀ H : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
      Module.finrank ℝ H=m →
      ((G.filter fun j => planeAngle H (u j)≤rho).card:ℝ)<(G.card:ℝ)/2)
    (x : EuclideanSpace ℝ (Fin n)) (hincident : ∀ j∈G, x∈T j) :
    broadCoefficient m B*rho^((m:ℝ)/B)*(G.card:ℝ) ≤
      multilinearKakeyaFunction (m+1) u T B x := by
  let eta := (2/Real.pi)*rho
  let good := broadGreedyTuples G u eta m
  have heta : 0≤eta := by dsimp [eta]; positivity
  have hcount := broadGreedyTuples_card_lower (k:=m+1) G u rho hu hkn
    (by simpa only [Nat.add_sub_cancel] using hbroad) m le_rfl
  have hcount' : (1/2:ℝ)^m*(G.card:ℝ)^(m+1)≤(good.card:ℝ) := by
    have he : (1/2:ℝ)^m*(G.card:ℝ)^(m+1)=(G.card:ℝ)*((G.card:ℝ)/2)^m := by
      rw [pow_succ,div_pow,div_pow,one_pow]
      ring
    rwa [he]
  have hh := multilinear_lower_of_tuple_count u T B (eta^m) ((1/2:ℝ)^m) (G.card:ℝ)
    hB (by positivity) (by positivity) (by positivity) x good
    (fun f hf i => hincident (f i) (broadGreedyTuples_mem G u eta m f hf i))
    (fun f hf => broadGreedyTuples_wedge_lower G u eta heta hu m f hf) hcount'
  rw [tuple_lower_bound_factorization (by omega : 0<m+1) hB (by positivity) (by positivity) (by positivity)] at hh
  have hpower : (eta^m)^((1:ℝ)/B)=(2/Real.pi)^((m:ℝ)/B)*rho^((m:ℝ)/B) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul heta]
    have he : (m:ℝ)*(1/B)=(m:ℝ)/B := by ring
    rw [he,Real.mul_rpow (by positivity) hrho.le]
  rw [hpower] at hh
  unfold broadCoefficient
  convert hh using 1
  push_cast
  ring

/-- Source indexing, with k directions and the exact k-1 exponent. -/
theorem broad_multilinear_pointwise_k {n N k : ℕ}
    (G : Finset (Fin N)) (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n)))
    (rho B : ℝ) (hrho : 0<rho) (hB : 0<B) (hk : 1≤k) (hkn : k≤n)
    (hu : ∀ j∈G, ‖u j‖=1)
    (hbroad : ∀ H : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
      Module.finrank ℝ H=k-1 →
      ((G.filter fun j => planeAngle H (u j)≤rho).card:ℝ)<(G.card:ℝ)/2)
    (x : EuclideanSpace ℝ (Fin n)) (hincident : ∀ j∈G, x∈T j) :
    broadCoefficient (k-1) B*rho^(((k:ℝ)-1)/B)*(G.card:ℝ) ≤
      multilinearKakeyaFunction k u T B x := by
  have hh := broad_multilinear_pointwise (m:=k-1) G u T rho B hrho hB
    (by omega) hu hbroad x hincident
  have he : k-1+1=k := by omega
  simpa only [he,Nat.cast_sub hk,Nat.cast_one] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.broadGreedyTuples_wedge_lower
#print axioms KakeyaTwoScale.broadCoefficient_pos
#print axioms KakeyaTwoScale.broad_multilinear_pointwise

#print axioms KakeyaTwoScale.broad_multilinear_pointwise_k
