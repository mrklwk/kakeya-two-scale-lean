module
public import KakeyaTwoScale.NestedCaptureVolumeBound

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

def orderedCaptureDilation {r : ℕ} (n : ℕ) (B : ℝ) (L : Fin r→ℝ) (i : Fin r) : ℝ :=
  if hi : i.val+1<r then recursionDilation n B*L i/L ⟨i.val+1,hi⟩ else recursionDilation n B

theorem orderedCaptureDilation_ge {r : ℕ} (n : ℕ) (B : ℝ) (hB : 0≤B)
    (L : Fin r→ℝ) (hL : ∀ i, 0<L i) (hmono : Antitone L) (i : Fin r) :
    recursionDilation n B≤orderedCaptureDilation n B L i := by
  unfold orderedCaptureDilation
  split_ifs with hi
  · apply (le_div_iff₀ (hL _)).mpr
    exact mul_le_mul_of_nonneg_left (hmono (by change i.val ≤ i.val+1; omega))
      (le_trans (by norm_num) (recursionDilation_ge_one n B hB))
  · rfl

theorem orderedCapture_chain (n r : ℕ) (B : ℝ) (L : Fin r→ℝ) (hmono : Antitone L) :
    (List.finRange r).IsChain (fun i j => j.val+1=(i.val+1)+1 ∧ L j≤L i ∧
      orderedCaptureDilation n B L i=recursionDilation n B*L i/L j) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [List.length_finRange] at hi
  simp only [List.getElem_finRange, Fin.val_cast]
  refine ⟨True.intro,hmono (by change i ≤ i+1; omega),?_⟩
  simp [orderedCaptureDilation,hi]

/-- Full regular flag of codimensions 1,...,r+1. The scale dilation and every
thickness hypothesis are derived from positivity, ordering and the long regime. -/
theorem uniform_ordered_capture_volume (n r e D : ℕ) (C : ℝ) (hC : 0≤C)
    (h : Fin (n+1)) :
    ∃ K : ℝ, 0<K ∧ ∃ M : ℕ,
      ∀ (P : Fin (r+1)→Fin e→MvPolynomial (Fin (n+1)) ℝ),
      (∀ i j, (P i j).totalDegree≤D) →
      ∀ (center : EuclideanSpace ℝ (Fin (n+1))) (L : Fin (r+1)→ℝ) (rho s ell : ℝ)
        (Q : ∀ i : Fin (r+1), Fin (i.val+1)→MvPolynomial (Fin (n+1)) ℝ),
      r+1≤n+1 → 0<rho → 0<ell → (∀ i, 0<L i ∧ rho≤L i/4) → Antitone L →
      (∀ i, (∀ j, (Q i j).totalDegree≤D) ∧
        (∀ x, rectangularPolynomialMap (Q i) x=0 →
          (fderiv ℝ (rectangularPolynomialMap (Q i)) x).range=⊤) ∧
        captureZeroSet (P i)={x | rectangularPolynomialMap (Q i) x=0}) →
      volume {v | ∃ a, universalEligibleLine D C h 0
        (captureParameters P center L rho s ell) v a} * ENNReal.ofReal (ell^(n+1)) ≤
        ENNReal.ofReal (K*(rho^(r+1)*L 0^n/
          (((List.finRange r).map (fun i => L i.succ)).prod)))*M := by
  obtain ⟨K,hK,M,hvol⟩ := uniform_nested_capture_volume_bound n (r+1) e D C hC h 0
    ((List.finRange r).map Fin.succ)
  refine ⟨K,hK,M,?_⟩
  intro P hP center L rho s ell Q hr hrho hell hscale hmono hQ
  have hB : 0≤C+4 := by linarith
  have hv := hvol P hP center L (orderedCaptureDilation n (C+4) L) rho s ell
    (fun i => i.val+1) Q hrho hell (by
      intro i _
      refine ⟨by have := i.isLt; omega,(hQ i).1,(hQ i).2.1,(hQ i).2.2,
        (hscale i).1,(hscale i).2,?_⟩
      exact orderedCaptureDilation_ge n (C+4) hB L (fun j => (hscale j).1) hmono i)
    (by simpa only [List.finRange_succ] using orderedCapture_chain n (r+1) (C+4) L hmono)
  simpa only [Fin.val_zero,Nat.zero_add,List.length_map,List.length_finRange,Nat.one_add,
    Nat.add_sub_cancel,List.map_map,Function.comp_def] using hv

end KakeyaTwoScale
#print axioms KakeyaTwoScale.orderedCapture_chain
#print axioms KakeyaTwoScale.uniform_ordered_capture_volume
