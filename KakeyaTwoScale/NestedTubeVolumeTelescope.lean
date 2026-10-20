module
public import KakeyaTwoScale.NestedVolumeTelescope

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The product-of-length volume bound for the exact recursive sets. Every
recurrence premise is derived from their polynomial and cylinder geometry. -/
theorem uniform_nestedTube_volume_telescope (n r e D : ℕ) (B kappa beta Dstar : ℝ)
    (hB : 0≤B) (hbeta : 0<beta) (hDstar : 1≤Dstar) (i : Fin r) (rest : List (Fin r)) :
    ∃ C : ℝ, 0<C ∧ ∀ (p : TubeRecursionParameter n r e→ℝ) (sigma : Fin r→ℕ)
      (Q : ∀ j, Fin (sigma j)→MvPolynomial (Fin (n+1)) ℝ),
      0<p (Sum.inl .radius) →
      (∀ j∈i::rest, sigma j≤n+1 ∧
        (∀ k, (Q j k).totalDegree≤D) ∧
        (∀ x, rectangularPolynomialMap (Q j) x=0 → (fderiv ℝ (rectangularPolynomialMap (Q j)) x).range=⊤) ∧
        nestedPolynomialZero D p j={x | rectangularPolynomialMap (Q j) x=0} ∧
        0<p (Sum.inl (.length j)) ∧
        p (Sum.inl .radius)≤p (Sum.inl (.length j))/4 ∧
        beta*p (Sum.inl .radius)≤kappa*p (Sum.inl (.length j)) ∧
        1≤p (Sum.inr j) ∧ 1≤p (Sum.inr j)*beta) →
      (i::rest).IsChain (fun j k => sigma k=sigma j+1 ∧
        p (Sum.inr j)=Dstar*p (Sum.inl (.length j))/p (Sum.inl (.length k))) →
      volume (nestedTubeSet D B kappa beta (i::rest) p)≤
        ENNReal.ofReal (C*((p (Sum.inl .radius))^(sigma i+rest.length)*
          (p (Sum.inl (.length i)))^(n+1-sigma i)/
          (rest.map (fun j => p (Sum.inl (.length j)))).prod)) := by
  obtain ⟨C,hC,hprod⟩ := uniform_nestedTube_volume_product n r e D B kappa beta hB hbeta (i::rest)
  refine ⟨C*Dstar^((n+1)*(i::rest).length),by positivity,?_⟩
  intro p sigma Q hrho hdata hchain
  have hv := hprod p sigma Q hrho hdata
  have hgeom (j) (hj : j∈i::rest) : sigma j≤n+1 ∧ 0<p (Sum.inl (.length j)) :=
    ⟨(hdata j hj).1,(hdata j hj).2.2.2.2.1⟩
  have ht := nestedVolumeWeight_telescope (n+1) sigma
    (fun j => p (Sum.inl (.length j))) (fun j => p (Sum.inr j))
    (p (Sum.inl .radius)) Dstar i rest hgeom hchain
  rw [ht] at hv
  refine hv.trans (ENNReal.ofReal_le_ofReal ?_)
  have hpow := pow_le_pow_right₀ hDstar (nestedVolumeExponent_le (n+1) sigma (i::rest))
  have hL := (hgeom i (by simp)).2
  have hden : 0<(rest.map (fun j => p (Sum.inl (.length j)))).prod := by
    apply List.prod_pos
    intro x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
    exact (hgeom j (List.mem_cons_of_mem i hj)).2
  have hn : 0≤(p (Sum.inl .radius))^(sigma i+rest.length)*
      (p (Sum.inl (.length i)))^(n+1-sigma i)/(rest.map (fun j => p (Sum.inl (.length j)))).prod := by positivity
  calc
    _ ≤ C*(Dstar^((n+1)*(i::rest).length)*
        ((p (Sum.inl .radius))^(sigma i+rest.length)*(p (Sum.inl (.length i)))^(n+1-sigma i)/
          (rest.map (fun j => p (Sum.inl (.length j)))).prod)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hn) hC.le
    _ = _ := by ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_nestedTube_volume_telescope
