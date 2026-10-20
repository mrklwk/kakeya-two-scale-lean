module
public import KakeyaTwoScale.OptimizedWeightedMass

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

theorem optimized_zahl_band_of_objective {n m k r : ℕ}
    (hn : 0<n) (hk : 2≤k) (hnmk : n=m+k) (D : ℕ→ℝ)
    (theta mu V delta Qprod w Qmax F E : ℝ)
    (htheta : 0<theta) (hmu : 0<mu) (hV : 0<V) (hdelta : 0<delta)
    (hQ : 0<Qprod) (hw : 0<w) (ha : 0<Qmax) (hF : 0<F)
    (hanalytic : theta*mu^(k:ℝ)*V^((k:ℝ)-1) ≤
      F*delta^((k:ℝ)-n)*Qprod/Real.exp (degreeObjectiveLog m r D))
    (hobjective : (m:ℝ)*(m+1)/(2*n)*Real.log ((V*mu/Qprod^(1/(k:ℝ)))/delta)+
      (1/2-((n:ℝ)-m)*((n:ℝ)-m-1)/(2*n*((n:ℝ)-1)))*(Real.log w-E) ≤
        degreeObjectiveLog m r D)
    (hpopulation : Qprod≤w*Qmax^((k:ℝ)-1)) (hminimum : w≤Qmax) :
    theta^(1/(zahlB n k-1))*mu^(zahlB n k/(zahlB n k-1))*V ≤
      (F*Real.exp (zahlOptimizerWeight n k*E))^(1/(zahlB n k-1))*
        delta^((zahlB n k-n)/(zahlB n k-1))*Qmax^((n:ℝ)/(n-1)) := by
  have hn' : 1<(n:ℝ) := by exact_mod_cast (show 1<n by omega)
  have hk' : (2:ℝ)≤k := by exact_mod_cast hk
  have hkn : (k:ℝ)≤n := by exact_mod_cast (show k≤n by omega)
  refine optimized_zahl_weighted_mass_positive n k theta mu V delta Qprod w Qmax F
    (Real.exp (zahlOptimizerWeight n k*E)) (Real.exp (degreeObjectiveLog m r D))
    hn' hk' hkn htheta hmu hV hdelta hQ hw ha hF (Real.exp_pos _) (Real.exp_pos _)
    hanalytic ?_ hpopulation hminimum
  have hreal : (n:ℝ)=(m:ℝ)+k := by exact_mod_cast hnmk
  have ht := optimized_exponent_matches_zahl hn hnmk
  have hu : (1/2-((n:ℝ)-m)*((n:ℝ)-m-1)/(2*n*((n:ℝ)-1)))=zahlOptimizerWeight n k := by
    unfold zahlOptimizerWeight
    rw [show (n:ℝ)-m=k by linarith]
  rw [hu,show (m:ℝ)*(m+1)/(2*n)=zahlB n k-k by linarith] at hobjective
  rw [Real.rpow_def_of_pos (by positivity : 0<(V*mu/Qprod^(1/(k:ℝ)))/delta), Real.rpow_def_of_pos hw,
    ←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hobjective]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.optimized_zahl_band_of_objective
