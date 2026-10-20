module
public import KakeyaTwoScale.OptimizedZahlExponent

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Scalar cancellation behind the repaired weighted endpoint. The Q and w
variables are logarithms of the product and minimum populations. -/
theorem weighted_endpoint_log_elimination
    (n k t u d theta mu V delta Q w a F G T : ℝ)
    (hk : 0<k) (hd : d=k+t) (hdq : 0≤d/k) (hdu : 0≤d/k-u)
    (hanalytic : theta+k*mu+(k-1)*V ≤ F+(k-n)*delta+Q-T)
    (hdegree : t*(V+mu-Q/k-delta)+u*w-G ≤ T)
    (hpopulation : Q≤w+(k-1)*a) (hminimum : w≤a) :
    theta+d*mu+(d-1)*V ≤ F+G+(d-n)*delta+(d-u)*a := by
  have hpop := mul_le_mul_of_nonneg_left hpopulation hdq
  have hmin := mul_le_mul_of_nonneg_left hminimum hdu
  have hratio : d/k=1+t/k := by rw [hd]; field_simp
  have hratioQ := congrArg (fun x : ℝ => x*Q) hratio
  have hratioA := congrArg (fun x : ℝ => x*k*a) hratio
  have hk0 := hk.ne'
  have hcancel : (d/k)*k=d := div_mul_cancel₀ d hk0
  have hcancelA := congrArg (fun x : ℝ => x*a) hcancel
  rw [hd] at hcancelA ⊢
  simp only [div_eq_mul_inv] at *
  rw [hd] at hpop hmin hratioQ hratioA
  nlinarith only [hanalytic,hdegree,hpop,hmin,hratioQ,hratioA,hcancelA]

/-- Explicit positive scalar inputs. The analytic inequality and degree
lower bound are premises, not conclusions about a constructed archive. -/
theorem optimized_weighted_mass_positive
    (n k t u d theta mu V delta Qprod w Qmax F G T : ℝ)
    (hk : 0<k) (hd : d=k+t) (hdq : 0≤d/k) (hdu : 0≤d/k-u)
    (htheta : 0<theta) (hmu : 0<mu) (hV : 0<V) (hdelta : 0<delta)
    (hQ : 0<Qprod) (hw : 0<w) (ha : 0<Qmax) (hF : 0<F) (hG : 0<G) (hT : 0<T)
    (hanalytic : theta*mu^k*V^(k-1) ≤ F*delta^(k-n)*Qprod/T)
    (hdegree : ((V*mu/Qprod^(1/k))/delta)^t*w^u ≤ G*T)
    (hpopulation : Qprod≤w*Qmax^(k-1)) (hminimum : w≤Qmax) :
    theta*mu^d*V^(d-1) ≤ (F*G)*delta^(d-n)*Qmax^(d-u) := by
  have han := Real.log_le_log (by positivity : 0<theta*mu^k*V^(k-1)) hanalytic
  have hdeg := Real.log_le_log (by positivity : 0<((V*mu/Qprod^(1/k))/delta)^t*w^u) hdegree
  have hpop := Real.log_le_log hQ hpopulation
  have hmin := Real.log_le_log hw hminimum
  simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_rpow] at han hdeg hpop
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_mul,Real.log_rpow]
  apply weighted_endpoint_log_elimination n k t u d _ _ _ _ _ _ _ _ _ _ hk hd hdq hdu
    han ?_ hpop hmin
  convert (show t*(Real.log V+Real.log mu-(1/k)*Real.log Qprod-Real.log delta)+
      u*Real.log w-Real.log G≤Real.log T by linarith only [hdeg]) using 1
  ring

/-- Raising the positive scalar estimate to the exact endpoint power. -/
theorem optimized_weighted_mass_root_positive
    (n k t u d theta mu V delta Qprod w Qmax F G T : ℝ)
    (hk : 0<k) (hd : d=k+t) (hdone : 1<d) (hdq : 0≤d/k) (hdu : 0≤d/k-u)
    (htheta : 0<theta) (hmu : 0<mu) (hV : 0<V) (hdelta : 0<delta)
    (hQ : 0<Qprod) (hw : 0<w) (ha : 0<Qmax) (hF : 0<F) (hG : 0<G) (hT : 0<T)
    (hanalytic : theta*mu^k*V^(k-1) ≤ F*delta^(k-n)*Qprod/T)
    (hdegree : ((V*mu/Qprod^(1/k))/delta)^t*w^u ≤ G*T)
    (hpopulation : Qprod≤w*Qmax^(k-1)) (hminimum : w≤Qmax) :
    theta^(1/(d-1))*mu^(d/(d-1))*V ≤
      (F*G)^(1/(d-1))*delta^((d-n)/(d-1))*Qmax^((d-u)/(d-1)) := by
  have hh := optimized_weighted_mass_positive n k t u d theta mu V delta Qprod w Qmax F G T
    hk hd hdq hdu htheta hmu hV hdelta hQ hw ha hF hG hT hanalytic hdegree hpopulation hminimum
  have hl := Real.log_le_log (by positivity : 0<theta*mu^d*V^(d-1)) hh
  simp (disch := positivity) only [Real.log_mul,Real.log_rpow] at hl
  have hscale := div_le_div_of_nonneg_right hl (show 0≤d-1 by linarith)
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_mul,Real.log_rpow]
  have hd1 : d-1≠0 := by linarith
  convert hscale using 1 <;> field_simp

/-- Total optimizer weight; the moment is zahlB n k-k. -/
def zahlOptimizerWeight (n k : ℝ) : ℝ := 1/2-k*(k-1)/(2*n*(n-1))

theorem zahl_optimizer_population_identity {n k : ℝ} (hn : 1<n)
    (hklo : 2≤k) (hkhi : k≤n) :
    (zahlB n k-zahlOptimizerWeight n k)/(zahlB n k-1)=n/(n-1) := by
  have hn0 : n≠0 := by linarith
  have hn1 : n-1≠0 := by linarith
  have hd := zahlB_gt_one (by linarith : 0<n) hklo hkhi
  apply (div_eq_div_iff (by linarith : zahlB n k-1≠0) hn1).mpr
  unfold zahlB zahlOptimizerWeight
  field_simp
  ring

theorem zahl_optimizer_population_signs {n k : ℝ} (hn : 1<n)
    (hklo : 2≤k) (hkhi : k≤n) :
    0≤zahlOptimizerWeight n k ∧
      0≤zahlB n k/k ∧ 0≤zahlB n k/k-zahlOptimizerWeight n k := by
  have hk : 0<k := by linarith
  have hd := zahlB_ge_k (by linarith : 0<n) hkhi
  have hdq : 1≤zahlB n k/k := (le_div_iff₀ hk).mpr (by simpa using hd)
  have hden : 0<2*n*(n-1) := by positivity
  have hnum : 0≤k*(k-1) := mul_nonneg hk.le (by linarith)
  have hu : zahlOptimizerWeight n k≤1/2 := by
    unfold zahlOptimizerWeight
    have := div_nonneg hnum hden.le
    linarith
  refine ⟨?_,by linarith,by linarith⟩
  unfold zahlOptimizerWeight
  have hproduct : k*(k-1)≤n*(n-1) :=
    mul_le_mul hkhi (by linarith) (by linarith) (by linarith)
  have hdiv : k*(k-1)/(2*n*(n-1))≤1/2 := (div_le_iff₀ hden).mpr (by nlinarith)
  linarith

/-- Exact published pth-power exponents for one positive band. All constants
and the terminal multilinear bound remain explicit. No geometric archive or
analytic estimate is manufactured by this scalar theorem. -/
theorem optimized_zahl_weighted_mass_positive
    (n k theta mu V delta Qprod w Qmax F G T : ℝ)
    (hn : 1<n) (hklo : 2≤k) (hkhi : k≤n)
    (htheta : 0<theta) (hmu : 0<mu) (hV : 0<V) (hdelta : 0<delta)
    (hQ : 0<Qprod) (hw : 0<w) (ha : 0<Qmax) (hF : 0<F) (hG : 0<G) (hT : 0<T)
    (hanalytic : theta*mu^k*V^(k-1) ≤ F*delta^(k-n)*Qprod/T)
    (hdegree : ((V*mu/Qprod^(1/k))/delta)^(zahlB n k-k)*
      w^(zahlOptimizerWeight n k) ≤ G*T)
    (hpopulation : Qprod≤w*Qmax^(k-1)) (hminimum : w≤Qmax) :
    theta^(1/(zahlB n k-1))*mu^(zahlB n k/(zahlB n k-1))*V ≤
      (F*G)^(1/(zahlB n k-1))*delta^((zahlB n k-n)/(zahlB n k-1))*
        Qmax^(n/(n-1)) := by
  have hs := zahl_optimizer_population_signs hn hklo hkhi
  have hh := optimized_weighted_mass_root_positive n k (zahlB n k-k) (zahlOptimizerWeight n k)
    (zahlB n k) theta mu V delta Qprod w Qmax F G T
    (by linarith) (by ring) (zahlB_gt_one (by linarith) hklo hkhi) hs.2.1 hs.2.2
    htheta hmu hV hdelta hQ hw ha hF hG hT hanalytic hdegree hpopulation hminimum
  rwa [zahl_optimizer_population_identity hn hklo hkhi] at hh

/-- The existing finite log optimizer supplies the actual scalar denominator.
Degree logs may be negative. Every geometric source constraint is explicit. -/
theorem optimized_degree_denominator {n m k : ℕ} (hn : 0<n) (hk : 2≤k)
    (hnmk : n=m+k) (D : ℕ→ℝ) (lambda delta w E : ℝ)
    (hlambda : 0<lambda) (hdelta : 0<delta) (hw : 0<w)
    (hconstraints : ∀ i<m, ((i:ℝ)+1)*Real.log (lambda/delta)+Real.log w-E ≤
      degreeConstraintLog n D (i+1)) :
    (lambda/delta)^(zahlB n k-k)*w^(zahlOptimizerWeight n k) ≤
      Real.exp (zahlOptimizerWeight n k*E)*Real.exp (degreeObjectiveLog m m D) := by
  have hh := degree_log_optimization n m D (by omega)
    (Real.log (lambda/delta)) (Real.log w) E hconstraints
  have hreal : (n:ℝ)=(m:ℝ)+k := by exact_mod_cast hnmk
  have ht := optimized_exponent_matches_zahl hn hnmk
  have hu : (1/2-((n:ℝ)-m)*((n:ℝ)-m-1)/(2*n*((n:ℝ)-1)))=zahlOptimizerWeight n k := by
    unfold zahlOptimizerWeight
    rw [show (n:ℝ)-m=k by linarith]
  rw [hu,show (m:ℝ)*(m+1)/(2*n)=zahlB n k-k by linarith] at hh
  rw [Real.rpow_def_of_pos (div_pos hlambda hdelta), Real.rpow_def_of_pos hw,
    ←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hh]

/-- A minimum-attaining index can be used for j; no relation density enters
this finite population bound. -/
theorem finite_population_product_le {k : ℕ} (a : Fin k→ℝ) (j : Fin k)
    (Qmax : ℝ) (ha : ∀ i, 0≤a i) (hmax : ∀ i, a i≤Qmax) :
    (∏ i, a i)≤a j*Qmax^((k:ℝ)-1) := by
  have hk : 1≤k := by have := j.isLt; omega
  have hprod : (∏ i∈Finset.univ.erase j, a i)≤∏ _i∈Finset.univ.erase j, Qmax :=
    Finset.prod_le_prod₀ (fun i _ => ha i) (fun i _ => hmax i)
  have hmul := mul_le_mul_of_nonneg_left hprod (ha j)
  rw [Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ,
    Fintype.card_fin] at hmul
  have he : (∏ i, a i)=a j*(∏ i∈Finset.univ.erase j, a i) := by
    rw [mul_comm,Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  rw [he,←Nat.cast_one,←Nat.cast_sub hk,Real.rpow_natCast]
  exact hmul

/-- Full-depth numerical optimizer and scalar cancellation assembled. The
terminal analytic estimate remains an explicit premise. -/
theorem optimized_zahl_band_of_degree_constraints {n m k : ℕ}
    (hn : 0<n) (hk : 2≤k) (hnmk : n=m+k) (D : ℕ→ℝ)
    (theta mu V delta Qprod w Qmax F E : ℝ)
    (htheta : 0<theta) (hmu : 0<mu) (hV : 0<V) (hdelta : 0<delta)
    (hQ : 0<Qprod) (hw : 0<w) (ha : 0<Qmax) (hF : 0<F)
    (hanalytic : theta*mu^(k:ℝ)*V^((k:ℝ)-1) ≤
      F*delta^((k:ℝ)-n)*Qprod/Real.exp (degreeObjectiveLog m m D))
    (hconstraints : ∀ i<m,
      ((i:ℝ)+1)*Real.log ((V*mu/Qprod^(1/(k:ℝ)))/delta)+Real.log w-E ≤
        degreeConstraintLog n D (i+1))
    (hpopulation : Qprod≤w*Qmax^((k:ℝ)-1)) (hminimum : w≤Qmax) :
    theta^(1/(zahlB n k-1))*mu^(zahlB n k/(zahlB n k-1))*V ≤
      (F*Real.exp (zahlOptimizerWeight n k*E))^(1/(zahlB n k-1))*
        delta^((zahlB n k-n)/(zahlB n k-1))*Qmax^((n:ℝ)/(n-1)) := by
  have hn' : 1<(n:ℝ) := by exact_mod_cast (show 1<n by omega)
  have hk' : (2:ℝ)≤k := by exact_mod_cast hk
  have hkn : (k:ℝ)≤n := by exact_mod_cast (show k≤n by omega)
  exact optimized_zahl_weighted_mass_positive n k theta mu V delta Qprod w Qmax F
    (Real.exp (zahlOptimizerWeight n k*E)) (Real.exp (degreeObjectiveLog m m D))
    hn' hk' hkn htheta hmu hV hdelta hQ hw ha hF (Real.exp_pos _) (Real.exp_pos _)
    hanalytic (optimized_degree_denominator hn hk hnmk D _ delta w E
      (by positivity) hdelta hw hconstraints) hpopulation hminimum

/-- Early-short completion supplies the same denominator with its explicit
additional error. Includes r=0; the last-degree floor is requested only if r>0. -/
theorem early_terminal_optimized_degree_denominator {n m k r : ℕ}
    (hn : 0<n) (hk : 2≤k) (hnmk : n=m+k) (hrm : r≤m) (D : ℕ→ℝ)
    (lambda delta w E : ℝ) (hlambda : 0<lambda) (hdelta : 0<delta) (hw : 0<w)
    (hE : 0≤E) (hzero : ∀ s, r≤s → D s=0)
    (hbefore : ∀ i, 1 ≤ i → i < r →
      (i:ℝ)*Real.log (lambda/delta)+Real.log w-E≤degreeConstraintLog n D i)
    (hterminal : Real.log (lambda/delta)-E≤degreePrefixLog D r)
    (hfloor : 0 < r → -E ≤ D (r-1)) (hpacking : Real.log w≤E) :
    (lambda/delta)^(zahlB n k-k)*w^(zahlOptimizerWeight n k) ≤
      Real.exp (zahlOptimizerWeight n k*((n:ℝ)+m+2)*E)*
        Real.exp (degreeObjectiveLog m r D) := by
  have hh := early_terminal_degree_optimization D hrm (by omega) hE hzero
    hbefore hterminal hfloor hpacking
  have hreal : (n:ℝ)=(m:ℝ)+k := by exact_mod_cast hnmk
  have ht := optimized_exponent_matches_zahl hn hnmk
  have hu : (1/2-((n:ℝ)-m)*((n:ℝ)-m-1)/(2*n*((n:ℝ)-1)))=zahlOptimizerWeight n k := by
    unfold zahlOptimizerWeight
    rw [show (n:ℝ)-m=k by linarith]
  rw [hu,show (m:ℝ)*(m+1)/(2*n)=zahlB n k-k by linarith] at hh
  rw [Real.rpow_def_of_pos (div_pos hlambda hdelta), Real.rpow_def_of_pos hw,
    ←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hh]

/-- The same exact scalar endpoint after early terminal completion. All
stopping, floor, packing, and terminal analytic inputs remain visible. -/
theorem optimized_zahl_band_of_early_terminal {n m k r : ℕ}
    (hn : 0<n) (hk : 2≤k) (hnmk : n=m+k) (hrm : r≤m) (D : ℕ→ℝ)
    (theta mu V delta Qprod w Qmax F E : ℝ)
    (htheta : 0<theta) (hmu : 0<mu) (hV : 0<V) (hdelta : 0<delta)
    (hQ : 0<Qprod) (hw : 0<w) (ha : 0<Qmax) (hF : 0<F)
    (hanalytic : theta*mu^(k:ℝ)*V^((k:ℝ)-1) ≤
      F*delta^((k:ℝ)-n)*Qprod/Real.exp (degreeObjectiveLog m r D))
    (hE : 0≤E) (hzero : ∀ s, r≤s → D s=0)
    (hbefore : ∀ i, 1 ≤ i → i < r →
      (i:ℝ)*Real.log ((V*mu/Qprod^(1/(k:ℝ)))/delta)+Real.log w-E≤degreeConstraintLog n D i)
    (hterminal : Real.log ((V*mu/Qprod^(1/(k:ℝ)))/delta)-E≤degreePrefixLog D r)
    (hfloor : 0 < r → -E ≤ D (r-1)) (hpacking : Real.log w≤E)
    (hpopulation : Qprod≤w*Qmax^((k:ℝ)-1)) (hminimum : w≤Qmax) :
    theta^(1/(zahlB n k-1))*mu^(zahlB n k/(zahlB n k-1))*V ≤
      (F*Real.exp (zahlOptimizerWeight n k*((n:ℝ)+m+2)*E))^(1/(zahlB n k-1))*
        delta^((zahlB n k-n)/(zahlB n k-1))*Qmax^((n:ℝ)/(n-1)) := by
  have hn' : 1<(n:ℝ) := by exact_mod_cast (show 1<n by omega)
  have hk' : (2:ℝ)≤k := by exact_mod_cast hk
  have hkn : (k:ℝ)≤n := by exact_mod_cast (show k≤n by omega)
  exact optimized_zahl_weighted_mass_positive n k theta mu V delta Qprod w Qmax F
    (Real.exp (zahlOptimizerWeight n k*((n:ℝ)+m+2)*E)) (Real.exp (degreeObjectiveLog m r D))
    hn' hk' hkn htheta hmu hV hdelta hQ hw ha hF (Real.exp_pos _) (Real.exp_pos _)
    hanalytic (early_terminal_optimized_degree_denominator hn hk hnmk hrm D _ delta w E
      (by positivity) hdelta hw hE hzero hbefore hterminal hfloor hpacking) hpopulation hminimum

/-- Zero band mass is discharged before logarithmic positive-case arguments.
This lemma never takes a logarithm of zero. -/
theorem weighted_band_mass_zero (d theta mu V : ℝ) (hd : 1<d)
    (hz : theta=0 ∨ mu=0 ∨ V=0) :
    theta^(1/(d-1))*mu^(d/(d-1))*V=0 := by
  have hd1 : 0<d-1 := by linarith
  have hq : 1/(d-1)≠0 := (div_pos (by norm_num) hd1).ne'
  have hp : d/(d-1)≠0 := (div_pos (by linarith) hd1).ne'
  rcases hz with h | h | h
  · rw [h,Real.zero_rpow hq]
    simp
  · rw [h,Real.zero_rpow hp]
    simp
  · simp [h]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.weighted_endpoint_log_elimination
#print axioms KakeyaTwoScale.optimized_weighted_mass_positive

#print axioms KakeyaTwoScale.optimized_weighted_mass_root_positive
#print axioms KakeyaTwoScale.zahl_optimizer_population_identity
#print axioms KakeyaTwoScale.zahl_optimizer_population_signs
#print axioms KakeyaTwoScale.optimized_zahl_weighted_mass_positive
#print axioms KakeyaTwoScale.optimized_degree_denominator

#print axioms KakeyaTwoScale.finite_population_product_le
#print axioms KakeyaTwoScale.optimized_zahl_band_of_degree_constraints
#print axioms KakeyaTwoScale.early_terminal_optimized_degree_denominator

#print axioms KakeyaTwoScale.optimized_zahl_band_of_early_terminal
#print axioms KakeyaTwoScale.weighted_band_mass_zero
