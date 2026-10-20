module
public import KakeyaTwoScale.PolynomialCaptureFormula
public import KakeyaTwoScale.HeightRescaling

@[expose] public section

open Set MvPolynomial
open OAI.Release061 OAI.Release061.SignElimination
noncomputable section
namespace KakeyaTwoScale

/-- Coefficients and geometry are REAL parameters of one fixed formula.
The monomial box in universalCapturePolynomial is finite before specialization. -/
inductive CaptureParameter (n r e : ℕ)
  | coefficient : Fin r → Fin e → (Fin (n+1) →₀ ℕ) → CaptureParameter n r e
  | center : Fin (n+1) → CaptureParameter n r e
  | length : Fin r → CaptureParameter n r e
  | radius : CaptureParameter n r e
  | slabStart : CaptureParameter n r e
  | slabLength : CaptureParameter n r e

def universalCapturePolynomial {n r e : ℕ} (D : ℕ)
    (p : CaptureParameter n r e → ℝ) (i : Fin r) (j : Fin e) (y : Fin (n+1) → ℝ) : ℝ :=
  ∑ a ∈ selectionMonomialBox (Fin (n+1)) D,
    p (.coefficient i j a) * ∏ k ∈ a.support, y k ^ a k

/-- Exact squared-distance witness formula for one truncated zero set. -/
def universalCapturePoint {n r e : ℕ} (D : ℕ) (C : ℝ) (h : Fin (n+1))
    (p : CaptureParameter n r e → ℝ) (v a : Fin n → ℝ) (i : Fin r)
    (t : ℝ) (y : Fin (n+1) → ℝ) : Prop :=
  (∀ j, universalCapturePolynomial D p i j y=0) ∧
  (∑ k, (y k-p (.center k))^2) ≤ ((C+4)*p (.length i))^2 ∧
  (∑ k, (p (.center k)+h.insertNth (α := fun _ => ℝ) t (fun j => a j+t*v j) k-y k)^2) < (p .radius)^2

theorem universalCapturePolynomial_scalar {X ι : Type*} {n r e : ℕ}
    (c : X → ι → ℝ) (D : ℕ) (p : X → CaptureParameter n r e → ℝ)
    (y : X → Fin (n+1) → ℝ)
    (hp : ∀ q, PolynomialScalar c (fun x => p x q))
    (hy : ∀ k, PolynomialScalar c (fun x => y x k)) (i : Fin r) (j : Fin e) :
    PolynomialScalar c (fun x => universalCapturePolynomial D (p x) i j (y x)) := by
  apply PolynomialScalar.sum
  intro a _
  exact (hp (.coefficient i j a)).mul
    (PolynomialScalar.prod a.support _ (fun k _ => (hy k).pow (a k)))

/-- Every atom of the geometric witness relation is proved polynomial in the
joint parameters and coordinates. No semialgebraicity premise for the relation. -/
theorem universalCapturePoint_sign {X ι : Type*} {n r e : ℕ}
    (c : X → ι → ℝ) (D : ℕ) (C : ℝ) (h : Fin (n+1))
    (p : X → CaptureParameter n r e → ℝ) (v a : X → Fin n → ℝ)
    (t : X → ℝ) (y : X → Fin (n+1) → ℝ)
    (hp : ∀ q, PolynomialScalar c (fun x => p x q))
    (hv : ∀ j, PolynomialScalar c (fun x => v x j))
    (ha : ∀ j, PolynomialScalar c (fun x => a x j))
    (ht : PolynomialScalar c t)
    (hy : ∀ k, PolynomialScalar c (fun x => y x k)) (i : Fin r) :
    PolynomialSignSet c {x | universalCapturePoint D C h (p x) (v x) (a x) i (t x) (y x)} := by
  have hg : ∀ k, PolynomialScalar c (fun x => h.insertNth (α := fun _ => ℝ) (t x) (fun j => a x j+t x*v x j) k) := by
    apply (Fin.forall_iff_succAbove h (P := fun k => PolynomialScalar c
      (fun x => h.insertNth (α := fun _ => ℝ) (t x) (fun j => a x j+t x*v x j) k))).mpr
    refine ⟨?_,fun j => ?_⟩
    · simpa using ht
    · simpa using (ha j).add (ht.mul (hv j))
  have hz := PolynomialSignSet.forall_finite
    (fun j x => universalCapturePolynomial D (p x) i j (y x)=0)
    (fun j => (universalCapturePolynomial_scalar c D p y hp hy i j).eq_zero)
  have hb : PolynomialScalar c (fun x => ∑ k, (y x k-p x (.center k))^2) := by
    simpa using PolynomialScalar.sum Finset.univ _ (fun k _ => ((hy k).sub (hp (.center k))).pow 2)
  have hd : PolynomialScalar c (fun x => ∑ k,
      (p x (.center k)+h.insertNth (α := fun _ => ℝ) (t x) (fun j => a x j+t x*v x j) k-y x k)^2) := by
    simpa using PolynomialScalar.sum Finset.univ _
      (fun k _ => (((hp (.center k)).add (hg k)).sub (hy k)).pow 2)
  exact hz.inter ((hb.le (((PolynomialScalar.const (C+4)).mul (hp (.length i))).pow 2)).inter
    (hd.lt ((hp .radius).pow 2)))

/-- The finite universal polynomial is literally the supplied polynomial when
its coefficients are inserted; the degree hypothesis proves the support bound. -/
theorem universalCapturePolynomial_specialize {n r e : ℕ} (D : ℕ)
    (P : Fin r → Fin e → MvPolynomial (Fin (n+1)) ℝ)
    (p : CaptureParameter n r e → ℝ)
    (hp : ∀ i j a, p (.coefficient i j a)=(P i j).coeff a)
    (hP : ∀ i j, (P i j).totalDegree ≤ D) (i : Fin r) (j : Fin e)
    (y : Fin (n+1) → ℝ) :
    universalCapturePolynomial D p i j y=eval y (P i j) := by
  classical
  simp only [universalCapturePolynomial,hp]
  rw [eval_eq]
  symm
  apply Finset.sum_subset (support_subset_selectionMonomialBox D (P i j) (hP i j))
  intro a _ ha
  simp only [notMem_support_iff.mp ha,zero_mul]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.universalCapturePoint_sign
#print axioms KakeyaTwoScale.universalCapturePolynomial_specialize
