module
public import KakeyaTwoScale.UniversalCaptureAtoms
public import KakeyaTwoScale.PolynomialSignQuantifiers
public import KakeyaTwoScale.CaptureRelationGeometry

@[expose] public section

open Set Metric MvPolynomial
open OAI.Release061 OAI.Release061.SignElimination
noncomputable section
namespace KakeyaTwoScale

def universalZeroNear {n r e : ℕ} (D : ℕ)
    (p : CaptureParameter n r e→ℝ) (i : Fin r) (x : Fin (n+1)→ℝ) : Prop :=
  0<p .radius ∧ ∃ y : Fin (n+1)→ℝ,
    (∀ j, universalCapturePolynomial D p i j y=0) ∧
    (∑ k, (x k-y k)^2)<(2*p .radius)^2

theorem universalZeroNear_sign {X ι : Type*} {n r e : ℕ}
    (c : X→ι→ℝ) (D : ℕ) (p : X→CaptureParameter n r e→ℝ)
    (x : X→Fin (n+1)→ℝ)
    (hp : ∀ q, PolynomialScalar c (fun z => p z q))
    (hx : ∀ j, PolynomialScalar c (fun z => x z j)) (i : Fin r) :
    PolynomialSignSet c {z | universalZeroNear D (p z) i (x z)} := by
  let c' : X × (Fin (n+1)→ℝ)→ι⊕Fin (n+1)→ℝ := fun z => Sum.elim (c z.1) z.2
  have lift {f : X→ℝ} (hf : PolynomialScalar c f) : PolynomialScalar c' (fun z => f z.1) :=
    hf.coordinate_preimage Prod.fst Sum.inl (by intros; rfl)
  have hy (j) : PolynomialScalar c' (fun z => z.2 j) := PolynomialScalar.coordinate (Sum.inr j)
  have hz := PolynomialSignSet.forall_finite
    (fun j (z : X × (Fin (n+1)→ℝ)) => universalCapturePolynomial D (p z.1) i j z.2=0)
    (fun j => (universalCapturePolynomial_scalar c' D (fun z => p z.1) Prod.snd
      (fun q => lift (hp q)) hy i j).eq_zero)
  have hd : PolynomialScalar c' (fun z => ∑ j, (x z.1 j-z.2 j)^2) :=
    PolynomialScalar.sum Finset.univ _ (fun j _ => ((lift (hx j)).sub (hy j)).pow 2)
  exact ((PolynomialScalar.const (c := c) 0).lt (hp .radius)).inter
    (polynomialSignSet_projection_finite (hz.inter
      (hd.lt (((PolynomialScalar.const 2).mul (lift (hp .radius))).pow 2))))

theorem universalZeroNear_geometry {n r e : ℕ} (D : ℕ)
    (p : CaptureParameter n r e→ℝ) (i : Fin r) (hp : 0<p .radius)
    (x : EuclideanSpace ℝ (Fin (n+1))) :
    universalZeroNear D p i x.ofLp ↔
      x∈thickening (2*p .radius) {y : EuclideanSpace ℝ (Fin (n+1)) |
        ∀ j, universalCapturePolynomial D p i j y.ofLp=0} := by
  constructor
  · rintro ⟨_,y,hy,hd⟩
    refine mem_thickening_iff.mpr ⟨WithLp.toLp 2 y,hy,?_⟩
    have he := euclidean_sum_sq_dist x (WithLp.toLp 2 y)
    rw [he] at hd
    exact (sq_lt_sq₀ dist_nonneg (by positivity)).mp hd
  · intro hx
    obtain ⟨y,hy,hd⟩ := mem_thickening_iff.mp hx
    refine ⟨hp,y.ofLp,hy,?_⟩
    rw [euclidean_sum_sq_dist x y]
    exact (sq_lt_sq₀ dist_nonneg (by positivity)).mpr hd

end KakeyaTwoScale
#print axioms KakeyaTwoScale.universalZeroNear_sign
#print axioms KakeyaTwoScale.universalZeroNear_geometry
