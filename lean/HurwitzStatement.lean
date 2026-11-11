import Mathlib

/-! # The Hurwitz-type bound, stated in terms of polynomials (definitions and the statement only)

N = 2^λ, variables x_i and y_j indexed by strings of λ bits. The claim: for an absolute constant c and
every λ ≥ 1, there is an identity

  (Σ_i x_i²)·(Σ_j y_j²) = Σ_{k < K} f_k·g_k

over ℚ, with f_k, g_k bilinear forms in x and y, and K ≤ (2λ)^c · 2^(√2·λ) = N^(√2 + o(1)).
This file imports Mathlib only. -/

open MvPolynomial Finset

namespace HurwitzSqrt2

/-- A string of λ bits: an index in [N], N = 2^λ. -/
abbrev Idx (lam : ℕ) : Type := Fin lam → Bool

/-- The variables: x_i is `Sum.inl i`, y_j is `Sum.inr j`. -/
abbrev Var (lam : ℕ) : Type := Idx lam ⊕ Idx lam

/-- The bilinear form Σ_{i,j} F(i,j)·x_i·y_j. -/
noncomputable def bil {lam : ℕ} (F : Idx lam → Idx lam → ℚ) : MvPolynomial (Var lam) ℚ :=
  ∑ i, ∑ j, C (F i j) * X (Sum.inl i) * X (Sum.inr j)

/-- (Σ_i x_i²)·(Σ_j y_j²). -/
noncomputable def sos (lam : ℕ) : MvPolynomial (Var lam) ℚ :=
  (∑ i, X (Sum.inl i) ^ 2) * (∑ j, X (Sum.inr j) ^ 2)

/-- The statement. -/
def Statement : Prop :=
  ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam →
    ∃ (K : ℕ) (f g : Fin K → Idx lam → Idx lam → ℚ),
      (K : ℝ) ≤ (2 * lam : ℝ) ^ c * 2 ^ (Real.sqrt 2 * lam) ∧
      sos lam = ∑ k, bil (f k) * bil (g k)

end HurwitzSqrt2
