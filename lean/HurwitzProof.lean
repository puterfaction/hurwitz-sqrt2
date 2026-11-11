import GeneralPieces.Main
import Mathlib

/-! # Proof of the Hurwitz-type bound from Theorem B of the 3-SAT paper

The definitions in namespace `HurwitzSqrt2` are copied verbatim from `HurwitzStatement.lean`.
The proof takes the pieces of Theorem B (`AppHalfPieces.ThmHalfPiecesPure`, proved in the
formal-math development), uses for each piece the cheaper of its two factorizations, multiplies
out, and divides by d. -/

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

namespace HurwitzSqrt2Proof

open HurwitzSqrt2

variable {lam : ℕ}

/-- The monomial x_x·y_y·x_v·y_u of the crossing polynomial. -/
noncomputable def mon (x y u v : Idx lam) : MvPolynomial (Var lam) ℚ :=
  X (Sum.inl x) * X (Sum.inr y) * X (Sum.inl v) * X (Sum.inr u)

/-- A function T(x,y,u,v) read as the polynomial Σ T(x,y,u,v)·x_x·y_y·x_v·y_u. -/
noncomputable def poly4 (T : Idx lam → Idx lam → Idx lam → Idx lam → ℚ) :
    MvPolynomial (Var lam) ℚ :=
  ∑ x, ∑ y, ∑ u, ∑ v, C (T x y u v) * mon x y u v

lemma poly4_add (T T' : Idx lam → Idx lam → Idx lam → Idx lam → ℚ) :
    poly4 (fun x y u v => T x y u v + T' x y u v) = poly4 T + poly4 T' := by
  simp only [poly4, C_add, add_mul, Finset.sum_add_distrib]

lemma poly4_zero : poly4 (lam := lam) (fun _ _ _ _ => 0) = 0 := by
  simp [poly4]

lemma poly4_sum {ι : Type*} (s : Finset ι) (T : ι → Idx lam → Idx lam → Idx lam → Idx lam → ℚ) :
    ∑ i ∈ s, poly4 (T i) = poly4 (fun x y u v => ∑ i ∈ s, T i x y u v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [poly4_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih]
    simp only [Finset.sum_insert ha]
    rw [poly4_add]

lemma poly4_cross (d : ℚ) :
    poly4 (lam := lam) (fun x y u v => d * (if x = v ∧ y = u then (1 : ℚ) else 0)) =
      C d * sos lam := by
  have h : ∀ x y : Idx lam,
      (∑ u, ∑ v, C (d * (if x = v ∧ y = u then (1 : ℚ) else 0)) * mon x y u v) =
        C d * (X (Sum.inl x) ^ 2 * X (Sum.inr y) ^ 2) := by
    intro x y
    rw [Fintype.sum_eq_single y]
    · rw [Fintype.sum_eq_single x]
      · simp only [and_self, if_true, mul_one, mon]
        ring
      · intro v hv
        simp [Ne.symm hv]
    · intro u hu
      apply Finset.sum_eq_zero
      intro v _
      simp [Ne.symm hu]
  unfold poly4
  simp only [h]
  unfold sos
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]

lemma bil_smul (r : ℚ) (F : Idx lam → Idx lam → ℚ) :
    bil (fun x y => r * F x y) = C r * bil F := by
  simp only [bil, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [C_mul]
  ring

lemma reorder5 {M : Type*} [AddCommMonoid M] {α β : Type*} [Fintype α] [Fintype β]
    (f : α → α → α → α → β → M) :
    ∑ x, ∑ y, ∑ u, ∑ v, ∑ θ, f x y u v θ = ∑ θ, ∑ x, ∑ y, ∑ u, ∑ v, f x y u v θ := by
  symm
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]

lemma bil_mul_bil (F G : Idx lam → Idx lam → ℚ) :
    bil F * bil G = ∑ x, ∑ y, ∑ v, ∑ u,
      C (F x y) * C (G v u) * (X (Sum.inl x) * X (Sum.inr y) * X (Sum.inl v) * X (Sum.inr u)) := by
  unfold bil
  rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ => ?_
  ring

/-- One piece, row-wise: T(x,y,u,v) = Σ_θ F(x,y,θ)·G(u,v,θ). -/
lemma poly4_row {a : ℕ} (T : Idx lam → Idx lam → Idx lam → Idx lam → ℚ)
    (F G : Idx lam × Idx lam → Pieces.Bits a → ℚ)
    (hT : ∀ x y u v, T x y u v = ∑ θ, F (x, y) θ * G (u, v) θ) :
    poly4 T = ∑ θ, bil (fun x y => F (x, y) θ) * bil (fun v u => G (u, v) θ) := by
  simp only [bil_mul_bil]
  conv_lhs => simp only [poly4, hT, map_sum, Finset.sum_mul]
  conv_lhs => rw [reorder5]
  refine Finset.sum_congr rfl fun θ _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun y _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
  simp only [C_mul, mon]
  try ring

/-- One piece, column-wise: T(x,y,u,v) = Σ_θ H(x,u,θ)·J(y,v,θ). -/
lemma poly4_col {b : ℕ} (T : Idx lam → Idx lam → Idx lam → Idx lam → ℚ)
    (H J : Idx lam × Idx lam → Pieces.Bits b → ℚ)
    (hT : ∀ x y u v, T x y u v = ∑ θ, H (x, u) θ * J (y, v) θ) :
    poly4 T = ∑ θ, bil (fun x u => H (x, u) θ) * bil (fun v y => J (y, v) θ) := by
  simp only [bil_mul_bil]
  conv_lhs => simp only [poly4, hT, map_sum, Finset.sum_mul]
  conv_lhs => rw [reorder5]
  refine Finset.sum_congr rfl fun θ _ => Finset.sum_congr rfl fun x _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [C_mul, mon]
  try ring

/-- Re-index a decomposition by `Fin n`. -/
lemma reindex {ι : Type*} [Fintype ι] {n : ℕ} (hn : Fintype.card ι = n)
    (P : MvPolynomial (Var lam) ℚ) (F G : ι → Idx lam → Idx lam → ℚ)
    (h : P = ∑ i, bil (F i) * bil (G i)) :
    ∃ fs gs : Fin n → Idx lam → Idx lam → ℚ, P = ∑ k, bil (fs k) * bil (gs k) := by
  let e := Fintype.equivFinOfCardEq hn
  refine ⟨fun k => F (e.symm k), fun k => G (e.symm k), ?_⟩
  rw [h]
  exact (e.symm.sum_comp (fun i => bil (F i) * bil (G i))).symm

/-- One piece: the cheaper of its two factorizations gives 2^min(a,b) products. -/
lemma piece_decomp (T : Pieces.Four lam) (a b : ℕ) (B : ℤ)
    (hr : Pieces.FactorsThrough (Pieces.rowwise T) a B)
    (hc : Pieces.FactorsThrough (Pieces.colwise T) b B) :
    ∃ fs gs : Fin (2 ^ min a b) → Idx lam → Idx lam → ℚ,
      poly4 (fun x y u v => (T x y u v : ℚ)) = ∑ k, bil (fs k) * bil (gs k) := by
  by_cases hab : a ≤ b
  · obtain ⟨f, f', hff, -, -⟩ := hr
    have hT : ∀ x y u v, ((T x y u v : ℤ) : ℚ) =
        ∑ θ, ((f (x, y) θ : ℤ) : ℚ) * ((f' (u, v) θ : ℤ) : ℚ) := by
      intro x y u v
      have := hff (x, y) (u, v)
      simp only [Pieces.rowwise] at this
      exact_mod_cast this
    have hcard : Fintype.card (Pieces.Bits a) = 2 ^ min a b := by
      rw [min_eq_left hab]; simp
    exact reindex hcard _ _ _ (poly4_row _ (fun p θ => (f p θ : ℚ)) (fun p θ => (f' p θ : ℚ)) hT)
  · obtain ⟨f, f', hff, -, -⟩ := hc
    have hT : ∀ x y u v, ((T x y u v : ℤ) : ℚ) =
        ∑ θ, ((f (x, u) θ : ℤ) : ℚ) * ((f' (y, v) θ : ℤ) : ℚ) := by
      intro x y u v
      have := hff (x, u) (y, v)
      simp only [Pieces.colwise] at this
      exact_mod_cast this
    have hcard : Fintype.card (Pieces.Bits b) = 2 ^ min a b := by
      rw [min_eq_right (by omega)]; simp
    exact reindex hcard _ _ _ (poly4_col _ (fun p θ => (f p θ : ℚ)) (fun p θ => (f' p θ : ℚ)) hT)

/-- All pieces together: Σ_s 2^min(crow s, ccol s) products, divided by d. -/
lemma decomp_of_family {ρ : ℝ} {c : ℕ} (P : Pieces.Family lam) (hP : P.Is ρ c) :
    ∃ (K : ℕ) (f g : Fin K → Idx lam → Idx lam → ℚ),
      K = ∑ s ∈ P.I, 2 ^ min (P.crow s) (P.ccol s) ∧ sos lam = ∑ k, bil (f k) * bil (g k) := by
  have hpiece : ∀ s ∈ P.I, ∃ fs gs : Fin (2 ^ min (P.crow s) (P.ccol s)) → Idx lam → Idx lam → ℚ,
      poly4 (fun x y u v => (P.A s x y u v : ℚ)) = ∑ k, bil (fs k) * bil (gs k) :=
    fun s hs => piece_decomp _ _ _ _ (hP.row s hs) (hP.col s hs)
  choose fs gs hfg using hpiece
  have hd : (P.d : ℚ) ≠ 0 := by
    have := hP.d_pos
    exact_mod_cast (show P.d ≠ 0 by omega)
  let F : (Σ s : P.I, Fin (2 ^ min (P.crow s) (P.ccol s))) → Idx lam → Idx lam → ℚ :=
    fun i x y => (1 / (P.d : ℚ)) * fs i.1.1 i.1.2 i.2 x y
  let G : (Σ s : P.I, Fin (2 ^ min (P.crow s) (P.ccol s))) → Idx lam → Idx lam → ℚ :=
    fun i => gs i.1.1 i.1.2 i.2
  have hsum : sos lam = ∑ i, bil (F i) * bil (G i) := by
    have h1 : ∀ i, bil (F i) * bil (G i) =
        C (1 / (P.d : ℚ)) * (bil (fs i.1.1 i.1.2 i.2) * bil (gs i.1.1 i.1.2 i.2)) := by
      intro i
      simp only [F, G]
      rw [bil_smul]
      ring
    simp only [h1, ← Finset.mul_sum]
    rw [Fintype.sum_sigma]
    have h2 : ∀ s : P.I, ∑ k, bil (fs s.1 s.2 k) * bil (gs s.1 s.2 k) =
        poly4 (fun x y u v => (P.A s.1 x y u v : ℚ)) := fun s => (hfg s.1 s.2).symm
    simp only [h2]
    rw [Finset.sum_coe_sort P.I (fun s => poly4 (fun x y u v => (P.A s x y u v : ℚ)))]
    rw [poly4_sum]
    have h3 : (fun x y u v => ∑ s ∈ P.I, (P.A s x y u v : ℚ)) =
        fun x y u v => (P.d : ℚ) * (if x = v ∧ y = u then (1 : ℚ) else 0) := by
      funext x y u v
      have := hP.sum_eq x y u v
      simp only [Pieces.cross] at this
      exact_mod_cast this
    rw [h3, poly4_cross, ← mul_assoc, ← C_mul, one_div, inv_mul_cancel₀ hd, map_one, one_mul]
  have hcard : Fintype.card (Σ s : P.I, Fin (2 ^ min (P.crow s) (P.ccol s))) =
      ∑ s ∈ P.I, 2 ^ min (P.crow s) (P.ccol s) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact Finset.sum_coe_sort P.I (fun s => 2 ^ min (P.crow s) (P.ccol s))
  obtain ⟨f, g, hfg'⟩ := reindex hcard _ F G hsum
  exact ⟨_, f, g, rfl, hfg'⟩

/-- The bound for one piece: 2^min(a,b) ≤ (2λ)^c · 2^(√2·λ) when a + b ≤ 4λ/√2 + c·log₂(2λ). -/
lemma two_pow_min_le {n c a b : ℕ} (hn : 1 ≤ n)
    (h : ((a + b : ℕ) : ℝ) ≤ 4 * (1 / Real.sqrt 2) * n + c * Real.logb 2 (2 * n)) :
    ((2 ^ min a b : ℕ) : ℝ) ≤ (2 * n : ℝ) ^ c * 2 ^ (Real.sqrt 2 * n) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 2 := by positivity
  have h4 : 4 * (1 / Real.sqrt 2) = 2 * Real.sqrt 2 := by
    field_simp
    nlinarith [hs2]
  have hL : (1 : ℝ) ≤ 2 * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hm : ((min a b : ℕ) : ℝ) ≤ Real.sqrt 2 * n + (c / 2) * Real.logb 2 (2 * n) := by
    have h2m : 2 * ((min a b : ℕ) : ℝ) ≤ ((a + b : ℕ) : ℝ) := by
      have : 2 * min a b ≤ a + b := by omega
      exact_mod_cast this
    rw [h4] at h
    linarith
  have key : (2 : ℝ) ^ ((min a b : ℕ) : ℝ) ≤ 2 ^ (Real.sqrt 2 * n) * (2 * n : ℝ) ^ ((c : ℝ) / 2) := by
    calc (2 : ℝ) ^ ((min a b : ℕ) : ℝ)
        ≤ 2 ^ (Real.sqrt 2 * n + (c / 2) * Real.logb 2 (2 * n)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hm
      _ = 2 ^ (Real.sqrt 2 * n) * (2 * n : ℝ) ^ ((c : ℝ) / 2) := by
          rw [Real.rpow_add (by norm_num), mul_comm ((c : ℝ) / 2),
            Real.rpow_mul (x := 2) (by norm_num) (Real.logb 2 (2 * n)) ((c : ℝ) / 2),
            Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
  have hc2 : (2 * n : ℝ) ^ ((c : ℝ) / 2) ≤ (2 * n : ℝ) ^ c := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith [show (0 : ℝ) ≤ c by positivity])
  have hpos : (0 : ℝ) ≤ 2 ^ (Real.sqrt 2 * n) := by positivity
  calc ((2 ^ min a b : ℕ) : ℝ) = (2 : ℝ) ^ ((min a b : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; push_cast; rfl
    _ ≤ 2 ^ (Real.sqrt 2 * n) * (2 * n : ℝ) ^ ((c : ℝ) / 2) := key
    _ ≤ 2 ^ (Real.sqrt 2 * n) * (2 * n : ℝ) ^ c := mul_le_mul_of_nonneg_left hc2 hpos
    _ = (2 * n : ℝ) ^ c * 2 ^ (Real.sqrt 2 * n) := by ring

end HurwitzSqrt2Proof

/-- The Hurwitz-type bound with N^(√2 + o(1)) products, from Theorem B. -/
theorem hurwitzSqrt2 : HurwitzSqrt2.Statement := by
  obtain ⟨c, hc⟩ := (show AppHalfPieces.ThmHalfPiecesPure from
    GeneralPieces.thmHalfPiecesPure AppHalfPieces.pieceFacts)
  refine ⟨2 * c, fun lam hlam => ?_⟩
  obtain ⟨mu, P, -, hP, -⟩ := hc lam hlam
  obtain ⟨K, f, g, hK, hsum⟩ := HurwitzSqrt2Proof.decomp_of_family P hP
  refine ⟨K, f, g, ?_, hsum⟩
  have hterm : ∀ s ∈ P.I, ((2 ^ min (P.crow s) (P.ccol s) : ℕ) : ℝ) ≤
      (2 * lam : ℝ) ^ c * 2 ^ (Real.sqrt 2 * lam) :=
    fun s hs => HurwitzSqrt2Proof.two_pow_min_le hlam (hP.caps s hs)
  have hI : ((#P.I : ℕ) : ℝ) ≤ (2 * lam : ℝ) ^ c := by exact_mod_cast hP.card_I
  rw [hK, Nat.cast_sum]
  calc ∑ s ∈ P.I, ((2 ^ min (P.crow s) (P.ccol s) : ℕ) : ℝ)
      ≤ ∑ s ∈ P.I, (2 * lam : ℝ) ^ c * 2 ^ (Real.sqrt 2 * lam) := Finset.sum_le_sum hterm
    _ = (#P.I : ℝ) * ((2 * lam : ℝ) ^ c * 2 ^ (Real.sqrt 2 * lam)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * lam : ℝ) ^ c * ((2 * lam : ℝ) ^ c * 2 ^ (Real.sqrt 2 * lam)) := by
        gcongr
    _ = (2 * lam : ℝ) ^ (2 * c) * 2 ^ (Real.sqrt 2 * lam) := by ring

#print axioms hurwitzSqrt2
