import sheet1

open_locale big_operators -- so that we can use `∑` instead of `finset.sum`
open_locale nat polynomial -- so that we can use `n!`
open nat finset
open power_series
open polynomial

--Today we construct the Bernoulli polynomials

-- taking A to be a commutative ring and a ℚ-algebra
variables {A : Type*} [comm_ring A] [algebra ℚ A]

/-- The Bernoulli polynomials are defined in terms of the negative Bernoulli numbers as `∑_{i = 0}^{n} (n choose i) B_i X^{n - i}`. -/
noncomputable def bernoulli_poly (n : ℕ) : ℚ[X] := 
  ∑ i in range (n + 1), polynomial.monomial (n - i) ((bernoulli_neg i) * (n.choose i))

lemma bernoulli_poly_def (n : ℕ) : bernoulli_poly n = ∑ i in range (n + 1), polynomial.monomial i ((bernoulli_neg (n - i)) * (n.choose i)) :=
begin
  rw ←sum_range_reflect,
  simp,
  rw [bernoulli_poly, sum_congr rfl],
  intros k h,
  rw nat.choose_symm _,
  { rw nat.sub_sub_self (mem_range_succ_iff.1 h) },
  rw mem_range at h,
  exact lt_succ_iff.mp h
end

-- You can also look up and prove some more properties, such as B_0(X) = 1 etc.

@[simp] theorem sum_bernoulli_poly (n : ℕ) :
  ∑ k in range (n + 1), ((n + 1).choose k : ℚ) • bernoulli_poly k =
    polynomial.monomial n (n + 1 : ℚ) :=
begin
-- `simp_rw`: new tactic unlocked!
-- the proof depends on your def, so no hints :( ask me for help!
-- always remember to first have a clear pen and paper proof!

-- not my own proof, based off `sum_bernoulli` in `number_theory.bernoulli_polynomials`

  -- ∑ (k = 0 to n) (n+1) choose k • BPₖ = (n + 1) xⁿ
  -- sub in definition of bernoulli polynomial `bernoulli_poly_def` to get
  --    ∑ (k = 0 to n) (n+1) choose k • (∑ (i = 0 to k) k choose i * B⁻(k-i) * xⁱ) = (n + 1) xⁿ
  -- take scalar multiplication in to inner sum
  --    ∑ (k = 0 to n) (∑ (i = 0 to k) [(n+1) choose k] • [k choose i] * B⁻(n-i) * xⁱ) = (n + 1) xⁿ
  -- technical details switching `range` to `Ico`
  -- change to the different way of summing over `(k,i)` in the range `0 ≤ i ≤ k < n + 1` (switch indices)
  --    ∑ (i = 0 to n) (∑ (k = i to n) [(n+1) choose k] • [k choose i] * B⁻(n-i) * xⁱ) = (n + 1) xⁿ
  -- Take back to range (starting at 0)
  --    ∑ (i = 0 to n) (∑ (k = 0 to n - i) [(n+1) choose (k + i)] • [k choose i] * B⁻(n-i) * xⁱ) = (n + 1) xⁿ
  simp_rw [bernoulli_poly_def, finset.smul_sum, finset.range_eq_Ico, ←finset.sum_Ico_Ico_comm,
    finset.sum_Ico_eq_sum_range],

  -- 
  -- ∑ (i = 0 to n) (∑ (k = 0 to n - i) B⁻(k) * [(k+i) choose i] xⁱ) = (n + 1) xⁿ
  simp only [add_tsub_cancel_left, tsub_zero, zero_add, linear_map.map_add], -- deleted `cast_succ`


  simp_rw [smul_monomial, mul_comm (_root_.bernoulli_neg _) _, smul_eq_mul, ←mul_assoc], -- what is the `_root_.` in `_root_.bernoulli_neg` for?
  conv_lhs { apply_congr, skip, conv
    { apply_congr, skip,
      rw [← nat.cast_mul, choose_mul ((le_tsub_iff_left $ mem_range_le H).1
        $ mem_range_le H_1) (le.intro rfl), nat.cast_mul, add_comm x x_1, add_tsub_cancel_right,
        mul_assoc, mul_comm, ←smul_eq_mul, ←smul_monomial] },
    rw [←sum_smul], },
  rw [sum_range_succ_comm],
  simp only [add_right_eq_self, cast_succ, mul_one, cast_one, cast_add, add_tsub_cancel_left,
    choose_succ_self_right, one_smul, _root_.bernoulli_neg_zero, sum_singleton, zero_add,
    linear_map.map_add, range_one],
  apply sum_eq_zero (λ x hx, _),
  have f : ∀ x ∈ range n, ¬ n + 1 - x = 1,
  { rintros x H, rw [mem_range] at H,
    rw [eq_comm],
    exact ne_of_lt (nat.lt_of_lt_of_le one_lt_two (le_tsub_of_add_le_left (succ_le_succ H))) },
  rw [sum_bernoulli_neg],
  have g : (ite (n + 1 - x = 1) (1 : ℚ) 0) = 0,
  { simp only [ite_eq_right_iff, one_ne_zero],
    intro h₁,
    exact (f x hx) h₁, },
  rw [g, zero_smul],
end

variable {A}

/-- The theorem that `∑ Bₙ(t)X^n/n!)(e^X-1)=Xe^{tX}`  -/
theorem bernoulli_generating_function (t : A) :
  mk (λ n, aeval t ((1 / n! : ℚ) • bernoulli_poly n)) * (exp A - 1) =
    power_series.X * rescale t (exp A) :=
begin
  -- check equality of power series by checking coefficients of X^n

  -- n = 0 case solved by `simp`

  -- n ≥ 1, the coefficients is a sum to n+2, so use `sum_range_succ` to write as
  -- last term plus sum to n+1

  -- last term is zero so kill with `add_zero`
 
  -- Let's multiply both sides by (n+1)! (OK because it's a unit)
  
  -- now tidy up unit mess and generally do trivial rearrangements
  -- to make RHS (n+1)*t^n

  -- But this is the RHS of `sum_bernoulli_poly`
 
  -- and now we have to prove a sum is a sum, but all the terms are equal.

  -- The rest is just trivialities, hampered by the fact that we're coercing
  -- factorials and binomial coefficients between ℕ and ℚ and A.

  -- deal with coefficients of e^X-1

  -- finally cancel the Bernoulli polynomial and the algebra_map
  sorry,
end