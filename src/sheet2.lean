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
noncomputable def bernoulli_poly (n : ℕ) : ℚ[X] := sorry

-- Now make an API for your definition
lemma bernoulli_poly_def (n : ℕ) : bernoulli_poly n = sorry :=
begin
-- Hint : Some useful lemmas might be `sum_range_reflect` and `sum_congr`
  sorry
end

-- You can also look up and prove some more properties, such as B_0(X) = 1 etc.

@[simp] theorem sum_bernoulli_poly (n : ℕ) :
  ∑ k in range (n + 1), ((n + 1).choose k : ℚ) • bernoulli_poly k =
    polynomial.monomial n (n + 1 : ℚ) :=
begin
-- `simp_rw`: new tactic unlocked!
-- the proof depends on your def, so no hints :( ask me for help!
-- always remember to first have a clear pen and paper proof!
  sorry
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