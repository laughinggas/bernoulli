import sheet1
import data.polynomial.ring_division

open_locale big_operators -- so that we can use `∑` instead of `finset.sum`
open_locale nat polynomial -- so that we can use `n!`
open nat finset
open power_series
open polynomial

--Today we construct the Bernoulli polynomials

-- taking A to be a commutative ring and a ℚ-algebra
variables {A : Type*} [comm_ring A] [algebra ℚ A]

/-- The Bernoulli polynomials are defined in terms of the negative Bernoulli numbers 
as `∑_{i = 0}^{n} (n choose i) B_i X^{n - i}`. -/
noncomputable def bernoulli_poly (n : ℕ) : ℚ[X] :=
  ∑ i in range (n + 1), (↑(n.choose i) * bernoulli_neg i) • X ^ (n - i)

-- Now make an API for your definition
lemma bernoulli_poly_def (n : ℕ) :
  bernoulli_poly n = ∑ i in range (n + 1), (↑(n.choose i) * bernoulli_neg i) • X ^ (n - i) :=
rfl
-- You can also look up and prove some more properties, such as B_0(X) = 1 etc.

@[simp] lemma bernoulli_poly_zero : bernoulli_poly 0 = 1 :=
by simp [bernoulli_poly_def]

@[simp] lemma bernoulli_poly_eval_zero (n : ℕ) : (bernoulli_poly n).eval 0 = bernoulli_neg n :=
begin
  rw [bernoulli_poly_def, ←coeff_zero_eq_eval_zero, finset_sum_coeff],
  simp_rw [polynomial.coeff_smul, algebra.id.smul_eq_mul],
  convert_to ∑ x in range (n + 1), (if x = n then ↑(n.choose x) * bernoulli_neg x else 0) = _,
  { refine sum_congr rfl (λ x hx, _),
    split_ifs,
    { simp [h] },
    replace hx := (le_of_lt_succ $ mem_range.mp hx).lt_of_ne h,
    rw [polynomial.coeff_X_pow, if_neg (tsub_pos_iff_lt.mpr hx).ne, mul_zero] },
  simp
end

@[simp] lemma bernoulli_poly_eval_one (n : ℕ) : (bernoulli_poly n).eval 1 = bernoulli' n :=
begin
  simp_rw [bernoulli_poly_def, eval_finset_sum, eval_smul, eval_pow, eval_X, one_pow],
  simp only [rat.smul_one_eq_coe, rat.cast_eq_id, id.def],
  rw [sum_range_succ, sum_bernoulli_neg, choose_self, nat.cast_one, one_mul, bernoulli'_eq]
end

lemma sum_zero {α β} {s : finset α} [add_comm_monoid β] : ∑ x in s, (0 : β) = 0 :=
sum_eq_zero $ λ x hx, rfl

@[simp] theorem sum_bernoulli_poly_aux (n : ℕ) :
  ∑ k in range (n + 1), ((n + 1).choose k : ℚ) • bernoulli_poly k =
    polynomial.monomial n (n + 1 : ℚ) :=
begin
  ext1 t,
  rw [finset_sum_coeff, polynomial.coeff_monomial],
  simp_rw [polynomial.coeff_smul, bernoulli_poly, finset_sum_coeff, polynomial.coeff_smul,
           polynomial.coeff_X_pow],
  simp_rw [smul_ite, sum_ite, smul_zero, sum_zero, add_zero, smul_sum, algebra.id.smul_eq_mul,
           mul_one],
  split_ifs; sorry
end


@[simp] theorem sum_bernoulli_poly (n : ℕ) :
  ∑ k in range n, (n.choose k : ℚ) • bernoulli_poly k =
    polynomial.monomial (n - 1) (n : ℚ) :=
begin
  cases n,
  { simp },
  convert sum_bernoulli_poly_aux n,
  norm_cast,
end


variable {A}

/-- The theorem that `∑ Bₙ(t) X^n/n!) (e^X-1) = Xe^{tX}`  -/
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
