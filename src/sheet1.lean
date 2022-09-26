import data.polynomial.algebra_map
import data.nat.choose.cast
import number_theory.bernoulli
-- where do these files come from?

open_locale big_operators -- so that we can use `∑` instead of `finset.sum`
open_locale nat polynomial -- so that we can use `n!`
open nat finset
open power_series
open polynomial

-- taking A to be a commutative ring and a ℚ-algebra
variables (A : Type*) [comm_ring A] [algebra ℚ A]

-- Go check the definition of `bernoulli'`!
/-- The Bernoulli numbers are defined to be `bernoulli'` with a parity sign. -/
def bernoulli_neg (n : ℕ) : ℚ := (-1)^n * bernoulli' n

-- What does the `simp` tag do?
@[simp] lemma bernoulli_neg_zero : bernoulli_neg 0 = 1 := sorry

-- Try to solve this with and without `norm_num`
@[simp] lemma bernoulli_neg_one : bernoulli_neg 1 = -1/2 := sorry

-- What does the statement say? Write a docstring
theorem bernoulli_neg_eq_bernoulli'_of_ne_one {n : ℕ} (hn : n ≠ 1) : bernoulli_neg n = bernoulli' n :=
begin
  -- Step 1. Might be better to look at this by breaking into cases `n = 0` and `n ≠ 0`
  -- Try using `by_cases` for this.
  -- Step 2. Now it might help to further split n into odd and even, how can you do that using `cases`?
  sorry,
end

-- Challenge!
-- What does the statement say? Write a docstring ; how do you get the `∑` symbol?
@[simp] theorem sum_bernoulli_neg (n : ℕ) :
  ∑ k in range n, (n.choose k : ℚ) * bernoulli_neg k = if n = 1 then 1 else 0 :=
begin
  -- Step 1. Break this into cases when n is 0 or nonzero. How is this different from using `by_cases`?
  -- Step 2. You will be needing cases again.
  -- Step 3. Find a way to make this a sum upto n. 
  -- Hint : It might help to prove that ∑_{i = 0}^{n - 1} ((n + 2) choose (i + 2)) * B_{i + 2} = n/2
  -- Can you rewrite this sum in valid Lean code?
  -- Step 4. Use a property of sum of bernoulli'
  -- Step 5. ring : New tactic unlocked! 
  sorry,
end