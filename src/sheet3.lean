import number_theory.bernoulli_polynomials

open finset polynomial
open_locale big_operators

-- Today's aim:   to prove this
-- Bernoulli polynomials multiplication theorem :
--  For k ≥ 1, B_m(k*x) = k^{m - 1} ∑ i in range k, B_m (x + i / k).

theorem bernoulli_eval_mul (m : ℕ) {k : ℕ} (hk : k ≠ 0) (x : ℚ) :
  (polynomial.bernoulli m).eval ((k : ℚ) * x) =
  k^(m - 1 : ℤ) * ∑ i in finset.range k, (polynomial.bernoulli m).eval (x + i / k) := 
begin
-- why is k ≠ 0 needed?
-- Step 1 : it suffices to prove that :
-- ∑_{i = 0}^{k - 1} ∑_{j = 0}^∞ k^{j - 1} / j! B_j (X + i/k) X^j * (e^X - 1) * (e^{kX} - 1) = (∑_{j = 0}^∞ B_j(kX)/j!) * (e^X - 1) * (e^{kX} - 1)
-- Note that you will need to use `power_series.mk` for this
-- You might want to look through the `power_series` library well
-- You might also want to look at `rescale` and `exp`
-- Another helpful lemma might be `bernoulli_generating_function`
  sorry
end
