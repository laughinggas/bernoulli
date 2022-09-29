import number_theory.bernoulli_polynomials

open finset polynomial power_series
open_locale big_operators nat

local notation `𝔹` := polynomial.bernoulli
local notation `psm` := power_series.mk

-- Today's aim:   to prove this
-- Bernoulli polynomials multiplication theorem :
--  For k ≥ 1, B_m(k*x) = k^{m - 1} ∑ i in range k, B_m (x + i / k).

theorem bernoulli_eval_mul (m : ℕ) {k : ℕ} (hk : k ≠ 0) (y : ℚ) :
  (polynomial.bernoulli m).eval ((k : ℚ) * y) =
  k^(m - 1 : ℤ) * ∑ i in finset.range k, (polynomial.bernoulli m).eval (y + i / k) := 
begin
-- why is k ≠ 0 needed?
-- Step 1 : it suffices to prove that :
-- ∑_{j = 0}^∞ k^{j - 1} / j! B_j (∑_{i = 0}^{k - 1} (X + i/k)) X^j * (e^X - 1) * (e^{kX} - 1) = (∑_{j = 0}^∞ B_j(kx)/j! * X^j) * (e^X - 1) * (e^{kX} - 1)
-- Note that you will need to use `power_series.mk` for this
-- You might want to look through the `power_series` library well
-- You might also want to look at `rescale` and `exp`
-- Another helpful lemma might be `bernoulli_generating_function`

  suffices : psm (λ j, ((k : ℚ) ^ (j - 1 : ℤ) / j!) * ∑ i in range k, (𝔹 m).eval (y + i / k)) * (exp ℚ - 1) * (rescale ↑k (exp ℚ) - 1) =
             psm (λ j, aeval (↑k * y) ((1 / j! : ℚ) • bernoulli j)) * (exp ℚ - 1) * (rescale ↑k (exp ℚ) - 1),
  { replace := mul_right_cancel₀ _ (mul_right_cancel₀ _ this),
    have hm : (m! : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero,
    replace := power_series.ext_iff.mp this m,
    simp only [coeff_mk, one_div, coe_aeval_eq_eval, eval_smul,
               algebra.id.smul_eq_mul, eq_inv_mul_iff_mul_eq₀ hm] at this,
    rw [←this, ←mul_assoc (m! : ℚ), ←mul_div_assoc, mul_div_cancel_left _ hm],
    all_goals { rw sub_ne_zero },
  },

end
