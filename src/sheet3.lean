import number_theory.bernoulli_polynomials

open finset polynomial power_series
open_locale big_operators nat

local notation `𝔹` := polynomial.bernoulli
local notation `psm` := power_series.mk

-- Today's aim:   to prove this
-- Bernoulli polynomials multiplication theorem :
--  For k ≥ 1, B_m(k*x) = k^{m - 1} ∑ i in range k, B_m (x + i / k).

-- nontrivial R comes for free but I cba
theorem exp_ne_constant {R} [ring R] [nontrivial R] [algebra ℚ R] (a : R) : exp R ≠ a • 1 :=
λ h, by simpa using power_series.ext_iff.mp h 1

theorem rescale_ne_constant {R} [comm_semiring R] [no_zero_divisors R]
  (s : power_series R) {a : R} (ha : a ≠ 0) (b : R) (hc : ∀ a : R, s ≠ a • 1) :
  rescale a s ≠ b • 1 := λ h, hc b
begin
  ext (-|t),
  simpa using power_series.ext_iff.mp h 0,
  simpa [ha] using power_series.ext_iff.mp h t.succ
end

theorem bernoulli_eval_mul (m : ℕ) {k : ℕ} (hk : k ≠ 0) (y : ℚ) :
  (polynomial.bernoulli m).eval ((k : ℚ) * y) =
  k^(m - 1 : ℤ) * ∑ i in finset.range k, (polynomial.bernoulli m).eval (y + i / k) := 
begin
-- Step 1 : it suffices to prove that :
-- ∑_{j = 0}^∞ k^{j - 1} / j! B_j (∑_{i = 0}^{k - 1} (X + i/k)) X^j * (e^X - 1) * (e^{kX} - 1) = (∑_{j = 0}^∞ B_j(kx)/j! * X^j) * (e^X - 1) * (e^{kX} - 1)
  suffices : psm (λ j, ((k : ℚ) ^ (j - 1 : ℤ) / j!) * ∑ i in range k, (𝔹 m).eval (y + i / k)) * (exp ℚ - 1) * (rescale ↑k (exp ℚ) - 1) =
    psm (λ j, (1 / j! : ℚ) * (𝔹 m).eval (k * y) ) * (exp ℚ - 1) * (rescale ↑k (exp ℚ) - 1),
    { replace := mul_right_cancel₀ _ (mul_right_cancel₀ _ this),
    have hm : (m! : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero,
    replace := power_series.ext_iff.mp this m,
    simp only [coeff_mk, one_div, coe_aeval_eq_eval, eval_smul,
               algebra.id.smul_eq_mul, eq_inv_mul_iff_mul_eq₀ hm] at this,
    rw [←this, ←mul_assoc (m! : ℚ), ←mul_div_assoc, mul_div_cancel_left _ hm],
    all_goals { rw sub_ne_zero },
    { convert exp_ne_constant (1 : ℚ),
      simp },
    { convert rescale_ne_constant _ _ _ _,
      exact (one_smul _ 1).symm,
      apply_instance,
      exact_mod_cast hk,
      exact exp_ne_constant } },

    -- (e^x - 1) = ∑ (n ≥ 0) x^{n+1}/(n+1)!
    -- (exp ℚ - 1) = ∑
    sorry,

end

