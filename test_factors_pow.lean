import Mathlib.Tactic.Simproc.Factors
import Mathlib.Data.Nat.Factors

-- Test with concrete powers
example : Nat.primeFactorsList (2^3) = [2, 2, 2] := by simp only [Nat.primeFactorsList_ofNat]
example : Nat.primeFactorsList (2^5) = [2, 2, 2, 2, 2] := by simp only [Nat.primeFactorsList_ofNat]
example : Nat.primeFactorsList (3^4) = [3, 3, 3, 3] := by simp only [Nat.primeFactorsList_ofNat]

-- Test if it works with variable exponents
example (n : ℕ) : Nat.primeFactorsList (2^n) = List.replicate n 2 := by
  -- This won't work with just simp
  -- simp only [Nat.primeFactorsList_ofNat] -- This fails
  simp only [Nat.Prime.primeFactorsList_pow Nat.prime_two]

-- The simproc only works when the argument is a concrete numeral
example : Nat.primeFactorsList 8 = [2, 2, 2] := by simp only [Nat.primeFactorsList_ofNat]
example : Nat.primeFactorsList 16 = [2, 2, 2, 2] := by simp only [Nat.primeFactorsList_ofNat]
example : Nat.primeFactorsList 32 = [2, 2, 2, 2, 2] := by simp only [Nat.primeFactorsList_ofNat]