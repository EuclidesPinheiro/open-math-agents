import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1
import Mathlib.NumberTheory.Bertrand

namespace OMA.R_Erdos137_erdos_137_variants_perfect_power_R1_H3_R1

open Finset

-- The square case of Erdős and Selfridge, Theorem 2, Section 3.
def H1 : Prop :=
  ∀ (k n : ℕ), 3 ≤ k → k < n →
    ∃ p : ℕ, k ≤ p ∧ p.Prime ∧ ¬ 2 ∣ (∏ m ∈ Ioc n (n + k), m).factorization p

-- The odd prime exponent case of Erdős and Selfridge, Theorem 2, Section 2.
def H2 : Prop :=
  ∀ (k n l : ℕ), 3 ≤ k → k < n → l.Prime → 2 < l →
    ∃ p : ℕ, k ≤ p ∧ p.Prime ∧ ¬ l ∣ (∏ m ∈ Ioc n (n + k), m).factorization p

lemma multiplicity_one_of_large_prime (n k p : ℕ) (hp : p.Prime)
    (hMem : p ∈ Ioc n (n + k)) (hLarge : n + k < 2 * p) :
    (∏ m ∈ Ioc n (n + k), m).factorization p = 1 := by
  have hNonzero : ∀ m ∈ Ioc n (n + k), m ≠ 0 := by
    intro m hm
    have hLower := (mem_Ioc.mp hm).1
    omega
  rw [Nat.factorization_prod hNonzero, Finsupp.finsetSum_apply, Finset.sum_eq_single p]
  · exact hp.factorization_self
  · intro m hm hne
    apply Nat.factorization_eq_zero_of_not_dvd
    rintro ⟨a, ha⟩
    have hUpper := (mem_Ioc.mp hm).2
    have hSmall : a < 2 := by
      by_contra! hTwo
      have hMul := Nat.mul_le_mul_left p hTwo
      omega
    rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl
    · exact hNonzero m hm (by simpa using ha)
    · exact hne (by simpa using ha)
  · intro hMissing
    exact (hMissing hMem).elim

theorem main : H1 → H2 → OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H3 := by
  intro hSquare hOdd k n l hk hl hPrime
  by_cases hn : k < n
  · obtain ⟨r, hr, hrl⟩ := Nat.exists_prime_and_dvd (n := l) (by omega)
    have hrLower := hr.two_le
    have hResult : ∃ p : ℕ, k ≤ p ∧ p.Prime ∧
        ¬ r ∣ (∏ m ∈ Ioc n (n + k), m).factorization p := by
      by_cases hrTwo : r = 2
      · subst r
        exact hSquare k n hk hn
      · exact hOdd k n r hk hn hr (by omega)
    obtain ⟨p, hpk, hp, hpNot⟩ := hResult
    exact ⟨p, hpk, hp, fun hdvd => hpNot (dvd_trans hrl hdvd)⟩
  · have hIn : ∃ p : ℕ, k ≤ p ∧ p.Prime ∧ p ∈ Ioc n (n + k) ∧ n + k < 2 * p := by
      by_cases hn' : n < k
      · obtain ⟨p, hpk, hpTop, hp⟩ := hPrime
        exact ⟨p, hpk, hp, mem_Ioc.mpr ⟨by omega, hpTop⟩, by omega⟩
      · obtain ⟨p, hp, hpLower, hpUpper⟩ := Nat.bertrand k (by omega)
        exact ⟨p, by omega, hp, mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
    obtain ⟨p, hpk, hp, hMem, hLarge⟩ := hIn
    refine ⟨p, hpk, hp, ?_⟩
    rw [multiplicity_one_of_large_prime n k p hp hMem hLarge, Nat.dvd_one]
    omega

end OMA.R_Erdos137_erdos_137_variants_perfect_power_R1_H3_R1
