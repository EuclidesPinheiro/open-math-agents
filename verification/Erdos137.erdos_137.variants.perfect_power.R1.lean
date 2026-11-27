import FormalConjectures.ErdosProblems.«137»

namespace OMA.R_Erdos137_erdos_137_variants_perfect_power_R1

open Finset

-- Two consecutive positive integers are coprime. If their product
-- is an lth power, both are lth powers, which cannot be consecutive.
def H1 : Prop :=
  ∀ (n x l : ℕ), 2 ≤ l → (∏ m ∈ Ioc n (n + 2), m) ≠ x ^ l

-- Below the least prime at least k, Bertrand's postulate provides
-- a prime that occurs exactly once in the product.
def H2 : Prop :=
  ∀ (k n : ℕ), 3 ≤ k → (¬ ∃ q : ℕ, k ≤ q ∧ q ≤ n + k ∧ q.Prime) →
    ∃ p : ℕ, p.Prime ∧ (∏ m ∈ Ioc n (n + k), m).factorization p = 1

-- Erdős and Selfridge, Theorem 2. A prime at least k has
-- multiplicity that is not divisible by l.
def H3 : Prop :=
  ∀ (k n l : ℕ), 3 ≤ k → 2 ≤ l → (∃ q : ℕ, k ≤ q ∧ q ≤ n + k ∧ q.Prime) →
    ∃ p : ℕ, k ≤ p ∧ p.Prime ∧ ¬ l ∣ (∏ m ∈ Ioc n (n + k), m).factorization p

theorem main : H1 → H2 → H3 → type_of% @Erdos137.erdos_137.variants.perfect_power := by
  intro hPair hSmall hLarge k hk n x l hl
  by_cases hTwo : k = 2
  · subst k
    exact hPair n x l hl
  have hk' : 3 ≤ k := by omega
  intro hPower
  have hDiv (p : ℕ) : l ∣ (∏ m ∈ Ioc n (n + k), m).factorization p := by
    rw [hPower, Nat.factorization_pow]
    exact ⟨x.factorization p, rfl⟩
  by_cases hPrime : ∃ q : ℕ, k ≤ q ∧ q ≤ n + k ∧ q.Prime
  · obtain ⟨p, _, _, hp⟩ := hLarge k n l hk' hl hPrime
    exact hp (hDiv p)
  · obtain ⟨p, _, hp⟩ := hSmall k n hk' hPrime
    have hOne := hDiv p
    rw [hp] at hOne
    have hLe : l ≤ 1 := Nat.le_of_dvd (by decide) hOne
    omega

end OMA.R_Erdos137_erdos_137_variants_perfect_power_R1
