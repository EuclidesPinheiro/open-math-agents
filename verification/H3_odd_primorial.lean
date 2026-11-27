import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

/-! The elementary factorial estimate used for the odd-exponent tail. -/

namespace Erdos137OddPrimorial

open Finset

def factorialNumerator (n : ℕ) : ℕ :=
  n.factorial * (n/30).factorial

def factorialDenominator (n : ℕ) : ℕ :=
  (n/2).factorial * (n/3).factorial * (n/5).factorial

def upperWeight (n : ℕ) : ℕ := n+n/30

def lowerWeight (n : ℕ) : ℕ := n/2+n/3+n/5

lemma lower_weight_le (n : ℕ) : lowerWeight n ≤ upperWeight n := by
  have hTable : ∀ r : Fin 30, lowerWeight r.val ≤ upperWeight r.val := by decide
  have hR := hTable ⟨n%30,Nat.mod_lt _ (by decide)⟩
  have h₂ : n/2 = 15*(n/30)+(n%30)/2 := by omega
  have h₃ : n/3 = 10*(n/30)+(n%30)/3 := by omega
  have h₅ : n/5 = 6*(n/30)+(n%30)/5 := by omega
  simp only [upperWeight,lowerWeight] at hR ⊢
  omega

lemma lower_weight_add_one_le {n : ℕ} (h₁ : 1 ≤ n) (h₅ : n ≤ 5) :
    lowerWeight n+1 ≤ upperWeight n := by
  interval_cases n <;> decide

def primeBand (n : ℕ) : Finset ℕ :=
  (Ioc (n/6) n).filter Nat.Prime

def primeBandProduct (n : ℕ) : ℕ := ∏ p ∈ primeBand n, p

lemma band_product_mul_primorial (n : ℕ) :
    primorial (n/6)*primeBandProduct n = primorial n := by
  have hSets : n.primesLE = (n/6).primesLE ∪ primeBand n := by
    ext p
    simp only [Nat.primesLE, Nat.primesBelow, primeBand, mem_union, mem_filter, mem_Ioc, mem_range]
    omega
  have hDisj : Disjoint (n/6).primesLE (primeBand n) := by
    rw [Finset.disjoint_left]
    intro p hLo hHi
    simp only [Nat.primesLE, Nat.primesBelow, primeBand, mem_filter, mem_Ioc, mem_range] at hLo hHi
    omega
  rw [primorial_eq_prod_primesLE, primeBandProduct, primorial_eq_prod_primesLE, hSets,
    Finset.prod_union hDisj]

lemma band_product_ne_zero (n : ℕ) : primeBandProduct n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (mem_filter.mp hp).2.ne_zero

lemma band_product_factorization (n p : ℕ) :
    (primeBandProduct n).factorization p = if p ∈ primeBand n then 1 else 0 := by
  have hPrime : ∀ q ∈ primeBand n, q.Prime := fun q hq => (mem_filter.mp hq).2
  unfold primeBandProduct
  rw [Nat.factorization_prod (fun q hq => (hPrime q hq).ne_zero), Finsupp.finsetSum_apply]
  have hZero (q : ℕ) (hq : q ∈ primeBand n) (hne : q ≠ p) : q.factorization p = 0 := by
    have hFac := (hPrime q hq).factorization_pow 1
    rw [pow_one] at hFac
    rw [hFac, Finsupp.single_apply, if_neg hne]
  by_cases hP : p ∈ primeBand n
  · rw [if_pos hP, Finset.sum_eq_single p]
    · exact (hPrime p hP).factorization_self
    · exact hZero
    · intro h
      exact (h hP).elim
  · rw [if_neg hP]
    apply sum_eq_zero
    intro q hq
    exact hZero q hq (fun e => hP (e ▸ hq))

lemma factorization_mul_value {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (p : ℕ) :
    (a*b).factorization p = a.factorization p+b.factorization p := by
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply]

lemma factorial_value_sum {p n t : ℕ} (hp : p.Prime) (ht : t ≤ n) :
    t.factorial.factorization p = ∑ j ∈ Ico 1 (n+1), t / p^j :=
  Nat.factorization_factorial hp ((Nat.log_le_self p t).trans_lt (by omega))

lemma div_by_two_denominators (n a b : ℕ) : n/a/b = n/b/a := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]

lemma factorial_numerator_factorization {n p : ℕ} (hp : p.Prime) :
    (factorialNumerator n).factorization p = ∑ j ∈ Ico 1 (n+1), upperWeight (n/p^j) := by
  unfold factorialNumerator
  rw [factorization_mul_value (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
    factorial_value_sum hp (le_rfl : n ≤ n), factorial_value_sum hp (Nat.div_le_self n 30),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold upperWeight
  rw [div_by_two_denominators n 30 (p^j)]

lemma factorial_denominator_factorization {n p : ℕ} (hp : p.Prime) :
    (factorialDenominator n).factorization p = ∑ j ∈ Ico 1 (n+1), lowerWeight (n/p^j) := by
  unfold factorialDenominator
  rw [factorization_mul_value (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _),
    factorization_mul_value (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
    factorial_value_sum hp (Nat.div_le_self n 2), factorial_value_sum hp (Nat.div_le_self n 3),
    factorial_value_sum hp (Nat.div_le_self n 5), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold lowerWeight
  rw [div_by_two_denominators n 2 (p^j), div_by_two_denominators n 3 (p^j),
    div_by_two_denominators n 5 (p^j)]

lemma denominator_ne_zero (n : ℕ) : factorialDenominator n ≠ 0 :=
  mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
    (Nat.factorial_ne_zero _)

lemma numerator_ne_zero (n : ℕ) : factorialNumerator n ≠ 0 :=
  mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)

theorem factorial_ratio_contains_prime_band (n : ℕ) :
    primeBandProduct n * factorialDenominator n ∣ factorialNumerator n := by
  apply (Nat.factorization_prime_le_iff_dvd
    (mul_ne_zero (band_product_ne_zero n) (denominator_ne_zero n)) (numerator_ne_zero n)).1
  intro p hp
  rw [factorization_mul_value (band_product_ne_zero n) (denominator_ne_zero n),
    band_product_factorization, factorial_numerator_factorization hp, factorial_denominator_factorization hp]
  by_cases hBand : p ∈ primeBand n
  · rw [if_pos hBand]
    have hpBounds := mem_Ioc.mp (mem_filter.mp hBand).1
    have hFirst : lowerWeight (n/p^1)+1 ≤ upperWeight (n/p^1) := by
      rw [pow_one]
      apply lower_weight_add_one_le ((Nat.le_div_iff_mul_le hp.pos).2 (by simpa using hpBounds.2))
      apply Nat.le_of_lt_succ
      exact (Nat.div_lt_iff_lt_mul hp.pos).2 (by
        exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 6)).1 (by simpa using hpBounds.1) |> fun h => by
          simpa only [Nat.mul_comm] using h)
    let R := Ico 1 (n+1)
    have hOne : 1 ∈ R := mem_Ico.mpr ⟨by decide, by have := hp.two_le; omega⟩
    change 1 + (∑ j ∈ R, lowerWeight (n/p^j)) ≤ ∑ j ∈ R, upperWeight (n/p^j)
    have hLo := Finset.sum_erase_add R (fun j => lowerWeight (n/p^j)) hOne
    have hHi := Finset.sum_erase_add R (fun j => upperWeight (n/p^j)) hOne
    rw [← hLo, ← hHi]
    calc
      _ = (∑ j ∈ R.erase 1, lowerWeight (n/p^j)) + (lowerWeight (n/p^1)+1) := by ac_rfl
      _ ≤ (∑ j ∈ R.erase 1, upperWeight (n/p^j)) + upperWeight (n/p^1) :=
        Nat.add_le_add (sum_le_sum (fun j _ => lower_weight_le (n/p^j))) hFirst
  · rw [if_neg hBand, Nat.zero_add]
    exact sum_le_sum (fun j _ => lower_weight_le _)

end Erdos137OddPrimorial
