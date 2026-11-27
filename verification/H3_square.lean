import FormalConjectures.ErdosProblems.«137»
import Mathlib.Data.Nat.Squarefree

/-! The finite counting and four-factor arguments for the quadratic branch. -/

namespace Erdos137H3Square

open Finset

def cutoff (k : ℕ) : ℕ :=
  if k < 20 then 3 else if k < 56 then 5 else if k < 176 then 7
  else if k < 416 then 11 else 13

def smallPrimes (k s : ℕ) : Finset ℕ :=
  ((range k).filter Nat.Prime).filter (· ≤ s)

def largePrimes (k s : ℕ) : Finset ℕ :=
  ((range k).filter Nat.Prime).filter (s < ·)

def multiples (n k p : ℕ) : Finset ℕ :=
  (Ioc n (n + k)).filter (p ∣ ·)

lemma card_multiples_le (n k p : ℕ) (hp : 0 < p) :
    (multiples n k p).card ≤ (k + p - 1) / p := by
  let left := (Ioc 0 n).filter (p ∣ ·)
  have hUnion : (Ioc 0 (n + k)).filter (p ∣ ·) = left ∪ multiples n k p := by
    ext m
    simp only [left, multiples, mem_union, mem_filter, mem_Ioc]
    omega
  have hDisj : Disjoint left (multiples n k p) := by
    rw [Finset.disjoint_left]
    intro m hl hr
    have hl' := mem_Ioc.mp (mem_filter.mp hl).1
    have hr' := mem_Ioc.mp (mem_filter.mp hr).1
    omega
  have hCard : (n + k) / p = n / p + (multiples n k p).card := by
    have h := congrArg Finset.card hUnion
    rw [Finset.card_union_of_disjoint hDisj, Nat.Ioc_filter_dvd_card_eq_div] at h
    dsimp only [left] at h
    rw [Nat.Ioc_filter_dvd_card_eq_div] at h
    exact h
  have hEq : (n + k) / p = (n % p + k) / p + n / p := by
    have hSplit := Nat.mod_add_div n p
    calc
      (n + k) / p = (n % p + k + p * (n / p)) / p := by
        have hv : n + k = n % p + k + p * (n / p) := by omega
        rw [hv]
      _ = (n % p + k) / p + n / p := Nat.add_mul_div_left _ _ hp
  have hMod := Nat.mod_lt n hp
  have hLe : (n % p + k) / p ≤ (k + p - 1) / p :=
    Nat.div_le_div_right (by omega)
  omega

lemma primeFactors_injective_on_squarefree {S : Finset ℕ} {a : ℕ → ℕ}
    (hSquare : ∀ t ∈ S, Squarefree (a t)) (hInj : Set.InjOn a ↑S) :
    Set.InjOn (fun t => (a t).primeFactors) ↑S := by
  intro i hi j hj h
  apply hInj hi hj
  calc
    a i = ∏ p ∈ (a i).primeFactors, p := (Nat.prod_primeFactors_of_squarefree (hSquare i hi)).symm
    _ = ∏ p ∈ (a j).primeFactors, p := by rw [h]
    _ = a j := Nat.prod_primeFactors_of_squarefree (hSquare j hj)

lemma squarefree_capacity (n k s : ℕ) (a : ℕ → ℕ)
    (hSquare : ∀ t ∈ Ioc n (n + k), Squarefree (a t))
    (hInj : Set.InjOn a ↑(Ioc n (n + k)))
    (hDvd : ∀ t ∈ Ioc n (n + k), a t ∣ t)
    (hSupport : ∀ t ∈ Ioc n (n + k), ∀ p ∈ (a t).primeFactors, p < k) :
    k ≤ 2 ^ (smallPrimes k s).card + ∑ p ∈ largePrimes k s, (k + p - 1) / p := by
  let S := Ioc n (n + k)
  let bad := (largePrimes k s).biUnion (multiples n k)
  let good := S \ bad
  have hBadSub : bad ⊆ S := by
    intro t ht
    obtain ⟨p, _, ht⟩ := mem_biUnion.mp ht
    exact (mem_filter.mp ht).1
  have hGoodSub : good ⊆ S := Finset.sdiff_subset
  have hGoodCard : good.card ≤ 2 ^ (smallPrimes k s).card := by
    rw [← Finset.card_powerset]
    apply Finset.card_le_card_of_injOn (fun t => (a t).primeFactors)
    · intro t ht
      apply mem_powerset.mpr
      intro p hp
      obtain ⟨hpPrime, hpDvd, _⟩ := Nat.mem_primeFactors.mp hp
      have htS := hGoodSub ht
      have hpLt := hSupport t htS p hp
      have hpSmall : p ≤ s := by
        by_contra! hpLarge
        have hLarge : p ∈ largePrimes k s := by
          simp [largePrimes, hpLt, hpPrime, hpLarge]
        have hHit : t ∈ multiples n k p := mem_filter.mpr ⟨htS, hpDvd.trans (hDvd t htS)⟩
        exact (mem_sdiff.mp ht).2 (mem_biUnion.mpr ⟨p, hLarge, hHit⟩)
      simp [smallPrimes, hpLt, hpPrime, hpSmall]
    · exact (primeFactors_injective_on_squarefree hSquare hInj).mono hGoodSub
  have hBadCard : bad.card ≤ ∑ p ∈ largePrimes k s, (k + p - 1) / p := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro p hp
    have hpPrime : p.Prime := (mem_filter.mp (mem_filter.mp hp).1).2
    exact card_multiples_le n k p hpPrime.pos
  have hTotal := Finset.card_sdiff_add_card_eq_card hBadSub
  have hSC : S.card = k := by simp [S]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma square_capacity_certificate :
    ∀ k : Fin 676, 3 ≤ k.val → k.val ≠ 4 → k.val ≠ 6 → k.val ≠ 8 →
      2 ^ (smallPrimes k.val (cutoff k.val)).card +
        (∑ p ∈ largePrimes k.val (cutoff k.val), (k.val + p - 1) / p) < k.val := by
  decide

theorem squarefree_coefficients_impossible_below_676 {n k : ℕ} {a : ℕ → ℕ}
    (hk : 3 ≤ k) (hUpper : k < 676) (h4 : k ≠ 4) (h6 : k ≠ 6) (h8 : k ≠ 8)
    (hSquare : ∀ t ∈ Ioc n (n + k), Squarefree (a t))
    (hInj : Set.InjOn a ↑(Ioc n (n + k)))
    (hDvd : ∀ t ∈ Ioc n (n + k), a t ∣ t)
    (hSupport : ∀ t ∈ Ioc n (n + k), ∀ p ∈ (a t).primeFactors, p < k) : False := by
  have hUpperCount := square_capacity_certificate ⟨k, hUpper⟩ hk h4 h6 h8
  have hLowerCount := squarefree_capacity n k (cutoff k) a hSquare hInj hDvd hSupport
  exact (not_lt_of_ge hLowerCount) hUpperCount

lemma four_consecutive_not_square (a x : ℕ) (ha : 0 < a) :
    a * (a + 1) * (a + 2) * (a + 3) ≠ x ^ 2 := by
  intro h
  let m := a ^ 2 + 3 * a + 1
  have heq : x ^ 2 + 1 = m ^ 2 := by
    rw [← h]
    dsimp [m]
    ring
  have hm : 1 < m := by dsimp [m]; nlinarith
  have hx : 0 < x := by
    by_contra! hx
    have hx' : x = 0 := by omega
    rw [hx'] at heq
    nlinarith
  have hxm : x < m :=
    (Nat.pow_lt_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp (by omega)
  have hgap : (x + 1) ^ 2 ≤ m ^ 2 :=
    (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).2 (by omega)
  nlinarith

theorem four_coefficients_cannot_permute_divisors_six (n : ℕ) (a x : ℕ → ℕ)
    (hRepr : ∀ t ∈ Ioc n (n + 4), t = a t * x t ^ 2)
    (hInj : Set.InjOn a ↑(Ioc n (n + 4)))
    (hSupport : ∀ t ∈ Ioc n (n + 4), a t ∈ ({1, 2, 3, 6} : Finset ℕ)) : False := by
  let S := Ioc n (n + 4)
  let values : Finset ℕ := {1, 2, 3, 6}
  have hImage : S.image a = values := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hz
      exact hSupport t ht
    · rw [Finset.card_image_of_injOn hInj]
      have hSC : S.card = 4 := by simp [S]
      rw [hSC]
      decide
  have hCoeff : (∏ t ∈ S, a t) = 36 := by
    calc
      (∏ t ∈ S, a t) = ∏ z ∈ S.image a, z := by
        rw [Finset.prod_image]
        exact hInj
      _ = 36 := by rw [hImage]; decide
  have hProduct : (∏ t ∈ S, t) = (6 * ∏ t ∈ S, x t) ^ 2 := by
    calc
      (∏ t ∈ S, t) = ∏ t ∈ S, a t * x t ^ 2 :=
        Finset.prod_congr rfl hRepr
      _ = (6 * ∏ t ∈ S, x t) ^ 2 := by
        rw [Finset.prod_mul_distrib, hCoeff, Finset.prod_pow, mul_pow]
        norm_num
  have hS : S = {n + 1, n + 2, n + 3, n + 4} := by
    ext z
    simp only [S, mem_Ioc, mem_insert, mem_singleton]
    omega
  have hList : (∏ t ∈ S, t) = (n + 1) * (n + 2) * (n + 3) * (n + 4) := by
    rw [hS]
    have h12 : n + 1 ≠ n + 2 := by omega
    have h13 : n + 1 ≠ n + 3 := by omega
    have h14 : n + 1 ≠ n + 4 := by omega
    have h23 : n + 2 ≠ n + 3 := by omega
    have h24 : n + 2 ≠ n + 4 := by omega
    have h34 : n + 3 ≠ n + 4 := by omega
    simp [Finset.prod_insert, h12, h13, h14, h23, h24, h34, Nat.mul_assoc]
  rw [hList] at hProduct
  have hFour := four_consecutive_not_square (n + 1) (6 * ∏ t ∈ S, x t) (by omega)
  exact hFour (by simpa [Nat.add_assoc] using hProduct)

def oddBoundAux (p : ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | fuel + 1, k =>
    if k ≤ 1 then k else
      let a := (k + p - 1) / p
      let b := a / p
      a - b + oddBoundAux p fuel b

def oddBound (k p : ℕ) : ℕ := oddBoundAux p k k

def factorialValuationAux (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, k =>
    if k = 0 then 0 else
      let q := k / p
      q + factorialValuationAux p fuel q

def factorialValuation (k p : ℕ) : ℕ := factorialValuationAux p k k

def savingPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19]

def baseDivisor (k : ℕ) : ℕ :=
  (savingPrimes.map fun p => p ^ (1 + factorialValuation (k - 1) p - oddBound k p)).prod

def blockDivisor : ℕ :=
  (savingPrimes.map fun p => p ^ (factorialValuation 650 p - oddBound 650 p)).prod

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma base_block_certificate :
    ∀ r : Fin 650, 2 ^ (674 + r.val) * (675 + r.val) * 4 ^ (676 + r.val) <
      3 ^ (674 + r.val) * baseDivisor (676 + r.val) := by
  decide

set_option maxRecDepth 100000 in
lemma gain_certificate :
    8 ^ 650 * (675 + 650) < (3 ^ 650 * blockDivisor) * 675 := by
  decide

lemma extend_gain {a c start interval length : ℕ} (hStart : start ≤ length)
    (hGain : a * (start + interval) < c * start) :
    a * (length + interval) < c * length := by
  have hAC : a ≤ c := by
    by_contra! h
    have h1 := Nat.mul_le_mul_right start h.le
    have h2 := Nat.mul_le_mul_left a (show start ≤ start + interval by omega)
    exact (not_lt_of_ge (h1.trans h2)) hGain
  have hTail := Nat.mul_le_mul_right (length - start) hAC
  have hLeft : length + interval = (start + interval) + (length - start) := by omega
  have hRight : length = start + (length - start) := by omega
  calc
    a * (length + interval) = a * (start + interval) + a * (length - start) := by
      rw [hLeft, Nat.mul_add]
    _ < c * start + c * (length - start) := Nat.add_lt_add_of_lt_of_le hGain hTail
    _ = c * length := by rw [← Nat.mul_add, ← hRight]

end Erdos137H3Square
