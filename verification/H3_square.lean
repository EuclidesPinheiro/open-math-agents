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

lemma squarefree_capacity_with_bad (n k s : ℕ) (a : ℕ → ℕ)
    (hSquare : ∀ t ∈ Ioc n (n + k), Squarefree (a t))
    (hInj : Set.InjOn a ↑(Ioc n (n + k)))
    (hDvd : ∀ t ∈ Ioc n (n + k), a t ∣ t)
    (hSupport : ∀ t ∈ Ioc n (n + k), ∀ p ∈ (a t).primeFactors, p < k) :
    k ≤ 2 ^ (smallPrimes k s).card + ((largePrimes k s).biUnion (multiples n k)).card := by
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
    · exact (primeFactors_injective_on_squarefree hSquare hInj).mono (fun _ ht => hGoodSub ht)
  have hTotal := Finset.card_sdiff_add_card_eq_card hBadSub
  have hSC : S.card = k := by simp [S]
  change k ≤ 2 ^ (smallPrimes k s).card + bad.card
  omega

lemma squarefree_capacity (n k s : ℕ) (a : ℕ → ℕ)
    (hSquare : ∀ t ∈ Ioc n (n + k), Squarefree (a t))
    (hInj : Set.InjOn a ↑(Ioc n (n + k)))
    (hDvd : ∀ t ∈ Ioc n (n + k), a t ∣ t)
    (hSupport : ∀ t ∈ Ioc n (n + k), ∀ p ∈ (a t).primeFactors, p < k) :
    k ≤ 2 ^ (smallPrimes k s).card + ∑ p ∈ largePrimes k s, (k + p - 1) / p := by
  let bad := (largePrimes k s).biUnion (multiples n k)
  have hBadCard : bad.card ≤ ∑ p ∈ largePrimes k s, (k + p - 1) / p := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro p hp
    have hpPrime : p.Prime := (mem_filter.mp (mem_filter.mp hp).1).2
    exact card_multiples_le n k p hpPrime.pos
  exact (squarefree_capacity_with_bad n k s a hSquare hInj hDvd hSupport).trans
    (Nat.add_le_add_left hBadCard _)

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

lemma small_coefficients_mem {a : ℕ} (ha : Squarefree a)
    (hSupport : ∀ p ∈ a.primeFactors, p ≤ 3) :
    a ∈ ({1, 2, 3, 6} : Finset ℕ) := by
  have hSub : a.primeFactors ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    have hPrime := (Nat.mem_primeFactors.mp hp).1
    have h2 := hPrime.two_le
    have h3 := hSupport p hp
    simp only [mem_insert, mem_singleton]
    omega
  have hDvd := Finset.prod_dvd_prod_of_subset a.primeFactors ({2, 3} : Finset ℕ) id hSub
  rw [show (∏ p ∈ a.primeFactors, id p) = a from Nat.prod_primeFactors_of_squarefree ha] at hDvd
  have hDvd6 : a ∣ 6 := by simpa using hDvd
  have hPos : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
  have hBound := Nat.le_of_dvd (by decide : 0 < (6 : ℕ)) hDvd6
  have hVals : ∀ j : Fin 7, 0 < j.val → j.val ∣ 6 →
      j.val ∈ ({1, 2, 3, 6} : Finset ℕ) := by decide
  exact hVals ⟨a, by omega⟩ hPos hDvd6

def exceptionalBad (k r : ℕ) : Finset ℕ :=
  (range k).filter (fun i => 5 ∣ r + i + 1 ∨ (k = 8 ∧ 7 ∣ r + i + 1))

lemma exceptional_six_positions :
    ∀ r : Fin 35, 2 ≤ (exceptionalBad 6 r.val).card →
      ∀ i : Fin 4, 1 + i.val ∉ exceptionalBad 6 r.val := by decide

lemma exceptional_eight_positions :
    ∀ r : Fin 35, 4 ≤ (exceptionalBad 8 r.val).card →
      ∀ i : Fin 4, 2 + i.val ∉ exceptionalBad 8 r.val := by decide

lemma exceptional_divisibility (n p i : ℕ) (hp : p ∣ 35) :
    (p ∣ n + i + 1) ↔ p ∣ n % 35 + i + 1 := by
  have hDiv : p ∣ 35 * (n / 35) := dvd_mul_of_dvd_left hp _
  have hDecomp := Nat.mod_add_div n 35
  have hEq : n + i + 1 = (n % 35 + i + 1) + 35 * (n / 35) := by omega
  rw [hEq]
  exact Nat.dvd_add_iff_left hDiv

lemma exceptional_bad_image (n k : ℕ) (hk : k = 6 ∨ k = 8) :
    (exceptionalBad k (n % 35)).image (fun i => n + i + 1) =
      (largePrimes k 3).biUnion (multiples n k) := by
  have hLarge : largePrimes k 3 = if k = 8 then ({5, 7} : Finset ℕ) else {5} := by
    rcases hk with rfl | rfl <;> decide
  have hMembership (t : ℕ) : t ∈ (largePrimes k 3).biUnion (multiples n k) ↔
      t ∈ Ioc n (n + k) ∧ (5 ∣ t ∨ (k = 8 ∧ 7 ∣ t)) := by
    rw [mem_biUnion, hLarge]
    rcases hk with rfl | rfl <;> simp [multiples, and_or_left]
  ext t
  rw [hMembership, mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨hiRange, hiPrime⟩ := mem_filter.mp hi
    have hiLt := mem_range.mp hiRange
    refine ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
    simpa only [exceptional_divisibility n 5 i (by decide : 5 ∣ 35),
      exceptional_divisibility n 7 i (by decide : 7 ∣ 35)] using hiPrime
  · rintro ⟨ht, htPrime⟩
    have h := mem_Ioc.mp ht
    let i := t - n - 1
    have hIt : n + i + 1 = t := by dsimp [i]; omega
    refine ⟨i, mem_filter.mpr ⟨mem_range.mpr (by dsimp [i]; omega), ?_⟩, hIt⟩
    rw [← exceptional_divisibility n 5 i (by decide : 5 ∣ 35),
      ← exceptional_divisibility n 7 i (by decide : 7 ∣ 35), hIt]
    exact htPrime

lemma exceptional_middle_avoids_large (n k : ℕ) (hk : k = 6 ∨ k = 8)
    (hCount : k - 4 ≤ ((largePrimes k 3).biUnion (multiples n k)).card) :
    ∀ t ∈ Ioc (n + (k - 4) / 2) (n + (k - 4) / 2 + 4),
      t ∉ (largePrimes k 3).biUnion (multiples n k) := by
  have hImage := exceptional_bad_image n k hk
  have hAddInj : Function.Injective (fun i : ℕ => n + i + 1) := by
    intro i j e
    omega
  rw [← hImage, Finset.card_image_of_injective _ hAddInj] at hCount
  let r : Fin 35 := ⟨n % 35, Nat.mod_lt _ (by decide)⟩
  intro t ht htBad
  have hBounds := mem_Ioc.mp ht
  rw [← hImage] at htBad
  obtain ⟨j, hj, hJt⟩ := mem_image.mp htBad
  rcases hk with rfl | rfl
  · change 2 ≤ (exceptionalBad 6 r.val).card at hCount
    change j ∈ exceptionalBad 6 r.val at hj
    let i : Fin 4 := ⟨j - 1, by omega⟩
    have hIdx : 1 + i.val = j := by dsimp [i]; omega
    exact exceptional_six_positions r hCount i (by simpa only [hIdx] using hj)
  · change 4 ≤ (exceptionalBad 8 r.val).card at hCount
    change j ∈ exceptionalBad 8 r.val at hj
    let i : Fin 4 := ⟨j - 2, by omega⟩
    have hIdx : 2 + i.val = j := by dsimp [i]; omega
    exact exceptional_eight_positions r hCount i (by simpa only [hIdx] using hj)

theorem exceptional_coefficients_impossible {n k : ℕ} {a x : ℕ → ℕ}
    (hk : k = 4 ∨ k = 6 ∨ k = 8)
    (hSquare : ∀ t ∈ Ioc n (n + k), Squarefree (a t))
    (hInj : Set.InjOn a ↑(Ioc n (n + k)))
    (hRepr : ∀ t ∈ Ioc n (n + k), t = a t * x t ^ 2)
    (hSupport : ∀ t ∈ Ioc n (n + k), ∀ p ∈ (a t).primeFactors, p < k) : False := by
  rcases hk with rfl | hk
  · apply four_coefficients_cannot_permute_divisors_six n a x hRepr hInj
    intro t ht
    apply small_coefficients_mem (hSquare t ht)
    intro p hp
    have hh := hSupport t ht p hp
    omega
  · have hDvd (t : ℕ) (ht : t ∈ Ioc n (n + k)) : a t ∣ t := ⟨x t ^ 2, hRepr t ht⟩
    have hCap := squarefree_capacity_with_bad n k 3 a hSquare hInj hDvd hSupport
    have hSmall : (smallPrimes k 3).card = 2 := by
      rcases hk with rfl | rfl <;> decide
    rw [hSmall, show (2 : ℕ) ^ 2 = 4 by decide] at hCap
    have hCount : k - 4 ≤ ((largePrimes k 3).biUnion (multiples n k)).card := by omega
    let m := n + (k - 4) / 2
    have hSub : Ioc m (m + 4) ⊆ Ioc n (n + k) := by
      intro t ht
      have hBounds := mem_Ioc.mp ht
      apply mem_Ioc.mpr
      dsimp [m] at hBounds
      rcases hk with rfl | rfl <;> omega
    apply four_coefficients_cannot_permute_divisors_six m a x
    · exact fun t ht => hRepr t (hSub ht)
    · exact hInj.mono (fun _ ht => hSub ht)
    · intro t ht
      have ht' := hSub ht
      apply small_coefficients_mem (hSquare t ht')
      intro p hp
      by_contra! hLarge
      obtain ⟨hpPrime, hpDvd, _⟩ := Nat.mem_primeFactors.mp hp
      have hpLt := hSupport t ht' p hp
      have hpIn : p ∈ largePrimes k 3 := by simp [largePrimes, hpPrime, hpLt, hLarge]
      have hHit : t ∈ multiples n k p := mem_filter.mpr ⟨ht', hpDvd.trans (hDvd t ht')⟩
      exact exceptional_middle_avoids_large n k hk hCount t ht
        (mem_biUnion.mpr ⟨p, hpIn, hHit⟩)

theorem normalized_square_impossible_below_676 {n k : ℕ} {a x : ℕ → ℕ}
    (hk : 3 ≤ k) (hUpper : k < 676)
    (hSquare : ∀ t ∈ Ioc n (n + k), Squarefree (a t))
    (hInj : Set.InjOn a ↑(Ioc n (n + k)))
    (hRepr : ∀ t ∈ Ioc n (n + k), t = a t * x t ^ 2)
    (hSupport : ∀ t ∈ Ioc n (n + k), ∀ p ∈ (a t).primeFactors, p < k) : False := by
  by_cases h : k = 4 ∨ k = 6 ∨ k = 8
  · exact exceptional_coefficients_impossible h hSquare hInj hRepr hSupport
  · exact squarefree_coefficients_impossible_below_676 hk hUpper
      (fun e => h (Or.inl e)) (fun e => h (Or.inr (Or.inl e)))
      (fun e => h (Or.inr (Or.inr e))) hSquare hInj
      (fun t ht => ⟨x t ^ 2, hRepr t ht⟩) hSupport

lemma square_remainders (t : ℕ) :
    ∃ a x : ℕ, a ≠ 0 ∧ t = a * x ^ 2 ∧
      ∀ p : ℕ, a.factorization p = t.factorization p % 2 := by
  by_cases ht : t = 0
  · subst t
    exact ⟨1, 0, by decide, by decide, by simp⟩
  let remainders := Finsupp.mapRange (fun e : ℕ => e % 2) (by decide) t.factorization
  let quotients := Finsupp.mapRange (fun e : ℕ => e / 2) (by decide) t.factorization
  have hRem : remainders ≤ t.factorization := by
    intro p
    exact Nat.mod_le _ _
  have hQuot : quotients ≤ t.factorization := by
    intro p
    exact Nat.div_le_self _ _
  let a := remainders.prod fun p e => p ^ e
  let x := quotients.prod fun p e => p ^ e
  have ha : a ≠ 0 := by
    have hd : a ∣ t := Nat.prod_pow_dvd_of_le_factorization hRem
    intro hz
    rw [hz] at hd
    exact ht (Nat.eq_zero_of_zero_dvd hd)
  have hx : x ≠ 0 := by
    have hd : x ∣ t := Nat.prod_pow_dvd_of_le_factorization hQuot
    intro hz
    rw [hz] at hd
    exact ht (Nat.eq_zero_of_zero_dvd hd)
  have hFactorA : a.factorization = remainders :=
    Nat.factorization_prod_pow_eq_self_of_le_factorization hRem
  have hFactorX : x.factorization = quotients :=
    Nat.factorization_prod_pow_eq_self_of_le_factorization hQuot
  refine ⟨a, x, ha, ?_, ?_⟩
  · apply Nat.eq_of_factorization_eq ht (mul_ne_zero ha (pow_ne_zero 2 hx))
    intro p
    rw [Nat.factorization_mul ha (pow_ne_zero 2 hx), Nat.factorization_pow, hFactorA, hFactorX]
    change t.factorization p = t.factorization p % 2 + 2 * (t.factorization p / 2)
    exact (Nat.mod_add_div _ _).symm
  · intro p
    rw [hFactorA]
    exact Finsupp.mapRange_apply

lemma large_prime_single {n k p t : ℕ} (hkp : k ≤ p)
    (ht : t ∈ Ioc n (n + k)) (hpt : p ∣ t) :
    (∏ m ∈ Ioc n (n + k), m).factorization p = t.factorization p := by
  have hNonzero : ∀ m ∈ Ioc n (n + k), m ≠ 0 := by
    intro m hm
    have hm' := (mem_Ioc.mp hm).1
    omega
  have htBounds := mem_Ioc.mp ht
  rw [Nat.factorization_prod hNonzero, Finsupp.finsetSum_apply, Finset.sum_eq_single t]
  · intro m hm hne
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpm
    have hmBounds := mem_Ioc.mp hm
    rcases lt_or_gt_of_ne hne with h | h
    · have hdiv := Nat.le_of_dvd (show 0 < t - m by omega) (Nat.dvd_sub hpt hpm)
      omega
    · have hdiv := Nat.le_of_dvd (show 0 < m - t by omega) (Nat.dvd_sub hpm hpt)
      omega
  · intro hMissing
    exact (hMissing ht).elim

lemma equal_square_coefficients_gap {k a x y : ℕ} (ha : a ≠ 0)
    (hSize : k ^ 2 ≤ a * x ^ 2) (hxy : x < y) : a * x ^ 2 + k ≤ a * y ^ 2 := by
  have hxA : x ≤ a * x := by
    have h := Nat.mul_le_mul_right x (show 1 ≤ a by omega)
    simpa only [Nat.one_mul] using h
  have hSquare : k ^ 2 ≤ (a * x) ^ 2 := calc
    k ^ 2 ≤ a * x ^ 2 := hSize
    _ = (a * x) * x := by ring
    _ ≤ (a * x) * (a * x) := Nat.mul_le_mul_left _ hxA
    _ = (a * x) ^ 2 := (pow_two _).symm
  have hkA := (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).1 hSquare
  have hMono : a * x ≤ a * y := Nat.mul_le_mul_left _ hxy.le
  calc
    a * x ^ 2 + k ≤ a * x ^ 2 + a * x := Nat.add_le_add_left hkA _
    _ = (a * x) * (x + 1) := by ring
    _ ≤ (a * y) * y := Nat.mul_le_mul hMono (by omega)
    _ = a * y ^ 2 := by ring

theorem h3_square_below_676 {n k : ℕ} (hk : 3 ≤ k) (hUpper : k < 676)
    (hSylvester : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ t ∈ Ioc n (n + k), t) :
    ∃ p : ℕ, k ≤ p ∧ p.Prime ∧ ¬ 2 ∣ (∏ t ∈ Ioc n (n + k), t).factorization p := by
  classical
  by_contra! hAll
  have hSize : k ^ 2 < n := by
    obtain ⟨p, hp, hkp, hProd⟩ := hSylvester
    obtain ⟨t, ht, hpt⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 hProd
    have hBounds := mem_Ioc.mp ht
    have ht0 : t ≠ 0 := by omega
    have hDiv := hAll p hkp.le hp
    rw [large_prime_single hkp.le ht hpt] at hDiv
    have he := Nat.le_of_dvd (hp.factorization_pos_of_dvd ht0 hpt) hDiv
    have hpSq := Nat.le_of_dvd (show 0 < t by omega)
      ((hp.pow_dvd_iff_le_factorization ht0).2 he)
    have hMon : (k + 1) ^ 2 ≤ p ^ 2 := pow_le_pow_left' (by omega) _
    nlinarith
  choose a x ha hRepr hFac using square_remainders
  have hSquare (t : ℕ) (_ : t ∈ Ioc n (n + k)) : Squarefree (a t) := by
    apply (Nat.squarefree_iff_factorization_le_one (ha t)).2
    intro p
    rw [hFac]
    omega
  have hSupport (t : ℕ) (ht : t ∈ Ioc n (n + k)) (p : ℕ)
      (hp : p ∈ (a t).primeFactors) : p < k := by
    by_contra! hkp
    obtain ⟨hpPrime, hpDvd, _⟩ := Nat.mem_primeFactors.mp hp
    have htDvd : a t ∣ t := ⟨x t ^ 2, hRepr t⟩
    have hDiv := hAll p hkp hpPrime
    rw [large_prime_single hkp ht (hpDvd.trans htDvd)] at hDiv
    have hZero : (a t).factorization p = 0 := by
      rw [hFac, Nat.mod_eq_zero_of_dvd hDiv]
    have := hpPrime.factorization_pos_of_dvd (ha t) hpDvd
    omega
  have hDistinct : Set.InjOn a ↑(Ioc n (n + k)) := by
    intro i hi j hj heq
    have hI := mem_Ioc.mp hi
    have hJ := mem_Ioc.mp hj
    have hApart (u v : ℕ) (hu : u ∈ Ioc n (n + k)) (hv : v ∈ Ioc n (n + k))
        (huv : u < v) (haEq : a u = a v) : False := by
      have huBounds := mem_Ioc.mp hu
      have hvBounds := mem_Ioc.mp hv
      have hRoot : x u < x v := by
        by_contra! h
        have hMon : x v ^ 2 ≤ x u ^ 2 := pow_le_pow_left' h _
        have hScale := Nat.mul_le_mul_left (a u) hMon
        rw [haEq, ← hRepr v, ← show a v * x u ^ 2 = u by rw [← haEq, ← hRepr u]] at hScale
        omega
      have hU : k ^ 2 ≤ a u * x u ^ 2 := by rw [← hRepr u]; omega
      have hGap := equal_square_coefficients_gap (ha u) hU hRoot
      rw [← hRepr u, haEq, ← hRepr v] at hGap
      omega
    rcases lt_trichotomy i j with h | h | h
    · exact (hApart i j hi hj h heq).elim
    · exact h
    · exact (hApart j i hj hi h heq.symm).elim
  exact normalized_square_impossible_below_676 hk hUpper hSquare hDistinct
    (fun t _ => hRepr t) hSupport

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

theorem quadratic_block_inequality (r : Fin 650) (q : ℕ) :
    let k := 676 + r.val + q * 650
    2 ^ (k - 2) * (k - 1) * 4 ^ k <
      3 ^ (k - 2) * (baseDivisor (676 + r.val) * blockDivisor ^ q) := by
  induction q with
  | zero =>
    have hBase := base_block_certificate r
    dsimp
    simp only [Nat.zero_mul, Nat.add_zero, pow_zero, Nat.mul_one]
    rw [show 676 + r.val - 2 = 674 + r.val by omega,
      show 676 + r.val - 1 = 675 + r.val by omega]
    exact hBase
  | succ q ih =>
    let k := 676 + r.val + q * 650
    let left := 2 ^ (k - 2) * 4 ^ k
    let right := 3 ^ (k - 2) * (baseDivisor (676 + r.val) * blockDivisor ^ q)
    have hLeft : 0 < left :=
      Nat.mul_pos (pow_pos (by decide) _) (pow_pos (by decide) _)
    have hBlock : 0 < 3 ^ 650 * blockDivisor :=
      Nat.mul_pos (pow_pos (by decide) _) (by decide)
    have hStart : 675 ≤ k - 1 := by dsimp [k]; omega
    have hGain := extend_gain hStart gain_certificate
    have hIh : left * (k - 1) < right := by
      dsimp [left, right, k]
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ih
    have hBoth : left * (8 ^ 650 * (k - 1 + 650)) <
        (3 ^ 650 * blockDivisor) * right := by
      calc
        left * (8 ^ 650 * (k - 1 + 650)) <
            left * ((3 ^ 650 * blockDivisor) * (k - 1)) :=
          Nat.mul_lt_mul_of_pos_left hGain hLeft
        _ = (3 ^ 650 * blockDivisor) * (left * (k - 1)) := by ac_rfl
        _ < (3 ^ 650 * blockDivisor) * right := Nat.mul_lt_mul_of_pos_left hIh hBlock
    have hk : 676 + r.val + q.succ * 650 = k + 650 := by dsimp [k]; omega
    dsimp
    rw [hk]
    have hMinusTwo : k + 650 - 2 = k - 2 + 650 := by omega
    have hMinusOne : k + 650 - 1 = k - 1 + 650 := by omega
    have hEight : (8 : ℕ) ^ 650 = 2 ^ 650 * 4 ^ 650 :=
      mul_pow 2 4 650
    dsimp only [left, right] at hBoth
    rw [hMinusTwo, hMinusOne, pow_add 2, pow_add 4, pow_add 3, pow_succ blockDivisor]
    simpa only [hEight, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hBoth

lemma mod36_count_le (n : ℕ) :
    3 * (n - n / 4 - n / 9 + n / 36) ≤ 2 * n + 6 := by
  have hResidues : ∀ r : Fin 36,
      3 * (r.val - r.val / 4 - r.val / 9) ≤ 2 * r.val + 6 := by decide
  have h := hResidues ⟨n % 36, Nat.mod_lt _ (by decide)⟩
  change 3 * (n % 36 - (n % 36) / 4 - (n % 36) / 9) ≤ 2 * (n % 36) + 6 at h
  have h4 : n / 4 = 9 * (n / 36) + (n % 36) / 4 := by omega
  have h9 : n / 9 = 4 * (n / 36) + (n % 36) / 9 := by omega
  omega

lemma avoiding_four_nine_card (n : ℕ) :
    3 * ((Ioc 0 n).filter fun t => ¬ 4 ∣ t ∧ ¬ 9 ∣ t).card ≤ 2 * n + 6 := by
  let S := Ioc 0 n
  let A := S.filter (4 ∣ ·)
  let B := S.filter (9 ∣ ·)
  let C := S.filter (fun t => ¬ 4 ∣ t ∧ ¬ 9 ∣ t)
  have hComp : S \ (A ∪ B) = C := by
    ext t
    simp only [S, A, B, C, mem_sdiff, mem_union, mem_filter]
    tauto
  have hSub : A ∪ B ⊆ S := by
    intro t ht
    rcases mem_union.mp ht with ht | ht <;> exact (mem_filter.mp ht).1
  have hInter : A ∩ B = S.filter (36 ∣ ·) := by
    ext t
    simp only [A, B, mem_inter, mem_filter]
    omega
  have hAB := card_union_add_card_inter A B
  have hCS := card_sdiff_add_card_eq_card hSub
  rw [hComp] at hCS
  have ha : A.card = n / 4 := Nat.Ioc_filter_dvd_card_eq_div n 4
  have hb : B.card = n / 9 := Nat.Ioc_filter_dvd_card_eq_div n 9
  have hi : (A ∩ B).card = n / 36 := by
    rw [hInter]
    exact Nat.Ioc_filter_dvd_card_eq_div n 36
  have hs : S.card = n := by simp [S]
  have hBound := mod36_count_le n
  change 3 * C.card ≤ 2 * n + 6
  omega

theorem separated_squarefree_product_lower (S : Finset ℕ)
    (hS : ∀ t ∈ S, 0 < t ∧ ¬ 4 ∣ t ∧ ¬ 9 ∣ t) :
    3 ^ (S.card - 2) * (S.card - 2).factorial ≤
      2 ^ (S.card - 2) * ∏ t ∈ S, t := by
  generalize hCard : S.card = m
  induction m using Nat.strong_induction_on generalizing S with
  | h m ih =>
    by_cases hSmall : m ≤ 2
    · have hZero : m - 2 = 0 := by omega
      have hProd : 0 < ∏ t ∈ S, t := Finset.prod_pos (fun t ht => (hS t ht).1)
      simpa only [hZero, pow_zero, Nat.factorial_zero, Nat.one_mul] using hProd
    · have hNonempty : S.Nonempty := Finset.card_pos.mp (by omega)
      let z := S.max' hNonempty
      have hz : z ∈ S := Finset.max'_mem _ _
      let T := S.erase z
      have hT : T.card = m - 1 := by simp [T, Finset.card_erase_of_mem hz, hCard]
      have hTdata : ∀ t ∈ T, 0 < t ∧ ¬ 4 ∣ t ∧ ¬ 9 ∣ t :=
        fun t ht => hS t (Finset.mem_of_mem_erase ht)
      have hPrev := ih (m - 1) (by omega) T hTdata hT
      have hIn : S ⊆ (Ioc 0 z).filter (fun t => ¬ 4 ∣ t ∧ ¬ 9 ∣ t) := by
        intro t ht
        exact mem_filter.mpr
          ⟨mem_Ioc.mpr ⟨(hS t ht).1, Finset.le_max' _ _ ht⟩, (hS t ht).2⟩
      have hSize := Finset.card_le_card hIn
      have hWheel := avoiding_four_nine_card z
      have hZ : 3 * (m - 2) ≤ 2 * z := by omega
      have hExp : m - 2 = (m - 1 - 2) + 1 := by omega
      have hProd : (∏ t ∈ S, t) = z * ∏ t ∈ T, t :=
        (Finset.mul_prod_erase S id hz).symm
      rw [hExp, pow_succ, pow_succ, Nat.factorial_succ, hProd]
      calc
        3 ^ (m - 1 - 2) * 3 * ((m - 1 - 2 + 1) * (m - 1 - 2).factorial) =
            (3 ^ (m - 1 - 2) * (m - 1 - 2).factorial) * (3 * (m - 2)) := by
          rw [hExp]
          ac_rfl
        _ ≤ (2 ^ (m - 1 - 2) * ∏ t ∈ T, t) * (2 * z) := Nat.mul_le_mul hPrev hZ
        _ = 2 ^ (m - 1 - 2) * 2 * (z * ∏ t ∈ T, t) := by ac_rfl

end Erdos137H3Square
