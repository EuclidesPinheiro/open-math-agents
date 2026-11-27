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
    constructor
    · rintro ⟨hU,hp⟩
      by_cases hL : p ≤ n/6
      · exact Or.inl ⟨by omega,hp⟩
      · exact Or.inr ⟨⟨by omega,by omega⟩,hp⟩
    · rintro (⟨hL,hp⟩ | ⟨⟨_,hU⟩,hp⟩)
      · exact ⟨by have := Nat.div_le_self n 6; omega, hp⟩
      · exact ⟨by omega,hp⟩
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
    have hFac : (q^1).factorization = Finsupp.single q 1 := (hPrime q hq).factorization_pow
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

def shiftedProduct (n : ℕ) (offsets : List ℕ) : ℕ :=
  (offsets.map (n+·)).prod

def pairedShiftBound (b : ℕ) (numerator denominator : List ℕ) : ℕ :=
  (List.zipWith (fun x y => max (b+x) (b+y)) numerator denominator).prod

lemma shifted_product_pos {n : ℕ} (hn : 0 < n) (as : List ℕ) :
    0 < shiftedProduct n as := by
  induction as with
  | nil => decide
  | cons a as ih =>
    simp only [shiftedProduct, List.map_cons,List.prod_cons]
    exact Nat.mul_pos (by omega) ih

lemma paired_shift_product_le (b n : ℕ) (hn : b ≤ n) (as bs : List ℕ)
    (hLen : as.length = bs.length) :
    shiftedProduct n as * shiftedProduct b bs ≤
      shiftedProduct n bs * pairedShiftBound b as bs := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => simp [shiftedProduct,pairedShiftBound]
    | cons z bs => simp at hLen
  | cons a as ih =>
    cases bs with
    | nil => simp at hLen
    | cons c bs =>
      have hTail := ih bs (by simpa using hLen)
      have hPair : (n+a)*(b+c) ≤ (n+c)*max (b+a) (b+c) := by
        by_cases h : a ≤ c
        · rw [max_eq_right (by omega)]
          exact Nat.mul_le_mul_right _ (by omega)
        · rw [max_eq_left (by omega)]
          have hDiff := Nat.mul_le_mul_left (a-c) (show b+c ≤ n+c by omega)
          rw [show n+a = (n+c)+(a-c) by omega, show b+a = (b+c)+(a-c) by omega]
          nlinarith only [hDiff]
      change ((n+a)*shiftedProduct n as)*((b+c)*shiftedProduct b bs) ≤
        ((n+c)*shiftedProduct n bs)*(max (b+a) (b+c)*pairedShiftBound b as bs)
      calc
        _ = ((n+a)*(b+c))*(shiftedProduct n as*shiftedProduct b bs) := by ac_rfl
        _ ≤ ((n+c)*max (b+a) (b+c))*(shiftedProduct n bs*pairedShiftBound b as bs) :=
          Nat.mul_le_mul hPair hTail
        _ = _ := by ac_rfl

def topOffsets (r : ℕ) : List ℕ :=
  ((List.range 30).map (·+1)) ++ [30-r]

def denominatorOffsets (r d m : ℕ) : List ℕ :=
  (List.range m).map fun j => d*(j+1) - r%d

def bottomOffsets (r : ℕ) : List ℕ :=
  denominatorOffsets r 2 15 ++ denominatorOffsets r 3 10 ++ denominatorOffsets r 5 6

def sortedTop (r : ℕ) : List ℕ := (topOffsets r).mergeSort (fun a b => decide (a ≤ b))

def sortedBottom (r : ℕ) : List ℕ := (bottomOffsets r).mergeSort (fun a b => decide (a ≤ b))

def scalingProduct : ℕ := 2^15*3^10*5^6

set_option maxRecDepth 100000 in
lemma sorted_shift_numeric : ∀ r : Fin 30,
    scalingProduct*100^30*pairedShiftBound 420 (sortedTop r.val) (sortedBottom r.val) ≤
      30*253^30*shiftedProduct 420 (sortedBottom r.val) := by
  decide

lemma bounded_shifted_product {n : ℕ} (hn : 420 ≤ n) :
    scalingProduct*100^30*shiftedProduct n (topOffsets (n%30)) ≤
      30*253^30*shiftedProduct n (bottomOffsets (n%30)) := by
  let r := n%30
  let a := sortedTop r
  let b := sortedBottom r
  have hALen : a.length = b.length := by
    simp [a,b,sortedTop,sortedBottom,topOffsets,bottomOffsets,denominatorOffsets]
  have hSorted := paired_shift_product_le 420 n hn a b hALen
  have hNum := sorted_shift_numeric ⟨r,Nat.mod_lt _ (by decide)⟩
  change scalingProduct*100^30*pairedShiftBound 420 a b ≤ 30*253^30*shiftedProduct 420 b at hNum
  have hAll : (scalingProduct*100^30*shiftedProduct n a)*shiftedProduct 420 b ≤
      (30*253^30*shiftedProduct n b)*shiftedProduct 420 b := by
    calc
      _ = (scalingProduct*100^30)*(shiftedProduct n a*shiftedProduct 420 b) := by ac_rfl
      _ ≤ (scalingProduct*100^30)*(shiftedProduct n b*pairedShiftBound 420 a b) :=
        Nat.mul_le_mul_left _ hSorted
      _ = shiftedProduct n b*(scalingProduct*100^30*pairedShiftBound 420 a b) := by ac_rfl
      _ ≤ shiftedProduct n b*(30*253^30*shiftedProduct 420 b) := Nat.mul_le_mul_left _ hNum
      _ = _ := by ac_rfl
  have hPos := shifted_product_pos (by decide : (0:ℕ)<420) b
  have hResult := Nat.le_of_mul_le_mul_right hAll hPos
  have ha : shiftedProduct n a = shiftedProduct n (topOffsets r) :=
    ((List.mergeSort_perm (topOffsets r) _).map _).prod_eq
  have hb : shiftedProduct n b = shiftedProduct n (bottomOffsets r) :=
    ((List.mergeSort_perm (bottomOffsets r) _).map _).prod_eq
  rw [ha,hb] at hResult
  exact hResult

lemma factorial_extend (n b : ℕ) :
    (n+b).factorial = n.factorial * ((List.range b).map (fun i => n+i+1)).prod := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show n+b.succ = (n+b)+1 by omega, Nat.factorial_succ, ih, List.range_succ,
      List.map_append, List.prod_append]
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,Nat.mul_one]
    ac_rfl

lemma list_product_scale {α : Type} (xs : List α) (a : ℕ) (f : α → ℕ) :
    (xs.map (fun x => a*f x)).prod = a^xs.length * (xs.map f).prod := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,ih]
    ac_rfl

lemma denominator_run {n d m : ℕ} (hd : 0 < d) (hDiv : d ∣ 30) :
    d^m * (n/d+m).factorial =
      (n/d).factorial * shiftedProduct n (denominatorOffsets (n%30) d m) := by
  have hMod : n%30%d = n%d := Nat.mod_mod_of_dvd _ hDiv
  have hScale :
      (List.range m).map (fun i => d*(n/d+i+1)) =
      (List.range m).map (fun i => n+(d*(i+1)-n%30%d)) := by
    apply List.map_congr_left
    intro i _
    have hRem := Nat.mod_lt n hd
    have hN := Nat.mod_add_div n d
    have hLarge : d ≤ d*(i+1) := by
      simpa only [Nat.mul_one] using (Nat.mul_le_mul_left d (Nat.succ_pos i))
    rw [hMod, show n/d+i+1 = n/d+(i+1) by omega, Nat.mul_add]
    omega
  rw [factorial_extend, Nat.mul_left_comm]
  congr 1
  unfold shiftedProduct denominatorOffsets
  simp only [List.map_map, Function.comp_apply]
  rw [← hScale, list_product_scale, List.length_range]

lemma numerator_jump (n : ℕ) :
    30*factorialNumerator (n+30) = factorialNumerator n*shiftedProduct n (topOffsets (n%30)) := by
  have hQuot : (n+30)/30 = n/30+1 := by omega
  have hLast : 30*(n/30+1) = n+(30-n%30) := by omega
  unfold factorialNumerator shiftedProduct topOffsets
  rw [hQuot, Nat.factorial_succ]
  have hBig := factorial_extend n 30
  simp only [Nat.add_assoc] at hBig
  rw [hBig, List.map_append, List.prod_append]
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,Nat.mul_one,
    List.map_map,Function.comp_def,Nat.add_assoc]
  rw [← hLast]
  ac_rfl

lemma denominator_jump (n : ℕ) :
    scalingProduct*factorialDenominator (n+30) =
      factorialDenominator n*shiftedProduct n (bottomOffsets (n%30)) := by
  have h₂ := denominator_run (n := n) (m := 15) (by decide : 0 < 2) (by decide : 2 ∣ 30)
  have h₃ := denominator_run (n := n) (m := 10) (by decide : 0 < 3) (by decide : 3 ∣ 30)
  have h₅ := denominator_run (n := n) (m := 6) (by decide : 0 < 5) (by decide : 5 ∣ 30)
  rw [show n/2+15 = (n+30)/2 by omega] at h₂
  rw [show n/3+10 = (n+30)/3 by omega] at h₃
  rw [show n/5+6 = (n+30)/5 by omega] at h₅
  let D₂ := shiftedProduct n (denominatorOffsets (n%30) 2 15)
  let D₃ := shiftedProduct n (denominatorOffsets (n%30) 3 10)
  let D₅ := shiftedProduct n (denominatorOffsets (n%30) 5 6)
  calc
    _ = (2^15*((n+30)/2).factorial) * (3^10*((n+30)/3).factorial) *
        (5^6*((n+30)/5).factorial) := by unfold scalingProduct factorialDenominator; ac_rfl
    _ = ((n/2).factorial*D₂)*((n/3).factorial*D₃)*((n/5).factorial*D₅) :=
      congrArg₂ (· * ·) (congrArg₂ (· * ·) h₂ h₃) h₅
    _ = _ := by
      simp only [D₂,D₃,D₅,factorialDenominator,shiftedProduct,bottomOffsets,
        List.map_append,List.prod_append]
      ac_rfl

lemma factorial_ratio_growth {n : ℕ} (hn : 420 ≤ n) :
    factorialNumerator (n+30)*factorialDenominator n*100^30 ≤
      factorialDenominator (n+30)*factorialNumerator n*253^30 := by
  have h := bounded_shifted_product hn
  have hnJump := numerator_jump n
  have hdJump := denominator_jump n
  have hPos : 0 < 30*scalingProduct := by decide
  apply Nat.le_of_mul_le_mul_left (k := 30*scalingProduct) _ hPos
  calc
    _ = (scalingProduct*100^30*shiftedProduct n (topOffsets (n%30))) *
        (factorialNumerator n*factorialDenominator n) := by
      calc
        _ = (30*factorialNumerator (n+30))*(scalingProduct*100^30*factorialDenominator n) := by ac_rfl
        _ = _ := by rw [hnJump]; ac_rfl
    _ ≤ (30*253^30*shiftedProduct n (bottomOffsets (n%30))) *
        (factorialNumerator n*factorialDenominator n) := Nat.mul_le_mul_right _ h
    _ = _ := by
      calc
        _ = (factorialDenominator n*shiftedProduct n (bottomOffsets (n%30))) *
            (30*253^30*factorialNumerator n) := by ac_rfl
        _ = _ := by rw [← hdJump]; ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma factorial_ratio_base : ∀ r : Fin 30,
    factorialNumerator (420+r.val)*100^(420+r.val) ≤
      factorialDenominator (420+r.val)*253^(420+r.val) := by
  decide

theorem factorial_ratio_upper {n : ℕ} (hn : 420 ≤ n) :
    factorialNumerator n*100^n ≤ factorialDenominator n*253^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hSmall : n < 450
    · have h := factorial_ratio_base ⟨n-420,by omega⟩
      change factorialNumerator (420+(n-420))*100^(420+(n-420)) ≤
        factorialDenominator (420+(n-420))*253^(420+(n-420)) at h
      rwa [show 420+(n-420) = n by omega] at h
    · let k := n-30
      have hk : 420 ≤ k := by dsimp [k]; omega
      have hK : k+30 = n := by dsimp [k]; omega
      have hPrev := ih k (by dsimp [k]; omega) hk
      have hGain := factorial_ratio_growth hk
      have hPos := Nat.pos_of_ne_zero (denominator_ne_zero k)
      rw [← hK,pow_add 100,pow_add 253]
      apply Nat.le_of_mul_le_mul_right (k := factorialDenominator k) _ hPos
      calc
        _ = (factorialNumerator (k+30)*factorialDenominator k*100^30)*100^k := by ac_rfl
        _ ≤ (factorialDenominator (k+30)*factorialNumerator k*253^30)*100^k :=
          Nat.mul_le_mul_right _ hGain
        _ = (factorialDenominator (k+30)*253^30)*(factorialNumerator k*100^k) := by ac_rfl
        _ ≤ (factorialDenominator (k+30)*253^30)*(factorialDenominator k*253^k) :=
          Nat.mul_le_mul_left _ hPrev
        _ = _ := by ac_rfl

end Erdos137OddPrimorial
