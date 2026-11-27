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

def factorialRun (n d : ℕ) : ℕ :=
  ∏ i ∈ range d, (n+i+1)

lemma factorial_extend (n d : ℕ) :
    (n+d).factorial = n.factorial*factorialRun n d := by
  induction d with
  | zero => simp [factorialRun]
  | succ d ih =>
    rw [show n+d.succ = (n+d)+1 by omega,Nat.factorial_succ,ih]
    unfold factorialRun
    rw [Finset.prod_range_succ]
    ac_rfl

def topRun (n : ℕ) : ℕ :=
  factorialRun n 30 * (n/30+1)

def bottomRun (n : ℕ) : ℕ :=
  factorialRun (n/2) 15 * factorialRun (n/3) 10 * factorialRun (n/5) 6

def scalingProduct : ℕ := 2^15*3^10*5^6

private lemma group_four (a b x y : ℕ) : (a*x)*(b*y) = (a*b)*(x*y) := by ac_rfl

private lemma group_six (a b c x y z : ℕ) :
    (a*x)*(b*y)*(c*z) = (a*b*c)*(x*y*z) := by ac_rfl

private lemma group_numerator (a b x y : ℕ) : (a*x)*(y*b) = (a*b)*(x*y) := by ac_rfl

lemma factorial_run_upper (n d : ℕ) : factorialRun n d ≤ (n+d)^d := by
  unfold factorialRun
  calc
    _ ≤ ∏ _ ∈ range d, (n+d) := Finset.prod_le_prod' (fun i hi => by
      have := mem_range.mp hi
      omega)
    _ = _ := by simp

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
lemma top_run_upper (n : ℕ) : 30*topRun n ≤ (n+30)^31 := by
  have hQuot : 30*(n/30+1) ≤ n+30 := by omega
  have h := Nat.mul_le_mul (factorial_run_upper n 30) hQuot
  change factorialRun n 30*(30*(n/30+1)) ≤ (n+30)^30*(n+30) at h
  unfold topRun
  rw [pow_succ (n+30) 30]
  calc
    _ = factorialRun n 30*(30*(n/30+1)) := Nat.mul_left_comm _ _ _
    _ ≤ _ := h

lemma scaled_factorial_run_lower (n d m : ℕ) (hd : 0 < d) :
    n^m ≤ d^m * factorialRun (n/d) m := by
  unfold factorialRun
  calc
    _ = ∏ _ ∈ range m, n := by simp
    _ ≤ ∏ i ∈ range m, (d*(n/d+i+1)) := by
      apply Finset.prod_le_prod'
      intro i _
      have hRem := Nat.mod_lt n hd
      have hN := Nat.mod_add_div n d
      have hi : d ≤ d*(i+1) := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left d (Nat.succ_pos i)
      rw [Nat.add_assoc,Nat.mul_add]
      omega
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
lemma bottom_run_lower (n : ℕ) : n^31 ≤ scalingProduct*bottomRun n := by
  calc
    _ = (n^15*n^10)*n^6 := by rw [← pow_add,← pow_add]
    _ ≤ (2^15*factorialRun (n/2) 15)*(3^10*factorialRun (n/3) 10)*
        (5^6*factorialRun (n/5) 6) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul (scaled_factorial_run_lower n 2 15 (by decide))
          (scaled_factorial_run_lower n 3 10 (by decide)))
        (scaled_factorial_run_lower n 5 6 (by decide))
    _ = _ := group_six _ _ _ _ _ _

lemma numerator_jump (n : ℕ) :
    factorialNumerator (n+30) = factorialNumerator n*topRun n := by
  have hQuot : (n+30)/30 = n/30+1 := by omega
  have hSmall : (n/30+1).factorial = (n/30+1)*(n/30).factorial := Nat.factorial_succ _
  unfold factorialNumerator topRun
  rw [hQuot, hSmall, factorial_extend n 30]
  exact group_numerator _ _ _ _

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
lemma denominator_jump (n : ℕ) :
    factorialDenominator (n+30) = factorialDenominator n*bottomRun n := by
  unfold factorialDenominator bottomRun
  rw [show (n+30)/2 = n/2+15 by omega,
    show (n+30)/3 = n/3+10 by omega,
    show (n+30)/5 = n/5+6 by omega,
    factorial_extend (n/2) 15,factorial_extend (n/3) 10,factorial_extend (n/5) 6]
  exact group_six _ _ _ _ _ _

private lemma compare_scaled_runs (t u x y a b s c m q : ℕ)
    (ht : c*t ≤ x) (hu : y ≤ s*u) (hScale : a*x ≤ b*y)
    (hNumeric : s*b*m ≤ c*a*q) (hPos : 0 < c*a) : t*m ≤ u*q := by
  apply Nat.le_of_mul_le_mul_left (c := c*a) _ hPos
  calc
    _ = (c*t)*(a*m) := by ac_rfl
    _ ≤ x*(a*m) := Nat.mul_le_mul_right _ ht
    _ = (a*x)*m := by ac_rfl
    _ ≤ (b*y)*m := Nat.mul_le_mul_right _ hScale
    _ = y*(b*m) := by ac_rfl
    _ ≤ (s*u)*(b*m) := Nat.mul_le_mul_right _ hu
    _ = (s*b*m)*u := by ac_rfl
    _ ≤ (c*a*q)*u := Nat.mul_le_mul_right _ hNumeric
    _ = _ := by ac_rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
lemma run_ratio {n : ℕ} (hn : 5000 ≤ n) : topRun n*100^30 ≤ bottomRun n*253^30 := by
  have hScaled : (5000*(n+30))^31 ≤ (5030*n)^31 := pow_le_pow_left' (by omega) _
  rw [mul_pow,mul_pow] at hScaled
  have hNumeric : scalingProduct*5030^31*100^30 ≤ 30*5000^31*253^30 := by decide
  exact compare_scaled_runs (topRun n) (bottomRun n) ((n+30)^31) (n^31) (5000^31) (5030^31)
    scalingProduct 30 (100^30) (253^30) (top_run_upper n) (bottom_run_lower n) hScaled hNumeric (by decide)

private lemma cross_multiply_step (a b t u m q : ℕ) (h : t*m ≤ u*q) :
    (a*t)*b*m ≤ (b*u)*a*q := by
  have hL : (a*t)*b*m = (t*m)*(a*b) := by ac_rfl
  have hR : (b*u)*a*q = (u*q)*(a*b) := by ac_rfl
  rw [hL,hR]
  exact Nat.mul_le_mul_right _ h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
lemma factorial_ratio_growth {n : ℕ} (hn : 5000 ≤ n) :
    factorialNumerator (n+30)*factorialDenominator n*100^30 ≤
      factorialDenominator (n+30)*factorialNumerator n*253^30 := by
  rw [numerator_jump,denominator_jump]
  exact cross_multiply_step _ _ _ _ _ _ (run_ratio hn)

private lemma factorial_run_lower (n r : ℕ) : (n+1)^r ≤ factorialRun n r := by
  unfold factorialRun
  rw [Finset.pow_eq_prod_const]
  exact Finset.prod_le_prod' (fun i _ => by omega)

private def baseTop (r : ℕ) : ℕ := 5029^r*167^((5000+r)/30-166)

private def baseBottom (r : ℕ) : ℕ :=
  2501^((5000+r)/2-2500)*1667^((5000+r)/3-1666)*1001^((5000+r)/5-1000)

private def RatioBase : Prop :=
    factorialNumerator 5000*100^5000*100000000 ≤ factorialDenominator 5000*253^5000

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
private lemma base_numerator_upper (r : ℕ) (hr : r < 30) :
    factorialNumerator (5000+r) ≤ factorialNumerator 5000 * baseTop r := by
  let d := (5000+r)/30-166
  have hd : (5000+r)/30 = 166+d := by dsimp [d]; omega
  have hd' : 166+d ≤ 167 := by omega
  have h1 := (factorial_run_upper 5000 r).trans
    (pow_le_pow_left' (by omega : 5000+r ≤ 5029) r)
  have h2 := (factorial_run_upper 166 d).trans (pow_le_pow_left' hd' d)
  unfold factorialNumerator baseTop
  rw [show (5000:ℕ)/30 = 166 by decide]
  conv_lhs => rw [hd, factorial_extend 5000 r, factorial_extend 166 d]
  calc
    _ = ((5000:ℕ).factorial*(166:ℕ).factorial)*(factorialRun 5000 r*factorialRun 166 d) := group_four _ _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
private lemma base_denominator_lower (r : ℕ) :
    factorialDenominator 5000 * baseBottom r ≤ factorialDenominator (5000+r) := by
  let d₂ := (5000+r)/2-2500
  let d₃ := (5000+r)/3-1666
  let d₅ := (5000+r)/5-1000
  have h₂ : (5000+r)/2 = 2500+d₂ := by dsimp [d₂]; omega
  have h₃ : (5000+r)/3 = 1666+d₃ := by dsimp [d₃]; omega
  have h₅ : (5000+r)/5 = 1000+d₅ := by dsimp [d₅]; omega
  unfold factorialDenominator baseBottom
  rw [show (5000:ℕ)/2 = 2500 by decide, show (5000:ℕ)/3 = 1666 by decide,
    show (5000:ℕ)/5 = 1000 by decide]
  conv_rhs => rw [h₂, h₃, h₅, factorial_extend 2500 d₂, factorial_extend 1666 d₃, factorial_extend 1000 d₅]
  calc
    _ ≤ (((2500:ℕ).factorial*(1666:ℕ).factorial)*(1000:ℕ).factorial)*(factorialRun 2500 d₂*factorialRun 1666 d₃*factorialRun 1000 d₅) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul (factorial_run_lower 2500 d₂)
        (factorial_run_lower 1666 d₃)) (factorial_run_lower 1000 d₅))
    _ = _ := (group_six _ _ _ _ _ _).symm

private lemma extend_base_ratio (N D t u q r m v c : ℕ)
    (hBase : N*q*c ≤ D*r) (hRun : t*m ≤ u*c*v) :
    (N*t)*(q*m) ≤ (D*u)*(r*v) := by
  calc
    _ = (N*q)*(t*m) := by ac_rfl
    _ ≤ (N*q)*(u*c*v) := Nat.mul_le_mul_left _ hRun
    _ = (N*q*c)*(u*v) := by ac_rfl
    _ ≤ (D*r)*(u*v) := Nat.mul_le_mul_right _ hBase
    _ = _ := by ac_rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
lemma factorial_ratio_base (r : Fin 30) (hExact : RatioBase) :
    factorialNumerator (5000+r.val)*100^(5000+r.val) ≤
      factorialDenominator (5000+r.val)*253^(5000+r.val) := by
  have hTable : ∀ j : Fin 30, baseTop j.val*100^j.val ≤ baseBottom j.val*100000000*253^j.val := by
    decide +kernel
  have hA := base_numerator_upper r.val r.isLt
  have hB := base_denominator_lower r.val
  have hRow := hTable r
  rw [pow_add 100,pow_add 253]
  calc
    _ ≤ (factorialNumerator 5000*baseTop r.val)*(100^5000*100^r.val) := Nat.mul_le_mul_right _ hA
    _ ≤ (factorialDenominator 5000*baseBottom r.val)*(253^5000*253^r.val) :=
      extend_base_ratio _ _ _ _ _ _ _ _ _ hExact hRow
    _ ≤ _ := Nat.mul_le_mul_right _ hB

private lemma combine_ratio_bounds (a b A B q r m v : ℕ) (hb : 0 < b)
    (hBase : a*q ≤ b*r) (hGrowth : A*b*m ≤ B*a*v) : A*(q*m) ≤ B*(r*v) := by
  apply Nat.le_of_mul_le_mul_right (c := b) _ hb
  calc
    _ = (A*b*m)*q := by ac_rfl
    _ ≤ (B*a*v)*q := Nat.mul_le_mul_right _ hGrowth
    _ = (B*v)*(a*q) := by ac_rfl
    _ ≤ (B*v)*(b*r) := Nat.mul_le_mul_left _ hBase
    _ = _ := by ac_rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem factorial_ratio_upper {n : ℕ} (hn : 5000 ≤ n) (hExact : RatioBase) :
    factorialNumerator n*100^n ≤ factorialDenominator n*253^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hSmall : n < 5030
    · have h := factorial_ratio_base ⟨n-5000,by omega⟩ hExact
      change factorialNumerator (5000+(n-5000))*100^(5000+(n-5000)) ≤
        factorialDenominator (5000+(n-5000))*253^(5000+(n-5000)) at h
      rwa [show 5000+(n-5000) = n by omega] at h
    · let k := n-30
      have hk : 5000 ≤ k := by dsimp [k]; omega
      have hK : k+30 = n := by dsimp [k]; omega
      have hPrev := ih k (by dsimp [k]; omega) hk
      have hGain := factorial_ratio_growth hk
      have hPos := Nat.pos_of_ne_zero (denominator_ne_zero k)
      rw [← hK,pow_add 100,pow_add 253]
      exact combine_ratio_bounds _ _ _ _ _ _ _ _ hPos hPrev hGain

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
lemma band_product_upper {n : ℕ} (hn : 5000 ≤ n) (hExact : RatioBase) :
    (primeBandProduct n : ℚ) ≤ (253/100 : ℚ)^n := by
  have hD := factorial_ratio_contains_prime_band n
  have hLE := Nat.le_of_dvd (Nat.pos_of_ne_zero (numerator_ne_zero n)) hD
  have hBound := (Nat.mul_le_mul_right (100^n) hLE).trans (factorial_ratio_upper hn hExact)
  have hCast : primeBandProduct n*100^n ≤ 253^n := by
    have h₁ : (primeBandProduct n*100^n)*factorialDenominator n ≤
        253^n*factorialDenominator n := by
      simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hBound
    exact Nat.le_of_mul_le_mul_right h₁ (Nat.pos_of_ne_zero (denominator_ne_zero n))
  rw [div_pow]
  apply (le_div_iff₀ (by positivity)).2
  exact_mod_cast hCast

def smallPrimorialBands : List (ℕ × ℕ) :=
  [(0,1), (2,4), (5,10), (11,16), (17,22), (23,30), (31,42), (43,58), (59,72), (73,96), (97,126), (127,156), (157,192), (193,232), (233,276), (277,336), (337,400), (401,466), (467,562), (563,658), (659,768), (769,886), (887,1030), (1031,1192), (1193,1380), (1381,1582), (1583,1810), (1811,2082), (2083,2380), (2381,2712), (2713,3088), (3089,3532), (3533,4012), (4013,4560), (4561,4999)]

private def PrimorialBase : Prop :=
    ∀ b ∈ smallPrimorialBands, primorial b.2 * 20^b.1 ≤ 61^b.1

private def PrimorialBandCover (start : ℕ) : List (ℕ × ℕ) → Prop
  | [] => 5000 ≤ start
  | b :: bs => b.1 = start ∧ start ≤ b.2 ∧ PrimorialBandCover (b.2+1) bs

private instance (start : ℕ) (bands : List (ℕ × ℕ)) :
    Decidable (PrimorialBandCover start bands) := by
  induction bands generalizing start with
  | nil => unfold PrimorialBandCover; infer_instance
  | cons b bs ih =>
    unfold PrimorialBandCover
    letI := ih (b.2+1)
    infer_instance

private lemma primorial_band_cover_of_chain (start r : ℕ) (bands : List (ℕ × ℕ))
    (hChain : PrimorialBandCover start bands) (hStart : start ≤ r) (hR : r < 5000) :
    ∃ b ∈ bands, b.1 ≤ r ∧ r ≤ b.2 := by
  induction bands generalizing start with
  | nil => exact (not_lt_of_ge (hChain.trans hStart) hR).elim
  | cons b bs ih =>
    rcases hChain with ⟨hL,_,hNext⟩
    by_cases h : r ≤ b.2
    · exact ⟨b,List.mem_cons_self,by omega,h⟩
    · obtain ⟨z,hB,h₁,h₂⟩ := ih (b.2+1) hNext (by omega)
      exact ⟨z,List.mem_cons_of_mem _ hB,h₁,h₂⟩

lemma primorial_base (r : Fin 5000) (hBands : PrimorialBase) : primorial r.val * 20^r.val ≤ 61^r.val := by
  obtain ⟨b,hb,hlo,hhi⟩ := primorial_band_cover_of_chain 0 r.val smallPrimorialBands
    (by decide) (Nat.zero_le _) r.isLt
  have h : primorial b.2 * 20^b.1 ≤ 61^b.1 := hBands b hb
  have hd : r.val = b.1 + (r.val-b.1) := by omega
  have hpow : (20 : ℕ)^(r.val-b.1) ≤ 61^(r.val-b.1) := pow_le_pow_left' (by decide) _
  calc
    _ ≤ primorial b.2 * 20^r.val := Nat.mul_le_mul_right _ (primorial_mono hhi)
    _ = (primorial b.2 * 20^b.1)*20^(r.val-b.1) := by
      conv_lhs => rw [hd,pow_add,Nat.mul_assoc]
    _ ≤ 61^b.1 * 61^(r.val-b.1) := Nat.mul_le_mul h hpow
    _ = _ := by rw [← pow_add,← hd]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem primorial_le_61_over_20 (n : ℕ) (hExact : RatioBase) (hBands : PrimorialBase) :
    (primorial n : ℚ) ≤ (61/20 : ℚ)^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hSmall : n < 5000
    · rw [div_pow]
      apply (le_div_iff₀ (by positivity)).2
      have h := primorial_base ⟨n,hSmall⟩ hBands
      exact_mod_cast h
    · have hBand := band_product_upper (show 5000 ≤ n by omega) hExact
      have hSmallP := ih (n/6) (Nat.div_lt_self (by omega) (by decide))
      have hMul : (primorial n : ℚ) = (primorial (n/6) : ℚ) * primeBandProduct n := by
        exact_mod_cast (band_product_mul_primorial n).symm
      have hPower : (primorial n : ℚ)^6 ≤ ((61/20 : ℚ)^n)^6 := by
        calc
          _ = (primorial (n/6) : ℚ)^6 * (primeBandProduct n : ℚ)^6 := by rw [hMul,mul_pow]
          _ ≤ ((61/20 : ℚ)^(n/6))^6 * ((253/100 : ℚ)^n)^6 :=
            mul_le_mul (pow_le_pow_left₀ (by positivity) hSmallP 6)
              (pow_le_pow_left₀ (by positivity) hBand 6) (by positivity) (by positivity)
          _ = (61/20 : ℚ)^(6*(n/6)) * ((253/100 : ℚ)^6)^n := by
            rw [← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm (n/6) 6, Nat.mul_comm n 6]
          _ ≤ (61/20 : ℚ)^(6*(n/6)) * ((61/20 : ℚ)^5)^n :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by norm_num) n) (by positivity)
          _ = (61/20 : ℚ)^(6*(n/6)+5*n) := by rw [← pow_mul, ← pow_add]
          _ ≤ (61/20 : ℚ)^(n*6) := pow_le_pow_right₀ (by norm_num) (by omega)
          _ = _ := pow_mul _ _ _
      exact le_of_pow_le_pow_left₀ (by decide : 6 ≠ 0) (by positivity) hPower

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem primorial_eighth_le_of_bases (n : ℕ) (hExact : RatioBase) (hBands : PrimorialBase) : (primorial n)^8 ≤ 2^(13*n) := by
  have h : (primorial n : ℚ)^8 ≤ (2:ℚ)^(13*n) := by
    calc
      _ ≤ ((61/20 : ℚ)^n)^8 := pow_le_pow_left₀ (by positivity) (primorial_le_61_over_20 n hExact hBands) _
      _ = ((61/20 : ℚ)^8)^n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm n 8]
      _ ≤ ((2:ℚ)^13)^n := pow_le_pow_left₀ (by positivity) (by norm_num) _
      _ = _ := by rw [← pow_mul]
  exact_mod_cast h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma factorial_ratio_at_5000 : RatioBase := by
  unfold RatioBase
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_primorial_band_bounds : PrimorialBase := by
  unfold PrimorialBase
  decide +kernel

theorem primorial_eighth_le (n : ℕ) : (primorial n)^8 ≤ 2^(13*n) :=
  primorial_eighth_le_of_bases n factorial_ratio_at_5000 small_primorial_band_bounds

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
lemma prime_count_linear_from_cutoff (n b C : ℕ) (hC : (Nat.primesLE (2^b)).card ≤ C) :
    (8*b)*n.primesLE.card ≤ 13*n+(8*b)*C := by
  let P := n.primesLE
  let S := P.filter (· ≤ 2^b)
  let T := P.filter (2^b < ·)
  have hS : S ⊆ Nat.primesLE (2^b) := by
    intro p hp
    rcases mem_filter.mp hp with ⟨hpP,hpU⟩
    have hp' := (mem_filter.mp hpP).2
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),hp'⟩
  have hSmall := (card_le_card hS).trans hC
  have hCount : S.card+T.card = P.card := by
    have h := card_filter_add_card_filter_not (s := P) (· ≤ (2^b:ℕ))
    simpa only [S,T,not_le] using h
  have hL : (2^b : ℕ)^T.card ≤ primorial n := by
    rw [primorial_eq_prod_primesLE]
    calc
      _ = ∏ _ ∈ T, (2^b : ℕ) := (Finset.prod_const _).symm
      _ ≤ ∏ p ∈ T, p := Finset.prod_le_prod' (fun p hp => by
        have h := (mem_filter.mp hp).2
        omega)
      _ ≤ ∏ p ∈ P, p := Finset.prod_le_prod_of_subset_of_one_le' (filter_subset ..)
        (fun p hp _ => (show p.Prime from (mem_filter.mp hp).2).pos)
  have hP := (pow_le_pow_left' hL 8).trans (primorial_eighth_le n)
  simp only [← pow_mul] at hP
  have hR : b*T.card*8 = (8*b)*T.card := by ac_rfl
  rw [hR] at hP
  have hc : (8*b)*T.card ≤ 13*n := by
    by_contra! hh
    exact (not_lt_of_ge hP) (Nat.pow_lt_pow_right (by decide) hh)
  have hProd : (8*b)*S.card ≤ (8*b)*C := Nat.mul_le_mul_left _ hSmall
  have hCount' := congrArg (fun t : ℕ => (8*b)*t) hCount
  rw [Nat.mul_add] at hCount'
  omega

end Erdos137OddPrimorial
