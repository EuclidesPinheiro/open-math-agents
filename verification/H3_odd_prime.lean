import FormalConjectures.ErdosProblems.«137»
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Sym.Card

/-! Arithmetic lemmas for the odd prime exponent case of Erdős–Selfridge. -/

namespace Erdos137PerfectPower

open Finset

lemma sylvester_schur_lower_bound {k n l p t : ℕ}
    (hl : 2 ≤ l) (hkp : k < p) (ht : t ∈ Ioc n (n + k))
    (hDvd : p ^ l ∣ t) : k ^ l < n := by
  have hInterval := mem_Ioc.mp ht
  have hPos : 0 < t := by omega
  have hUpper : p ^ l ≤ n + k := (Nat.le_of_dvd hPos hDvd).trans hInterval.2
  let r := l - 2
  have hlr : l = r + 2 := by dsimp [r]; omega
  have hRoot : k + 1 ≤ p := by omega
  have hPow : (k + 1) ^ l ≤ p ^ l :=
    (Nat.pow_le_pow_iff_left (by omega : l ≠ 0)).2 hRoot
  have hMono : k ^ r ≤ (k + 1) ^ r := pow_le_pow_left' (by omega) r
  have hGap : k ^ l + (k + 1) ≤ (k + 1) ^ l := by
    by_cases hk : k = 0
    · simp [hk, show l ≠ 0 by omega]
    have hOne : 1 ≤ k ^ r := pow_pos (by omega : 0 < k) r
    rw [hlr, pow_add k, pow_add (k + 1)]
    have hExtra := Nat.mul_le_mul_right (k + 1) hOne
    calc
      k ^ r * k ^ 2 + (k + 1) ≤ k ^ r * (k ^ 2 + (k + 1)) := by
        rw [Nat.mul_add]
        simpa only [Nat.one_mul] using Nat.add_le_add_left hExtra _
      _ ≤ k ^ r * (k + 1) ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
      _ ≤ (k + 1) ^ r * (k + 1) ^ 2 := Nat.mul_le_mul_right _ hMono
  have := hGap.trans (hPow.trans hUpper)
  omega

lemma large_prime_factorization_single {k n p t : ℕ}
    (hkp : k ≤ p) (ht : t ∈ Ioc n (n + k)) (hpt : p ∣ t) :
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

theorem sylvester_schur_power_bounds_of_no_witness {k n l : ℕ}
    (hl : 2 ≤ l)
    (hSylvester : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ m ∈ Ioc n (n + k), m)
    (hAll : ∀ p : ℕ, k ≤ p → p.Prime →
      l ∣ (∏ m ∈ Ioc n (n + k), m).factorization p) :
    k ^ l < n ∧ (k + 1) ^ l ≤ n + k := by
  obtain ⟨p, hp, hkp, hProd⟩ := hSylvester
  obtain ⟨m, hm, hpm⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hProd
  have hmBounds := mem_Ioc.mp hm
  have hmNonzero : m ≠ 0 := by omega
  have hDiv := hAll p hkp.le hp
  rw [large_prime_factorization_single hkp.le hm hpm] at hDiv
  have hPos := hp.factorization_pos_of_dvd hmNonzero hpm
  have hPow := (hp.pow_dvd_iff_le_factorization hmNonzero).2 (Nat.le_of_dvd hPos hDiv)
  refine ⟨sylvester_schur_lower_bound hl hkp hm hPow, ?_⟩
  exact (pow_le_pow_left' (show k + 1 ≤ p by omega) l).trans
    ((Nat.le_of_dvd (Nat.pos_of_ne_zero hmNonzero) hPow).trans hmBounds.2)

theorem sylvester_schur_lower_bound_of_no_witness {k n l : ℕ}
    (hl : 2 ≤ l)
    (hSylvester : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ m ∈ Ioc n (n + k), m)
    (hAll : ∀ p : ℕ, k ≤ p → p.Prime →
      l ∣ (∏ m ∈ Ioc n (n + k), m).factorization p) : k ^ l < n :=
  (sylvester_schur_power_bounds_of_no_witness hl hSylvester hAll).1

lemma cube_gap {x l : ℕ} (hl : 3 ≤ l) :
    x ^ l + 3 * x ^ (l - 1) ≤ (x + 1) ^ l := by
  let r := l - 3
  have hlr : l = r + 3 := by dsimp [r]; omega
  have hPrev : l - 1 = r + 2 := by omega
  have hMono : x ^ r ≤ (x + 1) ^ r := pow_le_pow_left' (by omega) r
  rw [hPrev, hlr, pow_add x r 3, pow_add x r 2, pow_add (x + 1) r 3]
  calc
    x ^ r * x ^ 3 + 3 * (x ^ r * x ^ 2) =
        x ^ r * (x ^ 3 + 3 * x ^ 2) := by ring
    _ ≤ x ^ r * (x + 1) ^ 3 := Nat.mul_le_mul_left _ (by
      calc
        x ^ 3 + 3 * x ^ 2 ≤ x ^ 3 + 3 * x ^ 2 + (3 * x + 1) := by omega
        _ = (x + 1) ^ 3 := by ring)
    _ ≤ (x + 1) ^ r * (x + 1) ^ 3 := Nat.mul_le_mul_right _ hMono

lemma pair_product_injective {n k i j u v : ℕ}
    (hn : k ^ 2 < n) (hij : i ≤ j) (huv : u ≤ v) (hj : j ≤ k) (hv : v ≤ k)
    (h : (n + i) * (n + j) = (n + u) * (n + v)) : i = u ∧ j = v := by
  have hijBound : i * j ≤ k ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) hj
  have huvBound : u * v ≤ k ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) hv
  have hSums : i + j = u + v := by
    rcases lt_trichotomy (i + j) (u + v) with hlt | heq | hgt
    · have hScale := Nat.mul_le_mul_left n (show i + j + 1 ≤ u + v by omega)
      nlinarith only [hScale, h, hijBound, hn, Nat.zero_le (u * v)]
    · exact heq
    · have hScale := Nat.mul_le_mul_left n (show u + v + 1 ≤ i + j by omega)
      nlinarith only [hScale, h, huvBound, hn, Nat.zero_le (i * j)]
  have hScale := congrArg (fun z : ℕ => n * z) hSums
  have hProds : i * j = u * v := by nlinarith only [hScale, h]
  have hSumsZ : (i : ℤ) + j = (u : ℤ) + v := by exact_mod_cast hSums
  have hProdsZ : (i : ℤ) * j = (u : ℤ) * v := by exact_mod_cast hProds
  have hScaleZ := congrArg (fun z : ℤ => (i : ℤ) * z) hSumsZ
  have hRoots : ((i : ℤ) - u) * ((i : ℤ) - v) = 0 := by
    nlinarith only [hScaleZ, hProdsZ]
  rcases mul_eq_zero.mp hRoots with hLeft | hRight
  · exact ⟨by omega, by omega⟩
  · omega

lemma scaled_pair_gap {n k l a x y : ℕ}
    (hn : k ^ l < n) (hl : 3 ≤ l) (ha : 0 < a)
    (hx : n ^ 2 ≤ a * x ^ l) (hxy : x < y) :
    a * x ^ l + 3 * (n * k) ≤ a * y ^ l := by
  have hnPos : 0 < n := by omega
  have hL : l ≠ 0 := by omega
  let w := a * x ^ (l - 1)
  have hMonoA : a ^ (l - 1) ≤ a ^ l :=
    pow_le_pow_right' (by omega) (Nat.sub_le _ _)
  have hP : (n * k) ^ l < w ^ l := by
    calc
      (n * k) ^ l = n ^ l * k ^ l := mul_pow _ _ _
      _ < n ^ l * n ^ (l - 2) := Nat.mul_lt_mul_of_pos_left
        (hn.trans_le (Nat.le_pow (by omega))) (pow_pos hnPos _)
      _ = (n ^ 2) ^ (l - 1) := by
        rw [← pow_add, ← pow_mul]
        congr 1
        omega
      _ ≤ (a * x ^ l) ^ (l - 1) := pow_le_pow_left' hx _
      _ ≤ w ^ l := by
        dsimp [w]
        simp only [mul_pow, ← pow_mul]
        rw [Nat.mul_comm l (l - 1)]
        exact Nat.mul_le_mul_right _ hMonoA
  have hw : n * k ≤ w := ((Nat.pow_lt_pow_iff_left hL).1 hP).le
  have hAtNext := (cube_gap (x := x) hl).trans
    (pow_le_pow_left' (show x + 1 ≤ y by omega) l)
  have hScaled := Nat.mul_le_mul_left a hAtNext
  rw [Nat.mul_add] at hScaled
  have hStep : 3 * (n * k) ≤ a * (3 * x ^ (l - 1)) := by
    calc
      3 * (n * k) ≤ 3 * w := Nat.mul_le_mul_left 3 hw
      _ = a * (3 * x ^ (l - 1)) := by dsimp [w]; ring
  exact (Nat.add_le_add_left hStep _).trans hScaled

theorem distinct_pair_products {n k l : ℕ} {a x : ℕ → ℕ}
    (hk : 0 < k) (hn : k ^ l < n) (hl : 3 ≤ l)
    (ha : ∀ i ≤ k, 0 < a i) (hRepr : ∀ i ≤ k, n + i = a i * x i ^ l)
    {i j u v : ℕ} (hij : i < j) (huv : u < v) (hj : j ≤ k) (hv : v ≤ k)
    (hCoeff : a i * a j = a u * a v) : i = u ∧ j = v := by
  have hL : l ≠ 0 := by omega
  have hnSquare : k ^ 2 < n := (pow_le_pow_right' (by omega : 1 ≤ k)
    (show 2 ≤ l by omega)).trans_lt hn
  have hnk : k < n := (Nat.le_pow (by omega : 0 < l)).trans_lt hn
  let A := a i * a j
  have hA : 0 < A := Nat.mul_pos (ha i (by omega)) (ha j hj)
  let s := x i * x j
  let t := x u * x v
  have hS : (n + i) * (n + j) = A * s ^ l := by
    dsimp [A, s]
    rw [hRepr i (by omega), hRepr j hj, mul_pow]
    ring
  have hT : (n + u) * (n + v) = A * t ^ l := by
    dsimp [A, t]
    rw [hRepr u (by omega), hRepr v hv]
    calc
      a u * x u ^ l * (a v * x v ^ l) = (a u * a v) * (x u * x v) ^ l := by
        rw [mul_pow]
        ring
      _ = (a i * a j) * (x u * x v) ^ l := by rw [hCoeff]
  have hLowS : n ^ 2 ≤ A * s ^ l := by
    rw [← hS, pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hLowT : n ^ 2 ≤ A * t ^ l := by
    rw [← hT, pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hUpperS : A * s ^ l ≤ (n + k) ^ 2 := by
    rw [← hS, pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hUpperT : A * t ^ l ≤ (n + k) ^ 2 := by
    rw [← hT, pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hBound : (n + k) ^ 2 < n ^ 2 + 3 * (n * k) := by
    have hMul := Nat.mul_lt_mul_of_pos_right hnk hk
    nlinarith only [hMul]
  have hEqual : s = t := by
    rcases lt_trichotomy s t with hlt | heq | hgt
    · have hGap := scaled_pair_gap hn hl hA hLowS hlt
      omega
    · exact heq
    · have hGap := scaled_pair_gap hn hl hA hLowT hgt
      omega
  apply pair_product_injective hnSquare hij.le huv.le hj hv
  rw [hS, hT, hEqual]

lemma power_remainders (l t : ℕ) (hl : l ≠ 0) :
    ∃ a x : ℕ, a ≠ 0 ∧ t = a * x ^ l ∧
      ∀ p : ℕ, a.factorization p = t.factorization p % l := by
  by_cases ht : t = 0
  · subst t
    exact ⟨1, 0, by decide, by simp [hl], by simp⟩
  let remainders := Finsupp.mapRange (fun e : ℕ => e % l) (Nat.zero_mod l) t.factorization
  let quotients := Finsupp.mapRange (fun e : ℕ => e / l) (Nat.zero_div l) t.factorization
  have hRem : remainders ≤ t.factorization := fun p => Nat.mod_le _ _
  have hQuot : quotients ≤ t.factorization := fun p => Nat.div_le_self _ _
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
  · apply Nat.eq_of_factorization_eq ht (mul_ne_zero ha (pow_ne_zero l hx))
    intro p
    rw [Nat.factorization_mul ha (pow_ne_zero l hx), Nat.factorization_pow, hFactorA, hFactorX]
    change t.factorization p = t.factorization p % l + l * (t.factorization p / l)
    exact (Nat.mod_add_div _ _).symm
  · intro p
    rw [hFactorA]
    exact Finsupp.mapRange_apply

lemma two_power_remainders {l A B : ℕ} (hl : l ≠ 0)
    (heq : ∀ p : ℕ, p.Prime → A.factorization p % l = B.factorization p % l) :
    ∃ c x y : ℕ, c ≠ 0 ∧ A = c * x ^ l ∧ B = c * y ^ l := by
  obtain ⟨a, x, ha, hA, haFac⟩ := power_remainders l A hl
  obtain ⟨b, y, hb, hB, hbFac⟩ := power_remainders l B hl
  have hab : a = b := by
    apply Nat.eq_of_factorization_eq ha hb
    intro p
    rw [haFac, hbFac]
    by_cases hp : p.Prime
    · exact heq p hp
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]
  exact ⟨a, x, y, ha, hA, hab.symm ▸ hB⟩

theorem normalize_odd_coefficients {n k l : ℕ} (hl : l ≠ 0)
    (hAll : ∀ p : ℕ, k ≤ p → p.Prime →
      l ∣ (∏ t ∈ Ioc n (n+k), t).factorization p) :
    ∃ a x : ℕ → ℕ,
      (∀ i ∈ Icc 1 k, a i ≠ 0) ∧
      (∀ i ∈ Icc 1 k, n+i = a i * x i ^ l) ∧
      (∀ i ∈ Icc 1 k, ∀ p ∈ (a i).primeFactors, p < k) ∧
      (∀ i ∈ Icc 1 k, ∀ p : ℕ, (a i).factorization p = (n+i).factorization p % l) := by
  choose a x ha hRepr hFac using fun i : ℕ => power_remainders l (n+i) hl
  refine ⟨a, x, fun i _ => ha i, fun i _ => hRepr i, ?_, fun i _ => hFac i⟩
  intro i hi p hp
  have hiB := mem_Icc.mp hi
  have ht : n+i ∈ Ioc n (n+k) := mem_Ioc.mpr ⟨by omega, by omega⟩
  obtain ⟨hpPrime, hpDvd, _⟩ := Nat.mem_primeFactors.mp hp
  by_contra! hpK
  have hpT : p ∣ n+i := by
    rw [hRepr i]
    exact hpDvd.trans (dvd_mul_right _ _)
  have hDiv := hAll p hpK hpPrime
  rw [large_prime_factorization_single hpK ht hpT] at hDiv
  have hPos := hpPrime.factorization_pos_of_dvd (ha i) hpDvd
  rw [hFac i, Nat.mod_eq_zero_of_dvd hDiv] at hPos
  exact (Nat.lt_irrefl 0) hPos

lemma scaled_power_eq_of_in_pair_interval {n k l A B : ℕ}
    (hk : 0 < k) (hn : k ^ l < n) (hl : 3 ≤ l)
    (hA : n ^ 2 ≤ A ∧ A ≤ (n + k) ^ 2) (hB : n ^ 2 ≤ B ∧ B ≤ (n + k) ^ 2)
    (heq : ∀ p : ℕ, p.Prime → A.factorization p % l = B.factorization p % l) : A = B := by
  obtain ⟨c, x, y, hc, hX, hY⟩ := two_power_remainders (by omega) heq
  have hnk : k < n := (Nat.le_pow (by omega : 0 < l)).trans_lt hn
  have hBound : (n + k) ^ 2 < n ^ 2 + 3 * (n * k) := by
    have hMul := Nat.mul_lt_mul_of_pos_right hnk hk
    nlinarith only [hMul]
  have hxy : x = y := by
    rcases lt_trichotomy x y with hlt | he | hgt
    · have hGap := scaled_pair_gap hn hl (Nat.pos_of_ne_zero hc) (hX ▸ hA.1) hlt
      rw [← hX, ← hY] at hGap
      omega
    · exact he
    · have hGap := scaled_pair_gap hn hl (Nat.pos_of_ne_zero hc) (hY ▸ hB.1) hgt
      rw [← hY, ← hX] at hGap
      omega
  rw [hX, hY, hxy]

lemma factorization_mul_power_mod {l a x : ℕ} (ha : a ≠ 0) (hx : x ≠ 0) (p : ℕ) :
    (a * x ^ l).factorization p % l = a.factorization p % l := by
  rw [Nat.factorization_mul ha (pow_ne_zero l hx), Nat.factorization_pow]
  change (a.factorization p + l * x.factorization p) % l = a.factorization p % l
  rw [Nat.add_mul_mod_self_left]

-- The upper bound from Sylvester–Schur lets us compare ratios using only
-- integer powers, including when the product contains more than two terms.
lemma scaled_power_gap_in_interval {n k l d c x y : ℕ}
    (hk : 0 < k) (hn : k ^ 2 ≤ n) (hTop : (k + 1) ^ l ≤ n + k)
    (hd : d < l) (hc : 0 < c)
    (hX : n ^ d ≤ c * x ^ l) (hY : c * y ^ l ≤ (n + k) ^ d)
    (hxy : x < y) : False := by
  have hl : l ≠ 0 := by omega
  have hyPow : y ^ l ≤ (n + k) ^ d := by
    have h := Nat.mul_le_mul_right (y ^ l) hc
    rw [Nat.one_mul] at h
    exact h.trans hY
  have hyTop : y * (k + 1) ≤ n + k := (Nat.pow_le_pow_iff_left hl).1 (by
    calc
      (y * (k + 1)) ^ l = y ^ l * (k + 1) ^ l := mul_pow _ _ _
      _ ≤ (n + k) ^ d * (n + k) := Nat.mul_le_mul hyPow hTop
      _ = (n + k) ^ (d + 1) := (pow_succ _ _).symm
      _ ≤ (n + k) ^ l := pow_le_pow_right' (by omega) (by omega))
  have hky : k * y ≤ n := by
    by_cases hy : k ≤ y
    · nlinarith only [hyTop, hy]
    · exact (Nat.mul_le_mul_left k (by omega : y ≤ k)).trans (by simpa [pow_two] using hn)
  have hRatio : x * (n + k) < y * n := by
    have hStep := Nat.mul_le_mul_right (n+k) (show x+1 ≤ y by omega)
    nlinarith only [hStep, hky, hk]
  have hPowered := (Nat.pow_lt_pow_iff_left hl).2 hRatio
  simp only [mul_pow] at hPowered
  have hComparison : y ^ l * n ^ d ≤ x ^ l * (n + k) ^ d := by
    apply Nat.le_of_mul_le_mul_left _ hc
    calc
      c * (y ^ l * n ^ d) = n ^ d * (c * y ^ l) := by ac_rfl
      _ ≤ (c * x ^ l) * (n + k) ^ d := Nat.mul_le_mul hX hY
      _ = c * (x ^ l * (n + k) ^ d) := by ac_rfl
  have hLift := Nat.mul_le_mul hComparison (pow_le_pow_left' (show n ≤ n+k by omega) (l-d))
  have hExp : d + (l-d) = l := by omega
  simp only [Nat.mul_assoc, ← pow_add, hExp] at hLift
  exact (not_lt_of_ge hLift) hPowered

lemma scaled_power_eq_of_in_product_interval {n k l d A B : ℕ}
    (hk : 0 < k) (hn : k ^ 2 ≤ n) (hTop : (k + 1) ^ l ≤ n + k) (hd : d < l)
    (hA : n ^ d ≤ A ∧ A ≤ (n + k) ^ d) (hB : n ^ d ≤ B ∧ B ≤ (n + k) ^ d)
    (heq : ∀ p : ℕ, p.Prime → A.factorization p % l = B.factorization p % l) : A = B := by
  obtain ⟨c, x, y, hc, hX, hY⟩ := two_power_remainders (by omega) heq
  have hxy : x = y := by
    rcases lt_trichotomy x y with hlt | he | hgt
    · exact (scaled_power_gap_in_interval hk hn hTop hd (Nat.pos_of_ne_zero hc)
        (hX ▸ hA.1) (hY ▸ hB.2) hlt).elim
    · exact he
    · exact (scaled_power_gap_in_interval hk hn hTop hd (Nat.pos_of_ne_zero hc)
        (hY ▸ hB.1) (hX ▸ hA.2) hgt).elim
  rw [hX, hY, hxy]

lemma gcd_block_multiset_product_le {n k i : ℕ} (hi : i ∈ Icc 1 k)
    (s : Multiset ℕ) (hs : ∀ j ∈ s, j ∈ Icc 1 k) (hne : i ∉ s) :
    (n + i).gcd (s.map (n + ·)).prod ≤ k ^ s.card := by
  have hiB := mem_Icc.mp hi
  have hiPos : 0 < n+i := by omega
  induction s using Multiset.induction_on with
  | empty => simp
  | cons j s ih =>
    have hj := mem_Icc.mp (hs j (Multiset.mem_cons_self _ _))
    have hji : i ≠ j := by
      rintro rfl
      exact hne (Multiset.mem_cons_self _ _)
    have hGCD : (n+i).gcd (n+j) ≤ k := by
      have hI := Nat.gcd_dvd_left (n+i) (n+j)
      have hJ := Nat.gcd_dvd_right (n+i) (n+j)
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · exact (Nat.le_of_dvd (show 0 < (n+j)-(n+i) by omega) (Nat.dvd_sub hJ hI)).trans (by omega)
      · exact (Nat.le_of_dvd (show 0 < (n+i)-(n+j) by omega) (Nat.dvd_sub hI hJ)).trans (by omega)
    have hTail := ih (fun t ht => hs t (Multiset.mem_cons_of_mem ht))
      (fun h => hne (Multiset.mem_cons_of_mem h))
    let M := (s.map (n+·)).prod
    have hd := Nat.gcd_mul_right_dvd_mul_gcd (n+i) (n+j) M
    have hPos : 0 < (n+i).gcd (n+j) * (n+i).gcd M :=
      Nat.mul_pos (Nat.gcd_pos_of_pos_left _ hiPos) (Nat.gcd_pos_of_pos_left _ hiPos)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
    exact (Nat.le_of_dvd hPos hd).trans (Nat.mul_le_mul hGCD hTail)

lemma block_multiset_prod_injective {n k l : ℕ} (hk : 0 < k) (hn : k^l < n)
    (s t : Multiset ℕ) (hs : ∀ i ∈ s, i ∈ Icc 1 k) (ht : ∀ i ∈ t, i ∈ Icc 1 k)
    (hCard : s.card = t.card) (hl : s.card < l)
    (heq : (s.map (n + ·)).prod = (t.map (n + ·)).prod) :
    s = t := by
  induction s using Multiset.induction_on generalizing t with
  | empty => exact (Multiset.card_eq_zero.mp (by simpa using hCard.symm)).symm
  | cons i s ih =>
    have hi := hs i (Multiset.mem_cons_self _ _)
    have hiPos : 0 < n+i := by have := (mem_Icc.mp hi).1; omega
    have hiT : i ∈ t := by
      by_contra hAbsent
      have hG := gcd_block_multiset_product_le (n := n) hi t ht hAbsent
      have hD : n+i ∣ (t.map (n+·)).prod := by
        rw [← heq, Multiset.map_cons, Multiset.prod_cons]
        exact dvd_mul_right _ _
      rw [Nat.gcd_eq_left_iff_dvd.mpr hD] at hG
      have hPow : k ^ t.card ≤ k ^ l :=
        pow_le_pow_right' (by omega : 1 ≤ k) (by omega)
      omega
    let u := t.erase i
    have hu : i ::ₘ u = t := Multiset.cons_erase hiT
    have huData : ∀ j ∈ u, j ∈ Icc 1 k :=
      fun j hj => ht j (Multiset.mem_of_mem_erase hj)
    rw [← hu] at hCard heq ⊢
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons] at hCard heq
    have hl' : s.card < l := by
      have h := Multiset.card_cons i s
      omega
    have hTail := ih u (fun j hj => hs j (Multiset.mem_cons_of_mem hj)) huData
      (by omega) hl' (Nat.mul_left_cancel hiPos heq)
    rw [hTail]

lemma multiset_prod_block_repr {n k l : ℕ} {a x : ℕ → ℕ}
    (hRepr : ∀ i ∈ Icc 1 k, n+i = a i * x i ^ l)
    (s : Multiset ℕ) (hs : ∀ i ∈ s, i ∈ Icc 1 k) :
    (s.map (n+·)).prod = (s.map a).prod * (s.map x).prod ^ l := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [hRepr i (hs i (Multiset.mem_cons_self _ _)),
      ih (fun j hj => hs j (Multiset.mem_cons_of_mem hj)), mul_pow]
    ac_rfl

theorem distinct_multiset_products_mod_l {n k l : ℕ} {a x : ℕ → ℕ}
    (hk : 0 < k) (hn : k^l < n) (hl : 2 ≤ l) (hTop : (k+1)^l ≤ n+k)
    (hRepr : ∀ i ∈ Icc 1 k, n+i = a i * x i ^ l)
    (s t : Multiset ℕ) (hs : ∀ i ∈ s, i ∈ Icc 1 k) (ht : ∀ i ∈ t, i ∈ Icc 1 k)
    (hCard : s.card = t.card) (hSmall : s.card < l)
    (hMod : ∀ p : ℕ, p.Prime →
      (s.map a).prod.factorization p % l = (t.map a).prod.factorization p % l) :
    s = t := by
  have hn0 : 0 < n := by omega
  have hSq : k^2 ≤ n := (pow_le_pow_right' (by omega : 1 ≤ k) hl).trans hn.le
  have hBounds (u : Multiset ℕ) (hu : ∀ i ∈ u, i ∈ Icc 1 k) :
      n^u.card ≤ (u.map (n+·)).prod ∧ (u.map (n+·)).prod ≤ (n+k)^u.card := by
    have hLo := Multiset.pow_card_le_prod (s := u.map (n+·)) (a := n) (by
      intro v hv
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hv
      omega)
    have hHi := Multiset.prod_le_pow_card (u.map (n+·)) (n+k) (by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hv
      have := (mem_Icc.mp (hu i hi)).2
      omega)
    simpa only [Multiset.card_map] using And.intro hLo hHi
  have hFac (u : Multiset ℕ) (hu : ∀ i ∈ u, i ∈ Icc 1 k) (p : ℕ) :
      (u.map (n+·)).prod.factorization p % l = (u.map a).prod.factorization p % l := by
    have hPos := ((pow_pos hn0 u.card).trans_le (hBounds u hu).1).ne'
    have hId := multiset_prod_block_repr hRepr u hu
    rw [hId] at hPos ⊢
    have ha : (u.map a).prod ≠ 0 := fun h => hPos (by rw [h, zero_mul])
    have hx : (u.map x).prod ≠ 0 := fun h => hPos (by rw [h, zero_pow (by omega : l ≠ 0), mul_zero])
    exact factorization_mul_power_mod ha hx p
  apply block_multiset_prod_injective hk hn s t hs ht hCard hSmall
  have htBounds := hBounds t ht
  rw [← hCard] at htBounds
  apply scaled_power_eq_of_in_product_interval hk hSq hTop hSmall (hBounds s hs) htBounds
  intro p hp
  rw [hFac s hs p, hFac t ht p]
  exact hMod p hp

theorem distinct_pair_products_mod_l {n k l : ℕ} {a x : ℕ → ℕ}
    (hk : 0 < k) (hn : k ^ l < n) (hl : 3 ≤ l)
    (hRepr : ∀ i ∈ Icc 1 k, n + i = a i * x i ^ l)
    {i j u v : ℕ} (hi : 1 ≤ i) (hu : 1 ≤ u) (hij : i ≤ j) (huv : u ≤ v)
    (hj : j ≤ k) (hv : v ≤ k)
    (heq : ∀ p : ℕ, p.Prime →
      (a i * a j).factorization p % l = (a u * a v).factorization p % l) :
    i = u ∧ j = v := by
  have hnSquare : k ^ 2 < n :=
    (pow_le_pow_right' (by omega : 1 ≤ k) (show 2 ≤ l by omega)).trans_lt hn
  have hBounds (r s : ℕ) (hr : r ≤ k) (hs : s ≤ k) :
      n ^ 2 ≤ (n + r) * (n + s) ∧ (n + r) * (n + s) ≤ (n + k) ^ 2 := by
    rw [pow_two, pow_two]
    exact ⟨Nat.mul_le_mul (by omega) (by omega), Nat.mul_le_mul (by omega) (by omega)⟩
  have hReprPair (r s : ℕ) (hr : r ∈ Icc 1 k) (hs : s ∈ Icc 1 k) :
      (n + r) * (n + s) = (a r * a s) * (x r * x s) ^ l := by
    rw [hRepr r hr, hRepr s hs, mul_pow]
    ring
  have hFac (r s : ℕ) (hr : r ∈ Icc 1 k) (hs : s ∈ Icc 1 k) (p : ℕ) :
      ((n + r) * (n + s)).factorization p % l = (a r * a s).factorization p % l := by
    have hPos : (n + r) * (n + s) ≠ 0 := mul_ne_zero (by omega) (by omega)
    have hId := hReprPair r s hr hs
    rw [hId] at hPos ⊢
    have ha : a r * a s ≠ 0 := fun h => hPos (by rw [h, zero_mul])
    have hx : x r * x s ≠ 0 := fun h => hPos (by rw [h, zero_pow (by omega : l ≠ 0), mul_zero])
    exact factorization_mul_power_mod ha hx p
  apply pair_product_injective hnSquare hij huv hj hv
  apply scaled_power_eq_of_in_pair_interval hk hn hl (hBounds i j (hij.trans hj) hj)
    (hBounds u v (huv.trans hv) hv)
  intro p hp
  rw [hFac i j (mem_Icc.mpr ⟨hi, hij.trans hj⟩) (mem_Icc.mpr ⟨hi.trans hij, hj⟩),
    hFac u v (mem_Icc.mpr ⟨hu, huv.trans hv⟩) (mem_Icc.mpr ⟨hu.trans huv, hv⟩)]
  exact heq p hp

lemma coefficient_with_only_two {a : ℕ} (ha : a ≠ 0)
    (hSupport : ∀ p ∈ a.primeFactors, p < 3) : a = 2 ^ a.factorization 2 := by
  apply Nat.eq_of_factorization_eq ha (pow_ne_zero _ (by decide))
  intro p
  have ht : Nat.Prime 2 := by decide
  rw [ht.factorization_pow, Finsupp.single_apply]
  by_cases hTwo : p = 2
  · subst p
    simp
  · rw [if_neg (Ne.symm hTwo)]
    by_cases hP : p.Prime
    · apply Nat.factorization_eq_zero_of_not_dvd
      intro hDvd
      have hSmall := hSupport p (Nat.mem_primeFactors.mpr ⟨hP, hDvd, ha⟩)
      have hLarge := hP.two_le
      omega
    · exact Nat.factorization_eq_zero_of_not_prime _ hP

theorem three_odd_exponent_of_sylvester {n l : ℕ} (hl : 3 ≤ l)
    (hSylvester : ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ ∏ t ∈ Ioc n (n+3), t) :
    ∃ p : ℕ, 3 ≤ p ∧ p.Prime ∧ ¬ l ∣ (∏ t ∈ Ioc n (n+3), t).factorization p := by
  by_contra! hAll
  obtain ⟨hN, hTop⟩ := sylvester_schur_power_bounds_of_no_witness (by omega) hSylvester hAll
  obtain ⟨a, x, ha, hRepr, hSupport, hFac⟩ := normalize_odd_coefficients (by omega) hAll
  have hData (i : ℕ) (hi : i ∈ Icc 1 3) :
      a i = 2 ^ ((n+i).factorization 2 % l) := by
    have h := coefficient_with_only_two (ha i hi) (hSupport i hi)
    rw [hFac i hi 2] at h
    exact h
  have hOne (i : ℕ) (hi : i ∈ Icc 1 3) (hiOdd : ¬ 2 ∣ n+i) : a i = 1 := by
    rw [hData i hi, Nat.factorization_eq_zero_of_not_dvd hiOdd, Nat.zero_mod, pow_zero]
  have hTwo (i : ℕ) (hi : i ∈ Icc 1 3) (hiEven : 2 ∣ n+i) (hiNotFour : ¬ 4 ∣ n+i) :
      a i = 2 := by
    have hp : Nat.Prime 2 := by decide
    have hNZ : n+i ≠ 0 := by have := (mem_Icc.mp hi).1; omega
    have hLo := hp.factorization_pos_of_dvd hNZ hiEven
    have hHi : ¬ 2 ≤ (n+i).factorization 2 := by
      intro hGe
      exact hiNotFour ((hp.pow_dvd_iff_le_factorization hNZ).2 hGe)
    rw [hData i hi, show (n+i).factorization 2 = 1 by omega, Nat.mod_eq_of_lt (by omega), pow_one]
  have hSingle (i j : ℕ) (hi : i ∈ Icc 1 3) (hj : j ∈ Icc 1 3)
      (hEq : a i = a j) : i = j := by
    have h := distinct_multiset_products_mod_l (by decide : 0 < 3) hN (by omega) hTop hRepr
      ({i} : Multiset ℕ) ({j} : Multiset ℕ)
      (by intro r hr; simpa only [Multiset.mem_singleton.mp hr] using hi)
      (by intro r hr; simpa only [Multiset.mem_singleton.mp hr] using hj)
      (by simp) (by simpa only [Multiset.card_singleton] using (show 1 < l by omega))
      (by simp [hEq])
    simpa using h
  have hCollision (u v w : ℕ) (hu : u ∈ Icc 1 3) (hv : v ∈ Icc 1 3) (hw : w ∈ Icc 1 3)
      (hwu : w ≠ u) (hwv : w ≠ v) (hu1 : a u = 1) (hv2 : a v = 2) : False := by
    let e := (n+w).factorization 2 % l
    have he : e < l := Nat.mod_lt _ (by omega)
    have hw2 : a w = 2 ^ e := hData w hw
    by_cases he0 : e = 0
    · apply hwu (hSingle w u hw hu ?_)
      rw [hw2, he0, pow_zero, hu1]
    let S : Multiset ℕ := w ::ₘ Multiset.replicate (e-1) u
    let T : Multiset ℕ := Multiset.replicate e v
    have hCardS : S.card = e := by
      simp only [S, Multiset.card_cons, Multiset.card_replicate]
      omega
    have hCardT : T.card = e := Multiset.card_replicate _ _
    have hS (i : ℕ) (hi : i ∈ S) : i ∈ Icc 1 3 := by
      rcases Multiset.mem_cons.mp hi with rfl | h
      · exact hw
      · have heq := Multiset.eq_of_mem_replicate h
        simpa only [heq] using hu
    have hT (i : ℕ) (hi : i ∈ T) : i ∈ Icc 1 3 := by
      have heq := Multiset.eq_of_mem_replicate hi
      simpa only [heq] using hv
    have hPr : (S.map a).prod = (T.map a).prod := by
      simp [S, T, hu1, hv2, hw2]
    have hEq := distinct_multiset_products_mod_l (by decide : 0 < 3) hN (by omega) hTop hRepr
      S T hS hT (hCardS.trans hCardT.symm) (by rwa [hCardS]) (by intro p hp; rw [hPr])
    have hwT : w ∈ T := hEq ▸ Multiset.mem_cons_self _ _
    exact hwv (Multiset.eq_of_mem_replicate hwT)
  have h1 : 1 ∈ Icc (1 : ℕ) 3 := by decide
  have h2 : 2 ∈ Icc (1 : ℕ) 3 := by decide
  have h3 : 3 ∈ Icc (1 : ℕ) 3 := by decide
  rcases (show n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 by omega)
    with h0 | hM | hE | hM
  · have hEq := hSingle 1 3 h1 h3 ((hOne 1 h1 (by omega)).trans (hOne 3 h3 (by omega)).symm)
    omega
  · exact hCollision 2 1 3 h2 h1 h3 (by decide) (by decide)
      (hOne 2 h2 (by omega)) (hTwo 1 h1 (by omega) (by omega))
  · have hEq := hSingle 1 3 h1 h3 ((hOne 1 h1 (by omega)).trans (hOne 3 h3 (by omega)).symm)
    omega
  · exact hCollision 2 3 1 h2 h3 h1 (by decide) (by decide)
      (hOne 2 h2 (by omega)) (hTwo 3 h3 (by omega) (by omega))

lemma factorization_le_of_dvd_difference {p i j : ℕ} (hp : p.Prime)
    (hi : i ≠ 0) (hij : i < j) (hMax : i.factorization p ≤ j.factorization p) :
    i.factorization p ≤ (j - i).factorization p := by
  have hj : j ≠ 0 := by omega
  have hDiff : j - i ≠ 0 := by omega
  let e := i.factorization p
  have hLeft : p ^ e ∣ i := (hp.pow_dvd_iff_le_factorization hi).2 (by rfl)
  have hRight : p ^ e ∣ j := (hp.pow_dvd_iff_le_factorization hj).2 hMax
  exact (hp.pow_dvd_iff_le_factorization hDiff).1 (Nat.dvd_sub hRight hLeft)

lemma prod_Ioc_zero_eq_factorial (m : ℕ) : (∏ d ∈ Ioc 0 m, d) = m.factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hSet : Ioc 0 (m + 1) = insert (m + 1) (Ioc 0 m) := by
      ext d
      simp only [mem_Ioc, mem_insert]
      omega
    rw [hSet, Finset.prod_insert (by simp), ih, Nat.factorial_succ]

lemma interval_distances_dvd_factorial {n k m : ℕ} (hm : m ∈ Ioc n (n + k)) :
    (∏ t ∈ (Ioc n (n + k)).erase m, ((m - t) + (t - m))) ∣ (k - 1).factorial := by
  have hmB := mem_Ioc.mp hm
  have hSplit : (Ioc n (n + k)).erase m = Ioo n m ∪ Ioc m (n + k) := by
    ext t
    simp only [mem_erase, mem_Ioc, mem_Ioo, mem_union]
    omega
  have hDisj : Disjoint (Ioo n m) (Ioc m (n + k)) := by
    rw [Finset.disjoint_left]
    intro t hl hr
    exact (not_lt_of_ge (mem_Ioo.mp hl).2.le) (mem_Ioc.mp hr).1
  have hLeft : (∏ t ∈ Ioo n m, ((m-t)+(t-m))) = (m-n-1).factorial := by
    have hi : Set.InjOn (fun t : ℕ => m-t) ↑(Ioo n m) := by
      intro s hs t ht he
      have hS := mem_Ioo.mp hs
      have hT := mem_Ioo.mp ht
      change m-s = m-t at he
      omega
    have hImage : (Ioo n m).image (fun t => m-t) = Ioc 0 (m-n-1) := by
      ext d
      simp only [mem_image, mem_Ioo, mem_Ioc]
      constructor
      · rintro ⟨t, ht, rfl⟩
        omega
      · intro hd
        exact ⟨m-d, by omega, by omega⟩
    calc
      _ = ∏ t ∈ Ioo n m, (m-t) := by
        refine Finset.prod_congr rfl (fun t ht => ?_)
        have := (mem_Ioo.mp ht).2
        omega
      _ = ∏ d ∈ (Ioo n m).image (fun t => m-t), d := by rw [Finset.prod_image hi]
      _ = _ := by rw [hImage, prod_Ioc_zero_eq_factorial]
  have hRight : (∏ t ∈ Ioc m (n+k), ((m-t)+(t-m))) = (n+k-m).factorial := by
    have hi : Set.InjOn (fun t : ℕ => t-m) ↑(Ioc m (n+k)) := by
      intro s hs t ht he
      have hS := mem_Ioc.mp hs
      have hT := mem_Ioc.mp ht
      change s-m = t-m at he
      omega
    have hImage : (Ioc m (n+k)).image (fun t => t-m) = Ioc 0 (n+k-m) := by
      ext d
      simp only [mem_image, mem_Ioc]
      constructor
      · rintro ⟨t, ht, rfl⟩
        omega
      · intro hd
        exact ⟨m+d, by omega, by omega⟩
    calc
      _ = ∏ t ∈ Ioc m (n+k), (t-m) := by
        refine Finset.prod_congr rfl (fun t ht => ?_)
        have := (mem_Ioc.mp ht).1
        omega
      _ = ∏ d ∈ (Ioc m (n+k)).image (fun t => t-m), d := by rw [Finset.prod_image hi]
      _ = _ := by rw [hImage, prod_Ioc_zero_eq_factorial]
  rw [hSplit, Finset.prod_union hDisj, hLeft, hRight,
    show k-1 = (m-n-1)+(n+k-m) by omega]
  exact Nat.factorial_mul_factorial_dvd_factorial_add _ _

theorem restricted_prod_dvd_factorial :
  ∀ (n k : ℕ) (a : ℕ → ℕ), 0 < k →
    (∀ t ∈ Ioc n (n + k), a t ∣ t) →
    (∀ t ∈ Ioc n (n + k), ∀ p ∈ (a t).primeFactors, p < k) →
    ∃ s ⊆ Ioc n (n + k),
      k - ((range k).filter Nat.Prime).card ≤ s.card ∧
      (∏ t ∈ s, a t) ∣ (k - 1).factorial := by
  intro n k a hk hDvd hSupport
  let R := Ioc n (n+k)
  let P := (range k).filter Nat.Prime
  have hR : R.Nonempty := ⟨n+1, mem_Ioc.mpr ⟨by omega, by omega⟩⟩
  choose m hm hMax using fun p : ℕ =>
    Finset.exists_max_image R (fun t => t.factorization p) hR
  let removed := P.image m
  let S := R \ removed
  have hSub : S ⊆ R := Finset.sdiff_subset
  have hRemoved : removed ⊆ R := by
    intro t ht
    obtain ⟨p, _, rfl⟩ := mem_image.mp ht
    exact hm p
  have hCard : S.card + removed.card = k := by
    have h := Finset.card_sdiff_add_card_eq_card hRemoved
    change S.card + removed.card = R.card at h
    simpa [R] using h
  have hPrimeCard : removed.card ≤ P.card := Finset.card_image_le
  refine ⟨S, hSub, ?_, ?_⟩
  · change k - P.card ≤ S.card
    omega
  have hPos (t : ℕ) (ht : t ∈ R) : t ≠ 0 := by
    have h := (mem_Ioc.mp ht).1
    omega
  have hA (t : ℕ) (ht : t ∈ S) : a t ≠ 0 := by
    intro hz
    have hd := hDvd t (hSub ht)
    rw [hz] at hd
    exact hPos t (hSub ht) (Nat.eq_zero_of_zero_dvd hd)
  have hAProd : (∏ t ∈ S, a t) ≠ 0 := Finset.prod_ne_zero_iff.mpr hA
  apply (Nat.factorization_prime_le_iff_dvd hAProd (Nat.factorial_ne_zero _)).1
  intro p hp
  rw [Nat.factorization_prod hA, Finsupp.finsetSum_apply]
  by_cases hpK : p < k
  · have hpP : p ∈ P := mem_filter.mpr ⟨mem_range.mpr hpK, hp⟩
    have hSErase : S ⊆ R.erase (m p) := by
      intro t ht
      refine mem_erase.mpr ⟨?_, hSub ht⟩
      rintro rfl
      exact (mem_sdiff.mp ht).2 (mem_image.mpr ⟨p, hpP, rfl⟩)
    let d := fun t : ℕ => (m p-t)+(t-m p)
    have hD0 (t : ℕ) (ht : t ∈ R.erase (m p)) : d t ≠ 0 := by
      have hNe := (mem_erase.mp ht).1
      dsimp [d]
      omega
    have hDProd0 : (∏ t ∈ R.erase (m p), d t) ≠ 0 := Finset.prod_ne_zero_iff.mpr hD0
    have hProd : (∏ t ∈ R.erase (m p), d t) ∣ (k-1).factorial :=
      interval_distances_dvd_factorial (hm p)
    have hProdVal := (Nat.factorization_le_iff_dvd hDProd0 (Nat.factorial_ne_zero _)).2 hProd p
    rw [Nat.factorization_prod hD0, Finsupp.finsetSum_apply] at hProdVal
    calc
      _ ≤ ∑ t ∈ S, (d t).factorization p := by
        apply Finset.sum_le_sum
        intro t ht
        have htR := hSub ht
        have hCoeff := (Nat.factorization_le_iff_dvd (hA t ht) (hPos t htR)).2 (hDvd t htR) p
        have hM := hMax p t htR
        rcases lt_or_gt_of_ne (mem_erase.mp (hSErase ht)).1 with hlt | hgt
        · exact hCoeff.trans (by
            simpa only [d, Nat.sub_eq_zero_of_le hlt.le, Nat.add_zero] using
              factorization_le_of_dvd_difference hp (hPos t htR) hlt hM)
        · have hPower : p ^ t.factorization p ∣ t :=
            (hp.pow_dvd_iff_le_factorization (hPos t htR)).2 le_rfl
          have hPowerM : p ^ t.factorization p ∣ m p :=
            (hp.pow_dvd_iff_le_factorization (hPos _ (hm p))).2 hM
          have hDiff := (hp.pow_dvd_iff_le_factorization (show t-m p ≠ 0 by omega)).1
            (Nat.dvd_sub hPower hPowerM)
          exact hCoeff.trans (by
            simpa only [d, Nat.sub_eq_zero_of_le hgt.le, Nat.zero_add] using hDiff)
      _ ≤ ∑ t ∈ R.erase (m p), (d t).factorization p :=
        Finset.sum_le_sum_of_subset_of_nonneg hSErase (fun _ _ _ => Nat.zero_le _)
      _ ≤ _ := hProdVal
  · have hZ (t : ℕ) (ht : t ∈ S) : (a t).factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact hpK (hSupport t (hSub ht) p (Nat.mem_primeFactors.mpr ⟨hp, hd, hA t ht⟩))
    rw [Finset.sum_eq_zero hZ]
    exact Nat.zero_le _

lemma ordered_pair_eq_of_insert_eq {a b c d : ℕ} (hab : a < b) (hcd : c < d)
    (heq : ({a,b} : Finset ℕ) = {c,d}) : a = c ∧ b = d := by
  have ha : a = c ∨ a = d := by
    have hm : a ∈ ({c,d} : Finset ℕ) := heq ▸ (by simp : a ∈ ({a,b} : Finset ℕ))
    simpa only [mem_insert, mem_singleton] using hm
  have hb : b = c ∨ b = d := by
    have hm : b ∈ ({c,d} : Finset ℕ) := heq ▸ (by simp : b ∈ ({a,b} : Finset ℕ))
    simpa only [mem_insert, mem_singleton] using hm
  omega

-- Count one representative per left factor, then inject the other edges
-- into the unordered pairs of distinct right factors.
theorem factor_cover_card_of_distinct_products (S U V : Finset ℕ)
    (hCover : ∀ t ∈ S, ∃ u ∈ U, ∃ v ∈ V, t = u*v)
    (hSidon : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a*b = c*d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c)) :
    S.card ≤ U.card + V.card.choose 2 := by
  classical
  have hSelect : ∀ t : ℕ, ∃ w : ℕ × ℕ,
      t ∈ S → w.1 ∈ U ∧ w.2 ∈ V ∧ t = w.1*w.2 := by
    intro t
    by_cases ht : t ∈ S
    · obtain ⟨u, hu, v, hv, he⟩ := hCover t ht
      exact ⟨(u,v), fun _ => ⟨hu,hv,he⟩⟩
    · exact ⟨(0,0), fun h => (ht h).elim⟩
  choose f hf using hSelect
  let u := fun t : ℕ => (f t).1
  let v := fun t : ℕ => (f t).2
  have hAnchor : ∀ i : ℕ, ∃ r : ℕ, i ∈ S.image u →
      r ∈ S ∧ u r = i ∧ ∀ t ∈ S, u t = i → v r ≤ v t := by
    intro i
    by_cases hi : i ∈ S.image u
    · obtain ⟨t, ht, hti⟩ := mem_image.mp hi
      obtain ⟨r, hr, hMin⟩ := (S.filter (fun q => u q = i)).exists_min_image v
        ⟨t, mem_filter.mpr ⟨ht, hti⟩⟩
      exact ⟨r, fun _ => ⟨(mem_filter.mp hr).1, (mem_filter.mp hr).2,
        fun q hq hqi => hMin q (mem_filter.mpr ⟨hq, hqi⟩)⟩⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose anchor hanchor using hAnchor
  have hA (t : ℕ) (ht : t ∈ S) :
      anchor (u t) ∈ S ∧ u (anchor (u t)) = u t ∧ v (anchor (u t)) ≤ v t := by
    obtain ⟨h1,h2,h3⟩ := hanchor (u t) (mem_image_of_mem u ht)
    exact ⟨h1,h2,h3 t ht rfl⟩
  have hValue (t : ℕ) (ht : t ∈ S) : t = u t * v t := (hf t ht).2.2
  have hAValue (t : ℕ) (ht : t ∈ S) : anchor (u t) = u t * v (anchor (u t)) := by
    calc
      _ = u (anchor (u t)) * v (anchor (u t)) := hValue _ (hA t ht).1
      _ = _ := by rw [(hA t ht).2.1]
  let first := S.filter fun t => t = anchor (u t)
  let rest := S.filter fun t => t ≠ anchor (u t)
  have hFirst : first.card ≤ U.card := by
    apply Finset.card_le_card_of_injOn u
    · intro t ht
      exact (hf t (mem_filter.mp ht).1).1
    · intro a ha b hb h
      have ha' := (mem_filter.mp ha).2
      have hb' := (mem_filter.mp hb).2
      change u a = u b at h
      exact ha'.trans ((congrArg anchor h).trans hb'.symm)
  have hStrict (t : ℕ) (ht : t ∈ rest) : v (anchor (u t)) < v t := by
    obtain ⟨htS, htNe⟩ := mem_filter.mp ht
    apply lt_of_le_of_ne (hA t htS).2.2
    intro hv
    apply htNe
    exact (hValue t htS).trans ((congrArg (fun w => u t * w) hv.symm).trans (hAValue t htS).symm)
  let pair := fun t : ℕ => ({v (anchor (u t)), v t} : Finset ℕ)
  have hRest : rest.card ≤ (V.powersetCard 2).card := by
    apply Finset.card_le_card_of_injOn pair
    · intro t ht
      have htS := (mem_filter.mp ht).1
      apply mem_powersetCard.mpr
      change ({v (anchor (u t)), v t} : Finset ℕ) ⊆ V ∧
        ({v (anchor (u t)), v t} : Finset ℕ).card = 2
      refine ⟨?_, by simp [(hStrict t ht).ne]⟩
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (hf _ (hA t htS).1).2.1
      · exact (hf _ htS).2.1
    · intro a ha b hb he
      have haS := (mem_filter.mp ha).1
      have hbS := (mem_filter.mp hb).1
      have haNe := (mem_filter.mp ha).2
      have hKeys := ordered_pair_eq_of_insert_eq (hStrict a ha) (hStrict b hb) he
      have hCross : a * anchor (u b) = b * anchor (u a) := by
        calc
          _ = (u a*v a) * (u b*v (anchor (u b))) :=
            congrArg₂ (· * ·) (hValue a haS) (hAValue b hbS)
          _ = (u b*v b) * (u a*v (anchor (u a))) := by
            rw [hKeys.1, hKeys.2]
            ac_rfl
          _ = _ := (congrArg₂ (· * ·) (hValue b hbS) (hAValue a haS)).symm
      rcases hSidon a haS _ (hA b hbS).1 b hbS _ (hA a haS).1 hCross with h | h
      · exact h.1
      · exact (haNe h.1).elim
  have hCard : first.card + rest.card = S.card :=
    card_filter_add_card_filter_not (s := S) (fun t => t = anchor (u t))
  rw [Finset.card_powersetCard] at hRest
  exact hCard ▸ Nat.add_le_add hFirst hRest

theorem product_lower_bound_from_maxima (S : Finset ℕ) (lower : ℕ → ℕ)
    (hMax : ∀ T ⊆ S, ∀ z ∈ T, (∀ t ∈ T, t ≤ z) → lower T.card ≤ z) :
    (∏ i ∈ range S.card, lower (i+1)) ≤ ∏ s ∈ S, s := by
  generalize h : S.card = m
  induction m using Nat.strong_induction_on generalizing S with
  | h m ih =>
    by_cases hm : m = 0
    · have hEmpty : S = ∅ := Finset.card_eq_zero.mp (h.trans hm)
      simp [hEmpty, hm]
    · have hS : S.Nonempty := card_pos.mp (by omega)
      let z := S.max' hS
      have hz : z ∈ S := max'_mem _ _
      let T := S.erase z
      have hT : T.card = m - 1 := by simp [T, card_erase_of_mem hz, h]
      have hTail := ih (m-1) (by omega) T
        (fun U hUT x hx hxMax => hMax U (hUT.trans (erase_subset z S)) x hx hxMax) hT
      have hLast := hMax S (Subset.refl _) z hz (fun t ht => le_max' _ _ ht)
      rw [h] at hLast
      have hProd : (∏ s ∈ S, s) = z * ∏ s ∈ T, s := (Finset.mul_prod_erase S id hz).symm
      rw [hProd, show m = (m-1)+1 by omega, Finset.prod_range_succ]
      rw [show m-1+1 = m by omega]
      exact (Nat.mul_le_mul hTail hLast).trans_eq (Nat.mul_comm _ _)

theorem greedy_small_factor (B L t : ℕ) (hB : 1 ≤ B) (ht : 0 < t) :
    ∃ u v : ℕ, t = u*v ∧ 0 < u ∧ 0 < v ∧ v ≤ B ∧
      (∀ p ∈ v.primeFactors, p ≤ L) ∧
      (u = 1 ∨ L < u.minFac ∨
        (B < v*u.minFac ∧ ∀ p ∈ v.primeFactors, p ≤ u.minFac)) := by
  have hAux (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (hvB : v ≤ B)
      (hSupport : ∀ p ∈ v.primeFactors, p ≤ L)
      (hSorted : ∀ p ∈ v.primeFactors, u ≠ 1 → p ≤ u.minFac) :
      ∃ a b : ℕ, u*v = a*b ∧ 0 < a ∧ 0 < b ∧ b ≤ B ∧
        (∀ p ∈ b.primeFactors, p ≤ L) ∧
        (a = 1 ∨ L < a.minFac ∨
          (B < b*a.minFac ∧ ∀ p ∈ b.primeFactors, p ≤ a.minFac)) := by
    induction u using Nat.strong_induction_on generalizing v with
    | h u ih =>
      by_cases hu1 : u = 1
      · exact ⟨u,v,rfl,hu,hv,hvB,hSupport,Or.inl hu1⟩
      by_cases hpL : u.minFac ≤ L
      · by_cases hFit : v*u.minFac ≤ B
        · let p := u.minFac
          have hp : p.Prime := Nat.minFac_prime hu1
          let w := u/p
          have hd : p ∣ u := Nat.minFac_dvd u
          have hMul : p*w = u := Nat.mul_div_cancel' hd
          have hw : 0 < w := Nat.div_pos (Nat.le_of_dvd hu hd) hp.pos
          have hwlt : w < u := Nat.div_lt_self hu hp.one_lt
          have hDvd : w ∣ u := ⟨p, by rw [Nat.mul_comm,hMul]⟩
          have hNextSupport (q : ℕ) (hq : q ∈ (v*p).primeFactors) : q ≤ L := by
            rw [Nat.primeFactors_mul hv.ne' hp.ne_zero, hp.primeFactors] at hq
            rcases mem_union.mp hq with h | h
            · exact hSupport q h
            · simpa only [mem_singleton.mp h] using hpL
          have hNextSorted (q : ℕ) (hq : q ∈ (v*p).primeFactors) (hw1 : w ≠ 1) :
              q ≤ w.minFac := by
            have hLe : p ≤ w.minFac := Nat.minFac_le_of_dvd (Nat.minFac_prime hw1).two_le
              ((Nat.minFac_dvd w).trans hDvd)
            rw [Nat.primeFactors_mul hv.ne' hp.ne_zero, hp.primeFactors] at hq
            rcases mem_union.mp hq with h | h
            · exact (hSorted q h hu1).trans hLe
            · simpa only [mem_singleton.mp h] using hLe
          obtain ⟨a,b,hEq,hA,hB',hCap,hSupp,hEnd⟩ :=
            ih w hwlt (v*p) hw (Nat.mul_pos hv hp.pos) hFit hNextSupport hNextSorted
          refine ⟨a,b,?_,hA,hB',hCap,hSupp,hEnd⟩
          calc
            u*v = (p*w)*v := by rw [hMul]
            _ = w*(v*p) := by ac_rfl
            _ = a*b := hEq
        · exact ⟨u,v,rfl,hu,hv,hvB,hSupport,Or.inr (Or.inr
            ⟨lt_of_not_ge hFit, fun p hp => hSorted p hp hu1⟩)⟩
      · exact ⟨u,v,rfl,hu,hv,hvB,hSupport,Or.inr (Or.inl (lt_of_not_ge hpL))⟩
  simpa only [Nat.mul_one] using hAux t 1 ht (by decide) hB (by simp) (by simp)

def coprimePrefix (q x : ℕ) : Finset ℕ :=
  (Ioc 0 x).filter fun a => a.Coprime q

lemma coprime_prefix_period_step (q x : ℕ) :
    (coprimePrefix q (q+x)).card = (coprimePrefix q q).card + (coprimePrefix q x).card := by
  let A := coprimePrefix q q
  let B := (coprimePrefix q x).image (q+·)
  have hUnion : coprimePrefix q (q+x) = A ∪ B := by
    ext a
    simp only [A,B,coprimePrefix,mem_union,mem_image,mem_filter,mem_Ioc]
    constructor
    · rintro ⟨⟨ha,hax⟩,hCop⟩
      by_cases hq : a ≤ q
      · exact Or.inl ⟨⟨ha,hq⟩,hCop⟩
      · have he : q + (a-q) = a := by omega
        have h : (q+(a-q)).Coprime q := he.symm ▸ hCop
        exact Or.inr ⟨a-q,⟨⟨by omega,by omega⟩,Nat.coprime_self_add_left.mp h⟩,he⟩
    · rintro (⟨⟨ha,hq⟩,hCop⟩ | ⟨t,⟨⟨ht,hx⟩,hCop⟩,rfl⟩)
      · exact ⟨⟨ha,by omega⟩,hCop⟩
      · exact ⟨⟨by omega,by omega⟩,Nat.coprime_self_add_left.mpr hCop⟩
  have hDisjoint : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have hA := (mem_Ioc.mp (mem_filter.mp ha).1).2
    obtain ⟨t,ht,he⟩ := mem_image.mp hb
    have hT := (mem_Ioc.mp (mem_filter.mp ht).1).1
    change q+t = a at he
    omega
  have hB : B.card = (coprimePrefix q x).card :=
    card_image_of_injective _ (fun a b h => by change q+a=q+b at h; omega)
  rw [hUnion, card_union_of_disjoint hDisjoint, hB]

lemma coprime_prefix_periods (q b r : ℕ) :
    (coprimePrefix q (b*q+r)).card = b*(coprimePrefix q q).card + (coprimePrefix q r).card := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show b.succ*q+r = q+(b*q+r) by rw [Nat.succ_mul]; ac_rfl,
      coprime_prefix_period_step, ih, Nat.succ_mul]
    ac_rfl

theorem coprime_prefix_affine (q phi error x : ℕ) (hq : 0 < q)
    (hFull : (coprimePrefix q q).card = phi)
    (hRest : ∀ r : Fin q, q*(coprimePrefix q r.val).card ≤ phi*r.val+error) :
    q*(coprimePrefix q x).card ≤ phi*x+error := by
  have hId : (x/q)*q+x%q = x := by
    rw [Nat.mul_comm, Nat.add_comm]
    exact Nat.mod_add_div _ _
  have h := coprime_prefix_periods q (x/q) (x%q)
  rw [hId,hFull] at h
  have hr := hRest ⟨x%q,Nat.mod_lt _ hq⟩
  change q*(coprimePrefix q (x%q)).card ≤ phi*(x%q)+error at hr
  calc
    _ = q*((x/q)*phi) + q*(coprimePrefix q (x%q)).card := by rw [h, Nat.mul_add]
    _ ≤ q*((x/q)*phi) + (phi*(x%q)+error) := Nat.add_le_add_left hr _
    _ = phi*((x/q)*q+x%q)+error := by ring
    _ = _ := by rw [hId]

private lemma coprime_prefix_succ (q x : ℕ) :
    (coprimePrefix q (x+1)).card =
      (coprimePrefix q x).card + if (x+1).Coprime q then 1 else 0 := by
  have hI : Ioc (0:ℕ) (x+1) = insert (x+1) (Ioc 0 x) := by
    ext t
    simp only [mem_Ioc,mem_insert]
    omega
  unfold coprimePrefix
  rw [hI, Finset.filter_insert]
  by_cases h : (x+1).Coprime q
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem]
    simp
  · rw [if_neg h, if_neg h, Nat.add_zero]

private def wheelScan (q phi error : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | fuel+1, x, count => decide (q*count ≤ phi*x+error) &&
    wheelScan q phi error fuel (x+1) (count + if (x+1).Coprime q then 1 else 0)

private lemma wheel_scan_sound (q phi error fuel : ℕ) :
    ∀ x j : ℕ, x ≤ j → j < x+fuel →
    wheelScan q phi error fuel x (coprimePrefix q x).card = true →
    q*(coprimePrefix q j).card ≤ phi*j+error := by
  induction fuel with
  | zero => intro x j h₁ h₂; omega
  | succ fuel ih =>
    intro x j h₁ h₂ hCheck
    simp only [wheelScan, Bool.and_eq_true, decide_eq_true_eq] at hCheck
    by_cases h : j = x
    · subst j
      exact hCheck.1
    · apply ih (x+1) j (by omega) (by omega)
      rw [coprime_prefix_succ]
      exact hCheck.2

private structure FactorCoverRow where
  prime : ℕ
  minDiv : ℕ
  period : ℕ
  phi : ℕ
  error : ℕ
  deriving DecidableEq

private def rightFactors (B L : ℕ) : Finset ℕ :=
  (range (B+1)).filter fun t => 0 < t ∧
    ((List.range (B+1)).all fun p => decide (p ∣ t → p.Prime → p ≤ L)) = true

private def leftFactorsForRow (row : FactorCoverRow) (x : ℕ) : Finset ℕ :=
  (coprimePrefix row.period (x/(row.prime*row.minDiv))).image (row.prime*·)

private def rowValid (row : FactorCoverRow) : Prop :=
  0 < row.prime ∧ 0 < row.minDiv ∧ 0 < row.period ∧
    (coprimePrefix row.period row.period).card = row.phi ∧
    ∀ r : Fin row.period, row.period*(coprimePrefix row.period r.val).card ≤ row.phi*r.val+row.error

private def rowComputes (row : FactorCoverRow) : Prop :=
  0 < row.prime ∧ 0 < row.minDiv ∧ 0 < row.period ∧
    (coprimePrefix row.period row.period).card = row.phi ∧
    wheelScan row.period row.phi row.error row.period 0 0 = true

private instance (row : FactorCoverRow) : Decidable (rowComputes row) := by
  unfold rowComputes
  infer_instance

private lemma valid_of_computes (row : FactorCoverRow) (h : rowComputes row) : rowValid row := by
  obtain ⟨hp,hv,hq,hFull,hScan⟩ := h
  refine ⟨hp,hv,hq,hFull,?_⟩
  intro r
  apply wheel_scan_sound row.period row.phi row.error row.period 0 r.val (Nat.zero_le _)
    (by simpa using r.isLt)
  have hZero : (coprimePrefix row.period 0).card = 0 := by simp [coprimePrefix]
  rw [hZero]
  exact hScan

private def rowDensity (row : FactorCoverRow) : ℚ :=
  (row.phi : ℚ) / (row.period*row.prime*row.minDiv)

private def rowError (row : FactorCoverRow) : ℚ := (row.error : ℚ) / row.period

private lemma left_factor_mem {row : FactorCoverRow} {x u v : ℕ} (hRow : rowValid row)
    (hu : 0 < u) (hv : row.minDiv ≤ v) (hSize : u*v ≤ x) (hDvd : row.prime ∣ u)
    (hCoprime : (u/row.prime).Coprime row.period) : u ∈ leftFactorsForRow row x := by
  have hP : 0 < row.prime := hRow.1
  have hMin : 0 < row.minDiv := hRow.2.1
  have hLe : row.prime ≤ u := Nat.le_of_dvd hu hDvd
  have hMul := Nat.mul_div_cancel' hDvd
  have hQuot : u/row.prime ≤ x/(row.prime*row.minDiv) := by
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos hP hMin)).2
    calc
      _ = (row.prime*(u/row.prime))*row.minDiv := by ac_rfl
      _ = u*row.minDiv := by rw [hMul]
      _ ≤ u*v := Nat.mul_le_mul_left _ hv
      _ ≤ x := hSize
  exact mem_image.mpr ⟨u/row.prime,
    mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.div_pos hLe hP, hQuot⟩,hCoprime⟩, hMul⟩

private lemma left_factor_count (row : FactorCoverRow) (x : ℕ) (hRow : rowValid row) :
    ((leftFactorsForRow row x).card : ℚ) ≤ rowDensity row * x + rowError row := by
  obtain ⟨hp,hv,hq,hFull,hRest⟩ := hRow
  have hCard : (leftFactorsForRow row x).card =
      (coprimePrefix row.period (x/(row.prime*row.minDiv))).card := by
    unfold leftFactorsForRow
    exact card_image_of_injective _ (fun a b h => Nat.mul_left_cancel hp h)
  rw [hCard]
  let d := row.prime*row.minDiv
  have hd : 0 < d := Nat.mul_pos hp hv
  have hAff := coprime_prefix_affine row.period row.phi row.error (x/d) hq hFull hRest
  have hAffQ : (row.period : ℚ) * (coprimePrefix row.period (x/d)).card ≤
      (row.phi : ℚ)*(x/d : ℕ) + row.error := by exact_mod_cast hAff
  have hDiv : ((x/d : ℕ) : ℚ) ≤ (x : ℚ)/d := by
    apply (le_div_iff₀ (by exact_mod_cast hd : (0:ℚ)<d)).2
    exact_mod_cast Nat.div_mul_le_self x d
  have hBound := hAffQ.trans (add_le_add
    (mul_le_mul_of_nonneg_left hDiv (by positivity : 0 ≤ (row.phi : ℚ))) (le_refl (row.error : ℚ)))
  have ht : (row.phi : ℚ)*((x : ℚ)/d) + row.error =
      (rowDensity row*(x : ℚ) + rowError row) * row.period := by
    have hperiod : (row.period : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    have hprime : (row.prime : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
    have hmin : (row.minDiv : ℚ) ≠ 0 := by exact_mod_cast hv.ne'
    unfold rowDensity rowError
    dsimp [d]
    push_cast
    field_simp [hperiod, hprime, hmin]
    <;> ring
  rw [ht] at hBound
  have hPos : (0:ℚ) < row.period := by exact_mod_cast hq
  have hScaled : ((coprimePrefix row.period (x/d)).card : ℚ)*row.period ≤
      (rowDensity row*(x : ℚ) + rowError row) * row.period := by
    simpa only [mul_comm (row.period : ℚ)] using hBound
  exact le_of_mul_le_mul_right hScaled hPos

set_option maxHeartbeats 0 in
private lemma graph_density_from_rows (rows : Finset FactorCoverRow)
    (B L x A C E : ℕ) (S : Finset ℕ) (hB : 1 ≤ B) (hC : 0 < C)
    (hS : ∀ t ∈ S, 0 < t ∧ t ≤ x)
    (hSidon : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a*b = c*d →
      (a=c ∧ b=d) ∨ (a=d ∧ b=c))
    (hRows : ∀ row ∈ rows, rowValid row)
    (hBase : ∃ row ∈ rows, row.prime = 1 ∧ row.minDiv = 1 ∧
      ∀ p ∈ range (row.period+1), p ∣ row.period → p.Prime → p ≤ L)
    (hNext : ∀ p ∈ (range (L+1)).filter Nat.Prime, ∃ row ∈ rows, row.prime = p ∧
      (∀ q ∈ range (row.period+1), q ∣ row.period → q.Prime → q < p) ∧
      ∀ v ∈ Ioo (B/p) row.minDiv, ∃ q ∈ range (B+1), p < q ∧ q ∣ v ∧ q.Prime)
    (hDensity : (∑ row ∈ rows, rowDensity row) ≤ (A:ℚ)/C)
    (hError : ((rightFactors B L).card.choose 2 : ℚ) +
      (∑ row ∈ rows, rowError row) ≤ E) :
    C*S.card ≤ A*x+C*E := by
  let V := rightFactors B L
  let U := rows.biUnion (fun row => leftFactorsForRow row x)
  obtain ⟨base,hbRows,hbP,hbMin,hbFactors⟩ := hBase
  have hCover : ∀ t ∈ S, ∃ u ∈ U, ∃ v ∈ V, t = u*v := by
    intro t ht
    obtain ⟨u,v,he,hu,hv,hvB,hSupport,hEnd⟩ := greedy_small_factor B L t hB (hS t ht).1
    have hvV : v ∈ V := by
      change v ∈ rightFactors B L
      refine mem_filter.mpr ⟨mem_range.mpr (by omega),hv,List.all_eq_true.mpr ?_⟩
      intro p _
      exact decide_eq_true (fun hd hp => hSupport p (Nat.mem_primeFactors.mpr ⟨hp,hd,hv.ne'⟩))
    have hSize : u*v ≤ x := he ▸ (hS t ht).2
    refine ⟨u, ?_, v,hvV,he⟩
    rcases hEnd with hu1 | hLarge | ⟨hOver,hSorted⟩
    · have hCop : (u/base.prime).Coprime base.period := by simp [hu1,hbP]
      exact mem_biUnion.mpr ⟨base,hbRows,left_factor_mem (hRows base hbRows) hu
        (by omega) hSize (by simp [hbP]) hCop⟩
    · have hCop : (u/base.prime).Coprime base.period := by
        rw [hbP,Nat.div_one]
        apply Nat.Coprime.symm
        apply Nat.coprime_of_dvd
        intro p hp hd huD
        have hBound := Nat.le_of_dvd (hRows base hbRows).2.2.1 hd
        have hP := hbFactors p (mem_range.mpr (by omega)) hd hp
        have hMin := Nat.minFac_le_of_dvd hp.two_le huD
        omega
      exact mem_biUnion.mpr ⟨base,hbRows,left_factor_mem (hRows base hbRows) hu
        (by omega) hSize (by simp [hbP]) hCop⟩
    · by_cases hu1 : u = 1
      · have hCop : (u/base.prime).Coprime base.period := by simp [hu1,hbP]
        exact mem_biUnion.mpr ⟨base,hbRows,left_factor_mem (hRows base hbRows) hu
          (by omega) hSize (by simp [hbP]) hCop⟩
      · let p := u.minFac
        have hp : p.Prime := Nat.minFac_prime hu1
        by_cases hPL : L < p
        · have hCop : (u/base.prime).Coprime base.period := by
            rw [hbP,Nat.div_one]
            apply Nat.Coprime.symm
            apply Nat.coprime_of_dvd
            intro r hr hd huD
            have hBound := Nat.le_of_dvd (hRows base hbRows).2.2.1 hd
            have hP := hbFactors r (mem_range.mpr (by omega)) hd hr
            have hMin : p ≤ r := Nat.minFac_le_of_dvd hr.two_le huD
            omega
          exact mem_biUnion.mpr ⟨base,hbRows,left_factor_mem (hRows base hbRows) hu
            (by omega) hSize (by simp [hbP]) hCop⟩
        · obtain ⟨row,hrRows,hrP,hrFactors,hrMin⟩ := hNext p
            (mem_filter.mpr ⟨mem_range.mpr (by omega),hp⟩)
          have hPDvd : row.prime ∣ u := by rw [hrP]; exact Nat.minFac_dvd u
          have hCop : (u/row.prime).Coprime row.period := by
            apply Nat.Coprime.symm
            apply Nat.coprime_of_dvd
            intro r hr hd hrU
            have hBound := Nat.le_of_dvd (hRows row hrRows).2.2.1 hd
            have hP := hrFactors r (mem_range.mpr (by omega)) hd hr
            have hMin : p ≤ r := Nat.minFac_le_of_dvd hr.two_le (hrU.trans (Nat.div_dvd_of_dvd hPDvd))
            omega
          have hVMin : row.minDiv ≤ v := by
            by_contra! hVSmall
            have hVDiv : B/p < v := (Nat.div_lt_iff_lt_mul hp.pos).2 hOver
            obtain ⟨q,_,hQ,hd,hpQ⟩ := hrMin v (mem_Ioo.mpr ⟨hVDiv,hVSmall⟩)
            have hQ' := hSorted q (Nat.mem_primeFactors.mpr ⟨hpQ,hd,hv.ne'⟩)
            omega
          exact mem_biUnion.mpr ⟨row,hrRows,left_factor_mem (hRows row hrRows) hu hVMin
            hSize hPDvd hCop⟩
  have hGraph := factor_cover_card_of_distinct_products S U V hCover hSidon
  have hCards : U.card ≤ ∑ row ∈ rows, (leftFactorsForRow row x).card := card_biUnion_le
  have hCombined : (S.card : ℚ) ≤
      (∑ row ∈ rows, rowDensity row)*x + ((V.card.choose 2 : ℚ) + ∑ row ∈ rows, rowError row) := by
    calc
      _ ≤ (U.card : ℚ)+V.card.choose 2 := by exact_mod_cast hGraph
      _ ≤ (∑ row ∈ rows, ((leftFactorsForRow row x).card : ℚ)) + V.card.choose 2 := by
        exact_mod_cast Nat.add_le_add_right hCards (V.card.choose 2)
      _ ≤ (∑ row ∈ rows, (rowDensity row*x+rowError row))+V.card.choose 2 :=
        add_le_add (sum_le_sum (fun row hrow => left_factor_count row x (hRows row hrow))) le_rfl
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_mul]; ac_rfl
  have hAll := hCombined.trans (add_le_add
    (mul_le_mul_of_nonneg_right hDensity (by positivity : 0 ≤ (x:ℚ))) hError)
  have hCQ : (0:ℚ) < C := by exact_mod_cast hC
  have hMul := mul_le_mul_of_nonneg_left hAll hCQ.le
  have hId : (C:ℚ)*((A:ℚ)/C*x+E) = (A:ℚ)*x+(C:ℚ)*E := by
    field_simp [hCQ.ne']
  rw [hId] at hMul
  exact_mod_cast hMul

private def rows36 : Finset FactorCoverRow :=
  {⟨1,1,210,48,318⟩,⟨2,32,1,1,0⟩,⟨3,16,2,1,1⟩,⟨5,8,6,2,4⟩,⟨7,6,30,8,28⟩}

private def rows100 : Finset FactorCoverRow :=
  {⟨1,1,2310,480,5820⟩,⟨2,64,1,1,0⟩,⟨3,36,2,1,1⟩,⟨5,24,6,2,4⟩,⟨7,15,30,8,28⟩,
    ⟨11,10,210,48,318⟩}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma rows36_valid : ∀ row ∈ rows36, rowValid row := by
  have h : ∀ row ∈ rows36, rowComputes row := by decide
  exact fun row hr => valid_of_computes row (h row hr)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma rows100_valid : ∀ row ∈ rows100, rowValid row := by
  have h : ∀ row ∈ rows100, rowComputes row := by decide
  exact fun row hr => valid_of_computes row (h row hr)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem distinct_products_rank_bounds (S : Finset ℕ) (x : ℕ)
    (hS : ∀ t ∈ S, 0 < t ∧ t ≤ x)
    (hSidon : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a*b = c*d →
      (a=c ∧ b=d) ∨ (a=d ∧ b=c)) :
    1260*S.card ≤ 353*x+1260*304 ∧ 21701*S.card ≤ 5000*x+21701*1492 := by
  have h36V : (rightFactors 36 7).card = 25 := by decide
  have h100V : (rightFactors 100 11).card = 55 := by decide
  have h36Density : (∑ row ∈ rows36, rowDensity row) ≤ (353:ℚ)/1260 := by
    norm_num [rows36, rowDensity, Finset.sum_insert]
  have h100Density : (∑ row ∈ rows100, rowDensity row) ≤ (5000:ℚ)/21701 := by
    norm_num [rows100, rowDensity, Finset.sum_insert]
  have h36Error : ((rightFactors 36 7).card.choose 2 : ℚ) +
      (∑ row ∈ rows36, rowError row) ≤ 304 := by
    rw [h36V]
    norm_num [rows36, rowError, Finset.sum_insert, show (25:ℕ).choose 2 = 300 by decide]
  have h100Error : ((rightFactors 100 11).card.choose 2 : ℚ) +
      (∑ row ∈ rows100, rowError row) ≤ 1492 := by
    rw [h100V]
    norm_num [rows100, rowError, Finset.sum_insert, show (55:ℕ).choose 2 = 1485 by decide]
  exact ⟨graph_density_from_rows rows36 36 7 x 353 1260 304 S (by decide) (by decide)
      hS hSidon rows36_valid (by decide) (by decide) h36Density h36Error,
    graph_density_from_rows rows100 100 11 x 5000 21701 1492 S (by decide) (by decide)
      hS hSidon rows100_valid (by decide) (by decide) h100Density h100Error⟩

def coefficientRankLower (i : ℕ) : ℕ :=
  max i (max ((1260*(i-304)+352)/353) ((21701*(i-1492)+4999)/5000))

theorem distinct_products_product_lower (S : Finset ℕ)
    (hPos : 0 ∉ S)
    (hSidon : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a*b = c*d →
      (a=c ∧ b=d) ∨ (a=d ∧ b=c)) :
    (∏ i ∈ range S.card, coefficientRankLower (i+1)) ≤ ∏ t ∈ S, t := by
  apply product_lower_bound_from_maxima S coefficientRankLower
  intro T hT z hz hZ
  have hData : ∀ t ∈ T, 0 < t ∧ t ≤ z := by
    intro t ht
    exact ⟨Nat.pos_of_ne_zero (fun h => hPos (h ▸ hT ht)),hZ t ht⟩
  have hRank := distinct_products_rank_bounds T z hData
    (fun a ha b hb c hc d hd h => hSidon a (hT ha) b (hT hb) c (hT hc) d (hT hd) h)
  have hTrivial : T.card ≤ z :=
    (card_le_card (show T ⊆ Ioc 0 z from fun t ht => mem_Ioc.mpr (hData t ht))).trans
      (by simp)
  have hFirst := hRank.1
  have hSecond := hRank.2
  unfold coefficientRankLower
  exact max_le hTrivial (max_le (by omega) (by omega))

theorem odd_branch_of_coefficient_product_bound {n k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l)
    (hSylvester : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ t ∈ Ioc n (n+k), t)
    (hLower : ∀ A : Finset ℕ, 0 ∉ A → k - ((range k).filter Nat.Prime).card ≤ A.card →
      (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a*b = c*d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
      (k-1).factorial < ∏ t ∈ A, t) :
    ∃ p : ℕ, k ≤ p ∧ p.Prime ∧ ¬ l ∣ (∏ t ∈ Ioc n (n+k), t).factorization p := by
  by_contra! hAll
  obtain ⟨hN,hTop⟩ := sylvester_schur_power_bounds_of_no_witness (by omega) hSylvester hAll
  obtain ⟨a,x,ha,hRepr,hSupport,_⟩ := normalize_odd_coefficients (by omega) hAll
  let R := Ioc n (n+k)
  let b := fun t : ℕ => a (t-n)
  have hIndex (t : ℕ) (ht : t ∈ R) : t-n ∈ Icc 1 k := by
    have h := mem_Ioc.mp ht
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hDvd (t : ℕ) (ht : t ∈ R) : b t ∣ t := by
    have h := mem_Ioc.mp ht
    have heq := hRepr (t-n) (hIndex t ht)
    rw [Nat.add_sub_of_le h.1.le] at heq
    exact ⟨x (t-n)^l, heq⟩
  obtain ⟨S,hS,hCount,hProduct⟩ := restricted_prod_dvd_factorial n k b (by omega)
    hDvd (fun t ht => hSupport (t-n) (hIndex t ht))
  have hPairs {i j u v : ℕ} (hi : i ∈ Icc 1 k) (hj : j ∈ Icc 1 k)
      (hu : u ∈ Icc 1 k) (hv : v ∈ Icc 1 k) (heq : a i*a j = a u*a v) :
      (i=u ∧ j=v) ∨ (i=v ∧ j=u) := by
    let A : Multiset ℕ := i ::ₘ {j}
    let B : Multiset ℕ := u ::ₘ {v}
    have hA : ∀ t ∈ A, t ∈ Icc 1 k := by
      intro t ht
      simp only [A, Multiset.mem_cons, Multiset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hi
      · exact hj
    have hB : ∀ t ∈ B, t ∈ Icc 1 k := by
      intro t ht
      simp only [B, Multiset.mem_cons, Multiset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hu
      · exact hv
    have hAB := distinct_multiset_products_mod_l (by omega) hN (by omega) hTop hRepr
      A B hA hB (by simp [A,B]) (by simpa [A] using (show 2 < l by omega))
      (by intro p hp; simp only [A,B,Multiset.map_cons,Multiset.prod_cons,
        Multiset.map_singleton,Multiset.prod_singleton]; rw [heq])
    have hiB : i ∈ B := hAB ▸ (Multiset.mem_cons_self _ _ : i ∈ A)
    have hSum := congrArg Multiset.sum hAB
    simp [A,B] at hSum
    have hiUV : i = u ∨ i = v := by simpa [B] using hiB
    omega
  have hPairsBlock (i j u v : ℕ) (hi : i ∈ S) (hj : j ∈ S) (hu : u ∈ S) (hv : v ∈ S)
      (heq : b i*b j = b u*b v) :
      (i=u ∧ j=v) ∨ (i=v ∧ j=u) := by
    have hI := (mem_Ioc.mp (hS hi)).1
    have hJ := (mem_Ioc.mp (hS hj)).1
    have hU := (mem_Ioc.mp (hS hu)).1
    have hV := (mem_Ioc.mp (hS hv)).1
    have h := hPairs (hIndex i (hS hi)) (hIndex j (hS hj))
      (hIndex u (hS hu)) (hIndex v (hS hv)) heq
    omega
  have hInj : Set.InjOn b ↑S := by
    intro i hi j hj heq
    have h := hPairsBlock i i j j hi hi hj hj (congrArg (fun d : ℕ => d*d) heq)
    omega
  have hZero : 0 ∉ S.image b := by
    intro h
    obtain ⟨i,hi,he⟩ := mem_image.mp h
    exact ha (i-n) (hIndex i (hS hi)) he
  have hCountImage : k - ((range k).filter Nat.Prime).card ≤ (S.image b).card := by
    rw [Finset.card_image_of_injOn hInj]
    exact hCount
  have hSidon : ∀ a ∈ S.image b, ∀ b' ∈ S.image b, ∀ c ∈ S.image b, ∀ d ∈ S.image b,
      a*b' = c*d → (a=c ∧ b'=d) ∨ (a=d ∧ b'=c) := by
    intro a ha' b' hb c hc d hd heq
    obtain ⟨i,hi,rfl⟩ := mem_image.mp ha'
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hb
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hc
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hd
    rcases hPairsBlock i j u v hi hj hu hv heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩
  have hLarge := hLower (S.image b) hZero hCountImage hSidon
  rw [Finset.prod_image hInj] at hLarge
  exact (not_lt_of_ge (Nat.le_of_dvd (Nat.factorial_pos _) hProduct)) hLarge

def rankProductCertificate (k : ℕ) : Prop :=
  (k-1).factorial <
    ∏ i ∈ range (k-((range k).filter Nat.Prime).card), coefficientRankLower (i+1)

theorem odd_branch_from_rank_certificate {n k l : ℕ}
    (hk : 3 ≤ k) (hl : 3 ≤ l)
    (hSylvester : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ t ∈ Ioc n (n+k), t)
    (hNumeric : rankProductCertificate k) :
    ∃ p : ℕ, k ≤ p ∧ p.Prime ∧ ¬ l ∣ (∏ t ∈ Ioc n (n+k), t).factorization p := by
  apply odd_branch_of_coefficient_product_bound hk hl hSylvester
  intro S hPos hCard hSidon
  have hMono := Finset.prod_le_prod_of_subset_of_one_le' (Finset.range_mono hCard)
    (f := fun i => coefficientRankLower (i+1)) (by
      intro i _ _
      exact (Nat.succ_pos i).trans_le (le_max_left _ _))
  exact hNumeric.trans_le (hMono.trans (distinct_products_product_lower S hPos hSidon))

end Erdos137PerfectPower

namespace Erdos137PerfectPower

open Finset

theorem ratio_residue_code_bound {n k l : ℕ} {a x : ℕ → ℕ} (S : Finset ℕ)
    {Code : Type} [Fintype Code] (code : ℕ × ℕ → Code)
    (hk : 0 < k) (hn : k^l < n) (hl : 3 ≤ l) (hTop : (k+1)^l ≤ n+k)
    (hRepr : ∀ i ∈ Icc 1 k, n+i = a i * x i ^ l)
    (hS : S ⊆ Icc 1 k) (ha : ∀ i ∈ S, a i ≠ 0)
    (hCode : ∀ r ∈ S.offDiag, ∀ s ∈ S.offDiag, code r = code s →
      ∀ p : ℕ, p.Prime →
      ((a r.1).factorization p : ZMod l) - (a r.2).factorization p =
      ((a s.1).factorization p : ZMod l) - (a s.2).factorization p) :
    S.card * (S.card - 1) ≤ Fintype.card Code := by
  classical
  have hInj : Set.InjOn code ↑S.offDiag := by
    rintro ⟨i,j⟩ hij ⟨u,v⟩ huv hEq
    obtain ⟨hi,hj,hijNe⟩ := mem_offDiag.mp hij
    obtain ⟨hu,hv,huvNe⟩ := mem_offDiag.mp huv
    have hMod (p : ℕ) (hp : p.Prime) :
        (a i * a v).factorization p % l = (a u * a j).factorization p % l := by
      rw [Nat.factorization_mul (ha i hi) (ha v hv), Nat.factorization_mul (ha u hu) (ha j hj),
        Finsupp.add_apply, Finsupp.add_apply]
      have hAdd := sub_eq_sub_iff_add_eq_add.mp (hCode _ hij _ huv hEq p hp)
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa only [Nat.cast_add] using hAdd)
    let A : Multiset ℕ := i ::ₘ {v}
    let B : Multiset ℕ := u ::ₘ {j}
    have hA : ∀ t ∈ A, t ∈ Icc 1 k := by
      intro t ht
      simp only [A, Multiset.mem_cons, Multiset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hS hi
      · exact hS hv
    have hB : ∀ t ∈ B, t ∈ Icc 1 k := by
      intro t ht
      simp only [B, Multiset.mem_cons, Multiset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hS hu
      · exact hS hj
    have hAB := distinct_multiset_products_mod_l hk hn (by omega) hTop hRepr
      A B hA hB (by simp [A,B]) (by simpa [A] using (show 2 < l by omega))
      (by intro p hp; simpa [A,B] using hMod p hp)
    have hiB : i ∈ B := hAB ▸ (Multiset.mem_cons_self _ _ : i ∈ A)
    have hiU : i = u := (show i = u ∨ i = j by simpa [B] using hiB).resolve_right hijNe
    have hSum := congrArg Multiset.sum hAB
    simp [A,B] at hSum
    exact Prod.ext hiU (by omega)
  have hCard : S.offDiag.card ≤ Fintype.card Code := by
    have := Finset.card_le_card_of_injOn code
      (fun (r : ℕ × ℕ) (_ : r ∈ S.offDiag) => mem_univ (code r)) hInj
    simpa using this
  simpa [Finset.offDiag_card, Nat.mul_sub_left_distrib, pow_two, Nat.mul_comm] using hCard

theorem ratio_residue_bound {n k l : ℕ} {a x : ℕ → ℕ} (S P : Finset ℕ)
    (hk : 0 < k) (hn : k^l < n) (hl : 3 ≤ l) (hTop : (k+1)^l ≤ n+k)
    (hRepr : ∀ i ∈ Icc 1 k, n+i = a i * x i ^ l)
    (hS : S ⊆ Icc 1 k) (ha : ∀ i ∈ S, a i ≠ 0)
    (hSupport : ∀ i ∈ S, (a i).primeFactors ⊆ P) :
    S.card * (S.card - 1) ≤ l ^ P.card := by
  classical
  letI : NeZero l := ⟨by omega⟩
  let ratio := fun r : ℕ × ℕ => fun p : P =>
    ((a r.1).factorization p : ZMod l) - (a r.2).factorization p
  have hZero (i : ℕ) (hi : i ∈ S) (p : ℕ) (hp : p.Prime) (hpP : p ∉ P) :
      (a i).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun hd => hpP (hSupport i hi
      (Nat.mem_primeFactors.mpr ⟨hp, hd, ha i hi⟩)))
  have hBound := ratio_residue_code_bound S ratio hk hn hl hTop hRepr hS ha (by
    intro r hr s hs heq p hp
    by_cases hP : p ∈ P
    · exact congrFun heq ⟨p,hP⟩
    · rcases mem_offDiag.mp hr with ⟨hr₁,hr₂,_⟩
      rcases mem_offDiag.mp hs with ⟨hs₁,hs₂,_⟩
      simp [hZero _ hr₁ p hp hP, hZero _ hr₂ p hp hP, hZero _ hs₁ p hp hP, hZero _ hs₂ p hp hP])
  simpa [Fintype.card_fun, Fintype.card_coe, ZMod.card] using hBound

def optionalPrimeVal (p : ℕ) {Q : Finset ℕ} (tag : Option Q) : ℕ :=
  match tag with
  | none => 0
  | some q => if q.val = p then 1 else 0

theorem tagged_ratio_residue_bound {n k l : ℕ} {a x : ℕ → ℕ} (S P Q : Finset ℕ)
    (hk : 0 < k) (hn : k^l < n) (hl : 3 ≤ l) (hTop : (k+1)^l ≤ n+k)
    (hRepr : ∀ i ∈ Icc 1 k, n+i = a i * x i ^ l)
    (hS : S ⊆ Icc 1 k) (ha : ∀ i ∈ S, a i ≠ 0) (tag : ℕ → Option Q)
    (hTag : ∀ i ∈ S, ∀ p : ℕ, p.Prime → p ∉ P →
      (a i).factorization p = optionalPrimeVal p (tag i)) :
    S.card * (S.card - 1) ≤ l ^ P.card * (Q.card+1)^2 := by
  classical
  letI : NeZero l := ⟨by omega⟩
  let encode := fun r : ℕ × ℕ =>
    ((fun p : P => ((a r.1).factorization p : ZMod l) - (a r.2).factorization p),
      (tag r.1, tag r.2))
  have hBound := ratio_residue_code_bound S encode hk hn hl hTop hRepr hS ha (by
    intro r hr s hs heq p hp
    by_cases hP : p ∈ P
    · exact congrFun (congrArg Prod.fst heq) ⟨p,hP⟩
    · rcases mem_offDiag.mp hr with ⟨hr₁,hr₂,_⟩
      rcases mem_offDiag.mp hs with ⟨hs₁,hs₂,_⟩
      have h₁ : tag r.1 = tag s.1 := congrArg (fun t => t.2.1) heq
      have h₂ : tag r.2 = tag s.2 := congrArg (fun t => t.2.2) heq
      rw [hTag _ hr₁ p hp hP, hTag _ hr₂ p hp hP, hTag _ hs₁ p hp hP,
        hTag _ hs₂ p hp hP, h₁, h₂])
  simpa [Fintype.card_prod, Fintype.card_fun, Fintype.card_option, Fintype.card_coe, ZMod.card,
    pow_two] using hBound

lemma multiset_prod_factorization (s : Multiset ℕ) (p : ℕ)
    (hs : ∀ a ∈ s, a ≠ 0) :
    s.prod.factorization p = (s.map (fun a => a.factorization p)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have hA := hs a (Multiset.mem_cons_self _ _)
    have hS : ∀ b ∈ s, b ≠ 0 := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    have hProd : s.prod ≠ 0 := by
      have h := Multiset.one_le_prod_of_one_le (fun b hb => Nat.pos_of_ne_zero (hS b hb))
      omega
    rw [Multiset.prod_cons, Nat.factorization_mul hA hProd, Finsupp.add_apply, ih hS,
      Multiset.map_cons, Multiset.sum_cons]

theorem multiset_residue_code_bound {n k l d : ℕ} {a x : ℕ → ℕ} (S : Finset ℕ)
    {Code : Type} [Fintype Code] (code : Sym S d → Code)
    (hk : 0 < k) (hn : k^l < n) (hl : 2 ≤ l) (hTop : (k+1)^l ≤ n+k) (hd : d < l)
    (hRepr : ∀ i ∈ Icc 1 k, n+i = a i * x i ^ l)
    (hS : S ⊆ Icc 1 k)
    (hCode : ∀ s t : Sym S d, code s = code t → ∀ p : ℕ, p.Prime →
      (s.val.map (fun i : S => a i.val)).prod.factorization p % l =
      (t.val.map (fun i : S => a i.val)).prod.factorization p % l) :
    (S.card+d-1).choose d ≤ Fintype.card Code := by
  classical
  have hActual (s : Sym S d) (i : ℕ) (hi : i ∈ s.val.map Subtype.val) : i ∈ Icc 1 k := by
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hi
    exact hS j.property
  have hInj : Function.Injective code := by
    intro s t h
    have hs : (s.val.map Subtype.val).card = d := (Multiset.card_map _ _).trans s.property
    have ht : (t.val.map Subtype.val).card = d := (Multiset.card_map _ _).trans t.property
    apply Subtype.ext
    apply Multiset.map_injective (f := Subtype.val) Subtype.val_injective
    apply distinct_multiset_products_mod_l hk hn hl hTop hRepr _ _
      (hActual s) (hActual t) (hs.trans ht.symm) (by rwa [hs])
    intro p hp
    simpa only [Multiset.map_map, Function.comp_def] using hCode s t h p hp
  have hCard := Fintype.card_le_of_injective code hInj
  simpa [Sym.card_sym_eq_choose, Fintype.card_coe] using hCard

theorem smooth_multiset_residue_bound {n k l d : ℕ} {a x : ℕ → ℕ} (S P : Finset ℕ)
    (hk : 0 < k) (hn : k^l < n) (hl : 2 ≤ l) (hTop : (k+1)^l ≤ n+k) (hd : d < l)
    (hRepr : ∀ i ∈ Icc 1 k, n+i = a i * x i ^ l)
    (hS : S ⊆ Icc 1 k) (ha : ∀ i ∈ S, a i ≠ 0)
    (hSupport : ∀ i ∈ S, (a i).primeFactors ⊆ P) :
    (S.card+d-1).choose d ≤ l ^ P.card := by
  classical
  letI : NeZero l := ⟨by omega⟩
  let coeff := fun i : S => a i.val
  let residue := fun s : Sym S d => fun p : P =>
    ((s.val.map coeff).prod.factorization p : ZMod l)
  have hFacZero (s : Sym S d) (p : ℕ) (hp : p.Prime) (hpP : p ∉ P) :
      (s.val.map coeff).prod.factorization p = 0 := by
    rw [multiset_prod_factorization _ p]
    · apply Multiset.sum_eq_zero
      intro e he
      obtain ⟨t,ht,rfl⟩ := Multiset.mem_map.mp he
      obtain ⟨i,_,rfl⟩ := Multiset.mem_map.mp ht
      exact Nat.factorization_eq_zero_of_not_dvd (fun hd => hpP (hSupport i.val i.property
        (Nat.mem_primeFactors.mpr ⟨hp, hd, ha i.val i.property⟩)))
    · intro t ht
      obtain ⟨i,_,rfl⟩ := Multiset.mem_map.mp ht
      exact ha i.val i.property
  have hCard := multiset_residue_code_bound S residue hk hn hl hTop hd hRepr hS (by
    intro s t h p hp
    change (s.val.map coeff).prod.factorization p % l =
      (t.val.map coeff).prod.factorization p % l
    by_cases hpP : p ∈ P
    · exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (congrFun h ⟨p,hpP⟩)
    · rw [hFacZero s p hp hpP, hFacZero t p hp hpP])
  simpa [Fintype.card_fun, Fintype.card_coe, ZMod.card] using hCard

theorem tagged_multiset_residue_bound {n k l d : ℕ} {a x : ℕ → ℕ} (S P Q : Finset ℕ)
    (hk : 0 < k) (hn : k^l < n) (hl : 2 ≤ l) (hTop : (k+1)^l ≤ n+k) (hd : d < l)
    (hRepr : ∀ i ∈ Icc 1 k, n+i = a i * x i ^ l)
    (hS : S ⊆ Icc 1 k) (ha : ∀ i ∈ S, a i ≠ 0) (tag : ℕ → Option Q)
    (hTag : ∀ i ∈ S, ∀ p : ℕ, p.Prime → p ∉ P →
      (a i).factorization p = optionalPrimeVal p (tag i)) :
    (S.card+d-1).choose d ≤ l ^ P.card * (Q.card+d).choose d := by
  classical
  letI : NeZero l := ⟨by omega⟩
  let coeff := fun i : S => a i.val
  let tagged := fun i : S => tag i.val
  let collect := fun s : Sym S d => (⟨s.val.map tagged, by simpa using s.property⟩ : Sym (Option Q) d)
  let code : Sym S d → ((P → ZMod l) × Sym (Option Q) d) := fun s =>
    ((fun p : P => ((s.val.map coeff).prod.factorization p : ZMod l)), collect s)
  have hFac (s : Sym S d) (p : ℕ) (hp : p.Prime) (hpP : p ∉ P) :
      (s.val.map coeff).prod.factorization p = ((collect s).val.map (optionalPrimeVal p)).sum := by
    rw [multiset_prod_factorization _ p]
    · have he : ((s.val.map coeff).map (fun a => a.factorization p)) =
          ((s.val.map tagged).map (optionalPrimeVal p)) := by
        simp only [Multiset.map_map]
        apply Multiset.map_congr rfl
        intro i hi
        exact hTag i.val i.property p hp hpP
      exact congrArg Multiset.sum he
    · intro b hb
      obtain ⟨i,_,rfl⟩ := Multiset.mem_map.mp hb
      exact ha i.val i.property
  have hCard := multiset_residue_code_bound S code hk hn hl hTop hd hRepr hS (by
    intro s t h p hp
    change (s.val.map coeff).prod.factorization p % l =
      (t.val.map coeff).prod.factorization p % l
    by_cases hpP : p ∈ P
    · exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (congrFun (congrArg Prod.fst h) ⟨p,hpP⟩)
    · have he : collect s = collect t := congrArg Prod.snd h
      rw [hFac s p hp hpP, hFac t p hp hpP, he])
  simpa [Fintype.card_prod, Sym.card_sym_eq_choose, Fintype.card_fun, Fintype.card_option,
    Fintype.card_coe, ZMod.card] using hCard

theorem middle_coefficient_tag {a : ℕ} (P Q : Finset ℕ) (ha : a ≠ 0)
    (hSupport : a.primeFactors ⊆ P ∪ Q) (hPrime : ∀ q ∈ Q, q.Prime)
    (hAvoid : ∀ q ∈ Q, ∀ r ∈ Q, ¬ q*r ∣ a) :
    ∃ tag : Option Q, ∀ p : ℕ, p.Prime → p ∉ P →
      a.factorization p = optionalPrimeVal p tag := by
  classical
  by_cases hSome : ∃ q ∈ Q, q ∣ a
  · obtain ⟨q, hqQ, hd⟩ := hSome
    refine ⟨some ⟨q,hqQ⟩, ?_⟩
    intro p hp hpP
    by_cases he : q = p
    · subst p
      simp only [optionalPrimeVal, if_true]
      have hq := hPrime q hqQ
      have hLo := hq.factorization_pos_of_dvd ha hd
      have hHi : ¬ 2 ≤ a.factorization q := by
        intro h
        exact hAvoid q hqQ q hqQ (by
          simpa only [pow_two] using (hq.pow_dvd_iff_le_factorization ha).2 h)
      omega
    · simp only [optionalPrimeVal, if_neg he]
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpA
      have hpQ := (mem_union.mp (hSupport (Nat.mem_primeFactors.mpr ⟨hp,hpA,ha⟩))).resolve_left hpP
      have hCop := (Nat.coprime_primes (hPrime q hqQ) hp).2 he
      exact hAvoid q hqQ p hpQ (hCop.mul_dvd_of_dvd_of_dvd hd hpA)
  · refine ⟨none, ?_⟩
    intro p hp hpP
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpA
    have hpQ := (mem_union.mp (hSupport (Nat.mem_primeFactors.mpr ⟨hp,hpA,ha⟩))).resolve_left hpP
    exact hSome ⟨p,hpQ,hpA⟩

def consecutivePowerDifference (q m : ℕ) : ℕ := (q+1)^m - q^m

lemma consecutive_power_difference_succ (q m : ℕ) :
    consecutivePowerDifference q (m+1) = (q+1)^m + q*consecutivePowerDifference q m := by
  have hle : q^m ≤ (q+1)^m := pow_le_pow_left' (by omega) _
  have hEq := Nat.sub_add_cancel hle
  have hMul := congrArg (fun z : ℕ => q*z) hEq
  change q*((q+1)^m-q^m+q^m) = q*(q+1)^m at hMul
  rw [Nat.mul_add] at hMul
  unfold consecutivePowerDifference
  rw [show (q+1)^(m+1) = (q+1)^m + q*(q+1)^m by rw [pow_succ]; ring,
    pow_succ' q m]
  omega

lemma consecutive_power_difference_scale {q : ℕ} (hq : 5 ≤ q) (m : ℕ) :
    5^m*q*consecutivePowerDifference q m ≤ q^m*5*consecutivePowerDifference 5 m := by
  induction m with
  | zero => simp [consecutivePowerDifference]
  | succ m ih =>
    have hPow : (5*(q+1))^m ≤ (6*q)^m := pow_le_pow_left' (by omega) m
    rw [consecutive_power_difference_succ q m, consecutive_power_difference_succ 5 m]
    change 5^(m+1)*q*((q+1)^m+q*consecutivePowerDifference q m) ≤
      q^(m+1)*5*(6^m+5*consecutivePowerDifference 5 m)
    calc
      _ = 5*q*(5*(q+1))^m + 5*q*(5^m*q*consecutivePowerDifference q m) := by
        rw [mul_pow, pow_succ 5 m]
        ring
      _ ≤ 5*q*(6*q)^m + 5*q*(q^m*5*consecutivePowerDifference 5 m) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hPow) (Nat.mul_le_mul_left _ ih)
      _ = _ := by rw [mul_pow, pow_succ q m]; ring

lemma smooth_count_growth_step {q m f : ℕ} (hq : 5 ≤ q) (hf : 0 < f)
    (hBase : 5*6^m ≤ (f+4)*5^m) :
    q*(q+1)^m ≤ (f+q-1)*q^m := by
  have hd₅ : consecutivePowerDifference 5 m + 5^m = 6^m :=
    Nat.sub_add_cancel (pow_le_pow_left' (by decide : (5:ℕ) ≤ 6) m)
  have hBaseDiff : 5*consecutivePowerDifference 5 m ≤ (f-1)*5^m := by
    have h := congrArg (fun z : ℕ => 5*z) hd₅
    change 5*(consecutivePowerDifference 5 m + 5^m) = 5*6^m at h
    rw [Nat.mul_add] at h
    rw [show f+4 = (f-1)+5 by omega, Nat.add_mul] at hBase
    omega
  have hDiff : q*consecutivePowerDifference q m ≤ (f-1)*q^m := by
    apply Nat.le_of_mul_le_mul_left _ (pow_pos (by decide : 0 < (5:ℕ)) m)
    calc
      _ = 5^m*q*consecutivePowerDifference q m := by ring
      _ ≤ q^m*5*consecutivePowerDifference 5 m := consecutive_power_difference_scale hq m
      _ = q^m*(5*consecutivePowerDifference 5 m) := by ring
      _ ≤ q^m*((f-1)*5^m) := Nat.mul_le_mul_left _ hBaseDiff
      _ = _ := by ring
  have hdq : consecutivePowerDifference q m + q^m = (q+1)^m :=
    Nat.sub_add_cancel (pow_le_pow_left' (by omega) m)
  rw [← hdq, Nat.mul_add, show f+q-1 = (f-1)+q by omega, Nat.add_mul]
  exact Nat.add_le_add_right hDiff _

lemma smooth_multiset_numeric_induction {l f m : ℕ} (hl : 5 ≤ l) (hf : 0 < f)
    (hBase : 5^m < (f+3).choose 4) (hStep : 5*6^m ≤ (f+4)*5^m) :
    l^m < (f+l-2).choose (l-1) := by
  induction l, hl using Nat.le_induction with
  | base => simpa using hBase
  | succ q hq ih =>
    have hSym₁ : (f+q-2).choose (f-1) = (f+q-2).choose (q-1) :=
      Nat.choose_symm_of_eq_add (by omega)
    have hSym₂ : (f+q-1).choose (f-1) = (f+q-1).choose q :=
      Nat.choose_symm_of_eq_add (by omega)
    have hId := Nat.choose_mul_succ_eq (f+q-2) (f-1)
    rw [show f+q-2+1 = f+q-1 by omega,
      show f+q-1-(f-1) = q by omega, hSym₁, hSym₂] at hId
    have hGain := smooth_count_growth_step hq hf hStep
    have hStrict := Nat.mul_lt_mul_of_pos_right ih (by omega : 0 < f+q-1)
    rw [hId] at hStrict
    have hStrict' : (f+q-1)*q^m < q*((f+q-1).choose q) := by
      calc
        _ = q^m*(f+q-1) := Nat.mul_comm _ _
        _ < (f+q-1).choose q * q := hStrict
        _ = _ := Nat.mul_comm _ _
    have hAll := hGain.trans_lt hStrict'
    have hNew : (q+1)^m < (f+q-1).choose q := Nat.lt_of_mul_lt_mul_left hAll
    simpa only [show f+(q+1)-2 = f+q-1 by omega, Nat.add_sub_cancel] using hNew

lemma tagged_count_growth_step {q m f r : ℕ} (hq : 5 ≤ q) (hfr : r+1 ≤ f)
    (hBase : (r+5)*6^m ≤ (f+4)*5^m) :
    (r+q)*(q+1)^m ≤ (f+q-1)*q^m := by
  have hd₅ : consecutivePowerDifference 5 m + 5^m = 6^m :=
    Nat.sub_add_cancel (pow_le_pow_left' (by decide : (5:ℕ) ≤ 6) m)
  have hBaseDiff : (r+5)*consecutivePowerDifference 5 m ≤ (f-r-1)*5^m := by
    have h := congrArg (fun z : ℕ => (r+5)*z) hd₅
    change (r+5)*(consecutivePowerDifference 5 m + 5^m) = (r+5)*6^m at h
    rw [Nat.mul_add] at h
    rw [show f+4 = (f-r-1)+(r+5) by omega, Nat.add_mul (f-r-1) (r+5) (5^m)] at hBase
    omega
  have hCompare : 5*(r+q) ≤ q*(r+5) := by
    have h := Nat.mul_le_mul_left r hq
    nlinarith only [h]
  have hDiff : (r+q)*consecutivePowerDifference q m ≤ (f-r-1)*q^m := by
    have hScaled : (5^m*q)*((r+q)*consecutivePowerDifference q m) ≤
        (5^m*q)*((f-r-1)*q^m) := by
      calc
        _ = (r+q)*(5^m*q*consecutivePowerDifference q m) := by ring
        _ ≤ (r+q)*(q^m*5*consecutivePowerDifference 5 m) :=
          Nat.mul_le_mul_left _ (consecutive_power_difference_scale hq m)
        _ = (5*(r+q))*(q^m*consecutivePowerDifference 5 m) := by ring
        _ ≤ (q*(r+5))*(q^m*consecutivePowerDifference 5 m) := Nat.mul_le_mul_right _ hCompare
        _ = (q*q^m)*((r+5)*consecutivePowerDifference 5 m) := by ring
        _ ≤ (q*q^m)*((f-r-1)*5^m) := Nat.mul_le_mul_left _ hBaseDiff
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hScaled
      (Nat.mul_pos (pow_pos (by decide : 0 < (5:ℕ)) m) (by omega))
  have hdq : consecutivePowerDifference q m + q^m = (q+1)^m :=
    Nat.sub_add_cancel (pow_le_pow_left' (by omega) m)
  rw [← hdq, Nat.mul_add, show f+q-1 = (f-r-1)+(r+q) by omega,
    Nat.add_mul (f-r-1) (r+q) (q^m)]
  exact Nat.add_le_add_right hDiff _

lemma tagged_multiset_numeric_induction {l f m r : ℕ} (hl : 5 ≤ l) (hfr : r+1 ≤ f)
    (hBase : 5^m * (r+4).choose 4 < (f+3).choose 4)
    (hStep : (r+5)*6^m ≤ (f+4)*5^m) :
    l^m * (r+l-1).choose (l-1) < (f+l-2).choose (l-1) := by
  induction l, hl using Nat.le_induction with
  | base => simpa [Nat.add_comm, Nat.add_assoc] using hBase
  | succ q hq ih =>
    have hSym₁ : (f+q-2).choose (f-1) = (f+q-2).choose (q-1) :=
      Nat.choose_symm_of_eq_add (by omega)
    have hSym₂ : (f+q-1).choose (f-1) = (f+q-1).choose q :=
      Nat.choose_symm_of_eq_add (by omega)
    have hSym₃ : (r+q-1).choose r = (r+q-1).choose (q-1) :=
      Nat.choose_symm_of_eq_add (by omega)
    have hSym₄ : (r+q).choose r = (r+q).choose q :=
      Nat.choose_symm_of_eq_add (by omega)
    have hNum := Nat.choose_mul_succ_eq (f+q-2) (f-1)
    rw [show f+q-2+1 = f+q-1 by omega,
      show f+q-1-(f-1) = q by omega, hSym₁, hSym₂] at hNum
    have hDen := Nat.choose_mul_succ_eq (r+q-1) r
    rw [show r+q-1+1 = r+q by omega, show r+q-r = q by omega, hSym₃, hSym₄] at hDen
    have hGain := tagged_count_growth_step hq hfr hStep
    have hStrict := Nat.mul_lt_mul_of_pos_right ih (by omega : 0 < f+q-1)
    rw [hNum] at hStrict
    have hAll : q*((q+1)^m*(r+q).choose q) < q*(f+q-1).choose q := by
      calc
        _ = (q+1)^m*((r+q).choose q*q) := by ring
        _ = ((r+q)*(q+1)^m)*(r+q-1).choose (q-1) := by rw [← hDen]; ring
        _ ≤ ((f+q-1)*q^m)*(r+q-1).choose (q-1) := Nat.mul_le_mul_right _ hGain
        _ = (q^m*(r+q-1).choose (q-1))*(f+q-1) := by ring
        _ < (f+q-1).choose q*q := hStrict
        _ = _ := Nat.mul_comm _ _
    have hNew := Nat.lt_of_mul_lt_mul_left hAll
    simpa only [show f+(q+1)-2 = f+q-1 by omega,
      show r+(q+1)-1 = r+q by omega, Nat.add_sub_cancel] using hNew

def intervalMultiples (n k p : ℕ) : Finset ℕ :=
  (Ioc n (n+k)).filter (p ∣ ·)

lemma interval_multiples_card_le (n k p : ℕ) (hp : 0 < p) :
    (intervalMultiples n k p).card ≤ (k+p-1)/p := by
  let left := (Ioc 0 n).filter (p ∣ ·)
  have hUnion : (Ioc 0 (n+k)).filter (p ∣ ·) = left ∪ intervalMultiples n k p := by
    ext m
    simp only [left, intervalMultiples, mem_union, mem_filter, mem_Ioc]
    omega
  have hDisj : Disjoint left (intervalMultiples n k p) := by
    rw [Finset.disjoint_left]
    intro m hl hr
    have hl' := mem_Ioc.mp (mem_filter.mp hl).1
    have hr' := mem_Ioc.mp (mem_filter.mp hr).1
    omega
  have hCard : (n+k)/p = n/p + (intervalMultiples n k p).card := by
    have h := congrArg Finset.card hUnion
    rw [Finset.card_union_of_disjoint hDisj, Nat.Ioc_filter_dvd_card_eq_div] at h
    dsimp only [left] at h
    rw [Nat.Ioc_filter_dvd_card_eq_div] at h
    exact h
  have hEq : (n+k)/p = (n%p+k)/p + n/p := by
    have hSplit := Nat.mod_add_div n p
    calc
      (n+k)/p = (n%p+k+p*(n/p))/p := by
        rw [show n+k = n%p+k+p*(n/p) by omega]
      _ = (n%p+k)/p + n/p := Nat.add_mul_div_left _ _ hp
  have hMod := Nat.mod_lt n hp
  have hLe : (n%p+k)/p ≤ (k+p-1)/p := Nat.div_le_div_right (by omega)
  omega

def lowPrimes (k cutoff : ℕ) : Finset ℕ :=
  (range k).filter fun p => p.Prime ∧ p ≤ cutoff

def highPrimes (k cutoff : ℕ) : Finset ℕ :=
  (range k).filter fun p => p.Prime ∧ cutoff < p

def smoothLowerBound (k cutoff : ℕ) : ℕ :=
  k - ∑ p ∈ highPrimes k cutoff, (k+p-1)/p

def middlePrimes (k low high : ℕ) : Finset ℕ :=
  (range k).filter fun p => p.Prime ∧ low < p ∧ p ≤ high

def orderedMiddlePairs (k low high : ℕ) : Finset (ℕ × ℕ) :=
  ((middlePrimes k low high).product (middlePrimes k low high)).filter fun z => z.1 ≤ z.2

def mediumLowerBound (k low high : ℕ) : ℕ :=
  k - ((∑ p ∈ highPrimes k high, (k+p-1)/p) +
    ∑ z ∈ orderedMiddlePairs k low high, (k+z.1*z.2-1)/(z.1*z.2))

def indexMultiples (n k p : ℕ) : Finset ℕ :=
  (Icc 1 k).filter fun i => p ∣ n+i

lemma index_multiples_card_le (n k p : ℕ) (hp : 0 < p) :
    (indexMultiples n k p).card ≤ (k+p-1)/p := by
  refine (Finset.card_le_card_of_injOn (n+·) ?_ ?_ :
    (indexMultiples n k p).card ≤ (intervalMultiples n k p).card).trans
    (interval_multiples_card_le n k p hp)
  · intro i hi
    obtain ⟨hR,hDvd⟩ := mem_filter.mp hi
    have hiB := mem_Icc.mp hR
    change n+i ∈ intervalMultiples n k p
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, hDvd⟩
  · intro i _ j _ e
    change n+i = n+j at e
    omega

theorem good_medium_coefficients {n k l : ℕ} {a x : ℕ → ℕ} (low high : ℕ)
    (ha : ∀ i ∈ Icc 1 k, a i ≠ 0)
    (hRepr : ∀ i ∈ Icc 1 k, n+i = a i*x i^l)
    (hSupport : ∀ i ∈ Icc 1 k, ∀ p ∈ (a i).primeFactors, p < k) :
    ∃ S ⊆ Icc 1 k, mediumLowerBound k low high ≤ S.card ∧
      ∃ tag : ℕ → Option (middlePrimes k low high),
        ∀ i ∈ S, ∀ p : ℕ, p.Prime → p ∉ lowPrimes k low →
          (a i).factorization p = optionalPrimeVal p (tag i) := by
  let I := Icc 1 k
  let P := lowPrimes k low
  let Q := middlePrimes k low high
  let H := highPrimes k high
  let D := orderedMiddlePairs k low high
  let bad₁ := H.biUnion (indexMultiples n k)
  let bad₂ := D.biUnion fun z => indexMultiples n k (z.1*z.2)
  let S := I \ (bad₁ ∪ bad₂)
  have hS : S ⊆ I := sdiff_subset
  have hpQ (p : ℕ) (hp : p ∈ Q) : p.Prime := (mem_filter.mp hp).2.1
  have hD (z : ℕ × ℕ) (hz : z ∈ D) : z.1 ∈ Q ∧ z.2 ∈ Q :=
    mem_product.mp (mem_filter.mp hz).1
  have goodD (q r : ℕ) (hq : q ∈ Q) (hr : r ∈ Q) (hqr : q ≤ r) :
      (q,r) ∈ D := mem_filter.mpr ⟨mem_product.mpr ⟨hq,hr⟩, hqr⟩
  have hBadSub : bad₁ ∪ bad₂ ⊆ I := by
    intro i hi
    rcases mem_union.mp hi with h | h
    · obtain ⟨p,hp,hi⟩ := mem_biUnion.mp h
      exact (mem_filter.mp hi).1
    · obtain ⟨z,hz,hi⟩ := mem_biUnion.mp h
      exact (mem_filter.mp hi).1
  have hCount₁ : bad₁.card ≤ ∑ p ∈ H, (k+p-1)/p :=
    card_biUnion_le.trans (sum_le_sum (fun p hp =>
      index_multiples_card_le n k p (mem_filter.mp hp).2.1.pos))
  have hCount₂ : bad₂.card ≤ ∑ z ∈ D, (k+z.1*z.2-1)/(z.1*z.2) :=
    card_biUnion_le.trans (sum_le_sum (fun z hz =>
      index_multiples_card_le n k _ (Nat.mul_pos (hpQ _ (hD z hz).1).pos (hpQ _ (hD z hz).2).pos)))
  have hUnion : (bad₁ ∪ bad₂).card ≤
      (∑ p ∈ H, (k+p-1)/p) + ∑ z ∈ D, (k+z.1*z.2-1)/(z.1*z.2) :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add hCount₁ hCount₂)
  have hCount : S.card + (bad₁ ∪ bad₂).card = k :=
    (card_sdiff_add_card_eq_card hBadSub).trans (by simp [I,Nat.card_Icc])
  have hKeep : mediumLowerBound k low high ≤ S.card := by
    change k - ((∑ p ∈ H, (k+p-1)/p) + ∑ z ∈ D, (k+z.1*z.2-1)/(z.1*z.2)) ≤ S.card
    omega
  refine ⟨S,hS,hKeep,?_⟩
  have hChoose : ∀ i : S, ∃ tag : Option Q, ∀ p : ℕ, p.Prime → p ∉ P →
      (a i.val).factorization p = optionalPrimeVal p tag := by
    rintro ⟨i,hi⟩
    have hiI := hS hi
    have haDvd : a i ∣ n+i := ⟨x i^l, hRepr i hiI⟩
    have hAvoid₁ (p : ℕ) (hp : p ∈ H) : ¬ p ∣ n+i := fun hd =>
      (mem_sdiff.mp hi).2 (mem_union_left _ (mem_biUnion.mpr ⟨p,hp,mem_filter.mpr ⟨hiI,hd⟩⟩))
    have hAvoid₂ (z : ℕ × ℕ) (hz : z ∈ D) : ¬ z.1*z.2 ∣ n+i := fun hd =>
      (mem_sdiff.mp hi).2 (mem_union_right _ (mem_biUnion.mpr ⟨z,hz,mem_filter.mpr ⟨hiI,hd⟩⟩))
    have hSupp : (a i).primeFactors ⊆ P ∪ Q := by
      intro p hp
      have hpK := hSupport i hiI p hp
      obtain ⟨hpPrime,hpDiv,_⟩ := Nat.mem_primeFactors.mp hp
      have hpRange := mem_range.mpr hpK
      by_cases hpL : p ≤ low
      · exact mem_union_left _ (mem_filter.mpr ⟨hpRange,hpPrime,hpL⟩)
      · have hpUpper : p ≤ high := by
          by_contra! hh
          exact hAvoid₁ p (mem_filter.mpr ⟨hpRange,hpPrime,hh⟩) (hpDiv.trans haDvd)
        exact mem_union_right _ (mem_filter.mpr ⟨hpRange,hpPrime,by omega,hpUpper⟩)
    have hAvoid (q : ℕ) (hq : q ∈ Q) (r : ℕ) (hr : r ∈ Q) : ¬ q*r ∣ a i := by
      intro hd
      rcases le_total q r with hqr | hrq
      · exact hAvoid₂ (q,r) (goodD q r hq hr hqr) (hd.trans haDvd)
      · apply hAvoid₂ (r,q) (goodD r q hr hq hrq)
        simpa only [Nat.mul_comm] using (hd.trans haDvd)
    exact middle_coefficient_tag P Q (ha i hiI) hSupp hpQ hAvoid
  choose tag hTag using hChoose
  refine ⟨fun i => if hi : i ∈ S then tag ⟨i,hi⟩ else none, ?_⟩
  intro i hi p hp hpP
  simpa only [dif_pos hi] using hTag ⟨i,hi⟩ p hp hpP

theorem odd_prime_of_medium_certificate {n k l low high f m r : ℕ}
    (hk : 3 ≤ k) (hPrime : l.Prime) (hl : 3 ≤ l)
    (hSylvester : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ t ∈ Ioc n (n+k), t)
    (hF : f ≤ mediumLowerBound k low high)
    (hM : (lowPrimes k low).card ≤ m) (hR : (middlePrimes k low high).card ≤ r)
    (hCubic : 3^m * (r+1)^2 < f*(f-1))
    (hFR : r+1 ≤ f)
    (hBase : 5^m * (r+4).choose 4 < (f+3).choose 4)
    (hStep : (r+5)*6^m ≤ (f+4)*5^m) :
    ∃ p : ℕ, k ≤ p ∧ p.Prime ∧ ¬ l ∣ (∏ t ∈ Ioc n (n+k), t).factorization p := by
  by_contra! hAll
  obtain ⟨hN,hTop⟩ := sylvester_schur_power_bounds_of_no_witness (by omega) hSylvester hAll
  obtain ⟨a,x,ha,hRepr,hSupport,_⟩ := normalize_odd_coefficients (by omega) hAll
  obtain ⟨S,hS,hCount,tag,hTag⟩ := good_medium_coefficients low high ha hRepr hSupport
  have hF' := hF.trans hCount
  have hPow : l^(lowPrimes k low).card ≤ l^m := pow_le_pow_right' (by omega) hM
  by_cases he : l = 3
  · subst l
    have hUpper := tagged_ratio_residue_bound S (lowPrimes k low) (middlePrimes k low high)
      (by omega) hN (by decide) hTop hRepr hS (fun i hi => ha i (hS hi)) tag hTag
    have hLower := Nat.mul_le_mul hF' (Nat.sub_le_sub_right hF' 1)
    have hSmall := pow_le_pow_left' (Nat.add_le_add_right hR 1) 2
    exact (not_lt_of_ge (hLower.trans (hUpper.trans (Nat.mul_le_mul hPow hSmall)))) hCubic
  · have hNotFour : l ≠ 4 := fun h => (by decide : ¬Nat.Prime 4) (h ▸ hPrime)
    have hLarge : 5 ≤ l := by omega
    have hUpper := tagged_multiset_residue_bound S (lowPrimes k low) (middlePrimes k low high)
      (by omega) hN (by omega) hTop (d := l-1) (by omega) hRepr hS
      (fun i hi => ha i (hS hi)) tag hTag
    have hLower := Nat.choose_le_choose (l-1)
      (show f+l-2 ≤ S.card+(l-1)-1 by omega)
    have hMid := Nat.choose_le_choose (l-1)
      (show (middlePrimes k low high).card+(l-1) ≤ r+l-1 by omega)
    have hStrict := tagged_multiset_numeric_induction hLarge hFR hBase hStep
    exact (not_lt_of_ge (hLower.trans (hUpper.trans (Nat.mul_le_mul hPow hMid)))) hStrict

theorem good_smooth_coefficients {n k l : ℕ} {a x : ℕ → ℕ} (cutoff : ℕ)
    (hRepr : ∀ i ∈ Icc 1 k, n+i = a i * x i ^ l)
    (hSupport : ∀ i ∈ Icc 1 k, ∀ p ∈ (a i).primeFactors, p < k) :
    ∃ S ⊆ Icc 1 k, smoothLowerBound k cutoff ≤ S.card ∧
      ∀ i ∈ S, (a i).primeFactors ⊆ lowPrimes k cutoff := by
  let R := Icc 1 k
  let bad := fun p : ℕ => R.filter fun i => p ∣ n+i
  let excluded := (highPrimes k cutoff).biUnion bad
  let allowed := R \ excluded
  have hSub : allowed ⊆ R := sdiff_subset
  have hExcluded : excluded ⊆ R := by
    intro i hi
    obtain ⟨p, hp, hi⟩ := mem_biUnion.mp hi
    exact (mem_filter.mp hi).1
  have hBoundPrime (p : ℕ) (hp : p ∈ highPrimes k cutoff) :
      (bad p).card ≤ (k+p-1)/p := by
    have hpPrime := (mem_filter.mp hp).2.1
    refine (Finset.card_le_card_of_injOn (n+·) ?_ ?_ :
      (bad p).card ≤ (intervalMultiples n k p).card).trans (interval_multiples_card_le n k p hpPrime.pos)
    · intro i hi
      obtain ⟨hR,hDvd⟩ := mem_filter.mp hi
      have hiB := mem_Icc.mp hR
      change n+i ∈ intervalMultiples n k p
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, hDvd⟩
    · intro i _ j _ e
      change n+i = n+j at e
      omega
  have hBound : excluded.card ≤ ∑ p ∈ highPrimes k cutoff, (k+p-1)/p :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum hBoundPrime)
  have hR : R.card = k := by simp [R, Nat.card_Icc]
  have hCount : allowed.card + excluded.card = k :=
    (Finset.card_sdiff_add_card_eq_card hExcluded).trans hR
  refine ⟨allowed, hSub, ?_, ?_⟩
  · unfold smoothLowerBound
    omega
  · intro i hi p hp
    have hiR := hSub hi
    have hpK := hSupport i hiR p hp
    obtain ⟨hP, hd, _⟩ := Nat.mem_primeFactors.mp hp
    refine mem_filter.mpr ⟨mem_range.mpr hpK, hP, ?_⟩
    by_contra! hpCut
    have hBad : p ∈ highPrimes k cutoff := mem_filter.mpr ⟨mem_range.mpr hpK, hP, hpCut⟩
    have hPN : p ∣ n+i := by
      rw [hRepr i hiR]
      exact hd.trans (dvd_mul_right _ _)
    exact (mem_sdiff.mp hi).2 (mem_biUnion.mpr ⟨p,hBad,mem_filter.mpr ⟨hiR,hPN⟩⟩)

private def smallPrimeList : List ℕ := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43,
  47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
  109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
  191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263,
  269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349,
  353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433,
  439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521,
  523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613,
  617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
  709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809,
  811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887,
  907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997
]

set_option maxRecDepth 100000 in
private def smallPrimeTable : Finset ℕ :=
  ⟨(smallPrimeList : Multiset ℕ), by decide⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma small_prime_table_correct : smallPrimeTable = (range 1001).filter Nat.Prime := by
  decide

private def fastLow (k c : ℕ) : Finset ℕ :=
  smallPrimeTable.filter fun p => p < k ∧ p ≤ c

private def fastHigh (k c : ℕ) : Finset ℕ :=
  smallPrimeTable.filter fun p => p < k ∧ c < p

private lemma fast_low_eq {k c : ℕ} (hk : k ≤ 1000) : fastLow k c = lowPrimes k c := by
  unfold fastLow lowPrimes
  rw [small_prime_table_correct]
  ext p
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨⟨_, hp⟩, hpK, hc⟩
    exact ⟨hpK, hp, hc⟩
  · rintro ⟨hpK, hp, hc⟩
    exact ⟨⟨by omega, hp⟩, hpK, hc⟩

private lemma fast_high_eq {k c : ℕ} (hk : k ≤ 1000) : fastHigh k c = highPrimes k c := by
  unfold fastHigh highPrimes
  rw [small_prime_table_correct]
  ext p
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨⟨_, hp⟩, hpK, hc⟩
    exact ⟨hpK, hp, hc⟩
  · rintro ⟨hpK, hp, hc⟩
    exact ⟨⟨by omega, hp⟩, hpK, hc⟩

private structure OddBand where
  lower : ℕ
  upper : ℕ
  cutoff : ℕ
  deriving DecidableEq

private def smallOddBands : List OddBand := [
  ⟨4, 5, 3⟩, ⟨6, 7, 5⟩, ⟨8, 11, 5⟩, ⟨12, 14, 5⟩, ⟨15, 19, 5⟩,
  ⟨20, 23, 7⟩, ⟨24, 31, 7⟩, ⟨32, 41, 7⟩, ⟨42, 53, 7⟩, ⟨54, 67, 11⟩,
  ⟨68, 83, 11⟩, ⟨84, 102, 11⟩, ⟨103, 123, 11⟩, ⟨124, 149, 13⟩,
  ⟨150, 179, 13⟩, ⟨180, 212, 13⟩, ⟨213, 249, 13⟩, ⟨250, 289, 13⟩,
  ⟨290, 332, 17⟩, ⟨333, 381, 17⟩, ⟨382, 434, 17⟩, ⟨435, 491, 17⟩,
  ⟨492, 553, 17⟩, ⟨554, 617, 17⟩, ⟨618, 683, 19⟩, ⟨684, 757, 19⟩,
  ⟨758, 834, 19⟩, ⟨835, 916, 19⟩, ⟨917, 1000, 19⟩
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma fast_small_odd_certificates : ∀ band ∈ smallOddBands,
    let f := band.lower - ∑ p ∈ fastHigh band.upper band.cutoff, (band.upper+p-1)/p
    let m := (fastLow band.upper band.cutoff).card
    band.upper ≤ 1000 ∧ 3^m < f*(f-1) ∧ 0 < f ∧
      5^m < (f+3).choose 4 ∧ 5*6^m ≤ (f+4)*5^m := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma small_odd_band_cover : ∀ r : Fin 997, ∃ band ∈ smallOddBands,
    band.lower ≤ r.val+4 ∧ r.val+4 ≤ band.upper := by
  decide

private lemma small_odd_certificate {k : ℕ} (hk : 4 ≤ k) (hkUpper : k ≤ 1000) :
    ∃ c f m : ℕ, f ≤ smoothLowerBound k c ∧ (lowPrimes k c).card ≤ m ∧
      3^m < f*(f-1) ∧ 0 < f ∧ 5^m < (f+3).choose 4 ∧ 5*6^m ≤ (f+4)*5^m := by
  obtain ⟨band, hBand, hLo, hHi⟩ := small_odd_band_cover ⟨k-4, by omega⟩
  change band.lower ≤ k-4+4 at hLo
  change k-4+4 ≤ band.upper at hHi
  have h : k-4+4 = k := by omega
  rw [h] at hLo hHi
  have hCert := fast_small_odd_certificates band hBand
  dsimp only at hCert
  rcases hCert with ⟨hUpper, hCert⟩
  rw [fast_high_eq hUpper, fast_low_eq hUpper] at hCert
  let m := (lowPrimes band.upper band.cutoff).card
  let f := band.lower - ∑ p ∈ highPrimes band.upper band.cutoff, (band.upper+p-1)/p
  have hLow : lowPrimes k band.cutoff ⊆ lowPrimes band.upper band.cutoff := by
    intro p hp
    rcases mem_filter.mp hp with ⟨hpK,hp⟩
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hpK).trans_le hHi), hp⟩
  have hHigh : highPrimes k band.cutoff ⊆ highPrimes band.upper band.cutoff := by
    intro p hp
    rcases mem_filter.mp hp with ⟨hpK,hp⟩
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hpK).trans_le hHi), hp⟩
  have hLoss : (∑ p ∈ highPrimes k band.cutoff, (k+p-1)/p) ≤
      ∑ p ∈ highPrimes band.upper band.cutoff, (band.upper+p-1)/p := by
    calc
      _ ≤ ∑ p ∈ highPrimes k band.cutoff, (band.upper+p-1)/p :=
        Finset.sum_le_sum (fun p _ => Nat.div_le_div_right (by omega))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hHigh (fun _ _ _ => Nat.zero_le _)
  refine ⟨band.cutoff, f, m, ?_, card_le_card hLow, hCert⟩
  change band.lower - (∑ p ∈ highPrimes band.upper band.cutoff, (band.upper+p-1)/p) ≤
    k - ∑ p ∈ highPrimes k band.cutoff, (k+p-1)/p
  omega

theorem small_cubic_of_sylvester {n k : ℕ} (hk : 4 ≤ k) (hkUpper : k ≤ 1000)
    (hSylvester : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ t ∈ Ioc n (n+k), t) :
    ∃ p : ℕ, k ≤ p ∧ p.Prime ∧ ¬ 3 ∣ (∏ t ∈ Ioc n (n+k), t).factorization p := by
  by_contra! hAll
  obtain ⟨hN,hTop⟩ := sylvester_schur_power_bounds_of_no_witness (by decide) hSylvester hAll
  obtain ⟨a,x,ha,hRepr,hSupport,_⟩ := normalize_odd_coefficients (by decide) hAll
  obtain ⟨c, f, m, hF, hM, hNumeric, _⟩ := small_odd_certificate hk hkUpper
  obtain ⟨S,hS,hCount,hPrime⟩ := good_smooth_coefficients c hRepr hSupport
  have hBound := ratio_residue_bound S (lowPrimes k c)
    (by omega) hN (by decide) hTop hRepr hS (fun i hi => ha i (hS hi)) hPrime
  have hF' := hF.trans hCount
  have hCountProduct := Nat.mul_le_mul hF' (Nat.sub_le_sub_right hF' 1)
  exact (not_lt_of_ge (hCountProduct.trans (hBound.trans
    (pow_le_pow_right' (by decide : (1:ℕ) ≤ 3) hM)))) hNumeric

theorem small_higher_exponent_of_sylvester {n k l : ℕ}
    (hk : 4 ≤ k) (hkUpper : k ≤ 1000) (hl : 5 ≤ l)
    (hSylvester : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ t ∈ Ioc n (n+k), t) :
    ∃ p : ℕ, k ≤ p ∧ p.Prime ∧ ¬ l ∣ (∏ t ∈ Ioc n (n+k), t).factorization p := by
  by_contra! hAll
  obtain ⟨hN,hTop⟩ := sylvester_schur_power_bounds_of_no_witness (by omega) hSylvester hAll
  obtain ⟨a,x,ha,hRepr,hSupport,_⟩ := normalize_odd_coefficients (by omega) hAll
  obtain ⟨c, f, m, hF, hM, _, hPos, hBase, hStep⟩ := small_odd_certificate hk hkUpper
  obtain ⟨S,hS,hCount,hPrime⟩ := good_smooth_coefficients c hRepr hSupport
  have hBound := smooth_multiset_residue_bound S (lowPrimes k c)
    (by omega) hN (by omega) hTop (d := l-1) (by omega) hRepr hS (fun i hi => ha i (hS hi)) hPrime
  have hStrict := smooth_multiset_numeric_induction hl hPos hBase hStep
  have hF' := hF.trans hCount
  have hMono := Nat.choose_le_choose (l-1)
    (show f+l-2 ≤ S.card+(l-1)-1 by omega)
  exact (not_lt_of_ge (hMono.trans (hBound.trans
    (pow_le_pow_right' (by omega : 1 ≤ l) hM)))) hStrict

theorem small_odd_prime_of_sylvester {n k l : ℕ} (hk : 3 ≤ k) (hkUpper : k ≤ 1000)
    (hPrime : l.Prime) (hl : 3 ≤ l)
    (hSylvester : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ t ∈ Ioc n (n+k), t) :
    ∃ p : ℕ, k ≤ p ∧ p.Prime ∧ ¬ l ∣ (∏ t ∈ Ioc n (n+k), t).factorization p := by
  by_cases hK : k = 3
  · subst k
    exact three_odd_exponent_of_sylvester hl hSylvester
  by_cases hL : l = 3
  · subst l
    exact small_cubic_of_sylvester (by omega) hkUpper hSylvester
  · have hNotFour : l ≠ 4 := fun e => (by decide : ¬Nat.Prime 4) (e ▸ hPrime)
    exact small_higher_exponent_of_sylvester (by omega) hkUpper (by omega) hSylvester

private structure MediumBand where
  lower : ℕ
  upper : ℕ
  lowPrime : ℕ
  highPrime : ℕ
  deriving DecidableEq

private def mediumOddBands : List MediumBand := [
  ⟨1001, 1113, 11, 31⟩, ⟨1114, 1235, 11, 31⟩, ⟨1236, 1367, 11, 31⟩,
  ⟨1368, 1507, 11, 31⟩, ⟨1508, 1662, 11, 37⟩, ⟨1663, 1828, 11, 37⟩,
  ⟨1829, 2014, 11, 41⟩, ⟨2015, 2223, 11, 43⟩, ⟨2224, 2454, 11, 47⟩,
  ⟨2455, 2698, 11, 47⟩, ⟨2699, 2953, 11, 47⟩, ⟨2954, 3233, 11, 53⟩,
  ⟨3234, 3533, 13, 53⟩, ⟨3534, 3860, 13, 59⟩, ⟨3861, 4219, 13, 61⟩,
  ⟨4220, 4605, 13, 61⟩, ⟨4606, 5024, 13, 67⟩, ⟨5025, 5473, 13, 67⟩,
  ⟨5474, 5973, 13, 73⟩, ⟨5974, 6502, 13, 73⟩, ⟨6503, 7071, 13, 79⟩,
  ⟨7072, 7691, 13, 83⟩, ⟨7692, 8345, 13, 83⟩, ⟨8346, 9043, 13, 89⟩,
  ⟨9044, 9770, 13, 89⟩, ⟨9771, 10544, 13, 97⟩, ⟨10545, 11365, 13, 101⟩,
  ⟨11366, 12241, 13, 103⟩, ⟨12242, 13183, 13, 109⟩, ⟨13184, 14179, 13, 113⟩,
  ⟨14180, 15224, 17, 113⟩, ⟨15225, 16325, 17, 113⟩, ⟨16326, 17497, 17, 127⟩,
  ⟨17498, 18741, 17, 131⟩, ⟨18742, 20047, 17, 131⟩, ⟨20048, 21448, 17, 139⟩,
  ⟨21449, 22900, 17, 139⟩, ⟨22901, 24439, 17, 151⟩, ⟨24440, 26041, 17, 151⟩,
  ⟨26042, 27727, 17, 157⟩, ⟨27728, 29474, 17, 163⟩, ⟨29475, 30000, 19, 167⟩
]

private def intervalEnd : ℕ → List MediumBand → ℕ
  | start, [] => start
  | _, band :: rest => intervalEnd (band.upper+1) rest

private def contiguous : ℕ → List MediumBand → Bool
  | _, [] => true
  | start, band :: rest =>
    decide (band.lower = start ∧ band.lower ≤ band.upper) && contiguous (band.upper+1) rest

private lemma cover_contiguous (bands : List MediumBand) {start k : ℕ}
    (hC : contiguous start bands = true) (hLo : start ≤ k) (hHi : k < intervalEnd start bands) :
    ∃ band ∈ bands, band.lower ≤ k ∧ k ≤ band.upper := by
  induction bands generalizing start with
  | nil =>
    simp only [intervalEnd] at hHi
    omega
  | cons band rest ih =>
    simp only [contiguous, Bool.and_eq_true, decide_eq_true_eq] at hC
    by_cases hB : k ≤ band.upper
    · exact ⟨band, by simp, by omega, hB⟩
    · obtain ⟨other, ho, hL, hU⟩ := ih (start := band.upper+1) hC.2 (by omega) hHi
      exact ⟨other, by simp [ho], hL, hU⟩

private lemma medium_band_cover {k : ℕ} (hk : 1001 ≤ k) (hkU : k ≤ 30000) :
    ∃ band ∈ mediumOddBands, band.lower ≤ k ∧ k ≤ band.upper :=
  cover_contiguous mediumOddBands (by decide) hk (by
    change k < 30001
    omega)

private def mediumPrimeList : List ℕ :=
  List.flatten [
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
     59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
     137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
     227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311,
     313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
     419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
     509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613,
     617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719,
     727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827],
    [829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
     947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049,
     1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163,
     1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283,
     1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423,
     1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511,
     1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619,
     1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747,
     1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877],
    [1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003,
     2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129,
     2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267,
     2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377,
     2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503,
     2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657,
     2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741,
     2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861,
     2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011],
    [3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167,
     3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301,
     3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413,
     3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541,
     3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671,
     3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797,
     3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923,
     3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057,
     4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211],
    [4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337,
     4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481,
     4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621,
     4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751,
     4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909,
     4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011,
     5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167,
     5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309,
     5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443],
    [5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573,
     5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711,
     5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849,
     5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007,
     6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133,
     6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271,
     6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379,
     6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563,
     6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701],
    [6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833,
     6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971,
     6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121,
     7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253,
     7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457,
     7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561,
     7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691,
     7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853,
     7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009],
    [8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161,
     8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291,
     8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443,
     8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609,
     8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731,
     8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861,
     8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011,
     9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161,
     9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311],
    [9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433,
     9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587,
     9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733,
     9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857,
     9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973, 10007, 10009, 10037,
     10039, 10061, 10067, 10069, 10079, 10091, 10093, 10099, 10103, 10111, 10133, 10139, 10141, 10151, 10159, 10163,
     10169, 10177, 10181, 10193, 10211, 10223, 10243, 10247, 10253, 10259, 10267, 10271, 10273, 10289, 10301, 10303,
     10313, 10321, 10331, 10333, 10337, 10343, 10357, 10369, 10391, 10399, 10427, 10429, 10433, 10453, 10457, 10459,
     10463, 10477, 10487, 10499, 10501, 10513, 10529, 10531, 10559, 10567, 10589, 10597, 10601, 10607, 10613, 10627],
    [10631, 10639, 10651, 10657, 10663, 10667, 10687, 10691, 10709, 10711, 10723, 10729, 10733, 10739, 10753, 10771,
     10781, 10789, 10799, 10831, 10837, 10847, 10853, 10859, 10861, 10867, 10883, 10889, 10891, 10903, 10909, 10937,
     10939, 10949, 10957, 10973, 10979, 10987, 10993, 11003, 11027, 11047, 11057, 11059, 11069, 11071, 11083, 11087,
     11093, 11113, 11117, 11119, 11131, 11149, 11159, 11161, 11171, 11173, 11177, 11197, 11213, 11239, 11243, 11251,
     11257, 11261, 11273, 11279, 11287, 11299, 11311, 11317, 11321, 11329, 11351, 11353, 11369, 11383, 11393, 11399,
     11411, 11423, 11437, 11443, 11447, 11467, 11471, 11483, 11489, 11491, 11497, 11503, 11519, 11527, 11549, 11551,
     11579, 11587, 11593, 11597, 11617, 11621, 11633, 11657, 11677, 11681, 11689, 11699, 11701, 11717, 11719, 11731,
     11743, 11777, 11779, 11783, 11789, 11801, 11807, 11813, 11821, 11827, 11831, 11833, 11839, 11863, 11867, 11887,
     11897, 11903, 11909, 11923, 11927, 11933, 11939, 11941, 11953, 11959, 11969, 11971, 11981, 11987, 12007, 12011],
    [12037, 12041, 12043, 12049, 12071, 12073, 12097, 12101, 12107, 12109, 12113, 12119, 12143, 12149, 12157, 12161,
     12163, 12197, 12203, 12211, 12227, 12239, 12241, 12251, 12253, 12263, 12269, 12277, 12281, 12289, 12301, 12323,
     12329, 12343, 12347, 12373, 12377, 12379, 12391, 12401, 12409, 12413, 12421, 12433, 12437, 12451, 12457, 12473,
     12479, 12487, 12491, 12497, 12503, 12511, 12517, 12527, 12539, 12541, 12547, 12553, 12569, 12577, 12583, 12589,
     12601, 12611, 12613, 12619, 12637, 12641, 12647, 12653, 12659, 12671, 12689, 12697, 12703, 12713, 12721, 12739,
     12743, 12757, 12763, 12781, 12791, 12799, 12809, 12821, 12823, 12829, 12841, 12853, 12889, 12893, 12899, 12907,
     12911, 12917, 12919, 12923, 12941, 12953, 12959, 12967, 12973, 12979, 12983, 13001, 13003, 13007, 13009, 13033,
     13037, 13043, 13049, 13063, 13093, 13099, 13103, 13109, 13121, 13127, 13147, 13151, 13159, 13163, 13171, 13177,
     13183, 13187, 13217, 13219, 13229, 13241, 13249, 13259, 13267, 13291, 13297, 13309, 13313, 13327, 13331, 13337],
    [13339, 13367, 13381, 13397, 13399, 13411, 13417, 13421, 13441, 13451, 13457, 13463, 13469, 13477, 13487, 13499,
     13513, 13523, 13537, 13553, 13567, 13577, 13591, 13597, 13613, 13619, 13627, 13633, 13649, 13669, 13679, 13681,
     13687, 13691, 13693, 13697, 13709, 13711, 13721, 13723, 13729, 13751, 13757, 13759, 13763, 13781, 13789, 13799,
     13807, 13829, 13831, 13841, 13859, 13873, 13877, 13879, 13883, 13901, 13903, 13907, 13913, 13921, 13931, 13933,
     13963, 13967, 13997, 13999, 14009, 14011, 14029, 14033, 14051, 14057, 14071, 14081, 14083, 14087, 14107, 14143,
     14149, 14153, 14159, 14173, 14177, 14197, 14207, 14221, 14243, 14249, 14251, 14281, 14293, 14303, 14321, 14323,
     14327, 14341, 14347, 14369, 14387, 14389, 14401, 14407, 14411, 14419, 14423, 14431, 14437, 14447, 14449, 14461,
     14479, 14489, 14503, 14519, 14533, 14537, 14543, 14549, 14551, 14557, 14561, 14563, 14591, 14593, 14621, 14627,
     14629, 14633, 14639, 14653, 14657, 14669, 14683, 14699, 14713, 14717, 14723, 14731, 14737, 14741, 14747, 14753],
    [14759, 14767, 14771, 14779, 14783, 14797, 14813, 14821, 14827, 14831, 14843, 14851, 14867, 14869, 14879, 14887,
     14891, 14897, 14923, 14929, 14939, 14947, 14951, 14957, 14969, 14983, 15013, 15017, 15031, 15053, 15061, 15073,
     15077, 15083, 15091, 15101, 15107, 15121, 15131, 15137, 15139, 15149, 15161, 15173, 15187, 15193, 15199, 15217,
     15227, 15233, 15241, 15259, 15263, 15269, 15271, 15277, 15287, 15289, 15299, 15307, 15313, 15319, 15329, 15331,
     15349, 15359, 15361, 15373, 15377, 15383, 15391, 15401, 15413, 15427, 15439, 15443, 15451, 15461, 15467, 15473,
     15493, 15497, 15511, 15527, 15541, 15551, 15559, 15569, 15581, 15583, 15601, 15607, 15619, 15629, 15641, 15643,
     15647, 15649, 15661, 15667, 15671, 15679, 15683, 15727, 15731, 15733, 15737, 15739, 15749, 15761, 15767, 15773,
     15787, 15791, 15797, 15803, 15809, 15817, 15823, 15859, 15877, 15881, 15887, 15889, 15901, 15907, 15913, 15919,
     15923, 15937, 15959, 15971, 15973, 15991, 16001, 16007, 16033, 16057, 16061, 16063, 16067, 16069, 16073, 16087],
    [16091, 16097, 16103, 16111, 16127, 16139, 16141, 16183, 16187, 16189, 16193, 16217, 16223, 16229, 16231, 16249,
     16253, 16267, 16273, 16301, 16319, 16333, 16339, 16349, 16361, 16363, 16369, 16381, 16411, 16417, 16421, 16427,
     16433, 16447, 16451, 16453, 16477, 16481, 16487, 16493, 16519, 16529, 16547, 16553, 16561, 16567, 16573, 16603,
     16607, 16619, 16631, 16633, 16649, 16651, 16657, 16661, 16673, 16691, 16693, 16699, 16703, 16729, 16741, 16747,
     16759, 16763, 16787, 16811, 16823, 16829, 16831, 16843, 16871, 16879, 16883, 16889, 16901, 16903, 16921, 16927,
     16931, 16937, 16943, 16963, 16979, 16981, 16987, 16993, 17011, 17021, 17027, 17029, 17033, 17041, 17047, 17053,
     17077, 17093, 17099, 17107, 17117, 17123, 17137, 17159, 17167, 17183, 17189, 17191, 17203, 17207, 17209, 17231,
     17239, 17257, 17291, 17293, 17299, 17317, 17321, 17327, 17333, 17341, 17351, 17359, 17377, 17383, 17387, 17389,
     17393, 17401, 17417, 17419, 17431, 17443, 17449, 17467, 17471, 17477, 17483, 17489, 17491, 17497, 17509, 17519],
    [17539, 17551, 17569, 17573, 17579, 17581, 17597, 17599, 17609, 17623, 17627, 17657, 17659, 17669, 17681, 17683,
     17707, 17713, 17729, 17737, 17747, 17749, 17761, 17783, 17789, 17791, 17807, 17827, 17837, 17839, 17851, 17863,
     17881, 17891, 17903, 17909, 17911, 17921, 17923, 17929, 17939, 17957, 17959, 17971, 17977, 17981, 17987, 17989,
     18013, 18041, 18043, 18047, 18049, 18059, 18061, 18077, 18089, 18097, 18119, 18121, 18127, 18131, 18133, 18143,
     18149, 18169, 18181, 18191, 18199, 18211, 18217, 18223, 18229, 18233, 18251, 18253, 18257, 18269, 18287, 18289,
     18301, 18307, 18311, 18313, 18329, 18341, 18353, 18367, 18371, 18379, 18397, 18401, 18413, 18427, 18433, 18439,
     18443, 18451, 18457, 18461, 18481, 18493, 18503, 18517, 18521, 18523, 18539, 18541, 18553, 18583, 18587, 18593,
     18617, 18637, 18661, 18671, 18679, 18691, 18701, 18713, 18719, 18731, 18743, 18749, 18757, 18773, 18787, 18793,
     18797, 18803, 18839, 18859, 18869, 18899, 18911, 18913, 18917, 18919, 18947, 18959, 18973, 18979, 19001, 19009],
    [19013, 19031, 19037, 19051, 19069, 19073, 19079, 19081, 19087, 19121, 19139, 19141, 19157, 19163, 19181, 19183,
     19207, 19211, 19213, 19219, 19231, 19237, 19249, 19259, 19267, 19273, 19289, 19301, 19309, 19319, 19333, 19373,
     19379, 19381, 19387, 19391, 19403, 19417, 19421, 19423, 19427, 19429, 19433, 19441, 19447, 19457, 19463, 19469,
     19471, 19477, 19483, 19489, 19501, 19507, 19531, 19541, 19543, 19553, 19559, 19571, 19577, 19583, 19597, 19603,
     19609, 19661, 19681, 19687, 19697, 19699, 19709, 19717, 19727, 19739, 19751, 19753, 19759, 19763, 19777, 19793,
     19801, 19813, 19819, 19841, 19843, 19853, 19861, 19867, 19889, 19891, 19913, 19919, 19927, 19937, 19949, 19961,
     19963, 19973, 19979, 19991, 19993, 19997, 20011, 20021, 20023, 20029, 20047, 20051, 20063, 20071, 20089, 20101,
     20107, 20113, 20117, 20123, 20129, 20143, 20147, 20149, 20161, 20173, 20177, 20183, 20201, 20219, 20231, 20233,
     20249, 20261, 20269, 20287, 20297, 20323, 20327, 20333, 20341, 20347, 20353, 20357, 20359, 20369, 20389, 20393],
    [20399, 20407, 20411, 20431, 20441, 20443, 20477, 20479, 20483, 20507, 20509, 20521, 20533, 20543, 20549, 20551,
     20563, 20593, 20599, 20611, 20627, 20639, 20641, 20663, 20681, 20693, 20707, 20717, 20719, 20731, 20743, 20747,
     20749, 20753, 20759, 20771, 20773, 20789, 20807, 20809, 20849, 20857, 20873, 20879, 20887, 20897, 20899, 20903,
     20921, 20929, 20939, 20947, 20959, 20963, 20981, 20983, 21001, 21011, 21013, 21017, 21019, 21023, 21031, 21059,
     21061, 21067, 21089, 21101, 21107, 21121, 21139, 21143, 21149, 21157, 21163, 21169, 21179, 21187, 21191, 21193,
     21211, 21221, 21227, 21247, 21269, 21277, 21283, 21313, 21317, 21319, 21323, 21341, 21347, 21377, 21379, 21383,
     21391, 21397, 21401, 21407, 21419, 21433, 21467, 21481, 21487, 21491, 21493, 21499, 21503, 21517, 21521, 21523,
     21529, 21557, 21559, 21563, 21569, 21577, 21587, 21589, 21599, 21601, 21611, 21613, 21617, 21647, 21649, 21661,
     21673, 21683, 21701, 21713, 21727, 21737, 21739, 21751, 21757, 21767, 21773, 21787, 21799, 21803, 21817, 21821],
    [21839, 21841, 21851, 21859, 21863, 21871, 21881, 21893, 21911, 21929, 21937, 21943, 21961, 21977, 21991, 21997,
     22003, 22013, 22027, 22031, 22037, 22039, 22051, 22063, 22067, 22073, 22079, 22091, 22093, 22109, 22111, 22123,
     22129, 22133, 22147, 22153, 22157, 22159, 22171, 22189, 22193, 22229, 22247, 22259, 22271, 22273, 22277, 22279,
     22283, 22291, 22303, 22307, 22343, 22349, 22367, 22369, 22381, 22391, 22397, 22409, 22433, 22441, 22447, 22453,
     22469, 22481, 22483, 22501, 22511, 22531, 22541, 22543, 22549, 22567, 22571, 22573, 22613, 22619, 22621, 22637,
     22639, 22643, 22651, 22669, 22679, 22691, 22697, 22699, 22709, 22717, 22721, 22727, 22739, 22741, 22751, 22769,
     22777, 22783, 22787, 22807, 22811, 22817, 22853, 22859, 22861, 22871, 22877, 22901, 22907, 22921, 22937, 22943,
     22961, 22963, 22973, 22993, 23003, 23011, 23017, 23021, 23027, 23029, 23039, 23041, 23053, 23057, 23059, 23063,
     23071, 23081, 23087, 23099, 23117, 23131, 23143, 23159, 23167, 23173, 23189, 23197, 23201, 23203, 23209, 23227],
    [23251, 23269, 23279, 23291, 23293, 23297, 23311, 23321, 23327, 23333, 23339, 23357, 23369, 23371, 23399, 23417,
     23431, 23447, 23459, 23473, 23497, 23509, 23531, 23537, 23539, 23549, 23557, 23561, 23563, 23567, 23581, 23593,
     23599, 23603, 23609, 23623, 23627, 23629, 23633, 23663, 23669, 23671, 23677, 23687, 23689, 23719, 23741, 23743,
     23747, 23753, 23761, 23767, 23773, 23789, 23801, 23813, 23819, 23827, 23831, 23833, 23857, 23869, 23873, 23879,
     23887, 23893, 23899, 23909, 23911, 23917, 23929, 23957, 23971, 23977, 23981, 23993, 24001, 24007, 24019, 24023,
     24029, 24043, 24049, 24061, 24071, 24077, 24083, 24091, 24097, 24103, 24107, 24109, 24113, 24121, 24133, 24137,
     24151, 24169, 24179, 24181, 24197, 24203, 24223, 24229, 24239, 24247, 24251, 24281, 24317, 24329, 24337, 24359,
     24371, 24373, 24379, 24391, 24407, 24413, 24419, 24421, 24439, 24443, 24469, 24473, 24481, 24499, 24509, 24517,
     24527, 24533, 24547, 24551, 24571, 24593, 24611, 24623, 24631, 24659, 24671, 24677, 24683, 24691, 24697, 24709],
    [24733, 24749, 24763, 24767, 24781, 24793, 24799, 24809, 24821, 24841, 24847, 24851, 24859, 24877, 24889, 24907,
     24917, 24919, 24923, 24943, 24953, 24967, 24971, 24977, 24979, 24989, 25013, 25031, 25033, 25037, 25057, 25073,
     25087, 25097, 25111, 25117, 25121, 25127, 25147, 25153, 25163, 25169, 25171, 25183, 25189, 25219, 25229, 25237,
     25243, 25247, 25253, 25261, 25301, 25303, 25307, 25309, 25321, 25339, 25343, 25349, 25357, 25367, 25373, 25391,
     25409, 25411, 25423, 25439, 25447, 25453, 25457, 25463, 25469, 25471, 25523, 25537, 25541, 25561, 25577, 25579,
     25583, 25589, 25601, 25603, 25609, 25621, 25633, 25639, 25643, 25657, 25667, 25673, 25679, 25693, 25703, 25717,
     25733, 25741, 25747, 25759, 25763, 25771, 25793, 25799, 25801, 25819, 25841, 25847, 25849, 25867, 25873, 25889,
     25903, 25913, 25919, 25931, 25933, 25939, 25943, 25951, 25969, 25981, 25997, 25999, 26003, 26017, 26021, 26029,
     26041, 26053, 26083, 26099, 26107, 26111, 26113, 26119, 26141, 26153, 26161, 26171, 26177, 26183, 26189, 26203],
    [26209, 26227, 26237, 26249, 26251, 26261, 26263, 26267, 26293, 26297, 26309, 26317, 26321, 26339, 26347, 26357,
     26371, 26387, 26393, 26399, 26407, 26417, 26423, 26431, 26437, 26449, 26459, 26479, 26489, 26497, 26501, 26513,
     26539, 26557, 26561, 26573, 26591, 26597, 26627, 26633, 26641, 26647, 26669, 26681, 26683, 26687, 26693, 26699,
     26701, 26711, 26713, 26717, 26723, 26729, 26731, 26737, 26759, 26777, 26783, 26801, 26813, 26821, 26833, 26839,
     26849, 26861, 26863, 26879, 26881, 26891, 26893, 26903, 26921, 26927, 26947, 26951, 26953, 26959, 26981, 26987,
     26993, 27011, 27017, 27031, 27043, 27059, 27061, 27067, 27073, 27077, 27091, 27103, 27107, 27109, 27127, 27143,
     27179, 27191, 27197, 27211, 27239, 27241, 27253, 27259, 27271, 27277, 27281, 27283, 27299, 27329, 27337, 27361,
     27367, 27397, 27407, 27409, 27427, 27431, 27437, 27449, 27457, 27479, 27481, 27487, 27509, 27527, 27529, 27539,
     27541, 27551, 27581, 27583, 27611, 27617, 27631, 27647, 27653, 27673, 27689, 27691, 27697, 27701, 27733, 27737],
    [27739, 27743, 27749, 27751, 27763, 27767, 27773, 27779, 27791, 27793, 27799, 27803, 27809, 27817, 27823, 27827,
     27847, 27851, 27883, 27893, 27901, 27917, 27919, 27941, 27943, 27947, 27953, 27961, 27967, 27983, 27997, 28001,
     28019, 28027, 28031, 28051, 28057, 28069, 28081, 28087, 28097, 28099, 28109, 28111, 28123, 28151, 28163, 28181,
     28183, 28201, 28211, 28219, 28229, 28277, 28279, 28283, 28289, 28297, 28307, 28309, 28319, 28349, 28351, 28387,
     28393, 28403, 28409, 28411, 28429, 28433, 28439, 28447, 28463, 28477, 28493, 28499, 28513, 28517, 28537, 28541,
     28547, 28549, 28559, 28571, 28573, 28579, 28591, 28597, 28603, 28607, 28619, 28621, 28627, 28631, 28643, 28649,
     28657, 28661, 28663, 28669, 28687, 28697, 28703, 28711, 28723, 28729, 28751, 28753, 28759, 28771, 28789, 28793,
     28807, 28813, 28817, 28837, 28843, 28859, 28867, 28871, 28879, 28901, 28909, 28921, 28927, 28933, 28949, 28961,
     28979, 29009, 29017, 29021, 29023, 29027, 29033, 29059, 29063, 29077, 29101, 29123, 29129, 29131, 29137, 29147],
    [29153, 29167, 29173, 29179, 29191, 29201, 29207, 29209, 29221, 29231, 29243, 29251, 29269, 29287, 29297, 29303,
     29311, 29327, 29333, 29339, 29347, 29363, 29383, 29387, 29389, 29399, 29401, 29411, 29423, 29429, 29437, 29443,
     29453, 29473, 29483, 29501, 29527, 29531, 29537, 29567, 29569, 29573, 29581, 29587, 29599, 29611, 29629, 29633,
     29641, 29663, 29669, 29671, 29683, 29717, 29723, 29741, 29753, 29759, 29761, 29789, 29803, 29819, 29833, 29837,
     29851, 29863, 29867, 29873, 29879, 29881, 29917, 29921, 29927, 29947, 29959, 29983, 29989]
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma medium_prime_list_exact :
    mediumPrimeList = (List.range 30001).filter (fun n => decide n.Prime) := by
  decide +kernel

private def mediumPrimeTable : Finset ℕ :=
  ⟨(mediumPrimeList : Multiset ℕ), by
    rw [medium_prime_list_exact]
    exact List.Nodup.filter _ List.nodup_range⟩

private lemma medium_table_filter_eq {k : ℕ} (hk : k ≤ 30000)
    (data : ℕ → Prop) [DecidablePred data] :
    (mediumPrimeTable.filter fun p => p < k ∧ data p) =
      (range k).filter (fun p => p.Prime ∧ data p) := by
  ext p
  have hTable : p ∈ mediumPrimeTable ↔ p < 30001 ∧ p.Prime := by
    change p ∈ mediumPrimeList ↔ p < 30001 ∧ p.Prime
    rw [medium_prime_list_exact, List.mem_filter, List.mem_range, decide_eq_true_eq]
  simp only [mem_filter,mem_range,hTable]
  constructor
  · rintro ⟨⟨_,hp⟩,hpK,hd⟩
    exact ⟨hpK,hp,hd⟩
  · rintro ⟨hpK,hp,hd⟩
    exact ⟨⟨by omega,hp⟩,hpK,hd⟩

private def fastMediumHigh (k c : ℕ) : Finset ℕ :=
  mediumPrimeTable.filter fun p => p < k ∧ c < p

private def fastMediumLow (k c : ℕ) : Finset ℕ :=
  mediumPrimeTable.filter fun p => p < k ∧ p ≤ c

private def fastMediumMiddle (k c d : ℕ) : Finset ℕ :=
  mediumPrimeTable.filter fun p => p < k ∧ c < p ∧ p ≤ d

private def fastMediumPairs (k c d : ℕ) : Finset (ℕ × ℕ) :=
  ((fastMediumMiddle k c d).product (fastMediumMiddle k c d)).filter fun z => z.1 ≤ z.2

private lemma fast_medium_high_eq {k c : ℕ} (hk : k ≤ 30000) :
    fastMediumHigh k c = highPrimes k c := medium_table_filter_eq hk (c < ·)

private lemma fast_medium_low_eq {k c : ℕ} (hk : k ≤ 30000) :
    fastMediumLow k c = lowPrimes k c := medium_table_filter_eq hk (· ≤ c)

private lemma fast_medium_middle_eq {k c d : ℕ} (hk : k ≤ 30000) :
    fastMediumMiddle k c d = middlePrimes k c d :=
  medium_table_filter_eq hk (fun p => c < p ∧ p ≤ d)

private lemma fast_medium_pairs_eq {k c d : ℕ} (hk : k ≤ 30000) :
    fastMediumPairs k c d = orderedMiddlePairs k c d := by
  unfold fastMediumPairs orderedMiddlePairs
  rw [fast_medium_middle_eq hk]

private abbrev medium_band_numeric_goal (band : MediumBand) : Prop :=
  let F := band.lower -
    ((∑ p ∈ fastMediumHigh band.upper band.highPrime, (band.upper+p-1)/p) +
      ∑ z ∈ fastMediumPairs band.upper band.lowPrime band.highPrime,
        (band.upper+z.1*z.2-1)/(z.1*z.2))
  let M := (fastMediumLow band.upper band.lowPrime).card
  let R := (fastMediumMiddle band.upper band.lowPrime band.highPrime).card
  band.upper ≤ 30000 ∧ 3^M*(R+1)^2 < F*(F-1) ∧ R+1 ≤ F ∧ 5^M*(R+4).choose 4 < (F+3).choose 4 ∧
    (R+5)*6^M ≤ (F+4)*5^M

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma medium_band_numeric : ∀ band ∈ mediumOddBands, medium_band_numeric_goal band := by
  decide +kernel

theorem medium_odd_prime_of_sylvester {n k l : ℕ} (hk : 1001 ≤ k) (hkU : k ≤ 30000)
    (hPrime : l.Prime) (hl : 3 ≤ l)
    (hSylvester : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ t ∈ Ioc n (n+k), t) :
    ∃ p : ℕ, k ≤ p ∧ p.Prime ∧ ¬ l ∣ (∏ t ∈ Ioc n (n+k), t).factorization p := by
  obtain ⟨band, hBand, hLo, hHi⟩ := medium_band_cover hk hkU
  have hNumeric := medium_band_numeric band hBand
  unfold medium_band_numeric_goal at hNumeric
  dsimp only at hNumeric
  rcases hNumeric with ⟨hBandUpper,hNumeric⟩
  rw [fast_medium_high_eq hBandUpper, fast_medium_low_eq hBandUpper,
    fast_medium_middle_eq hBandUpper, fast_medium_pairs_eq hBandUpper] at hNumeric
  let low := band.lowPrime
  let high := band.highPrime
  let M := (lowPrimes band.upper low).card
  let R := (middlePrimes band.upper low high).card
  let F := band.lower -
    ((∑ p ∈ highPrimes band.upper high, (band.upper+p-1)/p) +
      ∑ z ∈ orderedMiddlePairs band.upper low high, (band.upper+z.1*z.2-1)/(z.1*z.2))
  have hLow : lowPrimes k low ⊆ lowPrimes band.upper low := by
    intro p hp
    rcases mem_filter.mp hp with ⟨hpK,ht⟩
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hpK).trans_le hHi), ht⟩
  have hMid : middlePrimes k low high ⊆ middlePrimes band.upper low high := by
    intro p hp
    rcases mem_filter.mp hp with ⟨hpK,ht⟩
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hpK).trans_le hHi), ht⟩
  have hHigh : highPrimes k high ⊆ highPrimes band.upper high := by
    intro p hp
    rcases mem_filter.mp hp with ⟨hpK,ht⟩
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hpK).trans_le hHi), ht⟩
  have hPair : orderedMiddlePairs k low high ⊆ orderedMiddlePairs band.upper low high := by
    intro z hz
    rcases mem_filter.mp hz with ⟨hz',hZ⟩
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hMid (mem_product.mp hz').1,
      hMid (mem_product.mp hz').2⟩, hZ⟩
  have hSum₁ : (∑ p ∈ highPrimes k high, (k+p-1)/p) ≤
      ∑ p ∈ highPrimes band.upper high, (band.upper+p-1)/p := by
    calc
      _ ≤ ∑ p ∈ highPrimes k high, (band.upper+p-1)/p :=
        sum_le_sum (fun p _ => Nat.div_le_div_right (by omega))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hHigh (fun _ _ _ => Nat.zero_le _)
  have hSum₂ : (∑ z ∈ orderedMiddlePairs k low high, (k+z.1*z.2-1)/(z.1*z.2)) ≤
      ∑ z ∈ orderedMiddlePairs band.upper low high, (band.upper+z.1*z.2-1)/(z.1*z.2) := by
    calc
      _ ≤ ∑ z ∈ orderedMiddlePairs k low high, (band.upper+z.1*z.2-1)/(z.1*z.2) :=
        sum_le_sum (fun z _ => Nat.div_le_div_right (by omega))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hPair (fun _ _ _ => Nat.zero_le _)
  have hF : F ≤ mediumLowerBound k low high := by
    dsimp only [F,mediumLowerBound]
    omega
  exact odd_prime_of_medium_certificate (by omega) hPrime hl hSylvester hF
    (show (lowPrimes k low).card ≤ M from card_le_card hLow)
    (show (middlePrimes k low high).card ≤ R from card_le_card hMid)
    hNumeric.1 hNumeric.2.1 hNumeric.2.2.1 hNumeric.2.2.2

end Erdos137PerfectPower
