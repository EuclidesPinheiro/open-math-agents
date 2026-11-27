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

end Erdos137PerfectPower

namespace Erdos137PerfectPower

open Finset

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
  have hInj : Set.InjOn ratio ↑S.offDiag := by
    rintro ⟨i,j⟩ hij ⟨u,v⟩ huv hEq
    obtain ⟨hi,hj,hijNe⟩ := mem_offDiag.mp hij
    obtain ⟨hu,hv,huvNe⟩ := mem_offDiag.mp huv
    have hMod (p : ℕ) (hp : p.Prime) :
        (a i * a v).factorization p % l = (a u * a j).factorization p % l := by
      rw [Nat.factorization_mul (ha i hi) (ha v hv), Nat.factorization_mul (ha u hu) (ha j hj),
        Finsupp.add_apply, Finsupp.add_apply]
      by_cases hP : p ∈ P
      · have hCoord := congrFun hEq (⟨p,hP⟩ : P)
        change ((a i).factorization p : ZMod l) - (a j).factorization p =
          ((a u).factorization p : ZMod l) - (a v).factorization p at hCoord
        have hAdd := sub_eq_sub_iff_add_eq_add.mp hCoord
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa only [Nat.cast_add] using hAdd)
      · simp [hZero i hi p hp hP, hZero j hj p hp hP, hZero u hu p hp hP, hZero v hv p hp hP]
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
  have hCard : S.offDiag.card ≤ Fintype.card (P → ZMod l) := by
    have := Finset.card_le_card_of_injOn ratio
      (fun (r : ℕ × ℕ) (_ : r ∈ S.offDiag) => mem_univ (ratio r)) hInj
    simpa using this
  simpa [Finset.offDiag_card, Fintype.card_fun, Fintype.card_coe, ZMod.card, Nat.mul_sub_left_distrib,
    pow_two, Nat.mul_comm] using hCard

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
  have hActual (s : Sym S d) (i : ℕ) (hi : i ∈ s.val.map Subtype.val) : i ∈ Icc 1 k := by
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hi
    exact hS j.property
  have hFacZero (s : Sym S d) (p : ℕ) (hp : p.Prime) (hpP : p ∉ P) :
      (s.val.map coeff).prod.factorization p = 0 := by
    rw [multiset_prod_factorization _ p]
    · apply Multiset.sum_eq_zero.mpr
      intro e he
      obtain ⟨t,ht,rfl⟩ := Multiset.mem_map.mp he
      obtain ⟨i,_,rfl⟩ := Multiset.mem_map.mp ht
      exact Nat.factorization_eq_zero_of_not_dvd (fun hd => hpP (hSupport i.val i.property
        (Nat.mem_primeFactors.mpr ⟨hp, hd, ha i.val i.property⟩)))
    · intro t ht
      obtain ⟨i,_,rfl⟩ := Multiset.mem_map.mp ht
      exact ha i.val i.property
  have hInj : Function.Injective residue := by
    intro s t h
    have hs : (s.val.map Subtype.val).card = d := (Multiset.card_map _).trans s.property
    have ht : (t.val.map Subtype.val).card = d := (Multiset.card_map _).trans t.property
    apply Subtype.ext
    apply Multiset.map_injective (f := Subtype.val) Subtype.val_injective
    apply distinct_multiset_products_mod_l hk hn hl hTop hRepr _ _
      (hActual s) (hActual t) (hs.trans ht.symm) (hs ▸ hd)
    intro p hp
    simp only [Multiset.map_map]
    change (s.val.map coeff).prod.factorization p % l =
      (t.val.map coeff).prod.factorization p % l
    by_cases hpP : p ∈ P
    · exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (congrFun h ⟨p,hpP⟩)
    · rw [hFacZero s p hp hpP, hFacZero t p hp hpP]
  have hCard := Fintype.card_le_of_injective residue hInj
  simpa [Sym.card_sym_eq_choose, Fintype.card_fun, Fintype.card_coe, ZMod.card] using hCard

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

def smallOddCutoff (k : ℕ) : ℕ :=
  if k < 10 then 3 else if k < 28 then 5 else if k < 77 then 7
  else if k < 143 then 11 else if k < 340 then 13 else if k < 646 then 17 else 19

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma fast_small_odd_certificates : ∀ r : Fin 997,
    let k := r.val+4
    let c := smallOddCutoff k
    let f := k - ∑ p ∈ fastHigh k c, (k+p-1)/p
    let m := (fastLow k c).card
    3^m < f*(f-1) ∧ 0 < f ∧ 5^m < (f+3).choose 4 ∧ 5*6^m ≤ (f+4)*5^m := by
  decide

lemma small_odd_certificates : ∀ r : Fin 997,
    let k := r.val+4
    let c := smallOddCutoff k
    let f := smoothLowerBound k c
    let m := (lowPrimes k c).card
    3^m < f*(f-1) ∧ 0 < f ∧ 5^m < (f+3).choose 4 ∧ 5*6^m ≤ (f+4)*5^m := by
  intro r
  have hk : r.val+4 ≤ 1000 := by omega
  have h := fast_small_odd_certificates r
  dsimp only at h ⊢
  rw [fast_high_eq hk, fast_low_eq hk] at h
  exact h

theorem small_cubic_of_sylvester {n k : ℕ} (hk : 4 ≤ k) (hkUpper : k ≤ 1000)
    (hSylvester : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ t ∈ Ioc n (n+k), t) :
    ∃ p : ℕ, k ≤ p ∧ p.Prime ∧ ¬ 3 ∣ (∏ t ∈ Ioc n (n+k), t).factorization p := by
  by_contra! hAll
  obtain ⟨hN,hTop⟩ := sylvester_schur_power_bounds_of_no_witness (by decide) hSylvester hAll
  obtain ⟨a,x,ha,hRepr,hSupport,_⟩ := normalize_odd_coefficients (by decide) hAll
  obtain ⟨S,hS,hCount,hPrime⟩ := good_smooth_coefficients (smallOddCutoff k) hRepr hSupport
  have hBound := ratio_residue_bound S (lowPrimes k (smallOddCutoff k))
    (by omega) hN (by decide) hTop hRepr hS (fun i hi => ha i (hS hi)) hPrime
  have hNumeric := (small_odd_certificates ⟨k-4, by omega⟩).1
  dsimp only at hNumeric
  rw [show k-4+4 = k by omega] at hNumeric
  have hCountProduct := Nat.mul_le_mul hCount (Nat.sub_le_sub_right hCount 1)
  exact (not_lt_of_ge (hCountProduct.trans hBound)) hNumeric

theorem small_higher_exponent_of_sylvester {n k l : ℕ}
    (hk : 4 ≤ k) (hkUpper : k ≤ 1000) (hl : 5 ≤ l)
    (hSylvester : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ t ∈ Ioc n (n+k), t) :
    ∃ p : ℕ, k ≤ p ∧ p.Prime ∧ ¬ l ∣ (∏ t ∈ Ioc n (n+k), t).factorization p := by
  by_contra! hAll
  obtain ⟨hN,hTop⟩ := sylvester_schur_power_bounds_of_no_witness (by omega) hSylvester hAll
  obtain ⟨a,x,ha,hRepr,hSupport,_⟩ := normalize_odd_coefficients (by omega) hAll
  obtain ⟨S,hS,hCount,hPrime⟩ := good_smooth_coefficients (smallOddCutoff k) hRepr hSupport
  have hBound := smooth_multiset_residue_bound S (lowPrimes k (smallOddCutoff k))
    (by omega) hN (by omega) hTop (d := l-1) (by omega) hRepr hS (fun i hi => ha i (hS hi)) hPrime
  have hNumeric := (small_odd_certificates ⟨k-4, by omega⟩).2
  dsimp only at hNumeric
  rw [show k-4+4 = k by omega] at hNumeric
  have hStrict := smooth_multiset_numeric_induction hl hNumeric.1 hNumeric.2.1 hNumeric.2.2
  have hMono := Nat.choose_le_choose (l-1)
    (show smoothLowerBound k (smallOddCutoff k)+l-2 ≤ S.card+(l-1)-1 by omega)
  exact (not_lt_of_ge (hMono.trans hBound)) hStrict

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

end Erdos137PerfectPower
