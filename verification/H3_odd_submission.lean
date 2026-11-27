import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1_H3_R1
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

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

private def mediumPrimeList : List ℕ := [
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
  907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997,
  1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091,
  1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193,
  1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291,
  1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423,
  1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493,
  1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601,
  1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699,
  1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811,
  1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931,
  1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029,
  2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137,
  2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267,
  2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357,
  2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459,
  2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593,
  2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693,
  2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791,
  2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903,
  2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023,
  3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167,
  3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271,
  3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373,
  3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511,
  3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607,
  3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709,
  3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833,
  3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931,
  3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057,
  4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177,
  4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283,
  4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423,
  4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547,
  4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657,
  4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789,
  4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931,
  4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011,
  5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147,
  5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279,
  5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413,
  5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507,
  5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647,
  5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743,
  5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857,
  5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007,
  6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121,
  6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247,
  6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343,
  6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473,
  6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607,
  6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733,
  6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857,
  6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971,
  6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103,
  7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229,
  7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369,
  7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517,
  7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603,
  7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723,
  7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873,
  7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009,
  8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123,
  8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263,
  8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387,
  8389, 8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537,
  8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663,
  8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753,
  8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867,
  8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011,
  9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151,
  9157, 9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277,
  9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397,
  9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491,
  9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623, 9629, 9631,
  9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767,
  9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871,
  9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973, 10007, 10009, 10037,
  10039, 10061, 10067, 10069, 10079, 10091, 10093, 10099, 10103, 10111, 10133, 10139, 10141, 10151,
  10159, 10163, 10169, 10177, 10181, 10193, 10211, 10223, 10243, 10247, 10253, 10259, 10267, 10271,
  10273, 10289, 10301, 10303, 10313, 10321, 10331, 10333, 10337, 10343, 10357, 10369, 10391, 10399,
  10427, 10429, 10433, 10453, 10457, 10459, 10463, 10477, 10487, 10499, 10501, 10513, 10529, 10531,
  10559, 10567, 10589, 10597, 10601, 10607, 10613, 10627, 10631, 10639, 10651, 10657, 10663, 10667,
  10687, 10691, 10709, 10711, 10723, 10729, 10733, 10739, 10753, 10771, 10781, 10789, 10799, 10831,
  10837, 10847, 10853, 10859, 10861, 10867, 10883, 10889, 10891, 10903, 10909, 10937, 10939, 10949,
  10957, 10973, 10979, 10987, 10993, 11003, 11027, 11047, 11057, 11059, 11069, 11071, 11083, 11087,
  11093, 11113, 11117, 11119, 11131, 11149, 11159, 11161, 11171, 11173, 11177, 11197, 11213, 11239,
  11243, 11251, 11257, 11261, 11273, 11279, 11287, 11299, 11311, 11317, 11321, 11329, 11351, 11353,
  11369, 11383, 11393, 11399, 11411, 11423, 11437, 11443, 11447, 11467, 11471, 11483, 11489, 11491,
  11497, 11503, 11519, 11527, 11549, 11551, 11579, 11587, 11593, 11597, 11617, 11621, 11633, 11657,
  11677, 11681, 11689, 11699, 11701, 11717, 11719, 11731, 11743, 11777, 11779, 11783, 11789, 11801,
  11807, 11813, 11821, 11827, 11831, 11833, 11839, 11863, 11867, 11887, 11897, 11903, 11909, 11923,
  11927, 11933, 11939, 11941, 11953, 11959, 11969, 11971, 11981, 11987, 12007, 12011, 12037, 12041,
  12043, 12049, 12071, 12073, 12097, 12101, 12107, 12109, 12113, 12119, 12143, 12149, 12157, 12161,
  12163, 12197, 12203, 12211, 12227, 12239, 12241, 12251, 12253, 12263, 12269, 12277, 12281, 12289,
  12301, 12323, 12329, 12343, 12347, 12373, 12377, 12379, 12391, 12401, 12409, 12413, 12421, 12433,
  12437, 12451, 12457, 12473, 12479, 12487, 12491, 12497, 12503, 12511, 12517, 12527, 12539, 12541,
  12547, 12553, 12569, 12577, 12583, 12589, 12601, 12611, 12613, 12619, 12637, 12641, 12647, 12653,
  12659, 12671, 12689, 12697, 12703, 12713, 12721, 12739, 12743, 12757, 12763, 12781, 12791, 12799,
  12809, 12821, 12823, 12829, 12841, 12853, 12889, 12893, 12899, 12907, 12911, 12917, 12919, 12923,
  12941, 12953, 12959, 12967, 12973, 12979, 12983, 13001, 13003, 13007, 13009, 13033, 13037, 13043,
  13049, 13063, 13093, 13099, 13103, 13109, 13121, 13127, 13147, 13151, 13159, 13163, 13171, 13177,
  13183, 13187, 13217, 13219, 13229, 13241, 13249, 13259, 13267, 13291, 13297, 13309, 13313, 13327,
  13331, 13337, 13339, 13367, 13381, 13397, 13399, 13411, 13417, 13421, 13441, 13451, 13457, 13463,
  13469, 13477, 13487, 13499, 13513, 13523, 13537, 13553, 13567, 13577, 13591, 13597, 13613, 13619,
  13627, 13633, 13649, 13669, 13679, 13681, 13687, 13691, 13693, 13697, 13709, 13711, 13721, 13723,
  13729, 13751, 13757, 13759, 13763, 13781, 13789, 13799, 13807, 13829, 13831, 13841, 13859, 13873,
  13877, 13879, 13883, 13901, 13903, 13907, 13913, 13921, 13931, 13933, 13963, 13967, 13997, 13999,
  14009, 14011, 14029, 14033, 14051, 14057, 14071, 14081, 14083, 14087, 14107, 14143, 14149, 14153,
  14159, 14173, 14177, 14197, 14207, 14221, 14243, 14249, 14251, 14281, 14293, 14303, 14321, 14323,
  14327, 14341, 14347, 14369, 14387, 14389, 14401, 14407, 14411, 14419, 14423, 14431, 14437, 14447,
  14449, 14461, 14479, 14489, 14503, 14519, 14533, 14537, 14543, 14549, 14551, 14557, 14561, 14563,
  14591, 14593, 14621, 14627, 14629, 14633, 14639, 14653, 14657, 14669, 14683, 14699, 14713, 14717,
  14723, 14731, 14737, 14741, 14747, 14753, 14759, 14767, 14771, 14779, 14783, 14797, 14813, 14821,
  14827, 14831, 14843, 14851, 14867, 14869, 14879, 14887, 14891, 14897, 14923, 14929, 14939, 14947,
  14951, 14957, 14969, 14983, 15013, 15017, 15031, 15053, 15061, 15073, 15077, 15083, 15091, 15101,
  15107, 15121, 15131, 15137, 15139, 15149, 15161, 15173, 15187, 15193, 15199, 15217, 15227, 15233,
  15241, 15259, 15263, 15269, 15271, 15277, 15287, 15289, 15299, 15307, 15313, 15319, 15329, 15331,
  15349, 15359, 15361, 15373, 15377, 15383, 15391, 15401, 15413, 15427, 15439, 15443, 15451, 15461,
  15467, 15473, 15493, 15497, 15511, 15527, 15541, 15551, 15559, 15569, 15581, 15583, 15601, 15607,
  15619, 15629, 15641, 15643, 15647, 15649, 15661, 15667, 15671, 15679, 15683, 15727, 15731, 15733,
  15737, 15739, 15749, 15761, 15767, 15773, 15787, 15791, 15797, 15803, 15809, 15817, 15823, 15859,
  15877, 15881, 15887, 15889, 15901, 15907, 15913, 15919, 15923, 15937, 15959, 15971, 15973, 15991,
  16001, 16007, 16033, 16057, 16061, 16063, 16067, 16069, 16073, 16087, 16091, 16097, 16103, 16111,
  16127, 16139, 16141, 16183, 16187, 16189, 16193, 16217, 16223, 16229, 16231, 16249, 16253, 16267,
  16273, 16301, 16319, 16333, 16339, 16349, 16361, 16363, 16369, 16381, 16411, 16417, 16421, 16427,
  16433, 16447, 16451, 16453, 16477, 16481, 16487, 16493, 16519, 16529, 16547, 16553, 16561, 16567,
  16573, 16603, 16607, 16619, 16631, 16633, 16649, 16651, 16657, 16661, 16673, 16691, 16693, 16699,
  16703, 16729, 16741, 16747, 16759, 16763, 16787, 16811, 16823, 16829, 16831, 16843, 16871, 16879,
  16883, 16889, 16901, 16903, 16921, 16927, 16931, 16937, 16943, 16963, 16979, 16981, 16987, 16993,
  17011, 17021, 17027, 17029, 17033, 17041, 17047, 17053, 17077, 17093, 17099, 17107, 17117, 17123,
  17137, 17159, 17167, 17183, 17189, 17191, 17203, 17207, 17209, 17231, 17239, 17257, 17291, 17293,
  17299, 17317, 17321, 17327, 17333, 17341, 17351, 17359, 17377, 17383, 17387, 17389, 17393, 17401,
  17417, 17419, 17431, 17443, 17449, 17467, 17471, 17477, 17483, 17489, 17491, 17497, 17509, 17519,
  17539, 17551, 17569, 17573, 17579, 17581, 17597, 17599, 17609, 17623, 17627, 17657, 17659, 17669,
  17681, 17683, 17707, 17713, 17729, 17737, 17747, 17749, 17761, 17783, 17789, 17791, 17807, 17827,
  17837, 17839, 17851, 17863, 17881, 17891, 17903, 17909, 17911, 17921, 17923, 17929, 17939, 17957,
  17959, 17971, 17977, 17981, 17987, 17989, 18013, 18041, 18043, 18047, 18049, 18059, 18061, 18077,
  18089, 18097, 18119, 18121, 18127, 18131, 18133, 18143, 18149, 18169, 18181, 18191, 18199, 18211,
  18217, 18223, 18229, 18233, 18251, 18253, 18257, 18269, 18287, 18289, 18301, 18307, 18311, 18313,
  18329, 18341, 18353, 18367, 18371, 18379, 18397, 18401, 18413, 18427, 18433, 18439, 18443, 18451,
  18457, 18461, 18481, 18493, 18503, 18517, 18521, 18523, 18539, 18541, 18553, 18583, 18587, 18593,
  18617, 18637, 18661, 18671, 18679, 18691, 18701, 18713, 18719, 18731, 18743, 18749, 18757, 18773,
  18787, 18793, 18797, 18803, 18839, 18859, 18869, 18899, 18911, 18913, 18917, 18919, 18947, 18959,
  18973, 18979, 19001, 19009, 19013, 19031, 19037, 19051, 19069, 19073, 19079, 19081, 19087, 19121,
  19139, 19141, 19157, 19163, 19181, 19183, 19207, 19211, 19213, 19219, 19231, 19237, 19249, 19259,
  19267, 19273, 19289, 19301, 19309, 19319, 19333, 19373, 19379, 19381, 19387, 19391, 19403, 19417,
  19421, 19423, 19427, 19429, 19433, 19441, 19447, 19457, 19463, 19469, 19471, 19477, 19483, 19489,
  19501, 19507, 19531, 19541, 19543, 19553, 19559, 19571, 19577, 19583, 19597, 19603, 19609, 19661,
  19681, 19687, 19697, 19699, 19709, 19717, 19727, 19739, 19751, 19753, 19759, 19763, 19777, 19793,
  19801, 19813, 19819, 19841, 19843, 19853, 19861, 19867, 19889, 19891, 19913, 19919, 19927, 19937,
  19949, 19961, 19963, 19973, 19979, 19991, 19993, 19997, 20011, 20021, 20023, 20029, 20047, 20051,
  20063, 20071, 20089, 20101, 20107, 20113, 20117, 20123, 20129, 20143, 20147, 20149, 20161, 20173,
  20177, 20183, 20201, 20219, 20231, 20233, 20249, 20261, 20269, 20287, 20297, 20323, 20327, 20333,
  20341, 20347, 20353, 20357, 20359, 20369, 20389, 20393, 20399, 20407, 20411, 20431, 20441, 20443,
  20477, 20479, 20483, 20507, 20509, 20521, 20533, 20543, 20549, 20551, 20563, 20593, 20599, 20611,
  20627, 20639, 20641, 20663, 20681, 20693, 20707, 20717, 20719, 20731, 20743, 20747, 20749, 20753,
  20759, 20771, 20773, 20789, 20807, 20809, 20849, 20857, 20873, 20879, 20887, 20897, 20899, 20903,
  20921, 20929, 20939, 20947, 20959, 20963, 20981, 20983, 21001, 21011, 21013, 21017, 21019, 21023,
  21031, 21059, 21061, 21067, 21089, 21101, 21107, 21121, 21139, 21143, 21149, 21157, 21163, 21169,
  21179, 21187, 21191, 21193, 21211, 21221, 21227, 21247, 21269, 21277, 21283, 21313, 21317, 21319,
  21323, 21341, 21347, 21377, 21379, 21383, 21391, 21397, 21401, 21407, 21419, 21433, 21467, 21481,
  21487, 21491, 21493, 21499, 21503, 21517, 21521, 21523, 21529, 21557, 21559, 21563, 21569, 21577,
  21587, 21589, 21599, 21601, 21611, 21613, 21617, 21647, 21649, 21661, 21673, 21683, 21701, 21713,
  21727, 21737, 21739, 21751, 21757, 21767, 21773, 21787, 21799, 21803, 21817, 21821, 21839, 21841,
  21851, 21859, 21863, 21871, 21881, 21893, 21911, 21929, 21937, 21943, 21961, 21977, 21991, 21997,
  22003, 22013, 22027, 22031, 22037, 22039, 22051, 22063, 22067, 22073, 22079, 22091, 22093, 22109,
  22111, 22123, 22129, 22133, 22147, 22153, 22157, 22159, 22171, 22189, 22193, 22229, 22247, 22259,
  22271, 22273, 22277, 22279, 22283, 22291, 22303, 22307, 22343, 22349, 22367, 22369, 22381, 22391,
  22397, 22409, 22433, 22441, 22447, 22453, 22469, 22481, 22483, 22501, 22511, 22531, 22541, 22543,
  22549, 22567, 22571, 22573, 22613, 22619, 22621, 22637, 22639, 22643, 22651, 22669, 22679, 22691,
  22697, 22699, 22709, 22717, 22721, 22727, 22739, 22741, 22751, 22769, 22777, 22783, 22787, 22807,
  22811, 22817, 22853, 22859, 22861, 22871, 22877, 22901, 22907, 22921, 22937, 22943, 22961, 22963,
  22973, 22993, 23003, 23011, 23017, 23021, 23027, 23029, 23039, 23041, 23053, 23057, 23059, 23063,
  23071, 23081, 23087, 23099, 23117, 23131, 23143, 23159, 23167, 23173, 23189, 23197, 23201, 23203,
  23209, 23227, 23251, 23269, 23279, 23291, 23293, 23297, 23311, 23321, 23327, 23333, 23339, 23357,
  23369, 23371, 23399, 23417, 23431, 23447, 23459, 23473, 23497, 23509, 23531, 23537, 23539, 23549,
  23557, 23561, 23563, 23567, 23581, 23593, 23599, 23603, 23609, 23623, 23627, 23629, 23633, 23663,
  23669, 23671, 23677, 23687, 23689, 23719, 23741, 23743, 23747, 23753, 23761, 23767, 23773, 23789,
  23801, 23813, 23819, 23827, 23831, 23833, 23857, 23869, 23873, 23879, 23887, 23893, 23899, 23909,
  23911, 23917, 23929, 23957, 23971, 23977, 23981, 23993, 24001, 24007, 24019, 24023, 24029, 24043,
  24049, 24061, 24071, 24077, 24083, 24091, 24097, 24103, 24107, 24109, 24113, 24121, 24133, 24137,
  24151, 24169, 24179, 24181, 24197, 24203, 24223, 24229, 24239, 24247, 24251, 24281, 24317, 24329,
  24337, 24359, 24371, 24373, 24379, 24391, 24407, 24413, 24419, 24421, 24439, 24443, 24469, 24473,
  24481, 24499, 24509, 24517, 24527, 24533, 24547, 24551, 24571, 24593, 24611, 24623, 24631, 24659,
  24671, 24677, 24683, 24691, 24697, 24709, 24733, 24749, 24763, 24767, 24781, 24793, 24799, 24809,
  24821, 24841, 24847, 24851, 24859, 24877, 24889, 24907, 24917, 24919, 24923, 24943, 24953, 24967,
  24971, 24977, 24979, 24989, 25013, 25031, 25033, 25037, 25057, 25073, 25087, 25097, 25111, 25117,
  25121, 25127, 25147, 25153, 25163, 25169, 25171, 25183, 25189, 25219, 25229, 25237, 25243, 25247,
  25253, 25261, 25301, 25303, 25307, 25309, 25321, 25339, 25343, 25349, 25357, 25367, 25373, 25391,
  25409, 25411, 25423, 25439, 25447, 25453, 25457, 25463, 25469, 25471, 25523, 25537, 25541, 25561,
  25577, 25579, 25583, 25589, 25601, 25603, 25609, 25621, 25633, 25639, 25643, 25657, 25667, 25673,
  25679, 25693, 25703, 25717, 25733, 25741, 25747, 25759, 25763, 25771, 25793, 25799, 25801, 25819,
  25841, 25847, 25849, 25867, 25873, 25889, 25903, 25913, 25919, 25931, 25933, 25939, 25943, 25951,
  25969, 25981, 25997, 25999, 26003, 26017, 26021, 26029, 26041, 26053, 26083, 26099, 26107, 26111,
  26113, 26119, 26141, 26153, 26161, 26171, 26177, 26183, 26189, 26203, 26209, 26227, 26237, 26249,
  26251, 26261, 26263, 26267, 26293, 26297, 26309, 26317, 26321, 26339, 26347, 26357, 26371, 26387,
  26393, 26399, 26407, 26417, 26423, 26431, 26437, 26449, 26459, 26479, 26489, 26497, 26501, 26513,
  26539, 26557, 26561, 26573, 26591, 26597, 26627, 26633, 26641, 26647, 26669, 26681, 26683, 26687,
  26693, 26699, 26701, 26711, 26713, 26717, 26723, 26729, 26731, 26737, 26759, 26777, 26783, 26801,
  26813, 26821, 26833, 26839, 26849, 26861, 26863, 26879, 26881, 26891, 26893, 26903, 26921, 26927,
  26947, 26951, 26953, 26959, 26981, 26987, 26993, 27011, 27017, 27031, 27043, 27059, 27061, 27067,
  27073, 27077, 27091, 27103, 27107, 27109, 27127, 27143, 27179, 27191, 27197, 27211, 27239, 27241,
  27253, 27259, 27271, 27277, 27281, 27283, 27299, 27329, 27337, 27361, 27367, 27397, 27407, 27409,
  27427, 27431, 27437, 27449, 27457, 27479, 27481, 27487, 27509, 27527, 27529, 27539, 27541, 27551,
  27581, 27583, 27611, 27617, 27631, 27647, 27653, 27673, 27689, 27691, 27697, 27701, 27733, 27737,
  27739, 27743, 27749, 27751, 27763, 27767, 27773, 27779, 27791, 27793, 27799, 27803, 27809, 27817,
  27823, 27827, 27847, 27851, 27883, 27893, 27901, 27917, 27919, 27941, 27943, 27947, 27953, 27961,
  27967, 27983, 27997, 28001, 28019, 28027, 28031, 28051, 28057, 28069, 28081, 28087, 28097, 28099,
  28109, 28111, 28123, 28151, 28163, 28181, 28183, 28201, 28211, 28219, 28229, 28277, 28279, 28283,
  28289, 28297, 28307, 28309, 28319, 28349, 28351, 28387, 28393, 28403, 28409, 28411, 28429, 28433,
  28439, 28447, 28463, 28477, 28493, 28499, 28513, 28517, 28537, 28541, 28547, 28549, 28559, 28571,
  28573, 28579, 28591, 28597, 28603, 28607, 28619, 28621, 28627, 28631, 28643, 28649, 28657, 28661,
  28663, 28669, 28687, 28697, 28703, 28711, 28723, 28729, 28751, 28753, 28759, 28771, 28789, 28793,
  28807, 28813, 28817, 28837, 28843, 28859, 28867, 28871, 28879, 28901, 28909, 28921, 28927, 28933,
  28949, 28961, 28979, 29009, 29017, 29021, 29023, 29027, 29033, 29059, 29063, 29077, 29101, 29123,
  29129, 29131, 29137, 29147, 29153, 29167, 29173, 29179, 29191, 29201, 29207, 29209, 29221, 29231,
  29243, 29251, 29269, 29287, 29297, 29303, 29311, 29327, 29333, 29339, 29347, 29363, 29383, 29387,
  29389, 29399, 29401, 29411, 29423, 29429, 29437, 29443, 29453, 29473, 29483, 29501, 29527, 29531,
  29537, 29567, 29569, 29573, 29581, 29587, 29599, 29611, 29629, 29633, 29641, 29663, 29669, 29671,
  29683, 29717, 29723, 29741, 29753, 29759, 29761, 29789, 29803, 29819, 29833, 29837, 29851, 29863,
  29867, 29873, 29879, 29881, 29917, 29921, 29927, 29947, 29959, 29983, 29989
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma medium_prime_list_exact :
    mediumPrimeList = (List.range 30001).filter (fun n => decide n.Prime) := by
  decide

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
  decide

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
    _ = factorialRun n 30*(30*(n/30+1)) := by ac_rfl
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
    _ = _ := by unfold scalingProduct bottomRun; ac_rfl

lemma numerator_jump (n : ℕ) :
    factorialNumerator (n+30) = factorialNumerator n*topRun n := by
  have hQuot : (n+30)/30 = n/30+1 := by omega
  have hSmall : (n/30+1).factorial = (n/30+1)*(n/30).factorial := Nat.factorial_succ _
  unfold factorialNumerator topRun
  rw [hQuot, hSmall, factorial_extend n 30]
  ac_rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
lemma denominator_jump (n : ℕ) :
    factorialDenominator (n+30) = factorialDenominator n*bottomRun n := by
  unfold factorialDenominator bottomRun
  rw [show (n+30)/2 = n/2+15 by omega,
    show (n+30)/3 = n/3+10 by omega,
    show (n+30)/5 = n/5+6 by omega,
    factorial_extend (n/2) 15,factorial_extend (n/3) 10,factorial_extend (n/5) 6]
  ac_rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
lemma run_ratio {n : ℕ} (hn : 5000 ≤ n) : topRun n*100^30 ≤ bottomRun n*253^30 := by
  have hScaled : (5000*(n+30))^31 ≤ (5030*n)^31 := pow_le_pow_left' (by omega) _
  rw [mul_pow,mul_pow] at hScaled
  have hNumeric : scalingProduct*5030^31*100^30 ≤ 30*5000^31*253^30 := by decide
  have hPos : 0 < 30*5000^31 := by decide
  apply Nat.le_of_mul_le_mul_left (c := 30*5000^31) _ hPos
  calc
    _ = (30*topRun n)*(5000^31*100^30) := by ac_rfl
    _ ≤ (n+30)^31*(5000^31*100^30) := Nat.mul_le_mul_right _ (top_run_upper n)
    _ = (5000^31*(n+30)^31)*100^30 := by ac_rfl
    _ ≤ (5030^31*n^31)*100^30 := Nat.mul_le_mul_right _ hScaled
    _ = n^31*(5030^31*100^30) := by ac_rfl
    _ ≤ (scalingProduct*bottomRun n)*(5030^31*100^30) :=
      Nat.mul_le_mul_right _ (bottom_run_lower n)
    _ = (scalingProduct*5030^31*100^30)*bottomRun n := by ac_rfl
    _ ≤ (30*5000^31*253^30)*bottomRun n := Nat.mul_le_mul_right _ hNumeric
    _ = _ := by ac_rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
lemma factorial_ratio_growth {n : ℕ} (hn : 5000 ≤ n) :
    factorialNumerator (n+30)*factorialDenominator n*100^30 ≤
      factorialDenominator (n+30)*factorialNumerator n*253^30 := by
  rw [numerator_jump,denominator_jump]
  calc
    _ = (topRun n*100^30)*(factorialNumerator n*factorialDenominator n) := by ac_rfl
    _ ≤ (bottomRun n*253^30)*(factorialNumerator n*factorialDenominator n) :=
      Nat.mul_le_mul_right _ (run_ratio hn)
    _ = _ := by ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma factorial_ratio_base : ∀ r : Fin 30,
    factorialNumerator (5000+r.val)*100^(5000+r.val) ≤
      factorialDenominator (5000+r.val)*253^(5000+r.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem factorial_ratio_upper {n : ℕ} (hn : 5000 ≤ n) :
    factorialNumerator n*100^n ≤ factorialDenominator n*253^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hSmall : n < 5030
    · have h := factorial_ratio_base ⟨n-5000,by omega⟩
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
      apply Nat.le_of_mul_le_mul_right (c := factorialDenominator k) _ hPos
      calc
        _ = (factorialNumerator (k+30)*factorialDenominator k*100^30)*100^k := by ac_rfl
        _ ≤ (factorialDenominator (k+30)*factorialNumerator k*253^30)*100^k :=
          Nat.mul_le_mul_right _ hGain
        _ = (factorialDenominator (k+30)*253^30)*(factorialNumerator k*100^k) := by ac_rfl
        _ ≤ (factorialDenominator (k+30)*253^30)*(factorialDenominator k*253^k) :=
          Nat.mul_le_mul_left _ hPrev
        _ = _ := by ac_rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
lemma band_product_upper {n : ℕ} (hn : 5000 ≤ n) :
    (primeBandProduct n : ℚ) ≤ (253/100 : ℚ)^n := by
  have hD := factorial_ratio_contains_prime_band n
  have hLE := Nat.le_of_dvd (Nat.pos_of_ne_zero (numerator_ne_zero n)) hD
  have hBound := (Nat.mul_le_mul_right (100^n) hLE).trans (factorial_ratio_upper hn)
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_primorial_band_bounds :
    ∀ b ∈ smallPrimorialBands, primorial b.2 * 20^b.1 ≤ 61^b.1 := by
  decide +kernel

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

lemma primorial_base (r : Fin 5000) : primorial r.val * 20^r.val ≤ 61^r.val := by
  obtain ⟨b,hb,hlo,hhi⟩ := primorial_band_cover_of_chain 0 r.val smallPrimorialBands
    (by decide) (Nat.zero_le _) r.isLt
  have h : primorial b.2 * 20^b.1 ≤ 61^b.1 := small_primorial_band_bounds b hb
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
theorem primorial_le_61_over_20 (n : ℕ) :
    (primorial n : ℚ) ≤ (61/20 : ℚ)^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hSmall : n < 5000
    · rw [div_pow]
      apply (le_div_iff₀ (by positivity)).2
      have h := primorial_base ⟨n,hSmall⟩
      exact_mod_cast h
    · have hBand := band_product_upper (show 5000 ≤ n by omega)
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
theorem primorial_eighth_le (n : ℕ) : (primorial n)^8 ≤ 2^(13*n) := by
  have h : (primorial n : ℚ)^8 ≤ (2:ℚ)^(13*n) := by
    calc
      _ ≤ ((61/20 : ℚ)^n)^8 := pow_le_pow_left₀ (by positivity) (primorial_le_61_over_20 n) _
      _ = ((61/20 : ℚ)^8)^n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm n 8]
      _ ≤ ((2:ℚ)^13)^n := pow_le_pow_left₀ (by positivity) (by norm_num) _
      _ = _ := by rw [← pow_mul]
  exact_mod_cast h

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

namespace Erdos137OddTail

open Finset

def retainedCount (k : ℕ) : ℕ := k - ((range k).filter Nat.Prime).card

def rankBound (i : ℕ) : ℕ :=
  max i (max ((1260*(i-304)+352)/353) ((21701*(i-1492)+4999)/5000))

lemma rank_self_le (i : ℕ) : i ≤ rankBound i := le_max_left _ _

lemma rank_scaled (i : ℕ) : 21701*(i-1492) ≤ 5000*rankBound i := by
  have h : (21701*(i-1492)+4999)/5000 ≤ rankBound i :=
    (le_max_right _ _).trans (le_max_right _ _)
  omega

set_option maxRecDepth 10000 in
lemma rank_factorial_product (r : ℕ) (hr : 1492 ≤ r) :
    21701^(r-1492) * (r-1492).factorial ≤
      5000^(r-1492) * ∏ i ∈ range r, rankBound (i+1) := by
  have h (d : ℕ) : 21701^d * d.factorial ≤ 5000^d *
      ∏ i ∈ range (1492+d), rankBound (i+1) := by
    induction d with
    | zero =>
      simp only [pow_zero, Nat.factorial_zero, mul_one, one_mul, Nat.add_zero]
      exact one_le_prod' fun i _ => (Nat.succ_pos i).trans_le (rank_self_le (i+1))
    | succ d ih =>
      have hNew : 21701*(d+1) ≤ 5000*rankBound (1492+d+1) := by
        simpa only [show 1492+d+1-1492 = d+1 by omega] using rank_scaled (1492+d+1)
      rw [show 1492+d.succ = (1492+d)+1 by omega, prod_range_succ, pow_succ 21701,
        pow_succ 5000, Nat.factorial_succ]
      calc
        _ = (21701^d*d.factorial)*(21701*(d+1)) := by ac_rfl
        _ ≤ (5000^d*∏ i ∈ range (1492+d), rankBound (i+1))*
              (5000*rankBound (1492+d+1)) := Nat.mul_le_mul ih hNew
        _ = _ := by ac_rfl
  have h' := h (r-1492)
  rwa [show 1492+(r-1492) = r by omega] at h'

lemma factorial_le_factorial_mul_pow (d s k : ℕ) (h : d+s ≤ k) :
    (d+s).factorial ≤ d.factorial*k^s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show d+s.succ = d+s+1 by omega, Nat.factorial_succ, pow_succ]
    exact (Nat.mul_le_mul h (ih (by omega))).trans_eq (by ac_rfl)

set_option maxRecDepth 10000 in
lemma tail_rank_contradiction (k P : ℕ) (hk : 2^21 ≤ k) (hP : P ≤ k)
    (hRatio : 120*(P+1492) ≤ 11*k) (hPower : (k^(P+1492))^12 ≤ 2^(23*k)) :
    (k-1).factorial < ∏ i ∈ range (k-P), rankBound (i+1) := by
  let d := k-P-1492
  have hD : 109*k ≤ 120*d := by dsimp [d]; omega
  have hS : d+(P+1492) = k := by dsimp [d]; omega
  have hUpper : (k-1).factorial ≤ d.factorial*k^(P+1492) :=
    (Nat.factorial_le (by omega)).trans (factorial_le_factorial_mul_pow d (P+1492) k hS.le)
  have hBase : (5000:ℚ)^109*2^230 < 21701^109 := by norm_num
  have hStep : (2:ℚ)^230 < (21701/5000)^109 := by
    rw [div_pow]
    exact (lt_div_iff₀ (by positivity)).2 (by simpa only [mul_comm] using hBase)
  have hPowerQ : ((k:ℚ)^(P+1492))^12 ≤ (2:ℚ)^(23*k) := by exact_mod_cast hPower
  have hStrict : (k:ℚ)^(P+1492) < (21701/5000 : ℚ)^d := by
    apply lt_of_pow_lt_pow_left₀ 120 (by positivity)
    calc
      ((k:ℚ)^(P+1492))^120 = (((k:ℚ)^(P+1492))^12)^10 := by
        simp only [← pow_mul, Nat.mul_assoc]
      _ ≤ ((2:ℚ)^(23*k))^10 := pow_le_pow_left₀ (by positivity) hPowerQ _
      _ = ((2:ℚ)^230)^k := by rw [← pow_mul, ← pow_mul]; congr 1; omega
      _ < ((21701/5000 : ℚ)^109)^k := pow_lt_pow_left₀ hStep (by positivity) (by omega)
      _ = (21701/5000 : ℚ)^(109*k) := by rw [pow_mul]
      _ ≤ (21701/5000 : ℚ)^(d*120) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = ((21701/5000 : ℚ)^d)^120 := pow_mul _ _ _
  have hRank := rank_factorial_product (k-P) (by omega : 1492 ≤ k-P)
  have hRankQ : (21701/5000 : ℚ)^d*(d.factorial : ℚ) ≤
      (∏ i ∈ range (k-P), rankBound (i+1) : ℕ) := by
    rw [div_pow, div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).2
    exact_mod_cast (show 21701^d*d.factorial ≤
      (∏ i ∈ range (k-P), rankBound (i+1))*5000^d by simpa only [d, mul_comm] using hRank)
  have hFinal : ((k-1).factorial : ℚ) < (∏ i ∈ range (k-P), rankBound (i+1) : ℕ) :=
    (show ((k-1).factorial : ℚ) ≤ (d.factorial : ℚ)*(k:ℚ)^(P+1492) by exact_mod_cast hUpper).trans_lt
      ((mul_lt_mul_of_pos_left hStrict (by exact_mod_cast Nat.factorial_pos d)).trans_le
        (by simpa only [mul_comm] using hRankQ))
  exact_mod_cast hFinal

lemma dyadic_exists (k p : ℕ) (hp : 0 < p) : ∃ j : ℕ, k ≤ 2^j*p :=
  ⟨k.log2+1, Nat.lt_log2_self.le.trans (Nat.le_mul_of_pos_right _ hp)⟩

noncomputable def dyadicHeight (k p : ℕ) : ℕ :=
  if hp : 0 < p then Nat.find (dyadic_exists k p hp) else 0

lemma le_dyadic_height (k p : ℕ) (hp : 0 < p) : k ≤ 2^(dyadicHeight k p)*p := by
  unfold dyadicHeight
  rw [dif_pos hp]
  exact Nat.find_spec (dyadic_exists k p hp)

lemma dyadic_height_le (k p i : ℕ) (hp : 0 < p) (hi : k ≤ 2^i*p) : dyadicHeight k p ≤ i := by
  unfold dyadicHeight
  rw [dif_pos hp]
  exact Nat.find_min' (dyadic_exists k p hp) hi

lemma filter_sum_one (S : Finset ℕ) (f : ℕ → Prop) [DecidablePred f] :
    (∑ j ∈ S, if f j then 1 else 0) = (S.filter f).card := by
  rw [← sum_filter]
  simp

lemma height_sum_bound_split (k : ℕ) :
    (∑ p ∈ (k-1).primesLE, dyadicHeight k p) ≤
      (k-1).primesLE.card + ∑ i ∈ range k.log2, (k/2^(i+1)).primesLE.card := by
  let P := (k-1).primesLE
  let J := range (k.log2+1)
  have hHeight (p : ℕ) (hp : p ∈ P) : dyadicHeight k p =
      ∑ i ∈ J, if i < dyadicHeight k p then 1 else 0 := by
    have hp' := (mem_filter.mp hp).2
    have hb := dyadic_height_le k p (k.log2+1) hp'.pos
      (Nat.lt_log2_self.le.trans (Nat.le_mul_of_pos_right _ hp'.pos))
    have hEq : J.filter (· < dyadicHeight k p) = range (dyadicHeight k p) := by
      ext i
      simp only [J, mem_filter, mem_range]
      omega
    rw [filter_sum_one, hEq, card_range]
  calc
    _ = ∑ p ∈ P, ∑ i ∈ J, if i < dyadicHeight k p then 1 else 0 :=
      sum_congr rfl hHeight
    _ = ∑ i ∈ J, ∑ p ∈ P, if i < dyadicHeight k p then 1 else 0 := sum_comm
    _ ≤ _ := by
      dsimp [J]
      rw [sum_range_succ']
      rw [Nat.add_comm P.card]
      apply add_le_add
      · apply sum_le_sum
        intro i _
        rw [filter_sum_one]
        apply card_le_card
        intro p hp
        have hp' := (mem_filter.mp (mem_filter.mp hp).1).2
        have hi := (mem_filter.mp hp).2
        have hPow : 2^(i+1)*p < k := by
          by_contra! h
          exact (not_le_of_gt hi) (dyadic_height_le k p (i+1) hp'.pos h)
        have hDiv : p ≤ k/2^(i+1) :=
          (Nat.le_div_iff_mul_le (by positivity)).2 (by simpa only [mul_comm] using hPow.le)
        exact mem_filter.mpr ⟨mem_range.mpr (by omega), hp'⟩
      · rw [filter_sum_one]
        exact card_filter_le _ _

lemma height_sum_bound (k : ℕ) :
    (∑ p ∈ (k-1).primesLE, dyadicHeight k p) ≤
      ∑ i ∈ range (k.log2+1), (k/2^i).primesLE.card := by
  apply (height_sum_bound_split k).trans
  rw [sum_range_succ', pow_zero, Nat.div_one]
  have h := card_le_card (Nat.primesLE_mono (Nat.sub_le k 1))
  omega

lemma pow_prime_card_le_mul_primorial (k : ℕ) : k^((k-1).primesLE.card) ≤
    2^(∑ p ∈ (k-1).primesLE, dyadicHeight k p)*primorial (k-1) := by
  rw [primorial_eq_prod_primesLE, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  calc
    _ = ∏ _ ∈ (k-1).primesLE, k := (prod_const _).symm
    _ ≤ _ := prod_le_prod' fun p hp => le_dyadic_height k p (Nat.mem_primesLE.mp hp).2.pos

def dyadicPrimeBound (n : ℕ) (countUpper : ℕ → ℕ) : ℕ :=
  (104*(n-1) + 64*(∑ j ∈ range n.log2, countUpper (n/2^(j+1)))) / ((n^64).log2-64)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma dyadic_prime_bound_valid {n : ℕ} (hn : 3 ≤ n) (countUpper : ℕ → ℕ)
    (hCount : ∀ m, m.primesLE.card ≤ countUpper m)
    (hPrimorial : ∀ m : ℕ, (primorial m)^8 ≤ 2^(13*m)) :
    (n-1).primesLE.card ≤ dyadicPrimeBound n countUpper := by
  let P := (n-1).primesLE.card
  let w := ∑ p ∈ (n-1).primesLE, dyadicHeight n p
  let b := ∑ j ∈ range n.log2, countUpper (n/2^(j+1))
  let f := (n^64).log2
  have hW : w ≤ P+b := (height_sum_bound_split n).trans
    (Nat.add_le_add_left (sum_le_sum (fun j _ => hCount _)) _)
  have hBound : (n^P)^8 ≤ 2^(8*w+13*(n-1)) := by
    calc
      _ ≤ (2^w*primorial (n-1))^8 := pow_le_pow_left' (pow_prime_card_le_mul_primorial n) _
      _ = 2^(w*8)*(primorial (n-1))^8 := by rw [mul_pow, ← pow_mul]
      _ ≤ 2^(w*8)*2^(13*(n-1)) := Nat.mul_le_mul_left _ (hPrimorial _)
      _ = _ := by rw [pow_add, Nat.mul_comm 8]
  have hLower : 2^f ≤ n^64 := Nat.log2_self_le (by positivity)
  have hPow : 2^(f*P) ≤ 2^(64*w+104*(n-1)) := by
    calc
      _ = (2^f)^P := pow_mul _ _ _
      _ ≤ (n^64)^P := pow_le_pow_left' hLower _
      _ = ((n^P)^8)^8 := by simp only [← pow_mul]; congr 1; omega
      _ ≤ (2^(8*w+13*(n-1)))^8 := pow_le_pow_left' hBound _
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hExp : f*P ≤ 64*w+104*(n-1) := by
    by_contra! h
    exact (not_lt_of_ge hPow) (Nat.pow_lt_pow_right (by decide) h)
  have hF : 64 < f := by
    apply (Nat.le_log2 (by positivity : n^64 ≠ 0)).2
    exact (show (2:ℕ)^65 ≤ 3^64 by decide).trans (pow_le_pow_left' hn _)
  have hLin : (f-64)*P ≤ 104*(n-1) + 64*b := by
    have hEq : f*P = (f-64)*P+64*P := by
      conv_lhs => rw [show f = (f-64)+64 by omega,Nat.add_mul]
    omega
  exact (Nat.le_div_iff_mul_le (by omega : 0 < f-64)).2 (by simpa only [Nat.mul_comm (f-64)] using hLin)

lemma sum_dyadic_div_le (k e : ℕ) : (∑ j ∈ range e, k/2^j) ≤ 2*k := by
  induction e generalizing k with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ']
    have h : (∑ j ∈ range e, k/2^(j+1)) = ∑ j ∈ range e, (k/2)/2^j := by
      apply sum_congr rfl
      intro j _
      rw [pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm 2]
    rw [h, pow_zero, Nat.div_one]
    have := ih (k/2)
    omega

lemma dyadic_exponential_absorption (C : ℕ) (hC : C*22 ≤ 2^21) (e : ℕ) (he : 21 ≤ e) :
    C*(e+1) ≤ 2^e := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  clear he
  induction d with
  | zero => exact hC
  | succ d ih =>
    have hStep : C*(21+d+1+1) ≤ 2*(C*(21+d+1)) := by nlinarith
    rw [show 21+d.succ = (21+d)+1 by omega,pow_succ]
    exact hStep.trans (by simpa only [mul_comm] using Nat.mul_le_mul_left 2 ih)

lemma dyadic_budget_arithmetic {k P e w : ℕ} (hk : 2097152 ≤ k)
    (hw : 128*w ≤ 26*k+857600*(e+1)) (hA : 93800*(e+1) ≤ k)
    (hB : 89520*(e+1) ≤ k) (hP : 168*P ≤ 8*w+13*k) :
    120*(P+1492) ≤ 11*k ∧ 12*(8*w+13*k+11936*(e+1)) ≤ 184*k := by
  have hw' : 448*w ≤ 123*k := by omega
  have hp' : 9408*P ≤ 851*k := by omega
  exact ⟨by omega, by omega⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma tail_from_prime_estimates (k : ℕ) (hk : 2^21 ≤ k)
    (hPrimorial : ∀ n : ℕ, (primorial n)^8 ≤ 2^(13*n))
    (hPrimeCount : ∀ n : ℕ, 128*n.primesLE.card ≤ 13*n+128*6700) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) := by
  let P := ((range k).filter Nat.Prime).card
  let e := k.log2
  let w := ∑ p ∈ (k-1).primesLE, dyadicHeight k p
  have hK : 0 < k := by omega
  have hProd : (k-1).primesLE = (range k).filter Nat.Prime := by
    unfold Nat.primesLE Nat.primesBelow
    rw [show k-1+1 = k by omega]
  have hP : P ≤ k := by
    simpa only [P,card_range] using card_filter_le (s := range k) Nat.Prime
  have hBounds := (Nat.log2_eq_iff hK.ne').mp (show k.log2 = e from rfl)
  have he : 21 ≤ e := (Nat.le_log2 hK.ne').2 hk
  have hAbsorb : 14*6700*(e+1) ≤ k := (dyadic_exponential_absorption (14*6700) (by decide) e he).trans hBounds.1
  have hOffset : 60*1492*(e+1) ≤ k := (dyadic_exponential_absorption (60*1492) (by decide) e he).trans hBounds.1
  have hW : 128*w ≤ 26*k+128*6700*(e+1) := by
    calc
      _ ≤ 128*(∑ j ∈ range (e+1), (k/2^j).primesLE.card) :=
        Nat.mul_le_mul_left 128 (height_sum_bound k)
      _ = ∑ j ∈ range (e+1), 128*(k/2^j).primesLE.card := by rw [mul_sum]
      _ ≤ ∑ j ∈ range (e+1), (13*(k/2^j)+128*6700) := sum_le_sum (fun j _ => hPrimeCount _)
      _ = 13*(∑ j ∈ range (e+1), k/2^j)+128*6700*(e+1) := by
        simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul, Nat.cast_id]
        rw [Nat.mul_comm (e+1)]
      _ ≤ _ := by
        simpa only [← Nat.mul_assoc] using Nat.add_le_add_right
          (Nat.mul_le_mul_left 13 (sum_dyadic_div_le k (e+1))) (128*6700*(e+1))
  have hKProd : k^P ≤ 2^w*primorial (k-1) := by
    rw [primorial_eq_prod_primesLE, show 2^w = ∏ p ∈ (k-1).primesLE, 2^(dyadicHeight k p) by
      exact (Finset.prod_pow_eq_pow_sum _ _ _).symm, ← Finset.prod_mul_distrib]
    calc
      _ = ∏ _ ∈ (k-1).primesLE, k := by rw [prod_const, hProd]
      _ ≤ _ := prod_le_prod' fun p hp => le_dyadic_height k p (mem_filter.mp hp).2.pos
  have hK8 : (k^P)^8 ≤ 2^(8*w+13*k) := by
    calc
      _ ≤ (2^w*primorial (k-1))^8 := pow_le_pow_left' hKProd _
      _ = 2^(w*8)*(primorial (k-1))^8 := by rw [mul_pow, ← pow_mul]
      _ ≤ 2^(w*8)*2^(13*(k-1)) := Nat.mul_le_mul_left _ (hPrimorial _)
      _ = 2^(w*8+13*(k-1)) := by rw [pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hPi : 168*P ≤ 8*w+13*k := by
    have hh : (2^21 : ℕ)^(P*8) ≤ 2^(8*w+13*k) :=
      (pow_le_pow_left' hk _).trans (by simpa only [pow_mul] using hK8)
    rw [← pow_mul] at hh
    by_contra! h
    exact (not_lt_of_ge hh) (Nat.pow_lt_pow_right (by decide) (by omega))
  obtain ⟨hCoeff,hExp⟩ := dyadic_budget_arithmetic (k := k) (P := P) (e := e) (w := w) hk
    hW hAbsorb hOffset hPi
  have hQ : (k^(P+1492))^8 ≤ 2^(8*w+13*k+8*1492*(e+1)) := by
    have hKExtra : (k^1492)^8 ≤ 2^(8*1492*(e+1)) := by
      calc
        _ ≤ ((2^(e+1))^1492)^8 := pow_le_pow_left' (pow_le_pow_left' hBounds.2.le _) _
        _ = _ := by simp only [← pow_mul]; congr 1; omega
    rw [pow_add, mul_pow, pow_add]
    exact Nat.mul_le_mul hK8 hKExtra
  have hPower : (k^(P+1492))^12 ≤ 2^(23*k) := by
    have hh : ((k^(P+1492))^12)^8 ≤ (2^(23*k))^8 := by
      calc
        _ = ((k^(P+1492))^8)^12 := by simp only [← pow_mul]; rfl
        _ ≤ (2^(8*w+13*k+8*1492*(e+1)))^12 := pow_le_pow_left' hQ _
        _ ≤ (2^(23*k))^8 := by
          rw [← pow_mul, ← pow_mul]
          exact Nat.pow_le_pow_right (by decide) (by omega)
    by_contra! h
    exact (not_lt_of_ge hh) (Nat.pow_lt_pow_left h (by decide))
  exact tail_rank_contradiction k P hk hP hCoeff hPower

end Erdos137OddTail

namespace Erdos137OddBridge

open Finset

def rankBound (i : ℕ) : ℕ :=
  max i (max ((1260*(i-304)+352)/353) ((21701*(i-1492)+4999)/5000))

def retainedCount (k : ℕ) : ℕ := k - ((range k).filter Nat.Prime).card

lemma retained_count_mono : Monotone retainedCount := by
  have h (k : ℕ) : retainedCount k = ((range k).filter (fun p => ¬p.Prime)).card := by
    unfold retainedCount
    have hCount := card_filter_add_card_filter_not (s := range k) Nat.Prime
    rw [card_range] at hCount
    omega
  intro k m hm
  rw [h,h]
  exact card_le_card (filter_subset_filter _ (range_mono hm))

lemma rank_scaled_first (i : ℕ) : 1260*(i-304) ≤ 353*rankBound i := by
  have h : (1260*(i-304)+352)/353 ≤ rankBound i :=
    (le_max_left _ _).trans (le_max_right _ _)
  omega

lemma rank_scaled_second (i : ℕ) : 21701*(i-1492) ≤ 5000*rankBound i := by
  have h : (21701*(i-1492)+4999)/5000 ≤ rankBound i :=
    (le_max_right _ _).trans (le_max_right _ _)
  omega

lemma extend_rank_power {t i a b c j : ℕ} (ht : 0 < t) (hti : t ≤ i) (ha : a ≤ t)
    (hb : 0 < b) (hWitness : 2^j*(b*t)^64 ≤ (c*(t-a))^64)
    (hRank : c*(i-a) ≤ b*rankBound i) :
    2^j*i^64 ≤ (rankBound i)^64 := by
  have hSub : (t-a)*i ≤ (i-a)*t := by
    have hA := Nat.sub_add_cancel ha
    have hB := Nat.sub_add_cancel (ha.trans hti)
    have hProd := Nat.mul_le_mul_left a hti
    nlinarith
  have hSlope : c*(t-a)*i ≤ b*rankBound i*t :=
    (show c*(t-a)*i ≤ c*(i-a)*t by
      simpa only [mul_assoc] using Nat.mul_le_mul_left c hSub).trans (Nat.mul_le_mul_right t hRank)
  have hGoal : (b*t)^64*(2^j*i^64) ≤ (b*t)^64*(rankBound i)^64 := by
    calc
      _ = (2^j*(b*t)^64)*i^64 := by ac_rfl
      _ ≤ (c*(t-a))^64*i^64 := Nat.mul_le_mul_right _ hWitness
      _ = (c*(t-a)*i)^64 := by rw [← mul_pow]
      _ ≤ (b*rankBound i*t)^64 := pow_le_pow_left' hSlope _
      _ = _ := by rw [show b*rankBound i*t = b*t*rankBound i by ac_rfl, mul_pow]
  exact Nat.le_of_mul_le_mul_left hGoal (by positivity)

lemma rank_power_at {t i j : ℕ} (ht : 0 < t) (hti : t ≤ i)
    (hW : (304 ≤ t ∧ 2^j*(353*t)^64 ≤ (1260*(t-304))^64) ∨
      (1492 ≤ t ∧ 2^j*(5000*t)^64 ≤ (21701*(t-1492))^64)) :
    2^j*i^64 ≤ (rankBound i)^64 := by
  rcases hW with ⟨hA,hW⟩ | ⟨hA,hW⟩
  · exact extend_rank_power ht hti hA (by decide) hW (rank_scaled_first i)
  · exact extend_rank_power ht hti hA (by decide) hW (rank_scaled_second i)

def gainedExponent (thresholds : List ℕ) (r : ℕ) : ℕ :=
  (thresholds.map fun t => r-(t-1)).sum

lemma sum_rank_gains (thresholds : List ℕ) (r : ℕ) :
    gainedExponent thresholds r =
      ∑ i ∈ range r, (thresholds.filter fun t => t ≤ i+1).length := by
  have hCount (t : ℕ) : (∑ i ∈ range r, if t ≤ i+1 then (1:ℕ) else 0) = r-(t-1) := by
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    have hSet : (range r).filter (fun i => t ≤ i+1) = Ico (t-1) r := by
      ext i
      simp only [mem_filter,mem_range,mem_Ico]
      omega
    rw [hSet, Nat.card_Ico]
    simp
  induction thresholds with
  | nil => simp [gainedExponent]
  | cons t ts ih =>
    have hT := hCount t
    simp only [gainedExponent,List.map_cons,List.sum_cons] at ih ⊢
    have hStep (i : ℕ) : ((t::ts).filter fun v => v ≤ i+1).length =
        (if t ≤ i+1 then 1 else 0) + (ts.filter fun v => v ≤ i+1).length := by
      by_cases hti : t ≤ i+1 <;> simp [hti, Nat.add_comm]
    simp_rw [hStep,sum_add_distrib]
    rw [hT, ih]

def carriesRankPower (t j : ℕ) : Prop :=
  0 < t ∧ ((304 ≤ t ∧ 2^j*(353*t)^64 ≤ (1260*(t-304))^64) ∨
    (1492 ≤ t ∧ 2^j*(5000*t)^64 ≤ (21701*(t-1492))^64))

instance (t j : ℕ) : Decidable (carriesRankPower t j) := by
  unfold carriesRankPower
  infer_instance

def RankThresholds (thresholds : List ℕ) (offset : ℕ) : Prop := match thresholds with
  | [] => True
  | t :: ts => carriesRankPower t (offset+1) ∧ RankThresholds ts (offset+1)

instance (thresholds : List ℕ) (offset : ℕ) : Decidable (RankThresholds thresholds offset) := by
  induction thresholds generalizing offset with
  | nil => unfold RankThresholds; infer_instance
  | cons t ts ih =>
    unfold RankThresholds
    letI := ih (offset+1)
    infer_instance

lemma rank_power_of_thresholds (ts : List ℕ) (j i : ℕ) (hT : RankThresholds ts j)
    (hN : 0 < (ts.filter fun t => t ≤ i).length) :
    2^(j+(ts.filter fun t => t ≤ i).length)*i^64 ≤ (rankBound i)^64 := by
  induction ts generalizing j with
  | nil => simpa using hN
  | cons t ts ih =>
    obtain ⟨hW,hTs⟩ := hT
    let r := (ts.filter fun t => t ≤ i).length
    have hCount : ((t::ts).filter fun t => t ≤ i).length = (if t ≤ i then 1 else 0)+r := by
      by_cases h : t ≤ i <;> simp [h,r,Nat.add_comm]
    rw [hCount] at hN ⊢
    by_cases hR : 0 < r
    · apply (Nat.mul_le_mul_right (i^64) (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) ?_)).trans
        (ih (j+1) hTs hR)
      split <;> omega
    · have hLE : t ≤ i := by
        by_contra hh
        rw [if_neg hh] at hN
        omega
      simp only [if_pos hLE, show r = 0 by omega, Nat.add_zero]
      exact rank_power_at hW.1 hLE hW.2

lemma rank_product_power (ts : List ℕ) (r : ℕ) (hT : RankThresholds ts 0) :
    2^(gainedExponent ts r)*(r.factorial)^64 ≤
      (∏ i ∈ range r, rankBound (i+1))^64 := by
  let g := fun i : ℕ => (ts.filter fun t => t ≤ i+1).length
  have hFact : (∏ i ∈ range r, (i+1)) = r.factorial := by
    induction r with
    | zero => simp
    | succ r ih => rw [prod_range_succ, ih, Nat.factorial_succ, Nat.mul_comm]
  rw [sum_rank_gains, ← Finset.prod_pow_eq_pow_sum, ← hFact, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  apply prod_le_prod'
  intro i _
  by_cases hi : 0 < g i
  · simpa only [g,Nat.zero_add] using rank_power_of_thresholds ts 0 (i+1) hT hi
  · simpa [g, show g i = 0 by omega] using
      (pow_le_pow_left' (show i+1 ≤ rankBound (i+1) from le_max_left _ _) 64)

lemma factorial_mul_bound (r d U : ℕ) (h : r+d ≤ U) :
    (r+d).factorial ≤ r.factorial*U^d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show r+d.succ = r+d+1 by omega, Nat.factorial_succ,pow_succ]
    exact (Nat.mul_le_mul h (ih (by omega))).trans_eq (by ac_rfl)

lemma rank_product_on_interval (ts : List ℕ) (lo hi P B k : ℕ)
    (hT : RankThresholds ts 0) (hLo : 3 ≤ lo) (hk₁ : lo ≤ k) (hk₂ : k ≤ hi)
    (hCount : ((range lo).filter Nat.Prime).card ≤ P)
    (hBudget : (hi-1)^64 ≤ 2^B)
    (hGain : (hi-1-(lo-P))*B < gainedExponent ts (lo-P)) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) := by
  let r := lo-P
  have hrK : r ≤ retainedCount k := by
    apply le_trans _ (retained_count_mono hk₁)
    unfold retainedCount
    dsimp [r]
    omega
  have hProd := rank_product_power ts r hT
  by_cases hr : r ≤ hi-1
  · have hUpper : (k-1).factorial ≤ r.factorial*(hi-1)^(hi-1-r) := by
      apply (Nat.factorial_le (by omega : k-1 ≤ hi-1)).trans
      have h := factorial_mul_bound r (hi-1-r) (hi-1) (by omega)
      rwa [show r+(hi-1-r) = hi-1 by omega] at h
    have hRaised : ((k-1).factorial)^64 ≤ 2^((hi-1-r)*B)*(r.factorial)^64 := by
      calc
        _ ≤ (r.factorial*(hi-1)^(hi-1-r))^64 := pow_le_pow_left' hUpper _
        _ = ((hi-1)^64)^(hi-1-r)*(r.factorial)^64 := by
          rw [mul_pow, mul_comm]; congr 1
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ (2^B)^(hi-1-r)*(r.factorial)^64 :=
          Nat.mul_le_mul_right _ (pow_le_pow_left' hBudget _)
        _ = _ := by rw [← pow_mul, Nat.mul_comm B]
    have hL : ((k-1).factorial)^64 < (∏ i ∈ range r, rankBound (i+1))^64 :=
      hRaised.trans_lt ((Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by decide) hGain)
        (by positivity)).trans_le hProd)
    exact (lt_of_pow_lt_pow_left' 64 hL).trans_le (prod_le_prod_of_subset_of_one_le'
      (range_mono hrK) (fun i _ _ => (Nat.succ_pos i).trans_le (le_max_left _ _)))
  · have hFac : (k-1).factorial < r.factorial :=
      Nat.factorial_lt_of_lt (by omega) (by omega)
    have hProd' : r.factorial ≤ ∏ i ∈ range r, rankBound (i+1) := by
      by_contra! h
      have hI := Nat.pow_lt_pow_left h (by decide : (64:ℕ) ≠ 0)
      exact (not_lt_of_ge ((Nat.le_mul_of_pos_left _ (by positivity)).trans hProd)) hI
    exact hFac.trans_le (hProd'.trans (prod_le_prod_of_subset_of_one_le'
      (range_mono hrK) (fun i _ _ => (Nat.succ_pos i).trans_le (le_max_left _ _))))

private def modPowByBits (a e m : ℕ) : ℕ → ℕ
  | 0 => 1 % m
  | fuel+1 =>
      if e = 0 then 1 % m else
        let next := modPowByBits (a*a%m) (e/2) m fuel
        if e%2 = 0 then next else a*next%m

private lemma mod_pow_by_bits_eq (a e m fuel : ℕ) (h : e < 2^fuel) :
    modPowByBits a e m fuel = a^e%m := by
  induction fuel generalizing a e with
  | zero =>
    have he : e = 0 := by simp at h; omega
    simp [modPowByBits,he]
  | succ fuel ih =>
    by_cases he : e = 0
    · simp [modPowByBits,he]
    have hHalf : e/2 < 2^fuel := by rw [pow_succ] at h; omega
    have hRest := ih (a*a%m) (e/2) hHalf
    have hRest' : (a*a%m)^(e/2)%m = a^(2*(e/2))%m := by
      rw [pow_mul, pow_two, ← Nat.pow_mod]
    simp only [modPowByBits,if_neg he,hRest,hRest']
    by_cases hEven : e%2 = 0
    · rw [if_pos hEven, show 2*(e/2) = e by omega]
    · rw [if_neg hEven]
      conv_rhs => rw [show e = 2*(e/2)+1 by omega, pow_succ' a]
      calc
        _ = (a%m*(a^(2*(e/2))%m))%m := by rw [Nat.mul_mod a, Nat.mod_mod]
        _ = _ := (Nat.mul_mod a _ m).symm

def fermatCandidate (n : ℕ) : Prop :=
  n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨
    (7 < n ∧ n.Coprime 210 ∧ modPowByBits 2 (n-1) n n.log2.succ = 1)

instance (n : ℕ) : Decidable (fermatCandidate n) := by
  unfold fermatCandidate
  infer_instance

lemma prime_is_fermat_candidate {p : ℕ} (hp : p.Prime) : fermatCandidate p := by
  by_cases h : p ≤ 7
  · interval_cases p <;> first | decide | exact False.elim ((show ¬Nat.Prime _ by decide) hp)
  unfold fermatCandidate
  right; right; right; right
  have hC : ∀ d : ℕ, 0 < d → d < p → p.Coprime d := fun d hd hd' =>
    (hp.coprime_iff_not_dvd).2 (fun hD => (not_le_of_gt hd') (Nat.le_of_dvd hd hD))
  have hSmall : p.Coprime 210 := by
    change p.Coprime (2*3*5*7)
    exact (((hC 2 (by decide) (by omega)).mul_right (hC 3 (by decide) (by omega))).mul_right
      (hC 5 (by decide) (by omega))).mul_right (hC 7 (by decide) (by omega))
  refine ⟨by omega,hSmall,?_⟩
  have hF : 2^(p-1)%p = 1%p := Nat.ModEq.pow_card_sub_one_eq_one hp (hC 2 (by decide) (by omega)).symm
  rw [mod_pow_by_bits_eq _ _ _ _ (by have := Nat.lt_log2_self (n := p); omega),
    hF, Nat.mod_eq_of_lt (by omega : 1 < p)]

def candidatePrefix (n : ℕ) : Finset ℕ := (range n).filter fermatCandidate

def candidateCount (a b : ℕ) : ℕ := ((range (b-a)).filter fun t => fermatCandidate (a+t)).card

lemma candidate_count_eq (a b : ℕ) : candidateCount a b = ((Ico a b).filter fermatCandidate).card := by
  have hImage : (((range (b-a)).filter fun t => fermatCandidate (a+t)).image (a+·)) =
      (Ico a b).filter fermatCandidate := by
    ext n
    simp only [mem_image,mem_filter,mem_range,mem_Ico]
    constructor
    · rintro ⟨t, ⟨ht,hC⟩,rfl⟩
      exact ⟨⟨by omega,by omega⟩,hC⟩
    · rintro ⟨⟨hA,hB⟩,hC⟩
      exact ⟨n-a,⟨by omega,by simpa only [Nat.add_sub_of_le hA] using hC⟩,Nat.add_sub_of_le hA⟩
  rw [← hImage, card_image_of_injective _ (fun t u he => by omega), candidateCount]

lemma candidate_prefix_add {a b : ℕ} (hab : a ≤ b) :
    (candidatePrefix b).card = (candidatePrefix a).card + candidateCount a b := by
  have hEq : candidatePrefix b = candidatePrefix a ∪ (Ico a b).filter fermatCandidate := by
    ext n
    simp only [candidatePrefix,mem_filter,mem_range,mem_union,mem_Ico]
    grind
  have hDis : Disjoint (candidatePrefix a) ((Ico a b).filter fermatCandidate) := by
    rw [Finset.disjoint_left]
    intro n h₁ h₂
    simp only [candidatePrefix,mem_filter,mem_range,mem_Ico] at h₁ h₂
    omega
  rw [hEq, Finset.card_union_of_disjoint hDis, candidate_count_eq]

structure RankInterval where
  upper : ℕ
  budget : ℕ
  increment : ℕ

def RankIntervals (ts : List ℕ) (start stop available : ℕ) (rows : List RankInterval) : Prop :=
  match rows with
  | [] => stop < start
  | row :: rest =>
      start ≤ row.upper ∧ (row.upper-1)^64 ≤ 2^row.budget ∧
      (row.upper-1-(start-available))*row.budget < gainedExponent ts (start-available) ∧
      candidateCount start (row.upper+1) ≤ row.increment ∧
      RankIntervals ts (row.upper+1) stop (available+row.increment) rest

instance (ts : List ℕ) (start stop available : ℕ) (rows : List RankInterval) :
    Decidable (RankIntervals ts start stop available rows) := by
  induction rows generalizing start available with
  | nil => unfold RankIntervals; infer_instance
  | cons row rest ih =>
    unfold RankIntervals
    letI := ih (row.upper+1) (available+row.increment)
    infer_instance

lemma rank_intervals_bound (ts : List ℕ) (start stop available k : ℕ) (rows : List RankInterval)
    (hT : RankThresholds ts 0) (hStart : 3 ≤ start) (hk : start ≤ k) (hStop : k ≤ stop)
    (hP : (candidatePrefix start).card ≤ available)
    (hRows : RankIntervals ts start stop available rows) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) := by
  induction rows generalizing start available with
  | nil => exact (not_lt_of_ge (hk.trans hStop) hRows).elim
  | cons row rows ih =>
    obtain ⟨hUpper,hBudget,hGain,hInc,hNext⟩ := hRows
    by_cases hK : k ≤ row.upper
    · have hCount : ((range start).filter Nat.Prime).card ≤ available :=
        (card_le_card (show (range start).filter Nat.Prime ⊆ candidatePrefix start from
          fun p hp => mem_filter.mpr ⟨(mem_filter.mp hp).1,prime_is_fermat_candidate (mem_filter.mp hp).2⟩)).trans hP
      exact rank_product_on_interval ts start row.upper available row.budget k hT hStart hk hK
        hCount hBudget hGain
    · apply ih (row.upper+1) (available+row.increment) (by omega) (by omega) _ hNext
      rw [candidate_prefix_add (by omega : start ≤ row.upper+1)]
      exact Nat.add_le_add hP hInc

def countFromIntervals (n start available : ℕ) : List RankInterval → ℕ
  | [] => available
  | row :: rows =>
      if n ≤ start then available else
        countFromIntervals n (row.upper+1) (available+row.increment) rows

lemma count_from_intervals_valid (ts : List ℕ) (start stop available n : ℕ) (rows : List RankInterval)
    (hn : n ≤ stop+1) (hP : (candidatePrefix start).card ≤ available)
    (hRows : RankIntervals ts start stop available rows) :
    (candidatePrefix n).card ≤ countFromIntervals n start available rows := by
  have hMono : Monotone (fun t => (candidatePrefix t).card) := fun a b hab =>
    card_le_card (filter_subset_filter _ (range_mono hab))
  induction rows generalizing start available with
  | nil => exact (hMono (by omega : n ≤ start)).trans hP
  | cons row rs ih =>
    obtain ⟨hUpper,_,_,hInc,hNext⟩ := hRows
    by_cases h : n ≤ start
    · exact (hMono h).trans (by simpa only [countFromIntervals, if_pos h] using hP)
    · rw [countFromIntervals, if_neg h]
      apply ih (row.upper+1) (available+row.increment) _ hNext
      rw [candidate_prefix_add (by omega : start ≤ row.upper+1)]
      exact Nat.add_le_add hP hInc

lemma primes_le_candidates (n : ℕ) : n.primesLE.card ≤ (candidatePrefix (n+1)).card := by
  apply card_le_card
  intro p hp
  obtain ⟨hU,hPrime⟩ := Nat.mem_primesLE.mp hp
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), prime_is_fermat_candidate hPrime⟩

lemma wheel_prime_count_upper (n : ℕ) : n.primesLE.card ≤ 211+48*((n+1)/210+1) := by
  have hBase : 211.primeCounting' ≤ 211 := by
    rw [← Nat.primesBelow_card_eq_primeCounting',Nat.primesBelow_eq_filter_range]
    exact (card_filter_le _ _).trans_eq (card_range _)
  by_cases h : 211 ≤ n+1
  · have hAdd := Nat.primeCounting'_add_le (a := 210) (k := 211) (by decide) (by decide) (n+1-211)
    have hTotient : Nat.totient 210 = 48 := by decide
    rw [show 211+(n+1-211) = n+1 by omega,hTotient] at hAdd
    rw [Nat.primesLE,Nat.primesBelow_card_eq_primeCounting']
    have hQ := Nat.div_le_div_right (show n+1-211 ≤ n+1 by omega)
    omega
  · have hMono := Nat.monotone_primeCounting' (show n+1 ≤ 211 by omega)
    rw [Nat.primesLE,Nat.primesBelow_card_eq_primeCounting']
    omega

def NumericRankIntervals (ts : List ℕ) (estimate : ℕ → ℕ) (start stop : ℕ) : List (ℕ × ℕ) → Prop
  | [] => stop < start
  | row :: rest =>
      start ≤ row.1 ∧ (row.1-1)^64 ≤ 2^row.2 ∧
      (row.1-1-(start-estimate start))*row.2 < gainedExponent ts (start-estimate start) ∧
      NumericRankIntervals ts estimate (row.1+1) stop rest

instance (ts : List ℕ) (estimate : ℕ → ℕ) (start stop : ℕ) (rows : List (ℕ × ℕ)) :
    Decidable (NumericRankIntervals ts estimate start stop rows) := by
  induction rows generalizing start with
  | nil => unfold NumericRankIntervals; infer_instance
  | cons row rest ih =>
    unfold NumericRankIntervals
    letI := ih (row.1+1)
    infer_instance

lemma numeric_rank_intervals_bound (ts : List ℕ) (estimate : ℕ → ℕ) (start stop k : ℕ)
    (rows : List (ℕ × ℕ)) (hT : RankThresholds ts 0) (hStart : 3 ≤ start) (hk : start ≤ k) (hStop : k ≤ stop)
    (hEstimate : ∀ n, 3 ≤ n → ((range n).filter Nat.Prime).card ≤ estimate n)
    (hRows : NumericRankIntervals ts estimate start stop rows) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) := by
  induction rows generalizing start with
  | nil => exact (not_lt_of_ge (hk.trans hStop) hRows).elim
  | cons row rows ih =>
    obtain ⟨hUpper,hBudget,hGain,hNext⟩ := hRows
    by_cases h : k ≤ row.1
    · exact rank_product_on_interval ts start row.1 (estimate start) row.2 k hT hStart hk h
        (hEstimate _ hStart) hBudget hGain
    · exact ih (row.1+1) (by omega) (by omega) hNext

private def dyadicRankThresholds : List ℕ := [
  425, 426, 428, 430, 432, 434, 436, 438, 440, 442, 445, 447, 449, 452, 454,
  456, 459, 461, 464, 467, 469, 472, 475, 478, 481, 484, 487, 490, 494, 497,
  500, 504, 508, 511, 515, 519, 523, 527, 531, 536, 540, 545, 550, 554, 559,
  565, 570, 575, 581, 587, 593, 599, 605, 612, 619, 626, 633, 641, 648, 656,
  665, 674, 683, 692, 702, 712, 722, 733, 745, 757, 769, 782, 796, 810, 825,
  840, 857, 874, 892, 912, 932, 953, 976, 1000, 1025, 1053, 1082, 1113, 1146, 1181,
  1220, 1261, 1306, 1354, 1407, 1465, 1528, 1598, 1676, 1763, 1860, 1970, 2094, 2238, 2404,
  2600, 2833, 3115, 3463, 3905, 4483, 5273, 6414, 7172, 7482, 7824, 8203, 8626, 9099, 9634,
  10243, 10941, 11752, 12703, 13835, 15205, 16895, 19035, 21830, 25635, 31118, 39702, 55056, 90393, 257409
]

private def dyadicRankIntervals : List RankInterval := [
  ⟨30041, 952, 3⟩, ⟨30081, 953, 3⟩, ⟨30123, 953, 7⟩, ⟨30162, 953, 4⟩,
  ⟨30202, 953, 4⟩, ⟨30243, 953, 4⟩, ⟨30285, 953, 4⟩, ⟨30328, 953, 5⟩,
  ⟨30372, 953, 3⟩, ⟨30415, 954, 3⟩, ⟨30460, 954, 3⟩, ⟨30508, 954, 5⟩,
  ⟨30557, 954, 6⟩, ⟨30606, 954, 3⟩, ⟨30658, 954, 4⟩, ⟨30709, 955, 7⟩,
  ⟨30759, 955, 3⟩, ⟨30812, 955, 5⟩, ⟨30867, 955, 7⟩, ⟨30921, 955, 6⟩,
  ⟨30976, 955, 5⟩, ⟨31033, 955, 5⟩, ⟨31088, 956, 6⟩, ⟨31144, 956, 4⟩,
  ⟨31203, 956, 9⟩, ⟨31260, 956, 8⟩, ⟨31315, 956, 4⟩, ⟨31373, 956, 6⟩,
  ⟨31429, 957, 6⟩, ⟨31485, 957, 3⟩, ⟨31546, 957, 7⟩, ⟨31607, 957, 6⟩,
  ⟨31670, 957, 8⟩, ⟨31728, 958, 5⟩, ⟨31789, 958, 5⟩, ⟨31852, 958, 5⟩,
  ⟨31918, 958, 5⟩, ⟨31987, 958, 4⟩, ⟨32061, 958, 8⟩, ⟨32132, 959, 8⟩,
  ⟨32204, 959, 8⟩, ⟨32277, 959, 6⟩, ⟨32353, 959, 9⟩, ⟨32425, 960, 10⟩,
  ⟨32495, 960, 6⟩, ⟨32568, 960, 8⟩, ⟨32642, 960, 9⟩, ⟨32716, 960, 6⟩,
  ⟨32789, 961, 7⟩, ⟨32864, 961, 7⟩, ⟨32941, 961, 8⟩, ⟨33020, 961, 8⟩,
  ⟨33100, 961, 9⟩, ⟨33177, 962, 6⟩, ⟨33258, 962, 8⟩, ⟨33340, 962, 7⟩,
  ⟨33426, 962, 10⟩, ⟨33508, 963, 8⟩, ⟨33592, 963, 10⟩, ⟨33676, 963, 10⟩,
  ⟨33760, 963, 8⟩, ⟨33846, 963, 9⟩, ⟨33930, 964, 8⟩, ⟨34016, 964, 6⟩,
  ⟨34107, 964, 6⟩, ⟨34203, 964, 9⟩, ⟨34298, 965, 11⟩, ⟨34393, 965, 11⟩,
  ⟨34489, 965, 9⟩, ⟨34587, 965, 9⟩, ⟨34685, 966, 11⟩, ⟨34783, 966, 11⟩,
  ⟨34882, 966, 8⟩, ⟨34981, 967, 9⟩, ⟨35083, 967, 8⟩, ⟨35190, 967, 11⟩,
  ⟨35299, 967, 9⟩, ⟨35409, 968, 12⟩, ⟨35520, 968, 9⟩, ⟨35636, 968, 13⟩,
  ⟨35749, 969, 5⟩, ⟨35871, 969, 13⟩, ⟨35995, 969, 12⟩, ⟨36122, 969, 13⟩,
  ⟨36247, 970, 10⟩, ⟨36378, 970, 13⟩, ⟨36512, 970, 11⟩, ⟨36647, 971, 15⟩,
  ⟨36784, 971, 15⟩, ⟨36918, 972, 14⟩, ⟨37054, 972, 15⟩, ⟨37191, 972, 11⟩,
  ⟨37330, 973, 12⟩, ⟨37474, 973, 13⟩, ⟨37623, 973, 20⟩, ⟨37765, 974, 10⟩,
  ⟨37915, 974, 14⟩, ⟨38069, 974, 13⟩, ⟨38225, 975, 12⟩, ⟨38388, 975, 17⟩,
  ⟨38549, 975, 9⟩, ⟨38722, 976, 20⟩, ⟨38895, 976, 17⟩, ⟨39068, 977, 15⟩,
  ⟨39247, 977, 22⟩, ⟨39420, 978, 16⟩, ⟨39598, 978, 14⟩, ⟨39784, 978, 17⟩,
  ⟨39972, 979, 19⟩, ⟨40163, 979, 19⟩, ⟨40354, 980, 14⟩, ⟨40554, 980, 18⟩,
  ⟨40756, 981, 15⟩, ⟨40968, 981, 23⟩, ⟨41178, 982, 19⟩, ⟨41394, 982, 23⟩,
  ⟨41608, 983, 19⟩, ⟨41829, 983, 22⟩, ⟨42050, 984, 25⟩, ⟨42272, 984, 21⟩,
  ⟨42495, 984, 28⟩, ⟨42716, 985, 20⟩, ⟨42944, 985, 24⟩, ⟨43170, 986, 19⟩,
  ⟨43405, 986, 18⟩, ⟨43646, 987, 21⟩, ⟨43895, 987, 21⟩, ⟨44148, 988, 27⟩,
  ⟨44399, 989, 23⟩, ⟨44658, 989, 25⟩, ⟨44918, 990, 24⟩, ⟨45185, 990, 23⟩,
  ⟨45457, 991, 24⟩, ⟨45738, 991, 24⟩, ⟨46024, 992, 24⟩, ⟨46321, 992, 28⟩,
  ⟨46620, 993, 27⟩, ⟨46923, 994, 31⟩, ⟨47232, 994, 23⟩, ⟨47550, 995, 32⟩,
  ⟨47872, 995, 32⟩, ⟨48197, 996, 29⟩, ⟨48527, 997, 29⟩, ⟨48868, 997, 33⟩,
  ⟨49211, 998, 36⟩, ⟨49554, 999, 32⟩, ⟨49906, 999, 31⟩, ⟨50264, 1000, 37⟩,
  ⟨50621, 1001, 32⟩, ⟨50989, 1001, 30⟩, ⟨51366, 1002, 34⟩, ⟨51749, 1003, 40⟩,
  ⟨52137, 1003, 35⟩, ⟨52531, 1004, 33⟩, ⟨52933, 1005, 37⟩, ⟨53346, 1005, 40⟩,
  ⟨53762, 1006, 37⟩, ⟨54185, 1007, 39⟩, ⟨54614, 1008, 41⟩, ⟨55052, 1008, 38⟩,
  ⟨55499, 1009, 37⟩, ⟨55956, 1010, 48⟩, ⟨56413, 1011, 38⟩, ⟨56886, 1011, 48⟩,
  ⟨57361, 1012, 50⟩, ⟨57835, 1013, 43⟩, ⟨58316, 1014, 45⟩, ⟨58809, 1014, 44⟩,
  ⟨59310, 1015, 47⟩, ⟨59816, 1016, 51⟩, ⟨60324, 1017, 40⟩, ⟨60846, 1018, 47⟩,
  ⟨61383, 1018, 45⟩, ⟨61932, 1019, 48⟩, ⟨62492, 1020, 50⟩, ⟨63061, 1021, 49⟩,
  ⟨63642, 1022, 56⟩, ⟨64229, 1023, 53⟩, ⟨64831, 1023, 47⟩, ⟨65452, 1024, 61⟩,
  ⟨66078, 1025, 59⟩, ⟨66712, 1026, 51⟩, ⟨67363, 1027, 61⟩, ⟨68022, 1028, 65⟩,
  ⟨68686, 1029, 53⟩, ⟨69369, 1030, 58⟩, ⟨70067, 1031, 59⟩, ⟨70781, 1032, 65⟩,
  ⟨71506, 1033, 75⟩, ⟨72240, 1033, 67⟩, ⟨72985, 1034, 67⟩, ⟨73742, 1035, 64⟩,
  ⟨74517, 1036, 68⟩, ⟨75306, 1037, 70⟩, ⟨76110, 1038, 75⟩, ⟨76924, 1039, 69⟩,
  ⟨77756, 1040, 81⟩, ⟨78595, 1041, 70⟩, ⟨79454, 1042, 74⟩, ⟨80331, 1043, 79⟩,
  ⟨81222, 1044, 84⟩, ⟨82124, 1045, 79⟩, ⟨83043, 1046, 81⟩, ⟨83979, 1047, 80⟩,
  ⟨84935, 1048, 83⟩, ⟨85910, 1049, 88⟩, ⟨86891, 1051, 83⟩, ⟨87894, 1052, 93⟩,
  ⟨88910, 1053, 81⟩, ⟨89954, 1054, 95⟩, ⟨91013, 1055, 97⟩, ⟨92087, 1056, 91⟩,
  ⟨93184, 1057, 106⟩, ⟨94290, 1058, 92⟩, ⟨95422, 1059, 106⟩, ⟨96567, 1060, 101⟩,
  ⟨97732, 1061, 96⟩, ⟨98915, 1063, 101⟩, ⟨100122, 1064, 104⟩, ⟨101353, 1065, 106⟩,
  ⟨102609, 1066, 119⟩, ⟨103879, 1067, 95⟩, ⟨105191, 1068, 116⟩, ⟨106526, 1069, 117⟩,
  ⟨107875, 1071, 112⟩, ⟨109256, 1072, 123⟩, ⟨110660, 1073, 120⟩, ⟨112094, 1074, 119⟩,
  ⟨113561, 1075, 130⟩, ⟨115054, 1076, 120⟩, ⟨116574, 1078, 136⟩, ⟨118119, 1079, 133⟩,
  ⟨119694, 1080, 129⟩, ⟨121308, 1081, 141⟩, ⟨122939, 1083, 146⟩, ⟨124596, 1084, 142⟩,
  ⟨126286, 1085, 145⟩, ⟨128009, 1086, 142⟩, ⟨129759, 1088, 156⟩, ⟨131537, 1089, 147⟩,
  ⟨133356, 1090, 159⟩, ⟨135207, 1091, 146⟩, ⟨137094, 1093, 172⟩, ⟨139006, 1094, 162⟩,
  ⟨140957, 1095, 168⟩, ⟨142936, 1096, 164⟩, ⟨144953, 1098, 160⟩, ⟨147023, 1099, 174⟩,
  ⟨149135, 1100, 180⟩, ⟨151274, 1102, 187⟩, ⟨153449, 1103, 189⟩, ⟨155661, 1104, 183⟩,
  ⟨157906, 1106, 186⟩, ⟨160199, 1107, 187⟩, ⟨162545, 1108, 190⟩, ⟨164930, 1110, 201⟩,
  ⟨167362, 1111, 200⟩, ⟨169847, 1112, 195⟩, ⟨172381, 1114, 216⟩, ⟨174961, 1115, 214⟩,
  ⟨177578, 1117, 215⟩, ⟨180251, 1118, 233⟩, ⟨182967, 1119, 220⟩, ⟨185727, 1121, 229⟩,
  ⟨188543, 1122, 235⟩, ⟨191414, 1123, 231⟩, ⟨194333, 1125, 250⟩, ⟨197302, 1126, 241⟩,
  ⟨200318, 1128, 246⟩, ⟨203398, 1129, 250⟩, ⟨206545, 1130, 257⟩, ⟨209739, 1132, 267⟩,
  ⟨212993, 1133, 262⟩, ⟨216299, 1135, 264⟩, ⟨219680, 1136, 275⟩, ⟨223112, 1138, 287⟩,
  ⟨226607, 1139, 281⟩, ⟨230178, 1140, 305⟩, ⟨233786, 1142, 281⟩, ⟨237482, 1143, 286⟩,
  ⟨241248, 1145, 302⟩, ⟨245095, 1146, 321⟩, ⟨248989, 1148, 324⟩, ⟨252953, 1149, 316⟩,
  ⟨256980, 1151, 319⟩, ⟨261097, 1152, 330⟩, ⟨265277, 1154, 332⟩, ⟨269548, 1155, 356⟩,
  ⟨273869, 1157, 336⟩, ⟨278291, 1158, 358⟩, ⟨282791, 1159, 364⟩, ⟨287364, 1161, 362⟩,
  ⟨292039, 1162, 364⟩, ⟨296799, 1164, 371⟩, ⟨300000, 1165, 240⟩
]

private def analyticRankIntervals : List (ℕ × ℕ) := [
  (300060, 1165), (300121, 1165), (300182, 1165), (300243, 1165), (300306, 1165), (300370, 1165),
  (300434, 1165), (300499, 1165), (300564, 1165), (300630, 1165), (300697, 1165), (300765, 1165),
  (300833, 1165), (300902, 1165), (300971, 1165), (301041, 1165), (301112, 1165), (301183, 1165),
  (301254, 1165), (301321, 1165), (301389, 1165), (301458, 1165), (301528, 1165), (301598, 1165),
  (301670, 1165), (301742, 1165), (301788, 1166), (301865, 1166), (301943, 1166), (302023, 1166),
  (302103, 1166), (302184, 1166), (302265, 1166), (302347, 1166), (302430, 1166), (302510, 1166),
  (302592, 1166), (302662, 1166), (302732, 1166), (302804, 1166), (302876, 1166), (302949, 1166),
  (303022, 1166), (303096, 1166), (303171, 1166), (303247, 1166), (303324, 1166), (303402, 1166),
  (303480, 1166), (303558, 1166), (303637, 1166), (303716, 1166), (303797, 1166), (303878, 1166),
  (303961, 1166), (304044, 1166), (304128, 1166), (304213, 1166), (304299, 1166), (304386, 1166),
  (304474, 1166), (304558, 1166), (304642, 1166), (304727, 1166), (304813, 1166), (304900, 1166),
  (304987, 1166), (305064, 1166), (305158, 1167), (305253, 1167), (305349, 1167), (305446, 1167),
  (305544, 1167), (305643, 1167), (305743, 1167), (305844, 1167), (305945, 1167), (306047, 1167),
  (306150, 1167), (306255, 1167), (306361, 1167), (306468, 1167), (306576, 1167), (306684, 1167),
  (306794, 1167), (306905, 1167), (307006, 1167), (307107, 1167), (307210, 1167), (307312, 1167),
  (307416, 1167), (307521, 1167), (307627, 1167), (307734, 1167), (307837, 1167), (307942, 1167),
  (308048, 1167), (308155, 1167), (308262, 1167), (308370, 1167), (308453, 1168), (308568, 1168),
  (308684, 1168), (308801, 1168), (308919, 1168), (309038, 1168), (309158, 1168), (309274, 1168),
  (309391, 1168), (309509, 1168), (309627, 1168), (309747, 1168), (309868, 1168), (309990, 1168),
  (310113, 1168), (310236, 1168), (310361, 1168), (310487, 1168), (310615, 1168), (310744, 1168),
  (310875, 1168), (311007, 1168), (311140, 1168), (311271, 1168), (311401, 1168), (311520, 1168),
  (311641, 1168), (311744, 1168), (311873, 1169), (312002, 1169), (312133, 1169), (312265, 1169),
  (312398, 1169), (312533, 1169), (312669, 1169), (312805, 1169), (312942, 1169), (313081, 1169),
  (313221, 1169), (313363, 1169), (313507, 1169), (313652, 1169), (313799, 1169), (313947, 1169),
  (314097, 1169), (314248, 1169), (314399, 1169), (314548, 1169), (314698, 1169), (314850, 1169),
  (315003, 1169), (315139, 1169), (315300, 1170), (315463, 1170), (315627, 1170), (315792, 1170),
  (315959, 1170), (316113, 1170), (316268, 1170), (316424, 1170), (316583, 1170), (316743, 1170),
  (316905, 1170), (317067, 1170), (317231, 1170), (317397, 1170), (317564, 1170), (317733, 1170),
  (317904, 1170), (318072, 1170), (318241, 1170), (318412, 1170), (318570, 1170), (318748, 1171),
  (318927, 1171), (319109, 1171), (319293, 1171), (319478, 1171), (319666, 1171), (319855, 1171),
  (320045, 1171), (320237, 1171), (320431, 1171), (320615, 1171), (320801, 1171), (320988, 1171),
  (321178, 1171), (321370, 1171), (321557, 1171), (321747, 1171), (321939, 1171), (322105, 1172),
  (322302, 1172), (322501, 1172), (322693, 1172), (322883, 1172), (323074, 1172), (323267, 1172),
  (323462, 1172), (323659, 1172), (323858, 1172), (324060, 1172), (324264, 1172), (324470, 1172),
  (324676, 1172), (324885, 1172), (325096, 1172), (325291, 1172), (325488, 1172), (325660, 1173),
  (325866, 1173), (326075, 1173), (326284, 1173), (326495, 1173), (326708, 1173), (326923, 1173),
  (327141, 1173), (327361, 1173), (327583, 1173), (327807, 1173), (328033, 1173), (328261, 1173),
  (328492, 1173), (328725, 1173), (328955, 1173), (329160, 1174), (329399, 1174), (329638, 1174),
  (329878, 1174), (330107, 1174), (330339, 1174), (330573, 1174), (330810, 1174), (331049, 1174),
  (331291, 1174), (331534, 1174), (331780, 1174), (332028, 1174), (332279, 1174), (332528, 1174),
  (332750, 1175), (333008, 1175), (333267, 1175), (333529, 1175), (333794, 1175), (334061, 1175),
  (334331, 1175), (334604, 1175), (334881, 1175), (335146, 1175), (335414, 1175), (335685, 1175),
  (335959, 1175), (336226, 1175), (336465, 1176), (336738, 1176), (337015, 1176), (337294, 1176),
  (337576, 1176), (337861, 1176), (338149, 1176), (338440, 1176), (338732, 1176), (339028, 1176),
  (339327, 1176), (339629, 1176), (339934, 1176), (340194, 1177), (340489, 1177), (340787, 1177),
  (341088, 1177), (341392, 1177), (341700, 1177), (342011, 1177), (342323, 1177), (342638, 1177),
  (342957, 1177), (343276, 1177), (343598, 1177), (343893, 1178), (344221, 1178), (344552, 1178),
  (344886, 1178), (345210, 1178), (345537, 1178), (345867, 1178), (346200, 1178), (346537, 1178),
  (346877, 1178), (347221, 1178), (347538, 1179), (347892, 1179), (348243, 1179), (348599, 1179),
  (348958, 1179), (349321, 1179), (349683, 1179), (350043, 1179), (350393, 1179), (350747, 1179),
  (351104, 1179), (351435, 1180), (351803, 1180), (352170, 1180), (352541, 1180), (352915, 1180),
  (353293, 1180), (353674, 1180), (354059, 1180), (354448, 1180), (354841, 1180), (355207, 1181),
  (355596, 1181), (355990, 1181), (356382, 1181), (356774, 1181), (357171, 1181), (357572, 1181),
  (357975, 1181), (358383, 1181), (358795, 1181), (359180, 1182), (359605, 1182), (360034, 1182),
  (360461, 1182), (360892, 1182), (361314, 1182), (361740, 1182), (362169, 1182), (362602, 1182),
  (363009, 1183), (363450, 1183), (363896, 1183), (364345, 1183), (364793, 1183), (365245, 1183),
  (365702, 1183), (366164, 1183), (366614, 1183), (367039, 1184), (367504, 1184), (367973, 1184),
  (368448, 1184), (368919, 1184), (369395, 1184), (369876, 1184), (370360, 1184), (370817, 1185),
  (371314, 1185), (371815, 1185), (372307, 1185), (372804, 1185), (373300, 1185), (373799, 1185),
  (374304, 1185), (374782, 1186), (375302, 1186), (375828, 1186), (376358, 1186), (376882, 1186),
  (377411, 1186), (377924, 1186), (378440, 1186), (378929, 1187), (379461, 1187), (379998, 1187),
  (380542, 1187), (381089, 1187), (381642, 1187), (382200, 1187), (382758, 1187), (383289, 1188),
  (383843, 1188), (384403, 1188), (384969, 1188), (385541, 1188), (386119, 1188), (386700, 1188),
  (387249, 1189), (387841, 1189), (388440, 1189), (389043, 1189), (389637, 1189), (390238, 1189),
  (390839, 1189), (391413, 1190), (392023, 1190), (392639, 1190), (393261, 1190), (393890, 1190),
  (394524, 1190), (395164, 1190), (395762, 1191), (396399, 1191), (397042, 1191), (397687, 1191),
  (398338, 1191), (398996, 1191), (399662, 1191), (400299, 1192), (400981, 1192), (401648, 1192),
  (402321, 1192), (403000, 1192), (403686, 1192), (404336, 1193), (405033, 1193), (405735, 1193),
  (406436, 1193), (407145, 1193), (407846, 1193), (408554, 1193), (409233, 1194), (409958, 1194),
  (410689, 1194), (411421, 1194), (412158, 1194), (412903, 1194), (413621, 1195), (414369, 1195),
  (415124, 1195), (415886, 1195), (416649, 1195), (417414, 1195), (418150, 1196), (418934, 1196),
  (419727, 1196), (420511, 1196), (421301, 1196), (422093, 1196), (422857, 1197), (423670, 1197),
  (424488, 1197), (425314, 1197), (426149, 1197), (426933, 1198), (427765, 1198), (428605, 1198),
  (429450, 1198), (430302, 1198), (431148, 1198), (431967, 1199), (432829, 1199), (433683, 1199),
  (434543, 1199), (435411, 1199), (436253, 1200), (437145, 1200), (438037, 1200), (438939, 1200),
  (439850, 1200), (440753, 1200), (441626, 1201), (442551, 1201), (443485, 1201), (444419, 1201),
  (445360, 1201), (446274, 1202), (447223, 1202), (448181, 1202), (449147, 1202), (450116, 1202),
  (451057, 1203), (452051, 1203), (453052, 1203), (454065, 1203), (455069, 1203), (456038, 1204),
  (457058, 1204), (458082, 1204), (459117, 1204), (460160, 1204), (461177, 1205), (462222, 1205),
  (463278, 1205), (464343, 1205), (465405, 1205), (466497, 1206), (467592, 1206), (468679, 1206),
  (469777, 1206), (470848, 1207), (471969, 1207), (473102, 1207), (474239, 1207), (475388, 1207),
  (476488, 1208), (477645, 1208), (478814, 1208), (479984, 1208), (481127, 1209), (482327, 1209),
  (483539, 1209), (484740, 1209), (485945, 1209), (487113, 1210), (488336, 1210), (489571, 1210),
  (490819, 1210), (492020, 1211), (493268, 1211), (494528, 1211), (495801, 1211), (497043, 1212),
  (498344, 1212), (499636, 1212), (500932, 1212), (502198, 1213), (503523, 1213), (504861, 1213),
  (506209, 1213), (507527, 1213), (508881, 1214), (510248, 1214), (511626, 1214), (513013, 1214),
  (514362, 1215), (515749, 1215), (517150, 1215), (518566, 1215), (519955, 1216), (521392, 1216),
  (522844, 1216), (524289, 1216), (525734, 1217), (527195, 1217), (528660, 1217), (530093, 1218),
  (531591, 1218), (533083, 1218), (534590, 1218), (536056, 1219), (537587, 1219), (539121, 1219),
  (540646, 1219), (542143, 1220), (543694, 1220), (545261, 1220), (546842, 1220), (548395, 1221),
  (549982, 1221), (551582, 1221), (553195, 1221), (554780, 1222), (556433, 1222), (558088, 1222),
  (559693, 1223), (561366, 1223), (563051, 1223), (564754, 1223), (566413, 1224), (568114, 1224),
  (569833, 1224), (571570, 1224), (573279, 1225), (575043, 1225), (576803, 1225), (578535, 1226),
  (580330, 1226), (582133, 1226), (583955, 1226), (585745, 1227), (587584, 1227), (589441, 1227),
  (591259, 1228), (593139, 1228), (595036, 1228), (596938, 1228), (598796, 1229), (600728, 1229),
  (601191, 1229), (601658, 1229), (602128, 1229), (602602, 1229), (603075, 1229), (603552, 1229),
  (603985, 1230), (604476, 1230), (604971, 1230), (605467, 1230), (605955, 1230), (606447, 1230),
  (606943, 1230), (607443, 1230), (607946, 1230), (608452, 1230), (608963, 1230), (609473, 1230),
  (609987, 1230), (610457, 1231), (610987, 1231), (611521, 1231), (612059, 1231), (612601, 1231),
  (613147, 1231), (613697, 1231), (614252, 1231), (614799, 1231), (615350, 1231), (615906, 1231),
  (616461, 1231), (616972, 1232), (617543, 1232), (618118, 1232), (618695, 1232), (619274, 1232),
  (619858, 1232), (620445, 1232), (621036, 1232), (621632, 1232), (622233, 1232), (622835, 1232),
  (623429, 1232), (623978, 1233), (624589, 1233), (625205, 1233), (625824, 1233), (626448, 1233),
  (627077, 1233), (627711, 1233), (628350, 1233), (628993, 1233), (629637, 1233), (630277, 1233),
  (630939, 1234), (631605, 1234), (632277, 1234), (632940, 1234), (633608, 1234), (634280, 1234),
  (634958, 1234), (635641, 1234), (636325, 1234), (637014, 1234), (637657, 1235), (638363, 1235),
  (639076, 1235), (639794, 1235), (640517, 1235), (641245, 1235), (641968, 1235), (642696, 1235),
  (643424, 1235), (644108, 1236), (644853, 1236), (645601, 1236), (646346, 1236), (647096, 1236),
  (647851, 1236), (648612, 1236), (649380, 1236), (650153, 1236), (650927, 1236), (651644, 1237),
  (652426, 1237), (653213, 1237), (654006, 1237), (654805, 1237), (655611, 1237), (656422, 1237),
  (657240, 1237), (658060, 1237), (658834, 1238), (659671, 1238), (660513, 1238), (661350, 1238),
  (662193, 1238), (663044, 1238), (663900, 1238), (664763, 1238), (665576, 1239), (666455, 1239),
  (667340, 1239), (668233, 1239), (669132, 1239), (670039, 1239), (670940, 1239), (671848, 1239),
  (672706, 1240), (673625, 1240), (674551, 1240), (675483, 1240), (676424, 1240), (677371, 1240),
  (678324, 1240), (679286, 1240), (680201, 1241), (681166, 1241), (682138, 1241), (683119, 1241),
  (684108, 1241), (685102, 1241), (686105, 1241), (687112, 1241), (688074, 1242), (689100, 1242),
  (690134, 1242), (691163, 1242), (692200, 1242), (693245, 1242), (694298, 1242), (695305, 1243),
  (696376, 1243), (697456, 1243), (698544, 1243), (699640, 1243), (700736, 1243), (701827, 1243),
  (702873, 1244), (703988, 1244), (705108, 1244), (706236, 1244), (707374, 1244), (708519, 1244),
  (709674, 1244), (710782, 1245), (711947, 1245), (713115, 1245), (714290, 1245), (715475, 1245),
  (716668, 1245), (717815, 1246), (719035, 1246), (720263, 1246), (721496, 1246), (722725, 1246),
  (723964, 1246), (725212, 1246), (726413, 1247), (727683, 1247), (728961, 1247), (730245, 1247),
  (731539, 1247), (732843, 1247), (734085, 1248), (735403, 1248), (736732, 1248), (738064, 1248),
  (739406, 1248), (740755, 1248), (742058, 1249), (743436, 1249), (744811, 1249), (746197, 1249),
  (747587, 1249), (748988, 1249), (750342, 1250), (751774, 1250), (753215, 1250), (754657, 1250),
  (756091, 1250), (757534, 1250), (758931, 1251), (760405, 1251), (761892, 1251), (763389, 1251),
  (764891, 1251), (766346, 1252), (767861, 1252), (769389, 1252), (770928, 1252), (772480, 1252),
  (774044, 1252), (775555, 1253), (777145, 1253), (778747, 1253), (780347, 1253), (781954, 1253),
  (783506, 1254), (785139, 1254), (786785, 1254), (788445, 1254), (790116, 1254), (791726, 1255),
  (793411, 1255), (795106, 1255), (796815, 1255), (798537, 1255), (800209, 1256), (801966, 1256),
  (803715, 1256), (805478, 1256), (807254, 1256), (808974, 1257), (810778, 1257), (812595, 1257),
  (814420, 1257), (816244, 1257), (818018, 1258), (819878, 1258), (821750, 1258), (823631, 1258),
  (825526, 1258), (827373, 1259), (829291, 1259), (831223, 1259), (833164, 1259), (835117, 1259),
  (837017, 1260), (839006, 1260), (840995, 1260), (842998, 1260), (844946, 1261), (846983, 1261),
  (849032, 1261), (851098, 1261), (853181, 1261), (855193, 1262), (857293, 1262), (859408, 1262),
  (861534, 1262), (863601, 1263), (865752, 1263), (867904, 1263), (870071, 1263), (872246, 1263),
  (874458, 1264), (876678, 1264), (878916, 1264), (881155, 1264), (883344, 1265), (885626, 1265),
  (887920, 1265), (890230, 1265), (892489, 1266), (894826, 1266), (897182, 1266), (899547, 1266),
  (901864, 1267), (904277, 1267), (906706, 1267), (909137, 1267), (911513, 1268), (913982, 1268),
  (916466, 1268), (918970, 1268), (921422, 1269), (923949, 1269), (926496, 1269), (929062, 1269),
  (931579, 1270), (934195, 1270), (936823, 1270), (939456, 1270), (942039, 1271), (944717, 1271),
  (947417, 1271), (950132, 1271), (952777, 1272), (955524, 1272), (958293, 1272), (961074, 1272),
  (963806, 1273), (966641, 1273), (969477, 1273), (972254, 1274), (975128, 1274), (978022, 1274),
  (980940, 1274), (983788, 1275), (986731, 1275), (989698, 1275), (992688, 1275), (995625, 1276),
  (998666, 1276), (1001705, 1276), (1004691, 1277), (1007785, 1277), (1010904, 1277), (1014036, 1277),
  (1017099, 1278), (1020272, 1278), (1023467, 1278), (1026606, 1279), (1029848, 1279), (1033094, 1279),
  (1036365, 1279), (1039586, 1280), (1042908, 1280), (1046255, 1280), (1049532, 1281), (1052902, 1281),
  (1056290, 1281), (1059705, 1281), (1063065, 1282), (1066521, 1282), (1070005, 1282), (1073425, 1283),
  (1076961, 1283), (1080515, 1283), (1083995, 1284), (1087582, 1284), (1091198, 1284), (1094840, 1284),
  (1098431, 1285), (1102111, 1285), (1105815, 1285), (1109467, 1286), (1113241, 1286), (1117010, 1286),
  (1120728, 1287), (1124568, 1287), (1128435, 1287), (1132242, 1288), (1136146, 1288), (1140077, 1288),
  (1143956, 1289), (1147951, 1289), (1151974, 1289), (1155932, 1289), (1160003, 1290), (1164095, 1290),
  (1168221, 1290), (1172270, 1291), (1176448, 1291), (1180650, 1291), (1184795, 1292), (1189061, 1292),
  (1193348, 1292), (1197568, 1293), (1201920, 1293), (1204903, 1293), (1207818, 1294), (1210848, 1294),
  (1213885, 1294), (1216943, 1294), (1220022, 1294), (1223029, 1295), (1226158, 1295), (1229307, 1295),
  (1232467, 1295), (1235555, 1296), (1238765, 1296), (1241992, 1296), (1245240, 1296), (1248416, 1297),
  (1251705, 1297), (1255016, 1297), (1258351, 1297), (1261613, 1298), (1265000, 1298), (1268397, 1298),
  (1271817, 1298), (1275164, 1299), (1278637, 1299), (1282134, 1299), (1285645, 1299), (1289081, 1300),
  (1292643, 1300), (1296218, 1300), (1299818, 1300), (1303345, 1301), (1306991, 1301), (1310661, 1301),
  (1314357, 1301), (1317979, 1302), (1321728, 1302), (1325493, 1302), (1329283, 1302), (1332999, 1303),
  (1336847, 1303), (1340723, 1303), (1344614, 1303), (1348425, 1304), (1352370, 1304), (1356344, 1304),
  (1360247, 1305), (1364268, 1305), (1368317, 1305), (1372393, 1305), (1376396, 1306), (1380533, 1306),
  (1384687, 1306), (1388869, 1306), (1392981, 1307), (1397228, 1307), (1401503, 1307), (1405688, 1308),
  (1410014, 1308), (1414365, 1308), (1418745, 1308), (1423055, 1309), (1427489, 1309), (1431952, 1309),
  (1436343, 1310), (1440879, 1310), (1445441, 1310), (1450023, 1310), (1454532, 1311), (1459184, 1311),
  (1463862, 1311), (1468455, 1312), (1473197, 1312), (1477971, 1312), (1482773, 1312), (1487499, 1313),
  (1492364, 1313), (1497256, 1313), (1502076, 1314), (1507048, 1314), (1512045, 1314), (1516948, 1315),
  (1522006, 1315), (1527098, 1315), (1532113, 1316), (1537266, 1316), (1542456, 1316), (1547681, 1316),
  (1552829, 1317), (1558135, 1317), (1563463, 1317), (1568714, 1318), (1574118, 1318), (1579559, 1318),
  (1584913, 1319), (1590422, 1319), (1595967, 1319), (1601438, 1320), (1607072, 1320), (1612726, 1320),
  (1618297, 1321), (1624034, 1321), (1629804, 1321), (1635486, 1322), (1641334, 1322), (1647221, 1322),
  (1653027, 1323), (1658988, 1323), (1664990, 1323), (1670912, 1324), (1676998, 1324), (1683128, 1324),
  (1689161, 1325), (1695368, 1325), (1701615, 1325), (1707788, 1326), (1714114, 1326), (1720482, 1326),
  (1726761, 1327), (1733211, 1327), (1739692, 1327), (1746096, 1328), (1752681, 1328), (1759304, 1328),
  (1765836, 1329), (1772549, 1329), (1779303, 1329), (1785977, 1330), (1792820, 1330), (1799710, 1330),
  (1806518, 1331), (1813510, 1331), (1820536, 1331), (1827476, 1332), (1834603, 1332), (1841652, 1333),
  (1848866, 1333), (1856132, 1333), (1863320, 1334), (1870702, 1334), (1878110, 1334), (1885443, 1335),
  (1892967, 1335), (1900537, 1335), (1908012, 1336), (1915685, 1336), (1923272, 1337), (1931059, 1337),
  (1938880, 1337), (1946616, 1338), (1954547, 1338), (1962531, 1338), (1970420, 1339), (1978504, 1339),
  (1986607, 1339), (1994817, 1340), (2003057, 1340), (2011217, 1341), (2019586, 1341), (2028012, 1341),
  (2036334, 1342), (2044868, 1342), (2053316, 1343), (2061969, 1343), (2070663, 1343), (2079278, 1344),
  (2088099, 1344), (2096983, 1344), (2097151, 1344)
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dyadic_rank_thresholds_valid : RankThresholds dyadicRankThresholds 0 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma candidate_count_30001 : (candidatePrefix 30001).card ≤ 3265 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma dyadic_rank_intervals_valid :
    RankIntervals dyadicRankThresholds 30001 300000 3265 dyadicRankIntervals := by decide +kernel

def countingBound (n : ℕ) : ℕ :=
  if n ≤ 300000 then
    min (countFromIntervals (n+1) 30001 3265 dyadicRankIntervals) (211+48*((n+1)/210+1))
  else 23350+(13*n)/144

lemma counting_bound_small {n : ℕ} (hn : n ≤ 300000) : n.primesLE.card ≤ countingBound n := by
  rw [countingBound, if_pos hn]
  exact le_min ((primes_le_candidates n).trans
    (count_from_intervals_valid _ 30001 300000 3265 (n+1) _ (by omega)
      candidate_count_30001 dyadic_rank_intervals_valid)) (wheel_prime_count_upper n)

set_option maxRecDepth 100000 in
lemma prime_count_at_65536 : (Nat.primesLE (2^16)).card ≤ 6700 :=
  (counting_bound_small (by decide)).trans (by decide +kernel)

set_option maxRecDepth 100000 in
lemma prime_count_at_262144 : (Nat.primesLE (2^18)).card ≤ 23350 :=
  (counting_bound_small (by decide)).trans (by decide +kernel)

lemma counting_bound_valid (hLinear : ∀ n, 144*n.primesLE.card ≤ 13*n+144*23350)
    (n : ℕ) : n.primesLE.card ≤ countingBound n := by
  by_cases h : n ≤ 300000
  · exact counting_bound_small h
  · rw [countingBound, if_neg h]
    have hL := hLinear n
    omega

def analyticCountingBound (n : ℕ) : ℕ :=
  (104*(n-1) + 64*(∑ j ∈ range n.log2, countingBound (n/2^(j+1)))) / ((n^64).log2-64)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma analytic_rank_intervals_valid :
    NumericRankIntervals dyadicRankThresholds analyticCountingBound 300001 (2^21-1) analyticRankIntervals := by
  decide +kernel

theorem bridge_rank_product (k : ℕ) (hk₁ : 30001 ≤ k) (hk₂ : k ≤ 300000) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) :=
  rank_intervals_bound _ 30001 300000 3265 k _ dyadic_rank_thresholds_valid
    (by decide) hk₁ hk₂ candidate_count_30001 dyadic_rank_intervals_valid

theorem analytic_rank_product (k : ℕ) (hk₁ : 300001 ≤ k) (hk₂ : k < 2^21)
    (hEstimate : ∀ n, 3 ≤ n → ((range n).filter Nat.Prime).card ≤ analyticCountingBound n) :
    (k-1).factorial < ∏ i ∈ range (retainedCount k), rankBound (i+1) :=
  numeric_rank_intervals_bound _ _ 300001 (2^21-1) k _ dyadic_rank_thresholds_valid
    (by decide) hk₁ (by omega) hEstimate analytic_rank_intervals_valid

end Erdos137OddBridge

/-! Sylvester–Schur for the interval used in Erdős 137.

The binomial theorem below is the existing Lean proof credited to @senamakel
in proofs/Erdos683.erdos_683.variant.sylvester_schur.lean. The last lemma
adapts its conclusion to the interval product used here.
-/

open Nat Finset


namespace SylvesterSchurOMA

/-- The number of primes `≤ k`. -/
def pc (k : ℕ) : ℕ := ((Finset.range (k + 1)).filter Nat.Prime).card

/-! ## Step 2: valuations of `N.choose k` -/

/-- A prime `p` with `p ≤ k`, `N < 3p`, `N < p²` and `2k ≤ N` does not divide `N.choose k`. -/
lemma factorization_choose_eq_zero_of_third {p N k : ℕ} (hp : p.Prime) (hpk : p ≤ k)
    (h3 : N < 3 * p) (hsq : N < p ^ 2) (h2k : 2 * k ≤ N) :
    (N.choose k).factorization p = 0 := by
  have hkN : k ≤ N := by omega
  have hlog : Nat.log p N < 2 := Nat.log_lt_of_lt_pow (by omega) hsq
  rw [Nat.factorization_choose hp hkN hlog]
  have hk1 : k % p = k - p := by
    rw [Nat.mod_eq_sub_mod hpk, Nat.mod_eq_of_lt (by omega)]
  have hk2 : (N - k) % p = N - k - p := by
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  rw [Finset.mem_Ico] at hi
  have : i = 1 := by omega
  subst this
  simp only [pow_one, hk1, hk2]
  omega

/-! ## Step 3: the counting bound -/

/-- Under the hypothesis that every prime factor of `N.choose k` is at most `k`,
`N.choose k ≤ N ^ π(k)`. -/
lemma choose_le_pow_primeCounting {N k : ℕ} (hN : 0 < N) (hkN : k ≤ N)
    (H : ∀ p, p.Prime → p ∣ N.choose k → p ≤ k) :
    N.choose k ≤ N ^ pc k := by
  have hC : N.choose k ≠ 0 := (Nat.choose_pos hkN).ne'
  calc N.choose k = ∏ p ∈ (N.choose k).primeFactors, p ^ (N.choose k).factorization p :=
        (Nat.prod_factorization_pow_eq_self hC).symm
    _ ≤ ∏ _p ∈ (N.choose k).primeFactors, N :=
        Finset.prod_le_prod' fun p _ => Nat.pow_factorization_choose_le hN
    _ = N ^ (N.choose k).primeFactors.card := Finset.prod_const _
    _ ≤ N ^ pc k := by
        apply Nat.pow_le_pow_right hN
        apply Finset.card_le_card
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpk := H p hpp (Nat.dvd_of_mem_primeFactors hp)
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hpp⟩

/-- Counting bound: `N ^ k ≤ 2 ^ k * k! * N ^ π(k)` when no prime above `k` divides `N.choose k`. -/
lemma counting_bound {N k : ℕ} (h2k : 2 * k ≤ N) (hN : 0 < N)
    (H : ∀ p, p.Prime → p ∣ N.choose k → p ≤ k) :
    N ^ k ≤ 2 ^ k * k ! * N ^ pc k := by
  have h1 : (N + 1 - k) ^ k ≤ N.descFactorial k := Nat.pow_sub_le_descFactorial N k
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
  have h2 : N ≤ 2 * (N + 1 - k) := by omega
  calc N ^ k ≤ (2 * (N + 1 - k)) ^ k := Nat.pow_le_pow_left h2 k
    _ = 2 ^ k * (N + 1 - k) ^ k := mul_pow _ _ _
    _ ≤ 2 ^ k * (k ! * N.choose k) := Nat.mul_le_mul_left _ h1
    _ ≤ 2 ^ k * (k ! * N ^ pc k) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (choose_le_pow_primeCounting hN (by omega) H))
    _ = 2 ^ k * k ! * N ^ pc k := by ring


/-! ## Step 4a: upper and lower bounds for `N.choose k` -/

lemma pc_mono {a b : ℕ} (h : a ≤ b) : pc a ≤ pc b := by
  unfold pc
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

/-- Upper bound when no prime above `k` divides `N.choose k`. -/
lemma choose_le_upper {N k : ℕ} (h2k : 2 * k ≤ N)
    (H : ∀ p, p.Prime → p ∣ N.choose k → p ≤ k) :
    N.choose k ≤ N ^ pc (Nat.sqrt N) * 4 ^ (min k (N / 3)) := by
  have hN : 0 < N ∨ N = 0 := by omega
  rcases hN with hN | hN
  swap
  · subst hN
    have : k = 0 := by omega
    subst this
    show 1 ≤ 0 ^ pc 0 * 4 ^ (min 0 (0 / 3))
    decide
  set f := (N.choose k).factorization with hf
  set m := min k (N / 3) with hm
  rw [← Nat.prod_pow_factorization_choose N k (by omega),
    ← Finset.prod_filter_mul_prod_filter_not (Finset.range (N + 1)) (· ≤ Nat.sqrt N)]
  apply Nat.mul_le_mul
  · -- small primes
    calc ∏ p ∈ (Finset.range (N + 1)).filter (· ≤ Nat.sqrt N), p ^ f p
        ≤ ∏ p ∈ (Finset.range (N + 1)).filter (· ≤ Nat.sqrt N), (if p.Prime then N else 1) := by
          apply Finset.prod_le_prod'
          intro p _
          split_ifs with hp
          · exact Nat.pow_factorization_choose_le hN
          · simp [hf, Nat.factorization_eq_zero_of_not_prime _ hp]
      _ = ∏ p ∈ ((Finset.range (N + 1)).filter (· ≤ Nat.sqrt N)).filter Nat.Prime, N :=
          (Finset.prod_filter _ _).symm
      _ = N ^ (((Finset.range (N + 1)).filter (· ≤ Nat.sqrt N)).filter Nat.Prime).card :=
          Finset.prod_const _
      _ ≤ N ^ pc (Nat.sqrt N) := by
          apply Nat.pow_le_pow_right hN
          unfold pc
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
          exact ⟨by omega, hp.2⟩
  · -- large primes
    calc ∏ p ∈ (Finset.range (N + 1)).filter (fun p => ¬ p ≤ Nat.sqrt N), p ^ f p
        ≤ ∏ p ∈ (Finset.range (N + 1)).filter (fun p => ¬ p ≤ Nat.sqrt N),
            (if p.Prime ∧ p ≤ m then p else 1) := by
          apply Finset.prod_le_prod'
          intro p hpS
          simp only [Finset.mem_filter, Finset.mem_range] at hpS
          have hp1 : 1 ≤ p := by have := hpS.2; omega
          have hsq : N < p ^ 2 := by
            have := Nat.sqrt_lt'.1 (show Nat.sqrt N < p by omega)
            exact this
          have hle1 : f p ≤ 1 := Nat.factorization_choose_le_one hsq
          rcases Nat.eq_zero_or_pos (f p) with h0 | hpos
          · rw [h0, pow_zero]; split_ifs
            · exact hp1
            · exact le_refl 1
          · have hne : (N.choose k).factorization p ≠ 0 := by rw [← hf]; omega
            have hp : p.Prime := by
              by_contra hnp
              exact hne (Nat.factorization_eq_zero_of_not_prime _ hnp)
            have hdvd : p ∣ N.choose k := Nat.dvd_of_factorization_pos hne
            have hpk := H p hp hdvd
            have h3 : 3 * p ≤ N := by
              by_contra hlt
              have := factorization_choose_eq_zero_of_third hp hpk (by omega) hsq h2k
              rw [← hf] at this
              omega
            have hpm : p ≤ m := by
              rw [hm]; apply le_min hpk; omega
            have : f p = 1 := by omega
            rw [this, pow_one, if_pos ⟨hp, hpm⟩]
      _ = ∏ p ∈ ((Finset.range (N + 1)).filter (fun p => ¬ p ≤ Nat.sqrt N)).filter
            (fun p => p.Prime ∧ p ≤ m), p := (Finset.prod_filter _ _).symm
      _ ≤ ∏ p ∈ (Finset.range (m + 1)).filter Nat.Prime, p := by
          apply Finset.prod_le_prod_of_subset_of_one_le'
          · intro p hp
            simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
            exact ⟨by omega, hp.2.1⟩
          · intro p hp _
            simp only [Finset.mem_filter] at hp
            exact hp.2.one_lt.le
      _ = primorial m := rfl
      _ ≤ 4 ^ m := primorial_le_four_pow m

/-- Lower bound: `4^k N^k ≤ 2k (2k)^k * N.choose k` for `2k ≤ N`. -/
lemma lower_bound {N k : ℕ} (hk : 0 < k) (h2k : 2 * k ≤ N) :
    4 ^ k * N ^ k ≤ 2 * k * (2 * k) ^ k * N.choose k := by
  have key : (2 * k).descFactorial k * N ^ k ≤ N.descFactorial k * (2 * k) ^ k := by
    have e1 : N ^ k = ∏ _i ∈ Finset.range k, N := by simp
    have e2 : (2 * k) ^ k = ∏ _i ∈ Finset.range k, (2 * k) := by simp
    rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range, e1, e2,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod'
    intro i hi
    rw [Finset.mem_range] at hi
    obtain ⟨a, ha⟩ : ∃ a, 2 * k = a + i := ⟨2 * k - i, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, N = b + i := ⟨N - i, by omega⟩
    have hab : a ≤ b := by omega
    rw [ha, hb, Nat.add_sub_cancel, Nat.add_sub_cancel]
    nlinarith
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    mul_assoc, mul_assoc] at key
  have key' := Nat.le_of_mul_le_mul_left key (Nat.factorial_pos k)
  have h4 := Nat.four_pow_le_two_mul_self_mul_centralBinom k hk
  rw [Nat.centralBinom_eq_two_mul_choose] at h4
  calc 4 ^ k * N ^ k ≤ 2 * k * (2 * k).choose k * N ^ k := Nat.mul_le_mul_right _ h4
    _ = 2 * k * ((2 * k).choose k * N ^ k) := by ring
    _ ≤ 2 * k * (N.choose k * (2 * k) ^ k) := Nat.mul_le_mul_left _ key'
    _ = 2 * k * (2 * k) ^ k * N.choose k := by ring


/-! ## Step 4b: prime counting by the mod-30 wheel -/

lemma pc_eq_count (x : ℕ) : pc x = Nat.count Nat.Prime (x + 1) := by
  rw [pc, Nat.count_eq_card_filter_range]

lemma pc_wheel {x : ℕ} (hx : 30 ≤ x) : pc x ≤ 10 + 8 * ((x - 30) / 30 + 1) := by
  rw [pc_eq_count]
  have h := Nat.primeCounting'_add_le (a := 30) (k := 31) (by norm_num) (by norm_num) (x - 30)
  have h31 : Nat.primeCounting' 31 = 10 := by decide
  have ht : Nat.totient 30 = 8 := by decide
  rw [h31, ht] at h
  have : 31 + (x - 30) = x + 1 := by omega
  rw [this] at h
  exact h

set_option maxRecDepth 100000 in
lemma three_pc_lt {k : ℕ} (hk : 34 ≤ k) : 3 * pc k < k := by
  rcases lt_or_ge k 160 with h | h
  · have key : ∀ k < 160, 34 ≤ k → 3 * pc k < k := by decide
    exact key k h hk
  · have := pc_wheel (x := k) (by omega)
    omega

/-! ## Step 4c: the large-`N` region via counting -/

lemma not_large_region {N k : ℕ} (hk : 34 ≤ k) (h2k : 2 * k ≤ N)
    (H : ∀ p, p.Prime → p ∣ N.choose k → p ≤ k) : N ^ 2 < (2 * k) ^ 3 := by
  by_contra hge'
  have hge := not_lt.1 hge'
  have hN : 0 < N := by omega
  have hc := counting_bound h2k hN H
  have h3 := three_pc_lt hk
  have hpk : pc k ≤ k := by omega
  have hfac : k ! ≤ k ^ k := Nat.factorial_le_pow k
  have h1 : N ^ (k - pc k) * N ^ pc k ≤ (2 * k) ^ k * N ^ pc k := by
    rw [← pow_add, Nat.sub_add_cancel hpk, mul_pow]
    calc N ^ k ≤ 2 ^ k * k ! * N ^ pc k := hc
      _ ≤ 2 ^ k * k ^ k * N ^ pc k := by gcongr
  have h2 : N ^ (k - pc k) ≤ (2 * k) ^ k :=
    Nat.le_of_mul_le_mul_right h1 (by positivity)
  have h4 : ((2 * k) ^ 3) ^ (k - pc k) ≤ (N ^ 2) ^ (k - pc k) := Nat.pow_le_pow_left hge _
  have h5 : (N ^ 2) ^ (k - pc k) ≤ ((2 * k) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact Nat.pow_le_pow_left h2 2
  rw [← pow_mul, ← pow_mul] at h4
  rw [← pow_mul, ← pow_mul] at h5
  have h6 : (2 * k) ^ (3 * (k - pc k)) ≤ (2 * k) ^ (k * 2) := le_trans h4 h5
  have h7 := (Nat.pow_le_pow_iff_right (show 1 < 2 * k by omega)).1 h6
  omega


/-! ## Step 4d: elementary growth lemmas -/

lemma poly1 : ∀ j ≥ 14, 48 * (j + 3) ^ 2 ≤ 2 ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have e : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
    have h : (j + 1 + 3) ^ 2 ≤ 2 * (j + 3) ^ 2 := by nlinarith
    rw [e]; linarith

lemma poly2 : ∀ j ≥ 14, 32 * (j + 4) ^ 2 ≤ 2 ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have e : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
    have h : (j + 1 + 4) ^ 2 ≤ 2 * (j + 4) ^ 2 := by nlinarith
    rw [e]; linarith

lemma poly3 : ∀ j ≥ 14, 128 * (j + 8) ^ 2 ≤ 4 * 2 ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have e : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
    have h : (j + 1 + 8) ^ 2 ≤ 2 * (j + 8) ^ 2 := by nlinarith
    rw [e]; linarith

lemma poly4 : ∀ j ≥ 14, 8 * (3 * j + 6) ^ 4 ≤ 50625 * 2 ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have e : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
    have h16 : 16 * (3 * (j + 1) + 6) ≤ 17 * (3 * j + 6) := by omega
    have h4 := Nat.pow_le_pow_left h16 4
    rw [mul_pow, mul_pow] at h4
    norm_num at h4
    rw [e]
    generalize (3 * (j + 1) + 6) ^ 4 = y at h4 ⊢
    generalize (3 * j + 6) ^ 4 = x at h4 ih
    generalize 2 ^ j = P at ih ⊢
    omega

/-- `2^(k/4) * 4^k ≤ 5^k`. -/
lemma five_pow (k : ℕ) : 2 ^ (k / 4) * 4 ^ k ≤ 5 ^ k := by
  obtain ⟨q, t, ht, rfl⟩ : ∃ q t, t < 4 ∧ k = 4 * q + t := ⟨k / 4, k % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 4).symm⟩
  have hq : (4 * q + t) / 4 = q := by omega
  rw [hq, pow_add, pow_add, pow_mul, pow_mul]
  have h1 : 2 ^ q * (4 ^ 4) ^ q ≤ (5 ^ 4) ^ q := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) q
  have h2 : 4 ^ t ≤ 5 ^ t := Nat.pow_le_pow_left (by norm_num) t
  calc 2 ^ q * ((4 ^ 4) ^ q * 4 ^ t) = (2 ^ q * (4 ^ 4) ^ q) * 4 ^ t := by ring
    _ ≤ (5 ^ 4) ^ q * 5 ^ t := Nat.mul_le_mul h1 h2

/-- `2^(k/2) * 2^k ≤ 3^k`. -/
lemma three_pow (k : ℕ) : 2 ^ (k / 2) * 2 ^ k ≤ 3 ^ k := by
  obtain ⟨q, t, ht, rfl⟩ : ∃ q t, t < 2 ∧ k = 2 * q + t := ⟨k / 2, k % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 2).symm⟩
  have hq : (2 * q + t) / 2 = q := by omega
  rw [hq, pow_add, pow_add, pow_mul, pow_mul]
  have h1 : 2 ^ q * (2 ^ 2) ^ q ≤ (3 ^ 2) ^ q := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) q
  have h2 : 2 ^ t ≤ 3 ^ t := Nat.pow_le_pow_left (by norm_num) t
  calc 2 ^ q * ((2 ^ 2) ^ q * 2 ^ t) = (2 ^ q * (2 ^ 2) ^ q) * 2 ^ t := by ring
    _ ≤ (3 ^ 2) ^ q * 3 ^ t := Nat.mul_le_mul h1 h2


lemma aux_lin (j : ℕ) : 114 * j + 228 ≤ 48 * (j + 3) ^ 2 := by nlinarith

lemma four_pow_eq (k : ℕ) : 4 ^ k = 2 ^ k * 2 ^ k := by
  rw [← mul_pow]; norm_num

/-! ## Step 4e: the middle region for `k ≥ 2^14` -/

lemma middle_region {N k : ℕ} (hk : 2 ^ 14 ≤ k) (h2k : 2 * k ≤ N) (hsm : N ^ 2 < (2 * k) ^ 3)
    (H : ∀ p, p.Prime → p ∣ N.choose k → p ≤ k) : False := by
  have hk' : 16384 ≤ k := by norm_num at hk; exact hk
  have hk0 : 0 < k := by omega
  have hN0 : 0 < N := by omega
  set j := Nat.log 2 k with hjdef
  have hj14 : 14 ≤ j := Nat.le_log_of_pow_le (by norm_num) hk
  have hjk : 2 ^ j ≤ k := Nat.pow_log_le_self 2 (by omega)
  have hkj : k < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  set r := Nat.sqrt N with hrdef
  have hr2 : r ^ 2 ≤ N := Nat.sqrt_le' N
  have hr30 : 30 ≤ r := Nat.le_sqrt'.2 (by omega)
  set s := pc r with hsdef
  have hs : s ≤ 18 + r / 3 := by have := pc_wheel hr30; omega
  set L := Nat.log 2 N + 1 with hLdef
  have hNL : N < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) N
  have hLb : ∀ e, N < 2 ^ e → L ≤ e := fun e he => by
    have := Nat.log_lt_of_lt_pow (by omega : N ≠ 0) he
    omega
  have hup : 2 * k * N ^ s < 2 ^ (L * (s + 1)) := by
    have h1 : 2 * k < 2 ^ L := by omega
    have h2 : N ^ s ≤ (2 ^ L) ^ s := Nat.pow_le_pow_left hNL.le s
    calc 2 * k * N ^ s < 2 ^ L * (2 ^ L) ^ s :=
          Nat.mul_lt_mul_of_lt_of_le h1 h2 (by positivity)
      _ = 2 ^ (L * (s + 1)) := by rw [← pow_mul, ← pow_add]; ring_nf
  have hLs : L * (s + 1) ≤ 19 * L + L * r / 3 := by
    calc L * (s + 1) ≤ L * (19 + r / 3) := Nat.mul_le_mul_left _ (by omega)
      _ = 19 * L + L * (r / 3) := by ring
      _ ≤ 19 * L + L * r / 3 := by
          have := Nat.mul_div_le_mul_div_assoc L r 3
          omega
  have fin : ∀ E, 2 ^ E ≤ 2 * k * N ^ s → L * (s + 1) ≤ E → False := fun E h1 h2 => by
    have h3 := lt_of_le_of_lt h1 hup
    have h4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h3
    omega
  have hstar : 4 ^ k * N ^ k ≤ 2 * k * (2 * k) ^ k * (N ^ s * 4 ^ (min k (N / 3))) :=
    le_trans (lower_bound hk0 h2k) (Nat.mul_le_mul_left _ (choose_le_upper h2k H))
  have hb : N ^ k ≤ 2 * k * (2 * k) ^ k * N ^ s := by
    have hm4 : 4 ^ (min k (N / 3)) ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) (min_le_left _ _)
    have h1 : N ^ k * 4 ^ k ≤ (2 * k * (2 * k) ^ k * N ^ s) * 4 ^ k := by
      calc N ^ k * 4 ^ k = 4 ^ k * N ^ k := by ring
        _ ≤ 2 * k * (2 * k) ^ k * (N ^ s * 4 ^ (min k (N / 3))) := hstar
        _ ≤ 2 * k * (2 * k) ^ k * (N ^ s * 4 ^ k) := by gcongr
        _ = (2 * k * (2 * k) ^ k * N ^ s) * 4 ^ k := by ring
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)
  have hkk : 0 < k ^ k := by positivity
  rcases lt_or_ge N (3 * k) with hN3 | hN3
  · -- `N < 3k`
    have hL3 : L ≤ j + 3 := hLb _ (by
      have : 2 ^ (j + 3) = 8 * 2 ^ j := by ring
      have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
      omega)
    have hLr : 4 * (L * r) ≤ k := by
      have : (4 * (L * r)) ^ 2 ≤ k ^ 2 := by
        calc (4 * (L * r)) ^ 2 = 16 * L ^ 2 * r ^ 2 := by ring
          _ ≤ 16 * (j + 3) ^ 2 * (3 * k) := by gcongr; omega
          _ = 48 * (j + 3) ^ 2 * k := by ring
          _ ≤ 2 ^ j * k := Nat.mul_le_mul_right _ (poly1 j hj14)
          _ ≤ k * k := Nat.mul_le_mul_right _ hjk
          _ = k ^ 2 := by ring
      exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
    have hL456 : 456 * L ≤ k := by have := poly1 j hj14; nlinarith
    rcases le_or_gt (2 * N) (5 * k) with h5 | h5
    · -- `2N ≤ 5k`
      have hm : min k (N / 3) = N / 3 := min_eq_right (by omega)
      rw [hm] at hstar
      have h1 : 4 ^ k * N ^ k ≤ (2 * k * N ^ s * 4 ^ (N / 3)) * N ^ k := by
        calc 4 ^ k * N ^ k ≤ 2 * k * (2 * k) ^ k * (N ^ s * 4 ^ (N / 3)) := hstar
          _ ≤ 2 * k * N ^ k * (N ^ s * 4 ^ (N / 3)) := by gcongr
          _ = (2 * k * N ^ s * 4 ^ (N / 3)) * N ^ k := by ring
      have h2 : 4 ^ k ≤ 2 * k * N ^ s * 4 ^ (N / 3) :=
        Nat.le_of_mul_le_mul_right h1 (by positivity)
      have h3 : 4 ^ (k - N / 3) * 4 ^ (N / 3) ≤ (2 * k * N ^ s) * 4 ^ (N / 3) := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]; exact h2
      have h4 := Nat.le_of_mul_le_mul_right h3 (by positivity)
      have h5' : 2 ^ (2 * (k - N / 3)) ≤ 2 * k * N ^ s := by
        rw [pow_mul]; norm_num; exact h4
      apply fin _ h5'
      generalize L * (s + 1) = A at hLs ⊢
      generalize L * r = B at hLs hLr
      omega
    · -- `5k < 2N < 6k`
      have h1 : 5 ^ k * k ^ k ≤ (2 * k * 4 ^ k * N ^ s) * k ^ k := by
        calc 5 ^ k * k ^ k = (5 * k) ^ k := (mul_pow _ _ _).symm
          _ ≤ (2 * N) ^ k := Nat.pow_le_pow_left (by omega) k
          _ = 2 ^ k * N ^ k := mul_pow _ _ _
          _ ≤ 2 ^ k * (2 * k * (2 * k) ^ k * N ^ s) := Nat.mul_le_mul_left _ hb
          _ = (2 * k * 4 ^ k * N ^ s) * k ^ k := by rw [mul_pow, four_pow_eq]; ring
      have h2 := Nat.le_of_mul_le_mul_right h1 hkk
      have h3 : 2 ^ (k / 4) * 4 ^ k ≤ (2 * k * N ^ s) * 4 ^ k := by
        calc 2 ^ (k / 4) * 4 ^ k ≤ 5 ^ k := five_pow k
          _ ≤ 2 * k * 4 ^ k * N ^ s := h2
          _ = (2 * k * N ^ s) * 4 ^ k := by ring
      apply fin _ (Nat.le_of_mul_le_mul_right h3 (by positivity))
      generalize L * (s + 1) = A at hLs ⊢
      generalize L * r = B at hLs hLr
      omega
  · -- `N ≥ 3k`
    rcases lt_or_ge N (8 * k) with h8 | h8
    · have hL4 : L ≤ j + 4 := hLb _ (by
        have : 2 ^ (j + 4) = 16 * 2 ^ j := by ring
        have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
        omega)
      have hLr : 2 * (L * r) ≤ k := by
        have : (2 * (L * r)) ^ 2 ≤ k ^ 2 := by
          calc (2 * (L * r)) ^ 2 = 4 * L ^ 2 * r ^ 2 := by ring
            _ ≤ 4 * (j + 4) ^ 2 * (8 * k) := by gcongr; omega
            _ = 32 * (j + 4) ^ 2 * k := by ring
            _ ≤ 2 ^ j * k := Nat.mul_le_mul_right _ (poly2 j hj14)
            _ ≤ k * k := Nat.mul_le_mul_right _ hjk
            _ = k ^ 2 := by ring
        exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
      have hL114 : 114 * L ≤ k := by have := poly2 j hj14; nlinarith
      have h1 : 2 ^ (k / 2) * 2 ^ k * 2 ^ k * k ^ k ≤ ((2 * k * N ^ s) * 2 ^ k * 2 ^ k) * k ^ k := by
        calc 2 ^ (k / 2) * 2 ^ k * 2 ^ k * k ^ k ≤ 3 ^ k * 2 ^ k * k ^ k := by
              gcongr; exact three_pow k
          _ = (6 * k) ^ k := by rw [mul_pow, show (6 : ℕ) = 3 * 2 by norm_num, mul_pow]
          _ ≤ (2 * N) ^ k := Nat.pow_le_pow_left (by omega) k
          _ = 2 ^ k * N ^ k := mul_pow _ _ _
          _ ≤ 2 ^ k * (2 * k * (2 * k) ^ k * N ^ s) := Nat.mul_le_mul_left _ hb
          _ = ((2 * k * N ^ s) * 2 ^ k * 2 ^ k) * k ^ k := by rw [mul_pow]; ring
      have h2 := Nat.le_of_mul_le_mul_right h1 hkk
      have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity)
      have h4 := Nat.le_of_mul_le_mul_right h3 (by positivity)
      apply fin _ h4
      generalize L * (s + 1) = A at hLs ⊢
      generalize L * r = B at hLs hLr
      omega
    rcases lt_or_ge N (128 * k) with h128 | h128
    · have hL8 : L ≤ j + 8 := hLb _ (by
        have : 2 ^ (j + 8) = 256 * 2 ^ j := by ring
        have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
        omega)
      have hLr : L * r ≤ 2 * k := by
        have : (L * r) ^ 2 ≤ (2 * k) ^ 2 := by
          calc (L * r) ^ 2 = L ^ 2 * r ^ 2 := by ring
            _ ≤ (j + 8) ^ 2 * (128 * k) := by gcongr; omega
            _ = 128 * (j + 8) ^ 2 * k := by ring
            _ ≤ 4 * 2 ^ j * k := Nat.mul_le_mul_right _ (poly3 j hj14)
            _ ≤ 4 * k * k := by gcongr
            _ = (2 * k) ^ 2 := by ring
        exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
      have hL19 : 19 * L ≤ k := by have := poly3 j hj14; nlinarith
      have h1 : 4 ^ k * 2 ^ k * k ^ k ≤ ((2 * k * N ^ s) * 2 ^ k) * k ^ k := by
        calc 4 ^ k * 2 ^ k * k ^ k = (8 * k) ^ k := by
              rw [mul_pow, show (8 : ℕ) = 4 * 2 by norm_num, mul_pow]
          _ ≤ N ^ k := Nat.pow_le_pow_left (by omega) k
          _ ≤ 2 * k * (2 * k) ^ k * N ^ s := hb
          _ = ((2 * k * N ^ s) * 2 ^ k) * k ^ k := by rw [mul_pow]; ring
      have h2 := Nat.le_of_mul_le_mul_right h1 hkk
      have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity)
      have h4 : 2 ^ (2 * k) ≤ 2 * k * N ^ s := by rw [pow_mul]; norm_num; exact h3
      apply fin _ h4
      generalize L * (s + 1) = A at hLs ⊢
      generalize L * r = B at hLs hLr
      omega
    · have hL6 : L ≤ 3 * j + 6 := hLb _ (by
        have e1 : (2 * k) ^ 3 < (2 ^ (j + 2)) ^ 3 := by
          apply Nat.pow_lt_pow_left _ (by norm_num)
          have : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
          omega
        have e2 : (2 ^ (j + 2)) ^ 3 = 2 ^ (3 * j + 6) := by rw [← pow_mul]; ring_nf
        have e3 : N ≤ N ^ 2 := by nlinarith
        omega)
      have hLr : L * r ≤ 15 * k := by
        have : (L * r) ^ 4 ≤ (15 * k) ^ 4 := by
          calc (L * r) ^ 4 = L ^ 4 * (r ^ 2) ^ 2 := by ring
            _ ≤ (3 * j + 6) ^ 4 * N ^ 2 := by gcongr
            _ ≤ (3 * j + 6) ^ 4 * (2 * k) ^ 3 := by gcongr
            _ = 8 * (3 * j + 6) ^ 4 * k ^ 3 := by ring
            _ ≤ 50625 * 2 ^ j * k ^ 3 := Nat.mul_le_mul_right _ (poly4 j hj14)
            _ ≤ 50625 * k * k ^ 3 := by gcongr
            _ = (15 * k) ^ 4 := by ring
        exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
      have hL38 : 38 * L ≤ k := by
        have h1 := poly1 j hj14
        have h2 : 114 * j + 228 ≤ 48 * (j + 3) ^ 2 := aux_lin j
        omega
      have h1 : 64 ^ k * 2 ^ k * k ^ k ≤ ((2 * k * N ^ s) * 2 ^ k) * k ^ k := by
        calc 64 ^ k * 2 ^ k * k ^ k = (128 * k) ^ k := by
              rw [mul_pow, show (128 : ℕ) = 64 * 2 by norm_num, mul_pow]
          _ ≤ N ^ k := Nat.pow_le_pow_left h128 k
          _ ≤ 2 * k * (2 * k) ^ k * N ^ s := hb
          _ = ((2 * k * N ^ s) * 2 ^ k) * k ^ k := by rw [mul_pow]; ring
      have h2 := Nat.le_of_mul_le_mul_right h1 hkk
      have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity)
      have h4 : 2 ^ (6 * k) ≤ 2 * k * N ^ s := by
        have e : (64 : ℕ) = 2 ^ 6 := by norm_num
        rw [e, ← pow_mul] at h3; exact h3
      apply fin _ h4
      generalize L * (s + 1) = A at hLs ⊢
      generalize L * r = B at hLs hLr
      omega

/-- Primes with gaps at most 34, from at most 68 up to `(128)^(3/2)`. -/
def band0 : List ℕ := [67, 101, 131, 163, 197, 229, 263, 293, 317, 349, 383, 409, 443, 467, 499, 523, 557, 587, 619, 653, 683, 709, 743, 773, 797, 829, 863, 887, 919, 953, 983, 1013, 1039, 1069, 1103, 1129, 1163, 1193, 1223, 1249, 1283, 1307, 1327, 1361, 1381, 1409, 1439, 1471]

/-- Primes with gaps at most 64, from at most 128 up to `(256)^(3/2)`. -/
def band1 : List ℕ := [127, 191, 251, 313, 373, 433, 491, 547, 607, 661, 719, 773, 829, 887, 947, 1009, 1069, 1129, 1193, 1249, 1307, 1367, 1429, 1493, 1553, 1613, 1669, 1733, 1789, 1847, 1907, 1951, 2011, 2069, 2131, 2179, 2243, 2297, 2357, 2417, 2477, 2539, 2593, 2657, 2719, 2777, 2837, 2897, 2957, 3019, 3083, 3137, 3191, 3253, 3313, 3373, 3433, 3491, 3547, 3607, 3671, 3733, 3797, 3853, 3917, 3967, 4027, 4091, 4153]

/-- Primes with gaps at most 128, from at most 256 up to `(512)^(3/2)`. -/
def band2 : List ℕ := [251, 379, 503, 631, 757, 883, 1009, 1129, 1249, 1373, 1499, 1627, 1753, 1879, 2003, 2131, 2251, 2377, 2503, 2621, 2749, 2861, 2971, 3089, 3217, 3343, 3469, 3593, 3719, 3847, 3967, 4093, 4219, 4339, 4463, 4591, 4703, 4831, 4957, 5081, 5209, 5333, 5449, 5573, 5701, 5827, 5953, 6079, 6203, 6329, 6451, 6577, 6703, 6829, 6949, 7069, 7193, 7321, 7433, 7561, 7687, 7793, 7919, 8039, 8167, 8293, 8419, 8543, 8669, 8783, 8893, 9013, 9137, 9257, 9377, 9497, 9623, 9749, 9871, 9973, 10099, 10223, 10343, 10463, 10589, 10711, 10837, 10957, 11083, 11197, 11321, 11447, 11551, 11677]

/-- Primes with gaps at most 256, from at most 512 up to `(1024)^(3/2)`. -/
def band3 : List ℕ := [509, 761, 1013, 1259, 1511, 1759, 2011, 2267, 2521, 2777, 3023, 3271, 3527, 3779, 4027, 4283, 4523, 4759, 5011, 5261, 5507, 5749, 5987, 6229, 6481, 6737, 6991, 7247, 7499, 7753, 8009, 8263, 8513, 8761, 9013, 9257, 9511, 9767, 10009, 10259, 10513, 10753, 11003, 11257, 11503, 11743, 11987, 12241, 12497, 12743, 12983, 13229, 13477, 13729, 13967, 14221, 14461, 14717, 14969, 15217, 15473, 15727, 15973, 16229, 16481, 16729, 16981, 17231, 17483, 17737, 17989, 18233, 18481, 18731, 18979, 19231, 19483, 19739, 19993, 20249, 20483, 20731, 20983, 21227, 21481, 21737, 21991, 22247, 22501, 22751, 23003, 23251, 23497, 23753, 24007, 24251, 24499, 24749, 24989, 25243, 25471, 25717, 25969, 26209, 26459, 26713, 26959, 27211, 27457, 27701, 27953, 28201, 28447, 28703, 28949, 29201, 29453, 29683, 29927, 30181, 30431, 30677, 30931, 31183, 31397, 31649, 31891, 32143, 32381, 32633, 32887]

/-- Primes with gaps at most 512, from at most 1024 up to `(2048)^(3/2)`. -/
def band4 : List ℕ := [1021, 1531, 2039, 2551, 3061, 3571, 4079, 4591, 5101, 5591, 6101, 6607, 7109, 7621, 8123, 8629, 9137, 9649, 10159, 10667, 11177, 11689, 12197, 12703, 13187, 13697, 14207, 14717, 15227, 15739, 16249, 16759, 17257, 17761, 18269, 18773, 19273, 19777, 20287, 20789, 21283, 21787, 22291, 22787, 23297, 23801, 24281, 24793, 25303, 25801, 26309, 26821, 27329, 27827, 28319, 28817, 29327, 29837, 30347, 30859, 31357, 31859, 32371, 32869, 33377, 33889, 34381, 34883, 35393, 35899, 36389, 36901, 37409, 37907, 38393, 38903, 39409, 39901, 40387, 40897, 41399, 41911, 42409, 42901, 43411, 43913, 44417, 44927, 45439, 45949, 46457, 46957, 47459, 47969, 48481, 48991, 49499, 49999, 50503, 51001, 51511, 52021, 52529, 53017, 53527, 54037, 54547, 55057, 55547, 56053, 56543, 57047, 57559, 58067, 58579, 59083, 59581, 60091, 60601, 61099, 61609, 62119, 62627, 63131, 63629, 64123, 64633, 65141, 65651, 66161, 66653, 67157, 67651, 68161, 68669, 69163, 69661, 70163, 70667, 71171, 71671, 72173, 72679, 73189, 73699, 74209, 74719, 75227, 75731, 76243, 76753, 77263, 77773, 78283, 78791, 79301, 79813, 80317, 80819, 81331, 81839, 82351, 82847, 83357, 83869, 84377, 84871, 85381, 85889, 86399, 86869, 87359, 87869, 88379, 88883, 89393, 89899, 90407, 90917, 91423, 91921, 92431, 92941]

/-- Primes with gaps at most 1024, from at most 2048 up to `(4096)^(3/2)`. -/
def band5 : List ℕ := [2039, 3061, 4079, 5101, 6121, 7129, 8147, 9161, 10181, 11197, 12211, 13229, 14251, 15271, 16273, 17293, 18313, 19333, 20357, 21379, 22397, 23417, 24439, 25463, 26479, 27487, 28499, 29501, 30517, 31541, 32563, 33587, 34607, 35617, 36637, 37657, 38677, 39679, 40699, 41719, 42743, 43759, 44777, 45779, 46771, 47791, 48809, 49831, 50849, 51871, 52889, 53899, 54919, 55933, 56957, 57977, 58997, 60017, 61031, 62053, 63073, 64091, 65111, 66109, 67129, 68147, 69163, 70183, 71191, 72211, 73189, 74209, 75227, 76249, 77269, 78283, 79301, 80317, 81331, 82351, 83357, 84377, 85381, 86399, 87421, 88427, 89449, 90473, 91493, 92507, 93529, 94547, 95569, 96589, 97613, 98627, 99643, 100649, 101663, 102679, 103703, 104723, 105733, 106753, 107777, 108799, 109819, 110821, 111833, 112843, 113843, 114859, 115883, 116903, 117917, 118931, 119953, 120977, 121997, 123017, 124021, 125029, 126047, 127051, 128053, 129061, 130079, 131101, 132113, 133121, 134129, 135151, 136163, 137183, 138197, 139201, 140221, 141241, 142237, 143261, 144271, 145289, 146309, 147331, 148339, 149351, 150373, 151397, 152419, 153443, 154459, 155473, 156493, 157513, 158537, 159553, 160553, 161573, 162593, 163613, 164627, 165617, 166631, 167641, 168643, 169667, 170689, 171713, 172721, 173743, 174767, 175783, 176807, 177823, 178831, 179849, 180871, 181891, 182899, 183919, 184913, 185923, 186947, 187963, 188983, 189997, 191021, 192043, 193057, 194071, 195089, 196111, 197123, 198139, 199153, 200177, 201193, 202201, 203221, 204233, 205253, 206273, 207293, 208309, 209333, 210347, 211369, 212383, 213407, 214399, 215417, 216431, 217439, 218461, 219467, 220471, 221489, 222511, 223529, 224527, 225529, 226553, 227569, 228593, 229613, 230611, 231631, 232643, 233663, 234683, 235699, 236723, 237737, 238759, 239783, 240797, 241817, 242819, 243839, 244861, 245881, 246899, 247913, 248909, 249923, 250919, 251941, 252949, 253969, 254993, 255989, 257003, 258023, 259033, 260047, 261071, 262079, 263101]

/-- Primes with gaps at most 2048, from at most 4096 up to `(8192)^(3/2)`. -/
def band6 : List ℕ := [4093, 6133, 8179, 10223, 12269, 14303, 16349, 18397, 20443, 22483, 24527, 26573, 28621, 30661, 32707, 34747, 36793, 38839, 40883, 42929, 44971, 47017, 49057, 51071, 53117, 55163, 57203, 59243, 61291, 63337, 65381, 67429, 69473, 71503, 73547, 75583, 77621, 79669, 81707, 83737, 85781, 87811, 89849, 91873, 93913, 95959, 97987, 100019, 102061, 104107, 106129, 108161, 110183, 112223, 114269, 116293, 118297, 120331, 122363, 124367, 126397, 128437, 130483, 132529, 134513, 136559, 138599, 140639, 142673, 144719, 146767, 148793, 150833, 152879, 154927, 156971, 159017, 161059, 163063, 165103, 167149, 169181, 171203, 173249, 175291, 177337, 179383, 181421, 183461, 185491, 187531, 189559, 191599, 193619, 195659, 197699, 199741, 201787, 203821, 205847, 207877, 209917, 211949, 213989, 216037, 218083, 220123, 222163, 224209, 226241, 228281, 230327, 232367, 234383, 236429, 238477, 240517, 242551, 244597, 246643, 248683, 250727, 252767, 254803, 256831, 258871, 260893, 262937, 264977, 267017, 269063, 271109, 273157, 275201, 277247, 279269, 281317, 283303, 285343, 287387, 289423, 291457, 293483, 295517, 297533, 299569, 301601, 303649, 305663, 307711, 309737, 311749, 313783, 315829, 317857, 319901, 321949, 323987, 326023, 328067, 330103, 332147, 334189, 336227, 338269, 340297, 342343, 344371, 346417, 348463, 350503, 352549, 354587, 356621, 358669, 360653, 362693, 364739, 366787, 368833, 370879, 372917, 374953, 376969, 379013, 381061, 383107, 385153, 387199, 389231, 391273, 393311, 395323, 397361, 399409, 401417, 403439, 405487, 407527, 409573, 411617, 413653, 415697, 417737, 419777, 421807, 423853, 425899, 427939, 429973, 432007, 434039, 436087, 438133, 440179, 442217, 444253, 446293, 448321, 450367, 452401, 454417, 456461, 458501, 460543, 462589, 464621, 466651, 468697, 470731, 472763, 474811, 476851, 478897, 480941, 482971, 484999, 487021, 489061, 491083, 493127, 495161, 497197, 499229, 501271, 503317, 505357, 507401, 509449, 511487, 513533, 515579, 517619, 519667, 521707, 523741, 525781, 527819, 529847, 531877, 533921, 535967, 538001, 540041, 542083, 544129, 546173, 548221, 550267, 552301, 554347, 556373, 558421, 560459, 562501, 564533, 566567, 568609, 570649, 572687, 574733, 576769, 578803, 580843, 582887, 584923, 586961, 588977, 591023, 593071, 595117, 597137, 599153, 601201, 603227, 605261, 607309, 609337, 611333, 613381, 615427, 617473, 619511, 621541, 623563, 625609, 627643, 629689, 631733, 633781, 635821, 637841, 639857, 641897, 643927, 645973, 648019, 650059, 652087, 654127, 656171, 658219, 660251, 662287, 664331, 666353, 668347, 670379, 672379, 674419, 676463, 678499, 680539, 682547, 684587, 686611, 688657, 690689, 692729, 694763, 696811, 698849, 700897, 702937, 704983, 707029, 709057, 711097, 713129, 715171, 717191, 719239, 721283, 723319, 725359, 727399, 729413, 731447, 733489, 735533, 737573, 739621, 741667]

/-- Primes with gaps at most 4096, from at most 8192 up to `(16384)^(3/2)`. -/
def band7 : List ℕ := [8191, 12281, 16369, 20443, 24533, 28627, 32719, 36809, 40903, 44987, 49081, 53173, 57269, 61363, 65449, 69539, 73613, 77699, 81773, 85853, 89939, 94033, 98129, 102217, 106307, 110359, 114451, 118543, 122611, 126703, 130787, 134873, 138967, 143063, 147151, 151247, 155333, 159421, 163517, 167611, 171707, 175783, 179849, 183943, 188029, 192121, 196201, 200297, 204377, 208469, 212561, 216653, 220747, 224831, 228923, 232987, 237073, 241169, 245261, 249341, 253433, 257519, 261601, 265621, 269713, 273803, 277897, 281993, 286073, 290161, 294251, 298343, 302429, 306517, 310591, 314651, 318743, 322807, 326903, 330997, 335089, 339173, 343267, 347359, 351437, 355529, 359621, 363691, 367781, 371873, 375967, 380059, 384151, 388237, 392333, 396427, 400523, 404597, 408691, 412771, 416851, 420941, 425027, 429119, 433207, 437293, 441361, 445453, 449549, 453643, 457739, 461819, 465901, 469993, 474077, 478171, 482263, 486349, 490421, 494497, 498583, 502669, 506743, 510827, 514903, 518989, 523049, 527143, 531239, 535333, 539401, 543497, 547583, 551671, 555767, 559859, 563947, 568033, 572107, 576203, 580291, 584387, 588481, 592577, 596671, 600751, 604837, 608903, 612977, 617059, 621143, 625237, 629311, 633407, 637499, 641581, 645661, 649751, 653831, 657911, 662003, 666091, 670177, 674273, 678367, 682463, 686551, 690629, 694721, 698779, 702869, 706961, 711049, 715123, 719203, 723293, 727369, 731447, 735533, 739621, 743711, 747781, 751871, 755959, 760043, 764131, 768221, 772313, 776401, 780469, 784561, 788651, 792731, 796819, 800909, 804997, 809093, 813167, 817237, 821333, 825421, 829511, 833597, 837679, 841751, 845833, 849923, 854017, 858113, 862207, 866293, 870367, 874459, 878551, 882631, 886667, 890761, 894811, 898897, 902987, 907073, 911167, 915259, 919351, 923441, 927533, 931621, 935717, 939793, 943871, 947963, 952057, 956147, 960229, 964309, 968389, 972481, 976571, 980641, 984733, 988829, 992923, 997019, 1001107, 1005203, 1009291, 1013377, 1017473, 1021561, 1025653, 1029731, 1033807, 1037903, 1041991, 1046081, 1050169, 1054259, 1058353, 1062443, 1066531, 1070621, 1074713, 1078807, 1082891, 1086937, 1091033, 1095119, 1099199, 1103293, 1107389, 1111457, 1115551, 1119623, 1123709, 1127803, 1131883, 1135969, 1139993, 1144081, 1148177, 1152233, 1156327, 1160413, 1164503, 1168553, 1172579, 1176673, 1180757, 1184839, 1188931, 1193021, 1197113, 1201201, 1205293, 1209379, 1213469, 1217561, 1221653, 1225729, 1229807, 1233899, 1237993, 1242089, 1246181, 1250273, 1254367, 1258457, 1262543, 1266631, 1270679, 1274773, 1278857, 1282951, 1287047, 1291139, 1295221, 1299317, 1303411, 1307507, 1311599, 1315673, 1319743, 1323799, 1327889, 1331969, 1336057, 1340153, 1344227, 1348313, 1352389, 1356473, 1360537, 1364633, 1368727, 1372799, 1376839, 1380931, 1385023, 1389107, 1393193, 1397287, 1401377, 1405451, 1409543, 1413623, 1417699, 1421779, 1425863, 1429951, 1434031, 1438123, 1442209, 1446301, 1450391, 1454477, 1458547, 1462631, 1466719, 1470797, 1474877, 1478963, 1483049, 1487131, 1491227, 1495321, 1499413, 1503503, 1507591, 1511687, 1515757, 1519831, 1523917, 1528013, 1532107, 1536191, 1540249, 1544341, 1548433, 1552517, 1556609, 1560683, 1564777, 1568873, 1572929, 1577021, 1581113, 1585201, 1589297, 1593379, 1597469, 1601563, 1605631, 1609717, 1613813, 1617893, 1621979, 1626073, 1630169, 1634257, 1638353, 1642447, 1646543, 1650637, 1654733, 1658827, 1662901, 1666991, 1671077, 1675139, 1679233, 1683317, 1687393, 1691479, 1695559, 1699651, 1703731, 1707791, 1711859, 1715927, 1720003, 1724083, 1728179, 1732273, 1736369, 1740461, 1744549, 1748639, 1752721, 1756817, 1760897, 1764979, 1769069, 1773157, 1777247, 1781341, 1785431, 1789519, 1793611, 1797673, 1801769, 1805863, 1809953, 1814047, 1818109, 1822189, 1826281, 1830349, 1834439, 1838531, 1842619, 1846711, 1850803, 1854899, 1858973, 1863067, 1867157, 1871249, 1875337, 1879429, 1883513, 1887607, 1891679, 1895767, 1899847, 1903931, 1908013, 1912093, 1916183, 1920271, 1924343, 1928419, 1932503, 1936579, 1940663, 1944737, 1948801, 1952893, 1956979, 1961059, 1965133, 1969223, 1973317, 1977407, 1981493, 1985587, 1989683, 1993763, 1997851, 2001919, 2006009, 2010103, 2014193, 2018287, 2022359, 2026447, 2030533, 2034619, 2038703, 2042797, 2046893, 2050987, 2055071, 2059157, 2063251, 2067337, 2071429, 2075483, 2079577, 2083643, 2087717, 2091809, 2095867, 2099963]

/-- Primes with gaps at most 8192, from at most 16384 up to `(32768)^(3/2)`. -/
def band8 : List ℕ := [16381, 24571, 32749, 40939, 49123, 57301, 65479, 73651, 81839, 90031, 98221, 106411, 114601, 122789, 130981, 139169, 147353, 155539, 163729, 171917, 180097, 188281, 196459, 204641, 212827, 220973, 229157, 237343, 245533, 253717, 261887, 270073, 278261, 286453, 294641, 302833, 311021, 319211, 327401, 335591, 343771, 351959, 360091, 368279, 376471, 384641, 392831, 401017, 409187, 417379, 425563, 433747, 441937, 450127, 458317, 466483, 474671, 482863, 491041, 499229, 507421, 515611, 523801, 531989, 540181, 548371, 556559, 564713, 572903, 581089, 589273, 597451, 605641, 613829, 622019, 630197, 638371, 646549, 654739, 662917, 671093, 679279, 687461, 695641, 703819, 712007, 720197, 728383, 736511, 744701, 752891, 761069, 769261, 777451, 785641, 793813, 801989, 810151, 818341, 826499, 834671, 842857, 851041, 859223, 867413, 875593, 883783, 891967, 900157, 908321, 916511, 924697, 932887, 941041, 949213, 957403, 965567, 973759, 981949, 990137, 998329, 1006513, 1014697, 1022881, 1031057, 1039249, 1047419, 1055611, 1063781, 1071943, 1080119, 1088309, 1096499, 1104683, 1112857, 1121047, 1129229, 1137407, 1145593, 1153777, 1161949, 1170139, 1178297, 1186489, 1194679, 1202867, 1211059, 1219241, 1227431, 1235593, 1243783, 1251961, 1260143, 1268327, 1276511, 1284691, 1292857, 1301033, 1309219, 1317409, 1325581, 1333751, 1341931, 1350119, 1358309, 1366493, 1374683, 1382861, 1391051, 1399231, 1407409, 1415591, 1423781, 1431967, 1440119, 1448309, 1456501, 1464689, 1472869, 1481047, 1489231, 1497421, 1505611, 1513777, 1521937, 1530107, 1538293, 1546477, 1554659, 1562833, 1571023, 1579187, 1587361, 1595527, 1603711, 1611901, 1620071, 1628261, 1636423, 1644611, 1652801, 1660963, 1669147, 1677337, 1685527, 1693711, 1701901, 1710091, 1718281, 1726471, 1734647, 1742809, 1750999, 1759181, 1767373, 1775563, 1783751, 1791943, 1800121, 1808309, 1816489, 1824679, 1832863, 1841039, 1849231, 1857407, 1865587, 1873771, 1881961, 1890149, 1898317, 1906481, 1914673, 1922863, 1931053, 1939243, 1947431, 1955609, 1963799, 1971967, 1980113, 1988299, 1996487, 2004679, 2012849, 2021029, 2029207, 2037391, 2045569, 2053757, 2061923, 2070091, 2078243, 2086433, 2094623, 2102809, 2110981, 2119171, 2127347, 2135537, 2143711, 2151899, 2160061, 2168239, 2176423, 2184583, 2192761, 2200949, 2209117, 2217301, 2225491, 2233657, 2241809, 2249987, 2258177, 2266343, 2274523, 2282711, 2290901, 2299093, 2307281, 2315471, 2323631, 2331781, 2339969, 2348161, 2356351, 2364521, 2372687, 2380877, 2389067, 2397259, 2405443, 2413613, 2421791, 2429983, 2438173, 2446363, 2454539, 2462731, 2470903, 2479069, 2487259, 2495443, 2503597, 2511779, 2519969, 2528161, 2536343, 2544523, 2552713, 2560891, 2569079, 2577241, 2585417, 2593609, 2601787, 2609963, 2618117, 2626307, 2634493, 2642639, 2650829, 2659001, 2667193, 2675369, 2683561, 2691743, 2699911, 2708099, 2716289, 2724481, 2732671, 2740853, 2749031, 2757221, 2765387, 2773579, 2781749, 2789939, 2798129, 2806291, 2814481, 2822669, 2830859, 2839049, 2847227, 2855399, 2863591, 2871767, 2879927, 2888117, 2896297, 2904487, 2912659, 2920837, 2929009, 2937173, 2945359, 2953537, 2961727, 2969903, 2978089, 2986259, 2994449, 3002641, 3010831, 3019019, 3027187, 3035371, 3043559, 3051751, 3059921, 3068111, 3076289, 3084481, 3092669, 3100861, 3109031, 3117223, 3125387, 3133547, 3141713, 3149903, 3158087, 3166279, 3174467, 3182659, 3190829, 3199013, 3207199, 3215383, 3223567, 3231757, 3239947, 3248137, 3256327, 3264491, 3272681, 3280867, 3289043, 3297209, 3305389, 3313577, 3321763, 3329939, 3338131, 3346309, 3354493, 3362683, 3370849, 3379037, 3387203, 3395369, 3403559, 3411743, 3419921, 3428099, 3436291, 3444481, 3452671, 3460819, 3468991, 3477161, 3485353, 3493541, 3501733, 3509917, 3518101, 3526283, 3534473, 3542657, 3550843, 3559019, 3567211, 3575371, 3583543, 3591733, 3599899, 3608071, 3616259, 3624443, 3632633, 3640823, 3649003, 3657187, 3665377, 3673529, 3681719, 3689911, 3698099, 3706259, 3714439, 3722629, 3730817, 3739009, 3747197, 3755387, 3763567, 3771751, 3779929, 3788117, 3796307, 3804491, 3812663, 3820853, 3828973, 3837151, 3845341, 3853529, 3861721, 3869881, 3878051, 3886237, 3894419, 3902609, 3910787, 3918949, 3927139, 3935311, 3943481, 3951611, 3959803, 3967993, 3976183, 3984347, 3992533, 4000723, 4008887, 4017067, 4025249, 4033423, 4041601, 4049789, 4057969, 4066151, 4074319, 4082489, 4090679, 4098869, 4107029, 4115213, 4123387, 4131577, 4139767, 4147943, 4156093, 4164271, 4172431, 4180621, 4188803, 4196993, 4205183, 4213369, 4221551, 4229741, 4237927, 4246111, 4254277, 4262459, 4270639, 4278829, 4286987, 4295177, 4303361, 4311551, 4319743, 4327913, 4336103, 4344283, 4352473, 4360663, 4368823, 4377001, 4385159, 4393321, 4401497, 4409687, 4417813, 4425997, 4434181, 4442363, 4450553, 4458739, 4466923, 4475083, 4483273, 4491439, 4499623, 4507799, 4515943, 4524097, 4532267, 4540439, 4548631, 4556813, 4565003, 4573183, 4581331, 4589521, 4597709, 4605901, 4614067, 4622257, 4630447, 4638631, 4646821, 4655009, 4663201, 4671389, 4679581, 4687769, 4695953, 4704127, 4712317, 4720501, 4728677, 4736861, 4745051, 4753219, 4761403, 4769593, 4777781, 4785961, 4794151, 4802339, 4810517, 4818691, 4826867, 4835057, 4843247, 4851397, 4859581, 4867771, 4875943, 4884127, 4892309, 4900501, 4908691, 4916869, 4925029, 4933207, 4941383, 4949551, 4957739, 4965923, 4974097, 4982273, 4990463, 4998647, 5006839, 5014979, 5023169, 5031361, 5039549, 5047739, 5055923, 5064091, 5072269, 5080451, 5088631, 5096813, 5104993, 5113169, 5121359, 5129489, 5137681, 5145871, 5154049, 5162233, 5170411, 5178599, 5186777, 5194967, 5203157, 5211347, 5219537, 5227727, 5235917, 5244103, 5252281, 5260469, 5268647, 5276833, 5284999, 5293181, 5301367, 5309539, 5317703, 5325869, 5334047, 5342237, 5350417, 5358607, 5366791, 5374973, 5383159, 5391349, 5399531, 5407693, 5415881, 5424053, 5432239, 5440427, 5448617, 5456807, 5464981, 5473147, 5481323, 5489513, 5497697, 5505889, 5514079, 5522261, 5530439, 5538581, 5546771, 5554951, 5563127, 5571283, 5579461, 5587627, 5595817, 5604007, 5612179, 5620369, 5628533, 5636693, 5644861, 5653049, 5661217, 5669387, 5677571, 5685763, 5693921, 5702063, 5710223, 5718413, 5726587, 5734747, 5742937, 5751113, 5759267, 5767453, 5775617, 5783807, 5791993, 5800159, 5808349, 5816521, 5824703, 5832847, 5841029, 5849203, 5857381, 5865571, 5873761, 5881919, 5890111, 5898293, 5906449, 5914627, 5922811, 5930963, 5939149]

def bnd : List ℕ := [0, 3, 9, 49, 20, 62, 36, 87, 57, 46, 40, 66, 58, 91, 79, 71, 66, 93, 86, 119, 109, 101, 95, 125, 117, 111, 107, 103, 99, 123, 119, 146, 140, 136]
def lpf : List ℕ := [2, 2, 2, 3, 2, 5, 3, 7, 2, 3, 5, 11, 3, 13, 7, 5, 2, 17, 3, 19, 5, 7, 11, 23, 3, 5, 13, 3, 7, 29, 5, 31, 2, 11, 17, 7, 3, 37, 19, 13, 5, 41, 7, 43, 11, 5, 23, 47, 3, 7, 5, 17, 13, 53, 3, 11, 7, 19, 29, 59, 5, 61, 31, 7, 2, 13, 11, 67, 17, 23, 7, 71, 3, 73, 37, 5, 19, 11, 13, 79, 5, 3, 41, 83, 7, 17, 43, 29, 11, 89, 5, 13, 23, 31, 47, 19, 3, 97, 7, 11, 5, 101, 17, 103, 13, 7, 53, 107, 3, 109, 11, 37, 7, 113, 19, 23, 29, 13, 59, 17, 5, 11, 61, 41, 31, 5, 7, 127, 2, 43, 13, 131, 11, 19, 67, 5, 17, 137, 23, 139, 7, 47, 71, 13, 3, 29, 73]
def smallPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139]

/-! ## Step 5: the finite residue -/

lemma prime_dvd_choose_of_dvd_term {p N k i : ℕ} (hp : p.Prime) (hkp : k < p) (hi : i < k)
    (hd : p ∣ N - i) : p ∣ N.choose k := by
  have h1 : p ∣ N.descFactorial k := by
    rw [Nat.descFactorial_eq_prod_range]
    exact dvd_trans hd (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hi))
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
  · exact absurd ((Nat.Prime.dvd_factorial hp).1 h) (by omega)
  · exact h

/-- Boolean check that consecutive entries of a list differ by at most `g`. -/
def chainOK (g : ℕ) : List ℕ → Bool
  | a :: b :: rest => decide (b ≤ a + g) && chainOK g (b :: rest)
  | _ => true

/-- The last entry of a list (`0` for the empty list). -/
def lastD : List ℕ → ℕ
  | [] => 0
  | [a] => a
  | _ :: b :: rest => lastD (b :: rest)

lemma window_ok (g N : ℕ) (hg : 0 < g) :
    ∀ (rest : List ℕ) (a : ℕ), chainOK g (a :: rest) = true → a ≤ N →
      N ≤ lastD (a :: rest) → ∃ p ∈ a :: rest, p ≤ N ∧ N < p + g
  | [], a, _, h1, h2 => ⟨a, List.mem_cons_self, h1, by simp only [lastD] at h2; omega⟩
  | b :: rest, a, hc, h1, h2 => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hc
    by_cases hN : N < b
    · exact ⟨a, List.mem_cons_self, h1, by omega⟩
    · obtain ⟨p, hp, h⟩ := window_ok g N hg rest b hc.2 (by omega)
        (by simp only [lastD] at h2; exact h2)
      exact ⟨p, List.mem_cons_of_mem _ hp, h⟩

lemma band_ok (L : List ℕ) (lo hi : ℕ) (hlo : 0 < lo) (hpr : ∀ p ∈ L, p.Prime)
    (hch : chainOK lo L = true) (ha2 : L.headD 0 ≤ 2 * lo) (hb2 : (2 * hi) ^ 3 ≤ lastD L ^ 2)
    {N k : ℕ} (hk1 : lo ≤ k) (hk2 : k < hi)
    (h2k : 2 * k ≤ N) (hsm : N ^ 2 < (2 * k) ^ 3) : ∃ p, p.Prime ∧ k < p ∧ p ∣ N.choose k := by
  have hNb : N ≤ lastD L := by
    have h3 : (2 * k) ^ 3 ≤ (2 * hi) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have : N ^ 2 < lastD L ^ 2 := by omega
    exact ((Nat.pow_lt_pow_iff_left (by norm_num)).1 this).le
  cases L with
  | nil =>
    simp only [lastD] at hb2
    have : 0 < (2 * hi) ^ 3 := pow_pos (by omega) 3
    omega
  | cons a rest =>
    simp only [List.headD_cons] at ha2
    obtain ⟨p, hpL, hpN, hNp⟩ := window_ok lo N hlo rest a hch (by omega) hNb
    refine ⟨p, hpr p hpL, by omega, ?_⟩
    exact prime_dvd_choose_of_dvd_term (i := N - p) (hpr p hpL) (by omega) (by omega)
      (by rw [show N - (N - p) = p by omega])

set_option maxRecDepth 100000 in
lemma band0_prime : ∀ p ∈ band0, p.Prime := by
  simp only [band0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band0_chain : chainOK 34 band0 = true := by decide

set_option maxRecDepth 100000 in
lemma band0_ends : band0.headD 0 ≤ 2 * 34 ∧ (2 * 64) ^ 3 ≤ lastD band0 ^ 2 := by decide

set_option maxRecDepth 100000 in
lemma band1_prime : ∀ p ∈ band1, p.Prime := by
  simp only [band1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band1_chain : chainOK 64 band1 = true := by decide

set_option maxRecDepth 100000 in
lemma band1_ends : band1.headD 0 ≤ 2 * 64 ∧ (2 * 128) ^ 3 ≤ lastD band1 ^ 2 := by decide

set_option maxRecDepth 100000 in
lemma band2_prime : ∀ p ∈ band2, p.Prime := by
  simp only [band2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band2_chain : chainOK 128 band2 = true := by decide

set_option maxRecDepth 100000 in
lemma band2_ends : band2.headD 0 ≤ 2 * 128 ∧ (2 * 256) ^ 3 ≤ lastD band2 ^ 2 := by decide

set_option maxRecDepth 100000 in
lemma band3_prime : ∀ p ∈ band3, p.Prime := by
  simp only [band3, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band3_chain : chainOK 256 band3 = true := by decide

set_option maxRecDepth 100000 in
lemma band3_ends : band3.headD 0 ≤ 2 * 256 ∧ (2 * 512) ^ 3 ≤ lastD band3 ^ 2 := by decide

set_option maxRecDepth 100000 in
lemma band4_prime : ∀ p ∈ band4, p.Prime := by
  simp only [band4, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band4_chain : chainOK 512 band4 = true := by decide

set_option maxRecDepth 100000 in
lemma band4_ends : band4.headD 0 ≤ 2 * 512 ∧ (2 * 1024) ^ 3 ≤ lastD band4 ^ 2 := by decide

set_option maxRecDepth 100000 in
lemma band5_prime : ∀ p ∈ band5, p.Prime := by
  simp only [band5, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band5_chain : chainOK 1024 band5 = true := by decide

set_option maxRecDepth 100000 in
lemma band5_ends : band5.headD 0 ≤ 2 * 1024 ∧ (2 * 2048) ^ 3 ≤ lastD band5 ^ 2 := by decide

set_option maxRecDepth 100000 in
lemma band6_prime : ∀ p ∈ band6, p.Prime := by
  simp only [band6, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band6_chain : chainOK 2048 band6 = true := by decide

set_option maxRecDepth 100000 in
lemma band6_ends : band6.headD 0 ≤ 2 * 2048 ∧ (2 * 4096) ^ 3 ≤ lastD band6 ^ 2 := by decide

set_option maxRecDepth 100000 in
lemma band7_prime : ∀ p ∈ band7, p.Prime := by
  simp only [band7, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band7_chain : chainOK 4096 band7 = true := by decide

set_option maxRecDepth 100000 in
lemma band7_ends : band7.headD 0 ≤ 2 * 4096 ∧ (2 * 8192) ^ 3 ≤ lastD band7 ^ 2 := by decide

set_option maxRecDepth 100000 in
lemma band8_prime : ∀ p ∈ band8, p.Prime := by
  simp only [band8, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band8_chain : chainOK 8192 band8 = true := by decide

set_option maxRecDepth 100000 in
lemma band8_ends : band8.headD 0 ≤ 2 * 8192 ∧ (2 * 16384) ^ 3 ≤ lastD band8 ^ 2 := by decide

lemma small_bound {N k B : ℕ} (hB : 2 ^ k * k ! < B ^ (k - pc k)) (hpk : pc k ≤ k)
    (hBN : B ≤ N) (hc : N ^ k ≤ 2 ^ k * k ! * N ^ pc k) (hN : 0 < N) : False := by
  have h1 : N ^ k = N ^ (k - pc k) * N ^ pc k := by rw [← pow_add, Nat.sub_add_cancel hpk]
  have h2 : B ^ (k - pc k) ≤ N ^ (k - pc k) := Nat.pow_le_pow_left hBN _
  have h3 : 2 ^ k * k ! * N ^ pc k < B ^ (k - pc k) * N ^ pc k :=
    Nat.mul_lt_mul_of_pos_right hB (by positivity)
  have h4 : B ^ (k - pc k) * N ^ pc k ≤ N ^ k := by rw [h1]; exact Nat.mul_le_mul_right _ h2
  omega

set_option maxRecDepth 100000 in
lemma small_table : ∀ k < 34, 1 ≤ k → pc k ≤ k ∧ 2 ^ k * k ! < (bnd.getD k 0) ^ (k - pc k) := by
  decide

set_option maxRecDepth 100000 in
lemma small_witness : ∀ k < 34, ∀ N < 147, 1 ≤ k → 2 * k ≤ N → N < bnd.getD k 0 →
    ∃ i < k, k < lpf.getD (N - i) 0 := by
  decide

set_option maxRecDepth 100000 in
lemma lpf_mem : ∀ j < 147, 2 ≤ j → lpf.getD j 0 ∈ smallPrimes ∧ lpf.getD j 0 ∣ j := by
  decide

lemma smallPrimes_prime : ∀ p ∈ smallPrimes, p.Prime := by
  simp only [smallPrimes, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  norm_num

lemma bnd_le (k : ℕ) (hk : k < 34) (hk1 : 1 ≤ k) : bnd.getD k 0 ≤ 147 := by
  interval_cases k <;> decide

/-- **Sylvester–Schur** in binomial form. -/
theorem sylvester (k N : ℕ) (hk : 0 < k) (h2k : 2 * k ≤ N) :
    ∃ p, p.Prime ∧ k < p ∧ p ∣ N.choose k := by
  by_contra hcon
  have H : ∀ p, p.Prime → p ∣ N.choose k → p ≤ k := fun p hp hd => by
    by_contra h
    exact hcon ⟨p, hp, by omega, hd⟩
  rcases lt_or_ge k 34 with hk34 | hk34
  · obtain ⟨hpk, hB⟩ := small_table k hk34 hk
    rcases lt_or_ge N (bnd.getD k 0) with hNB | hNB
    · have h147 := bnd_le k hk34 hk
      obtain ⟨i, hi, hki⟩ := small_witness k hk34 N (by omega) hk h2k hNB
      obtain ⟨hmem, hdvd⟩ := lpf_mem (N - i) (by omega) (by omega)
      have hq := smallPrimes_prime _ hmem
      exact hcon ⟨_, hq, hki, prime_dvd_choose_of_dvd_term hq hki hi hdvd⟩
    · exact small_bound hB hpk hNB (counting_bound h2k (by omega) H) (by omega)
  · have hsm := not_large_region hk34 h2k H
    rcases lt_or_ge k 16384 with hkb | hkb
    · apply hcon

      rcases lt_or_ge k 64 with h0 | h0
      · exact band_ok band0 34 64 (by norm_num) band0_prime band0_chain band0_ends.1
          band0_ends.2 (by omega) h0 h2k hsm
      rcases lt_or_ge k 128 with h1 | h1
      · exact band_ok band1 64 128 (by norm_num) band1_prime band1_chain band1_ends.1
          band1_ends.2 (by omega) h1 h2k hsm
      rcases lt_or_ge k 256 with h2 | h2
      · exact band_ok band2 128 256 (by norm_num) band2_prime band2_chain band2_ends.1
          band2_ends.2 (by omega) h2 h2k hsm
      rcases lt_or_ge k 512 with h3 | h3
      · exact band_ok band3 256 512 (by norm_num) band3_prime band3_chain band3_ends.1
          band3_ends.2 (by omega) h3 h2k hsm
      rcases lt_or_ge k 1024 with h4 | h4
      · exact band_ok band4 512 1024 (by norm_num) band4_prime band4_chain band4_ends.1
          band4_ends.2 (by omega) h4 h2k hsm
      rcases lt_or_ge k 2048 with h5 | h5
      · exact band_ok band5 1024 2048 (by norm_num) band5_prime band5_chain band5_ends.1
          band5_ends.2 (by omega) h5 h2k hsm
      rcases lt_or_ge k 4096 with h6 | h6
      · exact band_ok band6 2048 4096 (by norm_num) band6_prime band6_chain band6_ends.1
          band6_ends.2 (by omega) h6 h2k hsm
      rcases lt_or_ge k 8192 with h7 | h7
      · exact band_ok band7 4096 8192 (by norm_num) band7_prime band7_chain band7_ends.1
          band7_ends.2 (by omega) h7 h2k hsm
      exact band_ok band8 8192 16384 (by norm_num) band8_prime band8_chain band8_ends.1
        band8_ends.2 (by omega) hkb h2k hsm
    · exact middle_region (by norm_num; omega) h2k hsm H

end SylvesterSchurOMA

namespace Erdos137H3Square

open Finset

theorem sylvester_block (n k : ℕ) (hk : 0 < k) (hn : k < n) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ t ∈ Ioc n (n+k), t := by
  obtain ⟨p, hp, hpBig, hpChoose⟩ := SylvesterSchurOMA.sylvester k (n+k) hk (by omega)
  have hd : p ∣ (n+k).descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact Dvd.dvd.mul_left hpChoose _
  rw [Nat.descFactorial_eq_prod_range] at hd
  obtain ⟨i, hi, hpTerm⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
  have hi' := mem_range.mp hi
  have ht : n+k-i ∈ Ioc n (n+k) := mem_Ioc.mpr ⟨by omega, by omega⟩
  exact ⟨p, hp, hpBig, hpTerm.trans (Finset.dvd_prod_of_mem (fun t : ℕ => t) ht)⟩

end Erdos137H3Square

open Finset

theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_perfect_power_R1_H3_R1.H2 := by
  intro k n l hk hn hlPrime hlOdd
  have hSylvester := Erdos137H3Square.sylvester_block n k (by omega) hn
  have hl : 3 ≤ l := by omega
  by_cases hSmall : k ≤ 1000
  · exact Erdos137PerfectPower.small_odd_prime_of_sylvester hk hSmall hlPrime hl hSylvester
  by_cases hMedium : k ≤ 30000
  · exact Erdos137PerfectPower.medium_odd_prime_of_sylvester (by omega) hMedium hlPrime hl hSylvester
  apply Erdos137PerfectPower.odd_branch_from_rank_certificate hk hl hSylvester
  by_cases hDirect : k ≤ 300000
  · exact Erdos137OddBridge.bridge_rank_product k (by omega) hDirect
  by_cases hBridge : k < 2^21
  · apply Erdos137OddBridge.analytic_rank_product k (by omega) hBridge
    intro m hm
    rw [← Nat.primesBelow_eq_filter_range, Nat.primesBelow_eq_primesLE_sub_one]
    exact Erdos137OddTail.dyadic_prime_bound_valid hm Erdos137OddBridge.countingBound
      (Erdos137OddBridge.counting_bound_valid (fun n =>
        Erdos137OddPrimorial.prime_count_linear_from_cutoff n 18 23350 Erdos137OddBridge.prime_count_at_262144))
      Erdos137OddPrimorial.primorial_eighth_le
  · exact Erdos137OddTail.tail_from_prime_estimates k (by omega)
      Erdos137OddPrimorial.primorial_eighth_le (fun n =>
        Erdos137OddPrimorial.prime_count_linear_from_cutoff n 16 6700 Erdos137OddBridge.prime_count_at_65536)
