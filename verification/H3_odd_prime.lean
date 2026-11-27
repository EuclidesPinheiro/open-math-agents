import FormalConjectures.ErdosProblems.«137»
import Mathlib.Data.Nat.Choose.Factorization

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

theorem sylvester_schur_lower_bound_of_no_witness {k n l : ℕ}
    (hl : 2 ≤ l)
    (hSylvester : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ m ∈ Ioc n (n + k), m)
    (hAll : ∀ p : ℕ, k ≤ p → p.Prime →
      l ∣ (∏ m ∈ Ioc n (n + k), m).factorization p) : k ^ l < n := by
  obtain ⟨p, hp, hkp, hProd⟩ := hSylvester
  obtain ⟨m, hm, hpm⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hProd
  have hmBounds := mem_Ioc.mp hm
  have hmNonzero : m ≠ 0 := by omega
  have hDiv := hAll p hkp.le hp
  rw [large_prime_factorization_single hkp.le hm hpm] at hDiv
  have hPos := hp.factorization_pos_of_dvd hmNonzero hpm
  have hPow := (hp.pow_dvd_iff_le_factorization hmNonzero).2 (Nat.le_of_dvd hPos hDiv)
  exact sylvester_schur_lower_bound hl hkp hm hPow

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
      _ = ∏ t ∈ Ioo n m, m-t := by
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
      _ = ∏ t ∈ Ioc m (n+k), t-m := by
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

end Erdos137PerfectPower
