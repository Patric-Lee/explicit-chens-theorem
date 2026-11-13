import BJSSquareHarmonic

noncomputable section
namespace ChenEffective
open Real Finset
open AnalyticNumberTheory.LargeSieve
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem inverse_square_summable : Summable (fun n : ℕ => 1/(n:ℝ)^2) := by
  have hh := Real.summable_nat_rpow.mpr (by norm_num : -(2:ℝ)< -1)
  simpa only [rpow_neg (Nat.cast_nonneg _),rpow_two,one_div] using hh

theorem inverse_three_halves_summable : Summable (fun n : ℕ => 1/((n:ℝ)*sqrt n)) := by
  have hh := Real.summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ)< -1)
  apply hh.congr
  intro n
  by_cases hn : n=0
  · subst n; norm_num
  have hn0 : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [rpow_neg hn0.le,show (3/2:ℝ)=1+1/2 by norm_num,rpow_add hn0,
    rpow_one,← sqrt_eq_rpow,one_div]

theorem square_harmonic_mass_large {x : ℝ} (hx : 1≤x) :
    Summable (fun n => |squareHarmonicResidual x n|) ∧
    (∑' n,|squareHarmonicResidual x n|) ≤ 20/sqrt x := by
  let q := ⌊sqrt x⌋₊
  have hx0 : 0<x := by linarith only [hx]
  have hs0 : 0<sqrt x := sqrt_pos.mpr hx0
  have hq : 1≤q := Nat.le_floor (by simpa using one_le_sqrt.mpr hx)
  have hq0 : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hqx : (q:ℝ)≤sqrt x := Nat.floor_le (sqrt_nonneg _)
  have hxq : sqrt x<(q:ℝ)+1 := Nat.lt_floor_add_one _
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  let head : ℕ → ℝ := fun n => if n∈Icc 1 q then 2/x else 0
  let tail : ℕ → ℝ := fun n => if q<n then
    (4/sqrt q)*(1/((n:ℝ)*sqrt n))+1/(n:ℝ)^2 else 0
  have hhead : Summable head := summable_of_ne_finset_zero (s:=Icc 1 q)
    (by intro n hn; exact if_neg hn)
  have ht3 : Summable (fun n : ℕ => if q<n then 1/((n:ℝ)*sqrt n) else 0) := by
    apply (inverse_three_halves_summable.indicator {n : ℕ | q<n}).congr
    intro n
    by_cases hn : q<n <;> simp [Set.indicator,hn]
  have ht2 : Summable (fun n : ℕ => if q<n then 1/(n:ℝ)^2 else 0) := by
    apply (inverse_square_summable.indicator {n : ℕ | q<n}).congr
    intro n
    by_cases hn : q<n <;> simp [Set.indicator,hn]
  have htail : Summable tail := by
    apply ((ht3.mul_left (4/sqrt q)).add ht2).congr
    intro n
    by_cases hn : q<n <;> simp [tail,hn]
  have hb (n : ℕ) : |squareHarmonicResidual x n|≤head n+tail n := by
    by_cases hn0 : n=0
    · subst n; simp [squareHarmonicResidual,head,tail]
    by_cases hn : n≤q
    · have hmem : n∈Icc 1 q := mem_Icc.mpr ⟨by omega,hn⟩
      simp only [head,tail,if_pos hmem,if_neg (by omega : ¬q<n),add_zero]
      have hnq : (n:ℝ)≤q := by exact_mod_cast hn
      exact square_harmonic_head hx (by omega) (hnq.trans hqx)
    · have hqn : q<n := by omega
      have hnm : n∉Icc 1 q := by simp only [mem_Icc]; omega
      simp only [head,tail,if_neg hnm,if_pos hqn,zero_add]
      exact square_harmonic_tail hx hq hqx (Nat.floor_lt (sqrt_nonneg _)|>.mp hqn)
  have habs : Summable (fun n => |squareHarmonicResidual x n|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hb (hhead.add htail)
  refine ⟨habs,?_⟩
  have hheadsum : (∑' n,head n)=(q:ℝ)*(2/x) := by
    rw [tsum_eq_sum (s:=Icc 1 q) (by intro n hn; exact if_neg hn)]
    calc
      _ = ∑ n∈Icc 1 q,(2/x) := sum_congr rfl (by intro n hn; exact if_pos hn)
      _ = _ := by simp
  have htailsum : (∑' n,tail n) ≤ 9/(q:ℝ) := by
    have he : tail = fun n =>
        (4/sqrt q)*(if q<n then 1/((n:ℝ)*sqrt n) else 0)+
        (if q<n then 1/(n:ℝ)^2 else 0) := by
      funext n; by_cases hn : q<n <;> simp [tail,hn]
    rw [he,(ht3.mul_left _).tsum_add ht2,tsum_mul_left]
    have h3 := inverse_three_halves_tail hq
    have h2 := inverse_square_tail hq
    have hs := sq_sqrt hq0.le
    calc
      _ ≤ (4/sqrt q)*(2/sqrt q)+1/(q:ℝ) := by
        exact add_le_add (mul_le_mul_of_nonneg_left h3 (by positivity)) h2
      _ = _ := by field_simp; nlinarith only [hs]
  have hh : (q:ℝ)*(2/x)≤2/sqrt x := by
    have hs := sq_sqrt hx0.le
    calc
      _ ≤ sqrt x*(2/x) := mul_le_mul_of_nonneg_right hqx (by positivity)
      _ = _ := by field_simp; nlinarith only [hs]
  have hqt : 9/(q:ℝ)≤18/sqrt x := by
    apply (div_le_div_iff₀ hq0 hs0).mpr
    linarith only [hxq,hq1]
  calc
    _ ≤ (∑' n, (head n+tail n)) := habs.tsum_le_tsum hb (hhead.add htail)
    _ = (∑' n,head n)+(∑' n,tail n) := hhead.tsum_add htail
    _ ≤ 2/sqrt x+18/sqrt x := by rw [hheadsum]; exact add_le_add hh (htailsum.trans hqt)
    _ = 20/sqrt x := by ring

theorem square_harmonic_mass_small {x : ℝ} (hx : 0<x) (hx1 : x<1) :
    Summable (fun n => |squareHarmonicResidual x n|) ∧
    (∑' n,|squareHarmonicResidual x n|) ≤ 20/sqrt x := by
  have hs : 0<sqrt x := sqrt_pos.mpr hx
  have hs1 : sqrt x≤1 := sqrt_le_one.mpr hx1.le
  have hlogx : -log x≤2/sqrt x := by
    have hh := log_le_rpow_div (by positivity : (0:ℝ)≤1/x) (by norm_num : (0:ℝ)<1/2)
    rw [log_div (by norm_num) hx.ne',log_one,zero_sub,← sqrt_eq_rpow,
      sqrt_div (by norm_num),sqrt_one] at hh
    convert hh using 1
    ring
  let major : ℕ → ℝ := fun n => (3/sqrt x)*(1/(n:ℝ)^2)+
    (4/sqrt x)*(1/((n:ℝ)*sqrt n))
  have hm : Summable major := (inverse_square_summable.mul_left _).add
    (inverse_three_halves_summable.mul_left _)
  have hb (n : ℕ) : |squareHarmonicResidual x n|≤major n := by
    by_cases hn : n=0
    · subst n; simp [squareHarmonicResidual,major]
    have hn1 : 1≤n := Nat.one_le_iff_ne_zero.mpr hn
    have hnR : (1:ℝ)≤n := by exact_mod_cast hn1
    have hn0 : (0:ℝ)<n := by positivity
    have hns : 0<sqrt (n:ℝ) := sqrt_pos.mpr hn0
    have hsq := sq_sqrt hn0.le
    have hsmall : x/(n:ℝ)^2<1 := (div_lt_one (sq_pos_of_pos hn0)).mpr (by nlinarith only [hx1,hnR])
    have hlogn := log_le_rpow_div hn0.le (by norm_num : (0:ℝ)<1/2)
    rw [← sqrt_eq_rpow] at hlogn
    have hln : 0≤log (n:ℝ) := log_natCast_nonneg n
    have hlx : log x≤0 := log_nonpos hx.le hx1.le
    have hab : |-(log x-2*log (n:ℝ)+eulerMascheroniConstant)|≤
        -log x+2*log (n:ℝ)+1 := by
      apply abs_le.mpr
      constructor <;> linarith only [hln,hlx,
        one_half_lt_eulerMascheroniConstant,eulerMascheroniConstant_lt_two_thirds]
    unfold squareHarmonicResidual
    rw [real_harmonic_zero_below_one hsmall,zero_sub,abs_div,abs_of_pos (sq_pos_of_pos hn0)]
    calc
      _ ≤ (-log x+2*log (n:ℝ)+1)/(n:ℝ)^2 :=
        div_le_div_of_nonneg_right hab (sq_nonneg _)
      _ ≤ ((2/sqrt x)+4*sqrt n+1)/(n:ℝ)^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        linarith only [hlogx,hlogn]
      _ ≤ major n := by
        dsimp only [major]
        field_simp
        nlinarith [mul_nonneg (by positivity : 0≤(n:ℝ)) (by linarith only [hs1] : 0≤1-sqrt x),
          mul_nonneg (by positivity : 0≤(n:ℝ)*sqrt n) (by linarith only [hs1] : 0≤1-sqrt x)]
  have habs := Summable.of_nonneg_of_le (fun n => abs_nonneg (squareHarmonicResidual x n)) hb hm
  refine ⟨habs,?_⟩
  have h2 : (∑' n : ℕ,1/(n:ℝ)^2)≤2 := by
    have hh := tsum_nat_rpow_neg_le 2 (by norm_num)
    simpa only [rpow_neg (Nat.cast_nonneg _),rpow_two,one_div,
      show (2:ℝ)-1=1 by norm_num,div_one,show (1:ℝ)+1=2 by norm_num] using hh
  have h3 : (∑' n : ℕ,1/((n:ℝ)*sqrt n))≤3 := by
    have hh := tsum_nat_rpow_neg_le (3/2) (by norm_num)
    have he (n : ℕ) : (n:ℝ)^(-(3/2:ℝ))=1/((n:ℝ)*sqrt n) := by
      by_cases hn : n=0
      · subst n; norm_num
      have hn0 : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [rpow_neg hn0.le,show (3/2:ℝ)=1+1/2 by norm_num,rpow_add hn0,
        rpow_one,← sqrt_eq_rpow,one_div]
    norm_num only [he,show (3/2:ℝ)-1=1/2 by norm_num,one_div_div,div_one] at hh
    exact hh
  calc
    _ ≤ ∑' n,major n := habs.tsum_le_tsum hb hm
    _ = (3/sqrt x)*(∑' n : ℕ,1/(n:ℝ)^2)+
        (4/sqrt x)*(∑' n : ℕ,1/((n:ℝ)*sqrt n)) := by
      rw [show major=fun n : ℕ => (3/sqrt x)*(1/(n:ℝ)^2)+
        (4/sqrt x)*(1/((n:ℝ)*sqrt n)) from rfl,
        (inverse_square_summable.mul_left _).tsum_add (inverse_three_halves_summable.mul_left _),
        tsum_mul_left,tsum_mul_left]
    _ ≤ (3/sqrt x)*2+(4/sqrt x)*3 := add_le_add
      (mul_le_mul_of_nonneg_left h2 (by positivity)) (mul_le_mul_of_nonneg_left h3 (by positivity))
    _ ≤ 20/sqrt x := by
      apply (le_div_iff₀ hs).mpr
      field_simp
      norm_num

theorem square_harmonic_mass {x : ℝ} (hx : 0<x) :
    Summable (fun n => |squareHarmonicResidual x n|) ∧
    (∑' n,|squareHarmonicResidual x n|) ≤ 20/sqrt x := by
  by_cases hh : 1≤x
  · exact square_harmonic_mass_large hh
  · exact square_harmonic_mass_small hx (lt_of_not_ge hh)

end ChenEffective
