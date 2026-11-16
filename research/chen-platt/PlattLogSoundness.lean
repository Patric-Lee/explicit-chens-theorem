import PlattLogKernel
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

noncomputable section
namespace ChenEffective.PlattWindow.LogCertificate
open Real Finset
set_option maxHeartbeats 1600000

theorem floor_div_bounds (a b : ℕ) (hb : 0 < b) :
    ((a/b:ℕ):ℝ) ≤ (a:ℝ)/b ∧ (a:ℝ)/b ≤ ((a/b:ℕ):ℝ)+1 := by
  refine ⟨Nat.cast_div_le, ?_⟩
  have h : (a:ℝ) < ((a/b:ℕ):ℝ)*b+b := by exact_mod_cast Nat.lt_div_mul_add (a:=a) hb
  have hb0 : (0:ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb0]
  linarith only [h]

theorem floorSum_bounds (S a b : ℕ) (hb : 0 < b) (j : ℕ) :
    (floorSum S a b j:ℝ) ≤ (S:ℝ)*∑ i ∈ range j, ((a:ℝ)/b)^(2*i+1)/(2*i+1) ∧
    (S:ℝ)*(∑ i ∈ range j, ((a:ℝ)/b)^(2*i+1)/(2*i+1)) ≤ (floorSum S a b j:ℝ)+j := by
  induction j with
  | zero => simp [floorSum]
  | succ j ih =>
    have h := floor_div_bounds (S*a^(2*j+1)) ((2*j+1)*b^(2*j+1)) (by positivity)
    have e : ((S*a^(2*j+1):ℕ):ℝ)/((2*j+1)*b^(2*j+1):ℕ) =
        (S:ℝ)*(((a:ℝ)/b)^(2*j+1)/(2*j+1)) := by
      have hb0 : (b:ℝ) ≠ 0 := by exact_mod_cast hb.ne'
      have hj0 : (2*(j:ℝ)+1) ≠ 0 := by positivity
      push_cast
      rw [div_pow]
      field_simp [hb0,hj0]
      <;> ring
    rw [e] at h
    simp only [floorSum,Nat.cast_add,Nat.cast_succ,sum_range_succ,mul_add]
    constructor <;> linarith only [ih.1,ih.2,h.1,h.2]

theorem unitBounds_sound {n d : ℕ} (hd : 0 < d) (hlo : d ≤ n) (hhi : n ≤ 2*d) :
    ((unitBounds n d).1:ℝ) ≤ (scale:ℝ)*log ((n:ℝ)/d) ∧
    (scale:ℝ)*log ((n:ℝ)/d) ≤ ((unitBounds n d).2:ℝ) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hn0 : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hd hlo)
  have hnd : 0 < n+d := by omega
  have hnd0 : (0:ℝ) < n+d := by positivity
  let z : ℝ := ((n-d:ℕ):ℝ)/(n+d)
  have he : z=((n:ℝ)-d)/(n+d) := by dsimp [z]; rw [Nat.cast_sub hlo]
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hz3 : z ≤ 1/3 := by
    rw [he,div_le_iff₀ hnd0]
    have ht : (n:ℝ) ≤ 2*d := by exact_mod_cast hhi
    linarith only [ht]
  have hz1 : z < 1 := lt_of_le_of_lt hz3 (by norm_num)
  have heq : (1+z)/(1-z)=(n:ℝ)/d := by
    rw [he]
    field_simp [hd0.ne',hnd0.ne']
    <;> ring
  have hl := sum_range_le_log_div hz0 hz1 16
  have hu := log_div_le_sum_range_add hz0 hz1 16
  rw [heq] at hl hu
  have hs := floorSum_bounds scale (n-d) (n+d) hnd 16
  simp only [Nat.cast_add] at hs
  change (floorSum scale (n-d) (n+d) 16:ℝ) ≤
      (scale:ℝ)*∑ i ∈ range 16,z^(2*i+1)/(2*i+1) ∧ _ at hs
  have hp := pow_le_pow_left₀ hz0 hz3 33
  have hden : (8/9:ℝ) ≤ 1-z^2 := by nlinarith only [hz0,hz3]
  have ht : 2*(scale:ℝ)*(z^33/(1-z^2)) ≤ 1 := by
    rw [← mul_div_assoc,div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ) < 8/9) hden)]
    norm_num [scale] at hp ⊢
    nlinarith only [hp,hden]
  have hS : (0:ℝ) ≤ scale := Nat.cast_nonneg _
  have hlS := mul_le_mul_of_nonneg_left hl hS
  have huS := mul_le_mul_of_nonneg_left hu hS
  dsimp [unitBounds]
  push_cast
  norm_num only [show 2*(16:ℕ)+1=33 by decide] at huS
  constructor <;> nlinarith only [hs.1,hs.2,hlS,huS,ht]

theorem rationalBounds_sound {n d k : ℕ} (hd : 0 < d)
    (hlo : d*2^k ≤ n) (hhi : n ≤ 2*(d*2^k)) :
    ((rationalBounds n d k).1:ℝ) ≤ (scale:ℝ)*log ((n:ℝ)/d) ∧
    (scale:ℝ)*log ((n:ℝ)/d) ≤ ((rationalBounds n d k).2:ℝ) := by
  have hn : 0 < n := lt_of_lt_of_le (by positivity) hlo
  have hb := unitBounds_sound (by positivity : 0 < d*2^k) hlo hhi
  have ha := unitBounds_sound (by norm_num : 0 < 1) (by norm_num : 1 ≤ 2) (by norm_num : 2 ≤ 2*1)
  have he : log ((n:ℝ)/d)=(k:ℝ)*log 2+log ((n:ℝ)/((d:ℝ)*2^k)) := by
    rw [log_div (by positivity) (by positivity),log_div (by positivity) (by positivity),
      log_mul (by positivity) (by positivity),log_pow]
    ring
  norm_num only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,div_one] at ha hb
  have hak := And.intro (mul_le_mul_of_nonneg_left ha.1 (Nat.cast_nonneg k))
    (mul_le_mul_of_nonneg_left ha.2 (Nat.cast_nonneg k))
  dsimp [rationalBounds]
  push_cast
  rw [he]
  constructor <;> nlinarith only [hb.1,hb.2,hak.1,hak.2]

theorem loglog_of_certificates {x k L U kl ku l u : ℕ}
    (hx : 0 < x) (hxl : 2^k ≤ x) (hxu : x ≤ 2*2^k)
    (hfirst : rationalBounds x 1 k = (L,U))
    (hL : scale < L)
    (hll : scale*2^kl ≤ L) (hlu : L ≤ 2*(scale*2^kl))
    (hul : scale*2^ku ≤ U) (huu : U ≤ 2*(scale*2^ku))
    (hlcert : (rationalBounds L scale kl).1=l)
    (hucert : (rationalBounds U scale ku).2=u) :
    (l:ℝ) ≤ (scale:ℝ)*log (log (x:ℝ)) ∧
    (scale:ℝ)*log (log (x:ℝ)) ≤ (u:ℝ) := by
  have hS : (0:ℝ) < scale := by norm_num [scale]
  have h1 := rationalBounds_sound (by norm_num : 0 < 1)
    (by simpa using hxl) (by simpa using hxu)
  rw [hfirst] at h1
  simp only [Prod.fst,Prod.snd,Nat.cast_one,div_one] at h1
  have h2 := (rationalBounds_sound (n:=L) (d:=scale) (k:=kl) (by norm_num [scale]) hll hlu).1
  have h3 := (rationalBounds_sound (n:=U) (d:=scale) (k:=ku) (by norm_num [scale]) hul huu).2
  rw [hlcert] at h2
  rw [hucert] at h3
  have hLp : (0:ℝ) < (L:ℝ)/scale := div_pos (by exact_mod_cast (lt_trans (by norm_num [scale] : 0 < scale) hL)) hS
  have hloglo : (L:ℝ)/scale ≤ log (x:ℝ) := (div_le_iff₀ hS).mpr (by nlinarith only [h1.1])
  have hloghi : log (x:ℝ) ≤ (U:ℝ)/scale := (le_div_iff₀ hS).mpr (by nlinarith only [h1.2])
  have hmlo := mul_le_mul_of_nonneg_left (log_le_log hLp hloglo) hS.le
  have hmhi := mul_le_mul_of_nonneg_left (log_le_log (hLp.trans_le hloglo) hloghi) hS.le
  exact ⟨h2.trans hmlo,hmhi.trans h3⟩

#print axioms loglog_of_certificates
end ChenEffective.PlattWindow.LogCertificate
