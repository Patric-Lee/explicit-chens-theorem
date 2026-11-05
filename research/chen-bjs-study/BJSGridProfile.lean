import BJSGridCertificate

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

private theorem bjs_exp_grid (i : ℕ) : exp ((i : ℝ)/32) ≤ (65/63 : ℝ)^i := by
  have he := exp_le_two_add_div_two_sub (by norm_num : (0 : ℝ)≤1/32)
    (by norm_num : (1/32 : ℝ)<2)
  norm_num at he
  have hp := pow_le_pow_left₀ (exp_pos (1/32 : ℝ)).le he i
  rw [← exp_nat_mul] at hp
  simpa only [div_eq_mul_inv,one_mul] using hp

theorem bjsStudy_grid_hat_profile (n : ℕ) (row : Array ℕ) (num : ℕ)
    (hg : BJSGridBound n row)
    (hc : ∀ i : Fin (32*(n+2)), 32*(2-eps n) ≤ i.val →
      row[i.val]! * max 96 (i.val+1) * 65^(i.val+1-64) * 1000000 ≤
        6*32*1000000000000*num * 63^(i.val+1-64)) :
    ∀ s ∈ closedDomain 2 n,
      layer 2 n s ≤ 2*exp 2*((num : ℝ)/1000000)*sieveHat s := by
  intro s hs
  have hhat := (sieveHat_pos s).le
  by_cases htop : (n : ℝ)+2 ≤ s
  · rw [bjsStudy_layer_zero htop]
    positivity
  have hs0 := closedDomain_pos (by norm_num : (1 : ℝ)<2) hs
  have heps : eps n ≤ 2 := by unfold eps; omega
  have hsub : ((2-eps n : ℕ) : ℝ)=2-(eps n : ℝ) := by
    rw [Nat.cast_sub heps]; norm_num
  let i : ℕ := ⌊32*s⌋₊
  have hf : (i : ℝ) ≤ 32*s := Nat.floor_le (by positivity)
  have hnxt : 32*s < (i+1 : ℕ) := by
    simpa only [i,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (32*s)
  have hi : i < 32*(n+2) := by
    have hh : (i : ℝ) < 32*((n : ℝ)+2) := by linarith only [hf,htop]
    exact_mod_cast hh
  have hlo : 32*(2-eps n) ≤ i := by
    apply Nat.le_floor
    push_cast
    rw [hsub]
    change (2 : ℝ)-(eps n : ℝ) ≤ s at hs
    linarith only [hs]
  have hleft : (i : ℝ)/32 ≤ s := by linarith only [hf]
  have hd : (i : ℝ)/32 ∈ closedDomain 2 n := by
    change (2 : ℝ)-(eps n : ℝ) ≤ (i : ℝ)/32
    have hh : ((32*(2-eps n) : ℕ) : ℝ) ≤ i := by exact_mod_cast hlo
    simp only [Nat.cast_mul,Nat.cast_ofNat,hsub] at hh
    linarith only [hh]
  let x : ℝ := (i+1 : ℕ)/32
  let k : ℕ := i+1-64
  let R : ℝ := (65/63 : ℝ)^k
  have hx : s ≤ x := by dsimp [x]; linarith only [hnxt]
  have hk : max 2 x-2=(k : ℝ)/32 := by
    by_cases h64 : 64 ≤ i+1
    · have hx2 : 2 ≤ x := by
        have hh : (64 : ℝ) ≤ (i+1 : ℕ) := by exact_mod_cast h64
        dsimp [x]; linarith only [hh]
      rw [max_eq_right hx2]
      dsimp [x,k]
      rw [Nat.cast_sub h64]
      norm_num
      ring
    · have hx2 : x ≤ 2 := by
        have hh : ((i+1 : ℕ) : ℝ) ≤ 64 := by exact_mod_cast (show i+1 ≤ 64 by omega)
        dsimp [x]; linarith only [hh]
      rw [max_eq_left hx2]
      have hk0 : k=0 := by dsimp [k]; omega
      simp [hk0]
  have hR : 0 < R := by dsimp [R]; positivity
  have he : exp (max 2 x-2) ≤ R := by rw [hk]; exact bjs_exp_grid k
  have hmax : max 3 x=((max 96 (i+1) : ℕ) : ℝ)/32 := by
    dsimp [x]
    push_cast
    rw [← max_div_div_right (by norm_num : (0 : ℝ)≤32)]
    norm_num
  have hmpos : 0 < max 3 x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hhatlow : 6/(max 3 x*R) ≤ 2*exp 2*sieveHat x := by
    have hinv := one_div_le_one_div_of_le (exp_pos (max 2 x-2)) he
    have hid : exp (2 : ℝ)*exp (-max 2 x)=1/exp (max 2 x-2) := by
      rw [← exp_add,one_div,← exp_neg]
      congr 1
      ring
    rw [sieveHat_max_formula]
    have hh := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 6/max 3 x by positivity)
    calc
      _ = (6/max 3 x)*(1/R) := by ring
      _ ≤ (6/max 3 x)*(1/exp (max 2 x-2)) := hh
      _ = _ := by rw [← hid]; ring
  have hcR : (row[i]! : ℝ)*(max 96 (i+1) : ℕ)*(65 : ℝ)^k*1000000 ≤
      6*32*1000000000000*(num : ℝ)*(63 : ℝ)^k := by
    exact_mod_cast hc ⟨i,hi⟩ hlo
  have hrow : (row[i]! : ℝ)/1000000000000 ≤
      ((num : ℝ)/1000000)*(6/(max 3 x*R)) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ)<1000000000000)).mpr
    have hid : (((num : ℝ)/1000000)*(6/(max 3 x*R)))*1000000000000 =
        (6*1000000000000*(num : ℝ)*(63 : ℝ)^k)/(1000000*max 3 x*(65 : ℝ)^k) := by
      dsimp [R]
      rw [div_pow]
      field_simp
    rw [hid]
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<1000000*max 3 x*(65 : ℝ)^k)).mpr
    rw [hmax]
    nlinarith only [hcR]
  apply (bjsStudy_layer_antitone n hd hs hleft).trans
  apply (hg i hlo hi.le).trans
  apply hrow.trans
  have hh := mul_le_mul_of_nonneg_left hhatlow (show 0≤(num : ℝ)/1000000 by positivity)
  have hh' := mul_le_mul_of_nonneg_left (sieveHat_antitone hx)
    (show 0≤2*exp 2*((num : ℝ)/1000000) by positivity)
  nlinarith only [hh,hh']

#print axioms bjsStudy_grid_hat_profile
end ChenEffective
