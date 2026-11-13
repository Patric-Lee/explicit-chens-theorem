import BJSLayerQuadrature
import BJSLayerTableData

noncomputable section
namespace ChenEffective
open Real Set Finset MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

def BJSGridBound (n : ℕ) (row : Array ℕ) : Prop :=
  ∀ i : ℕ, 32*(2-eps n) ≤ i → i ≤ 32*(n+2) →
    layer 2 n ((i : ℝ)/32) ≤ (row[i]! : ℝ)/1000000000000

def BJSGridStepChecks (n : ℕ) (prev row tail : Array ℕ) : Prop :=
  tail[32*(n+3)]! =0 ∧
  (∀ j : Fin (32*(n+3)), 32*(2+eps (n+1)) ≤ j.val →
    tail[j.val]! =tail[j.val+1]!+prev[j.val-32]!) ∧
  (∀ i : Fin (32*(n+3)+1), 32*(2-eps (n+1)) ≤ i.val →
    tail[max i.val (32*(2+eps (n+1)))]! ≤ i.val*row[i.val]!)

theorem bjsStudy_integer_tail_sum (prev tail : Array ℕ) (start last a m : ℕ)
    (ha : start ≤ a) (hend : a+m ≤ last)
    (hstep : ∀ j, start ≤ j → j < last → tail[j]! =tail[j+1]!+prev[j-32]!) :
    (∑ j ∈ range m, prev[a+j-32]!)+tail[a+m]! =tail[a]! := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp := ih (by omega)
    have hs := hstep (a+m) (by omega) (by omega)
    rw [Finset.sum_range_succ]
    have hid : a+(m+1)=a+m+1 := by omega
    rw [hid]
    omega

theorem bjsStudy_grid_base (row : Array ℕ)
    (hcheck : ∀ i : Fin 97, 32 ≤ i.val →
      1000000000000*(96-i.val) ≤ i.val*row[i.val]!) : BJSGridBound 1 row := by
  intro i hi hu
  norm_num [eps] at hi hu
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hiR : (i : ℝ)≤96 := by exact_mod_cast hu
  have hc := hcheck ⟨i,by omega⟩ hi
  have hcR : (1000000000000 : ℝ)*(96-i) ≤ (i : ℝ)*(row[i]! : ℝ) := by
    exact_mod_cast hc
  have hform : layer 2 1 ((i : ℝ)/32)=(3-(i : ℝ)/32)/((i : ℝ)/32) := by
    simp only [layer,show (2 : ℝ)+1=3 by norm_num,
      min_eq_left (show (i : ℝ)/32≤3 by linarith only [hiR]),
      intervalIntegral.integral_const,smul_eq_mul,mul_one]
    ring
  rw [hform]
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<(i : ℝ)/32)).mpr
  nlinarith only [hcR]

theorem bjsStudy_grid_step {n : ℕ} (hn : 0 < n) (prev row tail : Array ℕ)
    (hprev : BJSGridBound n prev) (hc : BJSGridStepChecks n prev row tail) :
    BJSGridBound (n+1) row := by
  intro i hi hu
  have he : eps (n+1)+eps n=1 := eps_succ_add n
  have hi0 : 0 < i := by unfold eps at hi; omega
  have hiR0 : (0 : ℝ) < i := by exact_mod_cast hi0
  have hs : (i : ℝ)/32 ∈ closedDomain 2 (n+1) := by
    change (2 : ℝ)-(eps (n+1) : ℝ) ≤ (i : ℝ)/32
    have hh : (32 : ℝ)*(2-(eps (n+1) : ℝ)) ≤ i := by
      have heps : eps (n+1) ≤ 2 := by unfold eps; omega
      have hsub : ((2-eps (n+1) : ℕ) : ℝ)=2-(eps (n+1) : ℝ) := by
        rw [Nat.cast_sub heps]; norm_num
      have hhi : ((32*(2-eps (n+1)) : ℕ) : ℝ) ≤ i := by exact_mod_cast hi
      simpa only [Nat.cast_mul,Nat.cast_ofNat,hsub] using hhi
    linarith only [hh]
  by_cases htop : 32*(n+3) ≤ i
  · rw [bjsStudy_layer_zero (n:=n+1) (by
      have hh : (32 : ℝ)*((n : ℝ)+3) ≤ i := by exact_mod_cast htop
      push_cast; linarith only [hh])]
    positivity
  let a : ℕ := max i (32*(2+eps (n+1)))
  let e : ℕ := 32*(n+3)
  have ha : a ≤ e := by
    apply max_le (by omega)
    have hnR : 2+eps (n+1) ≤ n+3 := by unfold eps; omega
    exact Nat.mul_le_mul_left 32 hnR
  have har : max ((i : ℝ)/32) (2+(eps (n+1) : ℝ))=(a : ℝ)/32 := by
    dsimp [a]
    push_cast
    rw [← max_div_div_right (by norm_num : (0 : ℝ)≤32)]
    congr 1
    field_simp
  have hcast : ((e-a : ℕ) : ℝ)=e-a := by rw [Nat.cast_sub ha]
  have heR : (e : ℝ)=32*((n : ℝ)+3) := by dsimp [e]; push_cast; ring
  have hq := bjsStudy_layer_successor_grid (n:=n) (m:=e-a) hn hs (by norm_num : (0 : ℝ)≤1/32)
    (by
      rw [har]
      have hh : (a : ℝ) ≤ e := by exact_mod_cast ha
      linarith only [hh,heR])
    (by rw [har,hcast,heR]; ring)
  rw [har] at hq
  have hpoints (j : ℕ) (hj : j∈range (e-a)) :
      32*(2-eps n) ≤ a+j-32 ∧ a+j-32≤32*(n+2) := by
    have hstart : 32*(2+eps (n+1)) ≤ a := le_max_right _ _
    have hj' := mem_range.mp hj
    dsimp [e] at hj' ha
    omega
  have hsum : (∑ j ∈ range (e-a), layer 2 n ((a : ℝ)/32+j*(1/32)-1)) ≤
      ((∑ j ∈ range (e-a), prev[a+j-32]!) : ℕ)/ (1000000000000 : ℝ) := by
    rw [Nat.cast_sum,Finset.sum_div]
    apply sum_le_sum
    intro j hj
    have hp := hpoints j hj
    have hindex : ((a+j-32 : ℕ) : ℝ)/32=(a : ℝ)/32+j*(1/32)-1 := by
      rw [Nat.cast_sub (by have hh:=le_max_right i (32*(2+eps (n+1))); change 32 ≤ a+j; dsimp [a]; omega)]
      push_cast
      ring
    rw [← hindex]
    exact hprev _ hp.1 hp.2
  have htail := bjsStudy_integer_tail_sum prev tail (32*(2+eps (n+1))) e a (e-a)
    (le_max_right _ _) (by omega) (fun j hj hje => hc.2.1 ⟨j,hje⟩ hj)
  have hid : a+(e-a)=e := Nat.add_sub_of_le ha
  rw [hid,hc.1,add_zero] at htail
  rw [htail] at hsum
  have hcR : (tail[a]! : ℝ)≤(i : ℝ)*(row[i]! : ℝ) := by
    exact_mod_cast hc.2.2 ⟨i,by omega⟩ hi
  apply hq.trans
  have hm := mul_le_mul_of_nonneg_left hsum (show 0≤(1/32 : ℝ)/((i : ℝ)/32) by positivity)
  apply hm.trans
  field_simp
  nlinarith only [hcR]

#print axioms bjsStudy_grid_step
end ChenEffective
