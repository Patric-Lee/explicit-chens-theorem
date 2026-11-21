import GRH14MediumPrimeSum
import GRH14MediumFactor

noncomputable section
namespace ChenEffective.GRH14
open Real Set Finset
open MathlibNt.SieveTheory SwitchingPrinciple
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

def mediumGridNat (i : ℕ) : ℝ := 1/10+(7/1920:ℝ)*i

theorem medium_grid_mono : Monotone mediumGridNat := by
  intro i j hij
  unfold mediumGridNat
  gcongr

theorem weighted_log_add (f : ℝ → ℝ) {N : ℕ} {a b c : ℝ}
    (hN : 1 ≤ N) (hab : a ≤ b) (hbc : b ≤ c) :
    MertensTheorem.weightedPrimeReciprocalLogSum f N a b+
      MertensTheorem.weightedPrimeReciprocalLogSum f N b c=
      MertensTheorem.weightedPrimeReciprocalLogSum f N a c := by
  unfold MertensTheorem.weightedPrimeReciprocalLogSum
  simp only [sum_filter]
  apply sum_Ioc_consecutive
  · exact Nat.floor_mono (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hab)
  · exact Nat.floor_mono (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hbc)

theorem medium_grid_partition (f : ℝ → ℝ) {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    MertensTheorem.weightedPrimeReciprocalLogSum f N (mediumGridNat 0) (mediumGridNat n)=
      ∑ i : Fin n, MertensTheorem.weightedPrimeReciprocalLogSum f N
        (mediumGridNat i.val) (mediumGridNat (i.val+1)) := by
  induction n with
  | zero => simp [MertensTheorem.weightedPrimeReciprocalLogSum]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [← ih]
    exact (weighted_log_add f hN (medium_grid_mono (Nat.zero_le n))
      (medium_grid_mono (Nat.le_succ n))).symm

theorem medium_darboux_cell (f : ℝ → ℝ) {N : ℕ} (hN : targetCutoff ≤ N)
    {a b U : ℝ} (ha : 1/10 ≤ a) (hab : a ≤ b) (hb : b ≤ 1/3)
    (hU : 0 ≤ U) (hf : ∀ x ∈ Icc a b, f x ≤ U) :
    MertensTheorem.weightedPrimeReciprocalLogSum f N a b ≤ U*((b-a)/a+100/log (N:ℝ)^2) := by
  have hL := target_log_lower hN
  have hLp : 0<log (N:ℝ) := by linarith only [hL]
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by have := (numerical_prime_pair_parameters hN).1; omega)
  have ha0 : 0<a := by linarith only [ha]
  have hb0 : 0<b := ha0.trans_le hab
  have htest : MertensTheorem.weightedPrimeReciprocalLogSum f N a b ≤ U*PrimeReciprocalLogScale.primeReciprocalLogInterval N a b := by
    unfold MertensTheorem.weightedPrimeReciprocalLogSum
    unfold PrimeReciprocalLogScale.primeReciprocalLogInterval
    rw [← numerical_prime_interval_carrier,mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨hpc,hprime⟩ := mem_filter.mp hp
    obtain ⟨hpa,hpb⟩ := MertensTheorem.mem_Ioc_rpowFloor_iff.mp hpc
    have hp0 : (0:ℝ)<p := by exact_mod_cast hprime.pos
    have halog := log_le_log (rpow_pos_of_pos hNp a) hpa.le
    have hblog := log_le_log hp0 hpb
    rw [log_rpow hNp] at halog hblog
    have hx : log (p:ℝ)/log (N:ℝ)∈Icc a b :=
      ⟨(le_div_iff₀ hLp).mpr (by nlinarith only [halog]),(div_le_iff₀ hLp).mpr hblog⟩
    simpa only [mul_one_div] using div_le_div_of_nonneg_right (hf _ hx) hp0.le
  have hm := numerical_prime_pair_interval hN ha hab (by linarith only [hb])
  have hl : log (b/a) ≤ (b-a)/a := by
    have hh := log_le_sub_one_of_pos (div_pos hb0 ha0)
    convert hh using 1 <;> field_simp <;> ring
  exact htest.trans (mul_le_mul_of_nonneg_left (hm.trans (add_le_add hl le_rfl)) hU)

theorem medium_darboux_grid (f : ℝ → ℝ) {N : ℕ} (hN : targetCutoff ≤ N)
    (U : Fin 64 → ℝ) (hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1)
    (hf : ∀ i x, x∈Icc (mediumCellStart i) (mediumCellStart i+7/1920) → f x ≤ U i) :
    MertensTheorem.weightedPrimeReciprocalLogSum f N (1/10) (1/3) ≤ (∑ i : Fin 64, U i*((7/1920:ℝ)/mediumCellStart i))+64*(100/log (N:ℝ)^2) := by
  have hN1 : 1 ≤ N := by have := (numerical_prime_pair_parameters hN).1; omega
  have hsum := Finset.sum_le_sum (fun i (_ : i∈(univ : Finset (Fin 64))) =>
    medium_darboux_cell f hN (a:=mediumCellStart i) (b:=mediumCellStart i+7/1920)
      (by unfold mediumCellStart; have hi := Nat.cast_nonneg (α:=ℝ) i.val; linarith only [hi])
      (by linarith)
      (by
        have hi : (i.val:ℝ) ≤ 63 := by exact_mod_cast (show i.val ≤ 63 by omega)
        unfold mediumCellStart
        linarith only [hi])
      (hU i).1 (hf i))
  have hp := medium_grid_partition f hN1 64
  have hc0 : mediumGridNat 0=(1/10:ℝ) := by norm_num [mediumGridNat]
  have hc64 : mediumGridNat 64=(1/3:ℝ) := by norm_num [mediumGridNat]
  rw [hc0,hc64] at hp
  have heq (i : Fin 64) : mediumGridNat i.val=mediumCellStart i ∧
      mediumGridNat (i.val+1)=mediumCellStart i+7/1920 := by
    constructor
    · rfl
    · unfold mediumGridNat mediumCellStart
      push_cast
      ring
  simp_rw [(heq _).1,(heq _).2] at hp
  rw [← hp] at hsum
  have hmass : (∑ i : Fin 64, U i) ≤ 64 := by
    have hh := sum_le_sum (fun i (_ : i∈(univ : Finset (Fin 64))) => (hU i).2)
    simpa using hh
  have hh := mul_le_mul_of_nonneg_right hmass (show 0 ≤ 100/log (N:ℝ)^2 by positivity)
  have hsplit : (∑ i : Fin 64, U i*((mediumCellStart i+7/1920-mediumCellStart i)/mediumCellStart i+
      100/log (N:ℝ)^2)) =
      (∑ i : Fin 64, U i*((7/1920:ℝ)/mediumCellStart i))+
        (∑ i : Fin 64, U i)*(100/log (N:ℝ)^2) := by
    rw [sum_mul,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hsplit] at hsum
  linarith only [hsum,hh]

def mediumKernelProfile (a : ℝ) : ℝ := 1/(5-10*a-(71/1000:ℝ))^2
def mediumHatProfile (a : ℝ) : ℝ := exp 2*sieveHat (5-10*a-(71/1000:ℝ))

theorem medium_cell_ratio_lower (i : Fin 64) : (3/2:ℝ) ≤ mediumCellRatio i := by
  have hi : (i.val:ℝ) ≤ 63 := by exact_mod_cast (show i.val ≤ 63 by omega)
  unfold mediumCellRatio mediumCellStart
  linarith only [hi]

theorem medium_kernel_prime_sum {N : ℕ} (hN : targetCutoff ≤ N) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumKernelProfile N (1/10) (1/3) ≤ (1/6:ℝ) := by
  let U := fun i : Fin 64 => 1/(mediumCellRatio i)^2
  have hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1 := by
    intro i
    have hs := medium_cell_ratio_lower i
    dsimp only [U]
    constructor
    · positivity
    · apply (div_le_iff₀ (by nlinarith only [hs] : 0<(mediumCellRatio i)^2)).mpr
      nlinarith only [hs,sq_nonneg (mediumCellRatio i-1)]
  have hf : ∀ i x, x∈Icc (mediumCellStart i) (mediumCellStart i+7/1920) → mediumKernelProfile x ≤ U i := by
    intro i x hx
    have hs := medium_cell_ratio_lower i
    have hle : mediumCellRatio i ≤ 5-10*x-(71/1000:ℝ) := by unfold mediumCellRatio; linarith only [hx.2]
    apply one_div_le_one_div_of_le (by nlinarith only [hs] : 0<(mediumCellRatio i)^2)
    exact pow_le_pow_left₀ (by linarith only [hs]) hle 2
  have hh := medium_darboux_grid mediumKernelProfile hN U hU hf
  have hc : (∑ i : Fin 64, U i*((7/1920:ℝ)/mediumCellStart i)) ≤ (1661/10000:ℝ) := by
    convert medium_kernel_grid_certificate using 1
    apply sum_congr rfl
    intro i _
    dsimp only [U,mediumKernelCell]
    ring
  have hL := target_log_lower hN
  have he : 64*(100/log (N:ℝ)^2) ≤ (1/1000000:ℝ) := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000000) hL 2
    rw [show 64*(100/log (N:ℝ)^2)=6400/log (N:ℝ)^2 by ring]
    apply (div_le_iff₀ (by nlinarith only [hL] : 0<log (N:ℝ)^2)).mpr
    nlinarith only [hp]
  linarith only [hh,hc,he]

theorem medium_hat_prime_sum {N : ℕ} (hN : targetCutoff ≤ N) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumHatProfile N (1/10) (1/3) ≤ (11/20:ℝ) := by
  let U := fun i : Fin 64 => exp 2*sieveHat (mediumCellRatio i)
  have hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1 := by
    intro i
    constructor
    · exact mul_nonneg (exp_pos 2).le (sieveHat_pos _).le
    · exact sieveHat_normalized_le_one _
  have hf : ∀ i x, x∈Icc (mediumCellStart i) (mediumCellStart i+7/1920) → mediumHatProfile x ≤ U i := by
    intro i x hx
    have hle : mediumCellRatio i ≤ 5-10*x-(71/1000:ℝ) := by unfold mediumCellRatio; linarith only [hx.2]
    exact mul_le_mul_of_nonneg_left (sieveHat_antitone hle) (exp_pos 2).le
  have hh := medium_darboux_grid mediumHatProfile hN U hU hf
  have hc : (∑ i : Fin 64, U i*((7/1920:ℝ)/mediumCellStart i)) ≤ (53/100:ℝ) := by
    apply le_trans _ medium_hat_grid_certificate
    apply sum_le_sum
    intro i _
    have ha : 0 ≤ (7/1920:ℝ)/mediumCellStart i := by unfold mediumCellStart; positivity
    have hp := mul_le_mul_of_nonneg_right
      (medium_hat_envelope_bound (medium_cell_ratio_lower i)) ha
    dsimp only [U,mediumHatCell]
    convert hp using 1 <;> ring
  have hL := target_log_lower hN
  have he : 64*(100/log (N:ℝ)^2) ≤ (1/1000000:ℝ) := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000000) hL 2
    rw [show 64*(100/log (N:ℝ)^2)=6400/log (N:ℝ)^2 by ring]
    apply (div_le_iff₀ (by nlinarith only [hL] : 0<log (N:ℝ)^2)).mpr
    nlinarith only [hp]
  linarith only [hh,hc,he]

#print axioms medium_kernel_prime_sum
#print axioms medium_hat_prime_sum
end ChenEffective.GRH14
