import BJSStudyElementaryMertens
import OptimizedMertensPower

/-! Closed-left reciprocal-prime intervals from bounds on actual prefixes.
The lower prefix is approached from the LEFT. This avoids losing a prime
when a itself is prime. No provisional BJS assumption is imported.
-/
noncomputable section
namespace ChenEffective
open Real Set Finset Filter AnalyticNumberTheory.Mertens
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

theorem bjsStudy_interval_prefix_disjoint (s : Finset ℕ) {x a b : ℝ}
    (hx : 0 ≤ x) (hxa : x < a) (hab : a ≤ b)
    (hs : ∀ p∈s, p.Prime ∧ a≤(p : ℝ) ∧ (p : ℝ) ≤ b) :
    (∑ p∈s, 1/(p : ℝ))+primeReciprocalSum ⌊x⌋₊ ≤ primeReciprocalSum ⌊b⌋₊ := by
  have hsubS : s ⊆ primesUpTo ⌊b⌋₊ := by
    intro p hp
    exact mem_primesUpTo.mpr ⟨(hs p hp).1,Nat.le_floor (hs p hp).2.2⟩
  have hsubP : primesUpTo ⌊x⌋₊ ⊆ primesUpTo ⌊b⌋₊ :=
    primesUpTo_mono (Nat.floor_mono (hxa.le.trans hab))
  have hdis : Disjoint s (primesUpTo ⌊x⌋₊) := by
    apply Finset.disjoint_left.mpr
    intro p hp hpx
    have hpr : (p : ℝ) ≤ x := (show (p : ℝ)≤⌊x⌋₊ by exact_mod_cast (mem_primesUpTo.mp hpx).2).trans (Nat.floor_le hx)
    linarith only [hpr,(hs p hp).2.1,hxa]
  unfold primeReciprocalSum
  rw [← Finset.sum_union hdis]
  exact sum_le_sum_of_subset_of_nonneg (Finset.union_subset hsubS hsubP) (fun p _ _ => by positivity)

theorem bjsStudy_interval_of_prefix (s : Finset ℕ) {a b t : ℝ} {L : ℝ→ℝ} {U : ℝ}
    (ht : 0 ≤ t) (ha : t < a) (hab : a ≤ b)
    (hs : ∀ p∈s, p.Prime ∧ a≤(p : ℝ) ∧ (p : ℝ) ≤ b)
    (hL : ∀ x : ℝ, t < x → L x ≤ primeReciprocalSum ⌊x⌋₊)
    (hU : primeReciprocalSum ⌊b⌋₊ ≤ U) (hc : ContinuousAt L a) :
    (∑ p∈s, 1/(p : ℝ)) ≤ U-L a := by
  have hf : Tendsto (fun x => (∑ p∈s, 1/(p : ℝ))+L x) (𝓝[<] a)
      (𝓝 ((∑ p∈s, 1/(p : ℝ))+L a)) :=
    tendsto_const_nhds.add (hc.tendsto.mono_left inf_le_left)
  have hlow : ∀ᶠ x in 𝓝[<] a, t < x := (eventually_gt_nhds ha).filter_mono inf_le_left
  have hbound : ∀ᶠ x in 𝓝[<] a, (∑ p∈s, 1/(p : ℝ))+L x ≤ U := by
    filter_upwards [hlow,self_mem_nhdsWithin] with x hxt hxa
    have hh := bjsStudy_interval_prefix_disjoint s (ht.trans hxt.le) hxa hab hs
    linarith only [hh,hL x hxt,hU]
  have hh := le_of_tendsto hf hbound
  linarith only [hh]

/-- The exact Rosser-Schoenfeld prefix input would imply the complete
ordered interval estimate. This lemma does NOT assert those inputs. -/
theorem bjsStudy_interval_of_half_log_squared_prefix {B : ℝ}
    (hL : ∀ x : ℝ, 1 < x → log (log x)+B-1/(2*(log x)^2) ≤ primeReciprocalSum ⌊x⌋₊)
    (hU : ∀ x : ℝ, 286 ≤ x → primeReciprocalSum ⌊x⌋₊ ≤ log (log x)+B+1/(2*(log x)^2))
    (s : Finset ℕ) (a b : ℝ) (ha : 1 < a) (hb : 286 ≤ b) (hab : a ≤ b)
    (hs : ∀ p∈s, p.Prime ∧ a≤(p : ℝ) ∧ (p : ℝ) ≤ b) :
    (∑ p∈s, 1/(p : ℝ)) ≤ log (log b/log a)+1/(log a)^2 := by
  have ha0 : 0 < a := by linarith only [ha]
  have hb0 : 0 < b := ha0.trans_le hab
  have hla : 0 < log a := log_pos ha
  have hlb : 0 < log b := log_pos (ha.trans_le hab)
  have hc : ContinuousAt (fun x : ℝ => log (log x)+B-1/(2*(log x)^2)) a := by
    fun_prop (disch := positivity)
  have hh := bjsStudy_interval_of_prefix s (by norm_num : (0 : ℝ)≤1) ha hab hs hL (hU b hb) hc
  have hlog : log a ≤ log b := log_le_log ha0 hab
  have he : 1/(2*(log b)^2)≤1/(2*(log a)^2) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith only [hlog,hla,hlb])
  rw [log_div hlb.ne' hla.ne']
  have hid : 2*(1/(2*(log a)^2))=1/(log a)^2 := by ring
  linarith only [hh,he,hid]

theorem bjsStudy_interval_power (s : Finset ℕ) {a b : ℝ}
    (ha : 9 < a) (hab : a ≤ b)
    (hs : ∀ p∈s, p.Prime ∧ a≤(p : ℝ) ∧ (p : ℝ) ≤ b) :
    (∑ p∈s, 1/(p : ℝ)) ≤ log (log b/log a)+60000000000000*a^(-1/68 : ℝ) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hla : 0 < log a := log_pos (by linarith only [ha])
  have hlb : 0 < log b := log_pos (by linarith only [ha,hab])
  have hL : ∀ x : ℝ, 9 < x → log (log x)+mertensSecondConstant-
      30000000000000*x^(-1/68 : ℝ) ≤ primeReciprocalSum ⌊x⌋₊ := by
    intro x hx
    exact sub_le_iff_le_add.mpr (by linarith only [(abs_le.mp (optimized_mertens_power hx.le)).1])
  have hU := (abs_le.mp (optimized_mertens_power (ha.le.trans hab))).2
  have hc : ContinuousAt (fun x : ℝ => log (log x)+mertensSecondConstant-
      30000000000000*x^(-1/68 : ℝ)) a := by
    have hlog := continuousAt_log ha0.ne'
    have hloglog := (continuousAt_log hla.ne').comp hlog
    have hpow := continuousAt_rpow_const a (-1/68 : ℝ) (Or.inl ha0.ne')
    exact (hloglog.add continuousAt_const).sub (continuousAt_const.mul hpow)
  have hh := bjsStudy_interval_of_prefix s (by norm_num : (0 : ℝ)≤9) ha hab hs hL
    (show primeReciprocalSum ⌊b⌋₊ ≤ log (log b)+mertensSecondConstant+30000000000000*b^(-1/68 : ℝ) by linarith only [hU]) hc
  have hp := rpow_le_rpow_of_nonpos ha0 hab (by norm_num : (-1/68 : ℝ)≤0)
  rw [log_div hlb.ne' hla.ne']
  linarith only [hh,hp]

#print axioms bjsStudy_interval_of_half_log_squared_prefix
#print axioms bjsStudy_interval_power
end ChenEffective
