import PlattAssemblyKernel
import PlattSegmentArithmetic
import PlattLogGridBridge
import PlattIncrementKernel

noncomputable section
set_option autoImplicit false
namespace ChenEffective.PlattWindow
open Real Finset AnalyticNumberTheory.Mertens
set_option maxHeartbeats 3000000

theorem prefix_fold_eq (scale lo w Y k : ℕ) :
    (List.range k).foldl (fun p j =>
      let q := reciprocalFloors scale lo w Y j
      (p.1+q.1,p.2+q.2)) (0,0) = segmentFixed scale lo w Y k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      segmentFixed]

theorem checkCutsTable_sound {start : ℕ} {table : List (ℕ × ℕ)} {cuts : List PrefixCut}
    (h : checkCutsTable start table cuts = true) {c : PrefixCut} (hc : c ∈ cuts) :
    start ≤ c.k ∧ table[c.k-start]? = some (c.lower,c.upper) := by
  induction table generalizing start cuts with
  | nil =>
    cases cuts <;> simp [checkCutsTable] at h hc
  | cons p ps ih =>
    cases cuts with
    | nil => simp at hc
    | cons d ds =>
      change (if d.k=start then _ else _) = true at h
      split at h
      next he =>
        obtain ⟨hp,ht⟩ := Bool.and_eq_true_iff.mp h
        have hp' := of_decide_eq_true hp
        rcases List.mem_cons.mp hc with rfl | hc
        · refine ⟨by omega, ?_⟩
          simp only [he,Nat.sub_self,List.getElem?_cons_zero,hp']
        · obtain ⟨hk,hv⟩ := ih ht hc
          refine ⟨by omega, ?_⟩
          have heq : c.k-start=(c.k-(start+1))+1 := by omega
          simpa only [heq,List.getElem?_cons_succ] using hv
      next he =>
        split at h
        next _ =>
          obtain ⟨hk,hv⟩ := ih h hc
          refine ⟨by omega, ?_⟩
          have heq : c.k-start=(c.k-(start+1))+1 := by omega
          simpa only [heq,List.getElem?_cons_succ] using hv
        next _ => simp at h

theorem checked_prefix_cut {scale lo w Y B : ℕ} {cuts : List PrefixCut}
    (h : checkPrefixCuts scale lo w Y B cuts = true) {c : PrefixCut} (hc : c ∈ cuts) :
    c.k ≤ B ∧ segmentFixed scale lo w Y c.k = (c.lower,c.upper) := by
  have hp' := (checkCutsTable_sound h hc).2
  simp only [Nat.sub_zero] at hp'
  unfold prefixTable at hp'
  rw [List.getElem?_scanl, List.length_range] at hp'
  by_cases hk : c.k ≤ B
  · refine ⟨hk, ?_⟩
    simpa only [if_pos hk, Option.some.injEq, List.take_range, Nat.min_eq_left hk,
      prefix_fold_eq] using hp'
  · simp only [if_neg hk, reduceCtorEq] at hp'

/-- Reuse a whole-segment prime certificate at any certified prefix cut. -/
theorem segment_prefix_reciprocal_certificate {scale lo w B Y n Qlo Qhi : ℕ}
    (hlo : lo % 2 = 1) (hlo3 : 3 ≤ lo)
    (htop : lo+2*2^w*B-1 ≤ PsiFinite.baseCover) (hn : n ≤ B)
    (hcert : segmentCounts lo w B = Y)
    (harith : segmentFixed scale lo w Y n = (Qlo,Qhi)) :
    (Qlo:ℝ) ≤ scale*(primeReciprocalSum (lo-1+2*2^w*n)-primeReciprocalSum (lo-1)) ∧
    scale*(primeReciprocalSum (lo-1+2*2^w*n)-primeReciprocalSum (lo-1)) ≤ (Qhi:ℝ) := by
  have hL := sum_le_sum (s:=range n) (fun k hk =>
    (reciprocalFloors_bounds (scale:=scale) hlo hlo3 htop ((mem_range.mp hk).trans_le hn) hcert).1)
  have hU := sum_le_sum (s:=range n) (fun k hk =>
    (reciprocalFloors_bounds (scale:=scale) hlo hlo3 htop ((mem_range.mp hk).trans_le hn) hcert).2)
  have he := (segmentFixed_eq scale lo w Y n).symm.trans harith
  have hl := congrArg Prod.fst he
  have hu := congrArg Prod.snd he
  change (∑ k ∈ range n,(reciprocalFloors scale lo w Y k).1)=Qlo at hl
  change (∑ k ∈ range n,(reciprocalFloors scale lo w Y k).2)=Qhi at hu
  simp only [← Finset.mul_sum,reciprocal_blocks_telescope,← Nat.cast_sum,hl,hu] at hL hU
  exact ⟨hL,hU⟩

/-- Combining disjoint increments adds interval bounds; the seam is exact. -/
theorem cumulative_bounds_join {S : ℝ} {a b c : ℕ} {al au bl bu : ℝ}
    (ha : al ≤ S*(primeReciprocalSum b-primeReciprocalSum a) ∧
      S*(primeReciprocalSum b-primeReciprocalSum a) ≤ au)
    (hb : bl ≤ S*(primeReciprocalSum c-primeReciprocalSum b) ∧
      S*(primeReciprocalSum c-primeReciprocalSum b) ≤ bu) :
    al+bl ≤ S*(primeReciprocalSum c-primeReciprocalSum a) ∧
      S*(primeReciprocalSum c-primeReciprocalSum a) ≤ au+bu := by
  constructor <;> nlinarith only [ha.1,ha.2,hb.1,hb.2]

theorem certified_increment_sound {r : IncrementRow} (h : IncrementCertified r) :
    (r.lower:ℝ) ≤ (2:ℝ)^48*(primeReciprocalSum r.b-primeReciprocalSum r.a) ∧
      (2:ℝ)^48*(primeReciprocalSum r.b-primeReciprocalSum r.a) ≤ (r.upper:ℝ) := by
  obtain ⟨lo,w,B,Y,ha,hb,hodd,hlo,htop,hcount,harith⟩ := h
  simpa only [ha,hb,Nat.cast_pow,Nat.cast_ofNat] using
    (segment_reciprocal_certificate (scale:=2^48) hodd hlo htop hcount harith)

theorem certified_increment_chain_sound {rows : List IncrementRow} {a b : ℕ}
    (hcert : CertifiedIncrements rows) (hchain : checkIncrementChain a b rows=true) :
    ((incrementTotals rows).1:ℝ) ≤ (2:ℝ)^48*(primeReciprocalSum b-primeReciprocalSum a) ∧
      (2:ℝ)^48*(primeReciprocalSum b-primeReciprocalSum a) ≤ ((incrementTotals rows).2:ℝ) := by
  induction hcert generalizing a with
  | nil =>
    have he : a=b := of_decide_eq_true hchain
    subst a
    simp [incrementTotals]
  | @cons r rs hr hrs ih =>
    have hc : (r.a=a ∧ r.a≤r.b) ∧ checkIncrementChain r.b b rs=true := by
      simpa only [checkIncrementChain,Bool.and_eq_true,decide_eq_true_eq] using hchain
    have h := cumulative_bounds_join (certified_increment_sound hr) (ih hc.2)
    simpa only [incrementTotals,Nat.cast_add,hc.1.1] using h

theorem checked_increment_summary_sound {rows : List IncrementRow} {a b L U : ℕ}
    (hcert : CertifiedIncrements rows) (h : checkIncrementSummary a b L U rows=true) :
    (L:ℝ) ≤ (2:ℝ)^48*(primeReciprocalSum b-primeReciprocalSum a) ∧
      (2:ℝ)^48*(primeReciprocalSum b-primeReciprocalSum a) ≤ (U:ℝ) := by
  have hp : checkIncrementChain a b rows=true ∧ incrementTotals rows=(L,U) := by
    simpa only [checkIncrementSummary,Bool.and_eq_true,decide_eq_true_eq] using h
  simpa only [hp.2] using certified_increment_chain_sound hcert hp.1

/-- Integer grid checks control the actual all-real cell once the certified
cumulative prime bounds and certified logarithm bounds have been supplied. -/
theorem checked_assembly_cell {S d Rlo Rhi logRL logRU U R : ℕ} {c : AssemblyCell}
    (hS : 0 < S) (hd : 0 < d)
    (h : checkAssemblyCell S d Rlo Rhi logRL logRU c = true)
    (hA : (c.aLower:ℝ) ≤ S*(primeReciprocalSum c.a-primeReciprocalSum U))
    (hB : S*(primeReciprocalSum c.b-primeReciprocalSum U) ≤ (c.bUpper:ℝ))
    (hR : (Rlo:ℝ) ≤ S*(primeReciprocalSum R-primeReciprocalSum U) ∧
      S*(primeReciprocalSum R-primeReciprocalSum U) ≤ (Rhi:ℝ))
    (hlogA : (c.logaLower:ℝ) ≤ S*log (log (c.a:ℝ)))
    (hlogB : S*log (log (c.b:ℝ)) ≤ (c.logbUpper:ℝ))
    (hlogR : (logRL:ℝ) ≤ S*log (log (R:ℝ)) ∧ S*log (log (R:ℝ)) ≤ (logRU:ℝ))
    {x : ℝ} (hax : (c.a:ℝ) ≤ x) (hxb : x ≤ (c.b:ℝ)) :
    |relativePrefix x (R:ℝ)| ≤ 1/(d:ℝ) := by
  have hn := of_decide_eq_true h
  obtain ⟨ha1,_,hl,hu⟩ := hn
  have hSp : (0:ℝ) < S := by exact_mod_cast hS
  have hdp : (0:ℝ) < d := by exact_mod_cast hd
  have hlR : -(S:ℝ) ≤ (d:ℝ)*((c.aLower:ℝ)-Rhi-c.logbUpper+logRL) := by exact_mod_cast hl
  have huR : (d:ℝ)*((c.bUpper:ℝ)-Rlo-c.logaLower+logRU) ≤ (S:ℝ) := by exact_mod_cast hu
  have haR : 1 < (c.a:ℝ) := by exact_mod_cast ha1
  have hpa := mul_le_mul_of_nonneg_left
    (primeReciprocalSum_mono (Nat.floor_mono hax)) hSp.le
  have hpb := mul_le_mul_of_nonneg_left
    (primeReciprocalSum_mono (Nat.floor_mono hxb)) hSp.le
  simp only [Nat.floor_natCast] at hpa hpb
  have hla : log (log (c.a:ℝ)) ≤ log (log x) :=
    log_le_log (log_pos haR) (log_le_log (by linarith only [haR]) hax)
  have hlb : log (log x) ≤ log (log (c.b:ℝ)) :=
    log_le_log (log_pos (haR.trans_le hax))
      (log_le_log (by linarith only [haR,hax]) hxb)
  have hlaS := mul_le_mul_of_nonneg_left hla hSp.le
  have hlbS := mul_le_mul_of_nonneg_left hlb hSp.le
  have he :
      (c.aLower:ℝ)-Rhi-c.logbUpper+logRL ≤ S*relativePrefix x (R:ℝ) ∧
      S*relativePrefix x (R:ℝ) ≤ (c.bUpper:ℝ)-Rlo-c.logaLower+logRU := by
    unfold relativePrefix
    simp only [Nat.floor_natCast]
    constructor <;> nlinarith only [hA,hB,hR.1,hR.2,hlogA,hlogB,hlogR.1,hlogR.2,hpa,hpb,hlaS,hlbS]
  have hlo : -(S:ℝ)/(d:ℝ) ≤ (c.aLower:ℝ)-Rhi-c.logbUpper+logRL :=
    (div_le_iff₀ hdp).mpr (by nlinarith only [hlR])
  have hhi : (c.bUpper:ℝ)-Rlo-c.logaLower+logRU ≤ (S:ℝ)/(d:ℝ) :=
    (le_div_iff₀ hdp).mpr (by nlinarith only [huR])
  rw [neg_div] at hlo
  have habs : |(S:ℝ)*relativePrefix x (R:ℝ)| ≤ (S:ℝ)/(d:ℝ) :=
    abs_le.mpr ⟨by nlinarith only [hlo,he.1],he.2.trans hhi⟩
  rw [abs_mul,abs_of_pos hSp,div_eq_mul_inv] at habs
  simpa only [one_div] using (mul_le_mul_iff_right₀ hSp).mp habs

/-- Cell-chain coverage includes the final endpoint explicitly, even for an
empty final subchain. Seven section seams therefore require exact equality. -/
theorem checked_cell_chain_cover {a b : ℕ} {cells : List AssemblyCell}
    (h : checkCellChain a b cells = true) {x : ℝ} (ha : (a:ℝ) ≤ x) (hb : x ≤ (b:ℝ)) :
    x=(b:ℝ) ∨ ∃ c ∈ cells, (c.a:ℝ) ≤ x ∧ x ≤ (c.b:ℝ) := by
  induction cells generalizing a with
  | nil =>
    have he : a=b := of_decide_eq_true h
    left
    subst a
    exact le_antisymm hb ha
  | cons c cs ih =>
    simp only [checkCellChain, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hca,_⟩,htail⟩ := h
    by_cases hx : x ≤ (c.b:ℝ)
    · right
      refine ⟨c, List.mem_cons_self, ?_, hx⟩
      simpa only [hca] using ha
    · have hnext : (c.b:ℝ) ≤ x := le_of_lt (lt_of_not_ge hx)
      rcases ih htail hnext with he | ⟨d,hd,hl,hu⟩
      · exact Or.inl he
      · exact Or.inr ⟨d,List.mem_cons_of_mem c hd,hl,hu⟩

#print axioms checked_prefix_cut
#print axioms segment_prefix_reciprocal_certificate
#print axioms checked_cell_chain_cover
#print axioms checked_assembly_cell
#print axioms cumulative_bounds_join
#print axioms checked_increment_summary_sound
end ChenEffective.PlattWindow
