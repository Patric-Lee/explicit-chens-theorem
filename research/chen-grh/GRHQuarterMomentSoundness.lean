import GRHQuarterMomentBounds
import GRHMomentCountSoundness

noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def envelopePrefix (F : Finset ℕ) (x : ℕ) : ℝ :=
  ∑ p∈F.filter (fun p=>p≤x),primeEnvelope p

theorem envelopePrefix_split (F : Finset ℕ) {a b : ℕ} (hab : a≤b) :
    envelopePrefix F b=envelopePrefix F a+
      ∑ p∈F.filter (fun p=>a<p ∧ p≤b),primeEnvelope p := by
  classical
  simp only [envelopePrefix,sum_filter]
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  by_cases hpa : p≤a
  · have hpb := hpa.trans hab
    simp [hpa,hpb,show ¬a<p by omega]
  · have hap : a<p := by omega
    by_cases hpb : p≤b <;> simp [hpa,hap,hpb]

theorem envelope_one_block (F : Finset ℕ) (hF : ∀ p∈F,p.Prime)
    {lo w degree u t c : ℕ} (hlo : 3≤lo) (hodd : lo%2=1)
    (hu : 0<u) (hroot : u^4≤lo*scale^4) (hdeg : degree=3 ∨ degree=7)
    (hlog : factorialFor degree*denominator^degree*majorantNumerator lo u≤
      expNumerator degree t*majorantDenominator u)
    (hcount : (c:ℝ)=∑ j∈range (2^w),if (lo+2*j).Prime then (1:ℝ) else 0) :
    (∑ p∈F.filter (fun p=>lo-1<p ∧ p≤lo+2*2^w-1),primeEnvelope p)≤
      (c:ℝ)*t/denominator := by
  have hW : 0<2^w := by positivity
  have hc := GRHSub12.prime_interval_card_le F hF (lo-1) (lo+2*2^w-1) lo w 1 c
    (by omega) (by omega) (by omega) hodd hlo
    (by simp only [Nat.mul_one];omega) (by simpa using hcount)
  have hweights :
      (∑ p∈F.filter (fun p=>lo-1<p ∧ p≤lo+2*2^w-1),primeEnvelope p)≤
      ∑ _p∈F.filter (fun p=>lo-1<p ∧ p≤lo+2*2^w-1),(t:ℝ)/denominator := by
    apply sum_le_sum
    intro p hp
    have hpl : lo≤p := by have := (mem_filter.mp hp).2.1;omega
    exact primeEnvelope_le_checked hlo hpl hu hroot hdeg hlog
  have hm := mul_le_mul_of_nonneg_right hc
    (show (0:ℝ)≤(t:ℝ)/denominator by positivity)
  simp only [sum_const,nsmul_eq_mul] at hweights
  exact hweights.trans (hm.trans_eq (by ring))

theorem packet_field_count {lo w B Y k : ℕ} (hodd : lo%2=1) (hlo : 3≤lo)
    (htop : lo+2*(2^w*B)-1≤PsiFinite.baseCover) (hk : k<B)
    (hcount : ChenEffective.PlattWindow.segmentCounts lo w B=Y) :
    ((ChenEffective.PlattWindow.packedField (2^w) Y k:ℕ):ℝ)=
      ∑ j∈range (2^w),if (blockLo lo w k+2*j).Prime then (1:ℝ) else 0 := by
  have hh := ChenEffective.PlattWindow.segmentCounts_prime_count hodd hlo
    (by simpa only [Nat.mul_assoc] using htop) hk hcount
  change ((ChenEffective.PlattWindow.packedField (2^w) Y k:ℕ):ℝ)=_ at hh
  apply hh.trans
  apply sum_congr rfl
  intro j hj
  have he : ChenEffective.PlattWindow.blockLeft lo w k+1+2*j=blockLo lo w k+2*j := by
    unfold ChenEffective.PlattWindow.blockLeft blockLo
    have hs : lo-1+1=lo := Nat.sub_add_cancel (by omega)
    nlinarith only [hs]
  rw [he]

theorem envelope_prefix_from (F : Finset ℕ) (hF : ∀ p∈F,p.Prime)
    {lo w degree B Y : ℕ} (hodd : lo%2=1) (hlo : 3≤lo)
    (htop : lo+2*(2^w*B)-1≤PsiFinite.baseCover)
    (hcount : ChenEffective.PlattWindow.segmentCounts lo w B=Y)
    (hdeg : degree=3 ∨ degree=7) (data : List (ℕ×ℕ)) :
    ∀ k : ℕ, k+data.length≤B →
      boundsCheckFrom (blockLo lo w k) w degree data=true →
      envelopePrefix F (blockLo lo w (k+data.length)-1)≤
        envelopePrefix F (blockLo lo w k-1)+(weightedSumFrom w Y k data:ℝ)/denominator := by
  induction data with
  | nil =>
    intro k hk hb
    simp only [List.length_nil,Nat.add_zero,weightedSumFrom,Nat.cast_zero,zero_div,add_zero]
    exact le_rfl
  | cons pair data ih =>
    rcases pair with ⟨u,t⟩
    intro k hk hb
    change (blockCheck (blockLo lo w k) degree u t &&
      boundsCheckFrom (blockLo lo w k+2*2^w) w degree data)=true at hb
    have hb' : blockCheck (blockLo lo w k) degree u t=true ∧
        boundsCheckFrom (blockLo lo w k+2*2^w) w degree data=true := by
      simpa only [Bool.and_eq_true] using hb
    obtain ⟨hhead,htail⟩ := hb'
    have hv : 0<u ∧ u^4≤blockLo lo w k*scale^4 ∧
        factorialFor degree*denominator^degree*majorantNumerator (blockLo lo w k) u≤
          expNumerator degree t*majorantDenominator u := of_decide_eq_true hhead
    have hkB : k<B := by simp only [List.length_cons] at hk;omega
    have hlo' : 3≤blockLo lo w k := by unfold blockLo;omega
    have hodd' : blockLo lo w k%2=1 := by unfold blockLo;omega
    have hfield := packet_field_count hodd hlo htop hkB hcount
    have hblock := envelope_one_block F hF hlo' hodd' hv.1 hv.2.1 hdeg hv.2.2 hfield
    have hshift : blockLo lo w k+2*2^w=blockLo lo w (k+1) := by unfold blockLo;ring
    rw [hshift] at htail hblock
    have hW : 0<2^w := by positivity
    have hmono : blockLo lo w k-1≤blockLo lo w (k+1)-1 := by rw [←hshift];omega
    have hsplit := envelopePrefix_split F hmono
    have hfirst : envelopePrefix F (blockLo lo w (k+1)-1)≤
        envelopePrefix F (blockLo lo w k-1)+
          (ChenEffective.PlattWindow.packedField (2^w) Y k:ℝ)*t/denominator := by
      rw [hsplit]
      linarith only [hblock]
    have hrest := ih (k+1) (by simp only [List.length_cons] at hk;omega) htail
    have he : (k+1)+data.length=k+((u,t)::data).length := by simp;omega
    rw [he] at hrest
    calc
      _ ≤ envelopePrefix F (blockLo lo w (k+1)-1)+
          (weightedSumFrom w Y (k+1) data:ℝ)/denominator := hrest
      _ ≤ (envelopePrefix F (blockLo lo w k-1)+
          (ChenEffective.PlattWindow.packedField (2^w) Y k:ℝ)*t/denominator)+
          (weightedSumFrom w Y (k+1) data:ℝ)/denominator := by linarith only [hfirst]
      _ = _ := by simp only [weightedSumFrom,Nat.cast_add,Nat.cast_mul];ring

theorem certified_envelope_prefix (F : Finset ℕ) (hF : ∀ p∈F,p.Prime)
    {lo w degree B Y weighted : ℕ} (hodd : lo%2=1) (hlo : 3≤lo)
    (htop : lo+2*(2^w*B)-1≤PsiFinite.baseCover) (data : List (ℕ×ℕ))
    (hcounts : Nat.beq (ChenEffective.PlattWindow.segmentCounts lo w B) Y=true)
    (hbounds : boundsCheck lo w degree B data=true)
    (hweighted : Nat.beq (weightedSum w Y data) weighted=true) :
    envelopePrefix F (lo+2*(2^w*B)-1)≤envelopePrefix F (lo-1)+(weighted:ℝ)/denominator := by
  have hb' : decide (data.length=B ∧ (degree=3 ∨ degree=7))=true ∧
      boundsCheckFrom lo w degree data=true := by
    simpa only [boundsCheck,Bool.and_eq_true] using hbounds
  obtain ⟨hheader,htail⟩ := hb'
  have hhead : data.length=B ∧ (degree=3 ∨ degree=7) := of_decide_eq_true hheader
  have hh := envelope_prefix_from F hF hodd hlo htop (Nat.eq_of_beq_eq_true hcounts)
    hhead.2 data 0 (by omega) (by simpa only [blockLo,Nat.mul_zero,Nat.add_zero] using htail)
  rw [hhead.1] at hh
  simp only [blockLo,Nat.zero_add,Nat.mul_zero,Nat.add_zero] at hh
  change envelopePrefix F (lo+2*(2^w*B)-1)≤envelopePrefix F (lo-1)+
    (weightedSum w Y data:ℝ)/denominator at hh
  rwa [Nat.eq_of_beq_eq_true hweighted] at hh

#print axioms certified_envelope_prefix
end ChenEffective.H10Band
end
