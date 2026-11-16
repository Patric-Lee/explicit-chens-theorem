import PlattPointPacketKernel
import PlattAssemblySoundness

noncomputable section
set_option autoImplicit false
namespace ChenEffective.PlattWindow
open AnalyticNumberTheory.Mertens
set_option maxHeartbeats 3000000

def ScaledPrimeBound (origin x lower upper : ℕ) : Prop :=
  (lower:ℝ) ≤ (2:ℝ)^48*(primeReciprocalSum x-primeReciprocalSum origin) ∧
    (2:ℝ)^48*(primeReciprocalSum x-primeReciprocalSum origin) ≤ (upper:ℝ)

theorem pointSegment_whole_sound (s : PointSegment) :
    ScaledPrimeBound (s.lo-1) (pointSegmentEnd s) s.lower s.upper := by
  have hc := Nat.eq_of_beq_eq_true s.certified.counts
  have ha := Bool.and_eq_true_iff.mp s.certified.arithmetic
  have hp : segmentFixed (2^48) s.lo s.w s.certified.packed s.B =
      (s.lower,s.upper) :=
    Prod.ext (Nat.eq_of_beq_eq_true ha.1) (Nat.eq_of_beq_eq_true ha.2)
  simpa only [ScaledPrimeBound,pointSegmentEnd,Nat.cast_pow,Nat.cast_ofNat] using
    (segment_reciprocal_certificate (scale:=2^48) s.certified.odd s.certified.left_large
      s.certified.within_cover hc hp)

theorem pointSegment_points_sound (s : PointSegment) {origin : ℕ}
    (hbase : ScaledPrimeBound origin (s.lo-1) s.baseLower s.baseUpper)
    {p : PrimePoint} (hp : p ∈ s.points) :
    ScaledPrimeBound origin p.1 p.2.1 p.2.2 := by
  rw [← s.certified.point_links] at hp
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
  have hc' : c ∈ s.cuts := List.mem_of_mem_take hc
  have hcut := checked_prefix_cut s.certified.checkpoints hc'
  have hcount := Nat.eq_of_beq_eq_true s.certified.counts
  have hlocal : ScaledPrimeBound (s.lo-1) (s.lo-1+2*2^s.w*c.k) c.lower c.upper := by
    simpa only [ScaledPrimeBound,Nat.cast_pow,Nat.cast_ofNat] using
      (segment_prefix_reciprocal_certificate (scale:=2^48) s.certified.odd
        s.certified.left_large s.certified.within_cover hcut.1 hcount hcut.2)
  simpa only [ScaledPrimeBound,Nat.cast_add] using cumulative_bounds_join hbase hlocal

theorem checkPointChain_sound {origin a l u b L U : ℕ} {segments : List PointSegment}
    (hcheck : checkPointChain a l u b L U segments=true)
    (hin : ScaledPrimeBound origin a l u) :
    (∀ p ∈ segments.flatMap PointSegment.points, ScaledPrimeBound origin p.1 p.2.1 p.2.2) ∧
      ScaledPrimeBound origin b L U := by
  induction segments generalizing a l u with
  | nil =>
    have h : a=b ∧ l=L ∧ u=U := of_decide_eq_true hcheck
    constructor
    · simp
    · simpa only [h.1,h.2.1,h.2.2] using hin
  | cons s ss ih =>
    have hc : (s.lo-1=a ∧ s.baseLower=l ∧ s.baseUpper=u) ∧
        checkPointChain (pointSegmentEnd s) (l+s.lower) (u+s.upper) b L U ss=true := by
      simpa only [checkPointChain,Bool.and_eq_true,decide_eq_true_eq] using hcheck
    have hbase : ScaledPrimeBound origin (s.lo-1) s.baseLower s.baseUpper := by
      simpa only [hc.1.1,hc.1.2.1,hc.1.2.2] using hin
    have hwhole : ScaledPrimeBound a (pointSegmentEnd s) s.lower s.upper := by
      simpa only [hc.1.1] using pointSegment_whole_sound s
    have hnext : ScaledPrimeBound origin (pointSegmentEnd s) (l+s.lower) (u+s.upper) := by
      simpa only [ScaledPrimeBound,Nat.cast_add] using cumulative_bounds_join hin hwhole
    obtain ⟨hpoints,hend⟩ := ih hc.2 hnext
    refine ⟨?_,hend⟩
    intro p hp
    simp only [List.flatMap_cons,List.mem_append] at hp
    rcases hp with hp | hp
    · exact pointSegment_points_sound s hbase hp
    · exact hpoints p hp

theorem pointChainCertificate_sound {origin a l u b L U : ℕ} {points : List PrimePoint}
    (h : PointChainCertificate a l u b L U points) (hin : ScaledPrimeBound origin a l u) :
    (∀ p ∈ points, ScaledPrimeBound origin p.1 p.2.1 p.2.2) ∧ ScaledPrimeBound origin b L U := by
  induction h with
  | leaf segments hcheck => exact checkPointChain_sound hcheck hin
  | append hx hy ihx ihy =>
    obtain ⟨hpx,hmid⟩ := ihx hin
    obtain ⟨hpy,hend⟩ := ihy hmid
    refine ⟨?_,hend⟩
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hpx p hp
    · exact hpy p hp
  | relabel he h ih => simpa only [← he] using ih hin

#print axioms pointChainCertificate_sound
end ChenEffective.PlattWindow
