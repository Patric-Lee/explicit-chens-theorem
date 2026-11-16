import PlattGlobalGridKernel
import PlattPointPacketSoundness
import PlattLogRowSoundness

noncomputable section
set_option autoImplicit false
namespace ChenEffective.PlattWindow
open AnalyticNumberTheory.Mertens
set_option maxHeartbeats 3000000

theorem checked_log_slice {rows : List LogCertificate.LogRow}
    (h : rows.all LogCertificate.checkRow=true) (start count : Nat) :
    ((rows.drop start).take count).all LogCertificate.checkRow=true := by
  apply List.all_eq_true.mpr
  intro r hr
  exact List.all_eq_true.mp h r (List.mem_of_mem_drop (List.mem_of_mem_take hr))

theorem checked_log_append {xs ys : List LogCertificate.LogRow}
    (hx : xs.all LogCertificate.checkRow=true) (hy : ys.all LogCertificate.checkRow=true) :
    (xs++ys).all LogCertificate.checkRow=true := by
  simp only [List.all_append,hx,hy,Bool.and_self]

theorem checkedLogRows_sound {rows : List LogCertificate.LogRow}
    (h : CheckedLogRows rows) : rows.all LogCertificate.checkRow=true := by
  induction h with
  | checked h => exact h
  | slice start count h ih => exact checked_log_slice ih start count
  | append hx hy ihx ihy => exact checked_log_append ihx ihy

theorem checkGridLinks_sound {cells : List AssemblyCell} {points : List PrimePoint}
    {logs : List LogCertificate.LogRow} (h : checkGridLinks cells points logs=true)
    {c : AssemblyCell} (hc : c∈cells) :
    ∃ p∈points, ∃ q∈points, ∃ r∈logs, ∃ t∈logs, CellLinked c p q r t := by
  induction cells generalizing points logs with
  | nil => simp at hc
  | cons d ds ih =>
    cases points with
    | nil => simp [checkGridLinks] at h
    | cons p ps =>
      cases ps with
      | nil => simp [checkGridLinks] at h
      | cons q qs =>
        cases logs with
        | nil => simp [checkGridLinks] at h
        | cons r rs =>
          cases rs with
          | nil => simp [checkGridLinks] at h
          | cons t ts =>
            have hh : CellLinked d p q r t ∧ checkGridLinks ds (q::qs) (t::ts)=true := by
              simpa only [checkGridLinks,Bool.and_eq_true,decide_eq_true_eq] using h
            rcases List.mem_cons.mp hc with he | ht
            · subst c
              exact ⟨p,by simp,q,by simp,r,by simp,t,by simp,hh.1⟩
            · obtain ⟨v,hv,w,hw,y,hy,z,hz,hl⟩ := ih hh.2 ht
              exact ⟨v,List.mem_cons_of_mem _ hv,w,List.mem_cons_of_mem _ hw,
                y,List.mem_cons_of_mem _ hy,z,List.mem_cons_of_mem _ hz,hl⟩

theorem checkPointCoverAux_sound {fuel : Nat} {xs ys : List PrimePoint}
    (h : checkPointCoverAux fuel xs ys=true) : ∀p∈ys,p∈xs := by
  induction fuel generalizing xs ys with
  | zero =>
    cases ys with
    | nil => simp
    | cons q qs => simp [checkPointCoverAux] at h
  | succ n ih =>
    cases ys with
    | nil => simp
    | cons q qs =>
      cases xs with
      | nil => simp [checkPointCoverAux] at h
      | cons p ps =>
        simp only [checkPointCoverAux] at h
        split at h
        next he =>
          intro v hv
          rcases List.mem_cons.mp hv with heq | hv
          · simpa only [heq,he] using (List.mem_cons_self : p∈p::ps)
          · exact ih h v hv
        next _ =>
          intro v hv
          exact List.mem_cons_of_mem p (ih h v hv)

theorem checkPointCover_sound {xs ys : List PrimePoint}
    (h : checkPointCover xs ys=true) : ∀p∈ys,p∈xs := checkPointCoverAux_sound h

theorem gridWindowCertificate_sound {a b : Nat} {points : List PrimePoint}
    (h : GridWindowCertificate a b points)
    (hpoints : ∀p∈points,ScaledPrimeBound 4000000 p.1 p.2.1 p.2.2)
    (hR : ScaledPrimeBound 4000000 10000000000 116863011702975 116863401833309)
    (hlogR : (882879348526828:ℝ) ≤ (2:ℝ)^48*Real.log (Real.log (10000000000:ℝ)) ∧
      (2:ℝ)^48*Real.log (Real.log (10000000000:ℝ)) ≤ (882879348527041:ℝ)) :
    ∀x:ℝ,(a:ℝ)≤x→x<(b:ℝ)→|relativePrefix x (10000000000:ℝ)|≤1/20000 := by
  induction h with
  | @leaf a b points cells logs hcells hlogs hseams hlinks =>
    intro x hx hxb
    rcases checked_cell_chain_cover hseams hx hxb.le with he | ⟨c,hc,hca,hcb⟩
    · exact False.elim ((ne_of_lt hxb) he)
    · obtain ⟨p,hp,q,hq,r,hr,t,ht,hl⟩ := checkGridLinks_sound hlinks hc
      obtain ⟨ha,hb,hal,hbu,hra,htb,hrl,htu⟩ := hl
      have hp' := hpoints p hp
      have hq' := hpoints q hq
      have hr' := LogCertificate.checkedRows_sound logs (checkedLogRows_sound hlogs) r hr
      have ht' := LogCertificate.checkedRows_sound logs (checkedLogRows_sound hlogs) t ht
      apply checked_assembly_cell (S:=2^48) (d:=20000) (U:=4000000)
        (R:=10000000000) (by decide) (by decide)
        (List.all_eq_true.mp hcells c hc) ?_ ?_ ?_ ?_ ?_ ?_ hca hcb
      · simpa only [ScaledPrimeBound,←ha,←hal,Nat.cast_pow,Nat.cast_ofNat] using hp'.1
      · simpa only [ScaledPrimeBound,←hb,←hbu,Nat.cast_pow,Nat.cast_ofNat] using hq'.2
      · simpa only [ScaledPrimeBound,Nat.cast_pow,Nat.cast_ofNat] using hR
      · simpa only [hra,hrl,LogCertificate.scale,Nat.cast_pow,Nat.cast_ofNat] using hr'.1
      · simpa only [htb,htu,LogCertificate.scale,Nat.cast_pow,Nat.cast_ofNat] using ht'.2
      · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hlogR
  | @append a b c xs ys hx hy ihx ihy =>
    intro x hax hxc
    by_cases hxb : x<(b:ℝ)
    · exact ihx (fun p hp => hpoints p (List.mem_append_left _ hp)) x hax hxb
    · exact ihy (fun p hp => hpoints p (List.mem_append_right _ hp)) x (le_of_not_gt hxb) hxc

#print axioms checkPointCover_sound
#print axioms gridWindowCertificate_sound
end ChenEffective.PlattWindow
