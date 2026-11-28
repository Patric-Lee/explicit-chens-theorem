import GRHH10PrimeIntervals

/-! Exact finite-band coverage and conditional pasting with the saved cutoff.
No representation estimate inside a band is asserted. -/
noncomputable section
namespace ChenEffective.H10Band
open Real
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
def bandEndpoints : Array ℕ := #[22026,22247,22470,22695,22922,23152,23384,23618,23855,24094,24335,24579,24825,25074,25325,25579,25835,26094,26355,26619,26886,27155,27427,27702,27980,28260,28543,28829,29118,29410,29705,30003,30304,30608,30915,31225,31538,31854,32173,32495,32820,33149,33481,33816,34155,34497,34842,35191,35543,35899,36258,36621,36988,37358,37732,38110,38492,38877,39266,39659,40056,40457,40862,41271,41684,42101,42523,42949,43379,43813,44252,44695,45142,45594,46050,46511,46977,47447,47922,48402,48887,49376,49870,50369,50873,51382,51896,52415,52940,53470,54005,54546,55092,55643,56200,56762,57330,57904,58484,59069,59660,60257,60860,61469,62084,62705,63333,63967,64607,65254,65907,66567,67233,67906,68586,69272,69965,70665,71372,72086,72807,73536,74272,75015,75766,76524,77290,78063,78844,79633,80430,81235,82048,82869,83698,84535,85381,86235,87098,87969,88849,89738,90636,91543,92459,93384,94318,95262,96215,97178,98150,99132,100124,101126,102138,103160,104192,105234,106287,107350,108424,109509,110605,111712,112830,113959,115099,116250,117413,118588,119774,120972,122182,123404,124639,125886,127145,128417,129702,131000,132310,133634,134971,136321,137685,139062,140453,141858,143277,144710,146158,147620,149097,150588,152094,153615,155152,156704,158272,159500]
def bandCount : ℕ := 199
def bandEndpoint (i : ℕ) : ℝ := (bandEndpoints[i]?.getD 159500 : ℕ)

theorem endpoints_checked : bandEndpoints.size=bandCount+1 ∧
    bandEndpoints[0]?.getD 0=22026 ∧
    bandEndpoints[bandCount]?.getD 0=159500 ∧
    ∀ i : Fin bandCount, bandEndpoints[i.val]?.getD 0 < bandEndpoints[i.val+1]?.getD 0 := by
  decide +kernel

theorem first_endpoint : bandEndpoint 0=22026 := by norm_num [bandEndpoint,bandEndpoints]
theorem last_endpoint : bandEndpoint bandCount=159500 := by norm_num [bandEndpoint,bandEndpoints,bandCount]

theorem adjacent_cover {n : ℕ} (hn : 0<n) (e : ℕ→ℝ) {x : ℝ}
    (hx : e 0≤x) (ht : x<e n) : ∃ i : ℕ, i<n ∧ e i≤x ∧ x<e (i+1) := by
  let P := fun i : ℕ => i<n ∧ x<e (i+1)
  have hex : ∃ i, P i := by
    refine ⟨n-1,?_,?_⟩
    · omega
    · simpa only [Nat.sub_add_cancel (by omega : 1≤n)] using ht
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  have hlow : e j≤x := by
    by_cases hz : j=0
    · simpa only [hz] using hx
    · by_contra h
      have hprev : P (j-1) := by
        constructor
        · have := hj.1; omega
        · simpa only [Nat.sub_add_cancel (by omega : 1≤j)] using (lt_of_not_ge h)
      have hm := Nat.find_min' hex hprev
      change j≤j-1 at hm
      omega
  exact ⟨j,hj.1,hlow,hj.2⟩

theorem log_band_cover {L : ℝ} (hL : 22026≤L) (hU : L<159500) :
    ∃ i : ℕ, i<bandCount ∧ bandEndpoint i≤L ∧ L<bandEndpoint (i+1) := by
  apply adjacent_cover (by norm_num [bandCount]) bandEndpoint
  · simpa only [first_endpoint] using hL
  · simpa only [last_endpoint] using hU

/-- A bridge proof for each band can be pasted with the existing cutoff.
Both the interior proofs and the saved theorem are explicit arguments. -/
theorem paste_saved_cutoff (P : ℕ→Prop)
    (hhigh : ∀ N : ℕ, 3^145000≤N → P N)
    (hbands : ∀ i : ℕ, i<bandCount → ∀ N : ℕ,
      bandEndpoint i≤log (N:ℝ) → log (N:ℝ)<bandEndpoint (i+1) → P N)
    {N : ℕ} (hN : exp (exp (10:ℝ))≤N) : P N := by
  by_cases hlarge : 3^145000≤N
  · exact hhigh N hlarge
  · have hn : (0:ℝ)<N := lt_of_lt_of_le (exp_pos _) hN
    have hlt : (N:ℝ)<((3^145000:ℕ):ℝ) := by exact_mod_cast (lt_of_not_ge hlarge)
    have hlog := (log_lt_log hn hlt).trans_le old_cutoff_log_cap
    obtain ⟨i,hi,hlo,hhi⟩ := log_band_cover (log_lower_of_double_exp_ten hN) hlog
    exact hbands i hi N hlo hhi

#print axioms endpoints_checked
#print axioms log_band_cover
#print axioms paste_saved_cutoff
end ChenEffective.H10Band
end
