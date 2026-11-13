import PlattPrefixBridge

noncomputable section
namespace ChenEffective.PlattWindow
open Real AnalyticNumberTheory.Mertens

def relativePrefix (x r : ℝ) : ℝ :=
  (primeReciprocalSum ⌊x⌋₊-primeReciprocalSum ⌊r⌋₊)-
    (log (log x)-log (log r))

theorem relativePrefix_eq (x r : ℝ) :
    relativePrefix x r = reciprocalError x-reciprocalError r :=
  (reciprocalError_sub x r).symm

/-- Outward-rounded endpoint data controls every real point of a cell,
including primes and noninteger endpoints. -/
theorem relative_cell {a b x r lower upper la ub lr ur : ℝ}
    (ha : 1 < a) (hax : a ≤ x) (hxb : x ≤ b)
    (hlower : lower ≤ primeReciprocalSum ⌊a⌋₊-primeReciprocalSum ⌊r⌋₊)
    (hupper : primeReciprocalSum ⌊b⌋₊-primeReciprocalSum ⌊r⌋₊ ≤ upper)
    (hla : la ≤ log (log a)) (hub : log (log b) ≤ ub)
    (hlr : lr ≤ log (log r)) (hur : log (log r) ≤ ur) :
    lower-ub+lr ≤ relativePrefix x r ∧ relativePrefix x r ≤ upper-la+ur := by
  have hpax := primeReciprocalSum_mono (Nat.floor_mono hax)
  have hpxb := primeReciprocalSum_mono (Nat.floor_mono hxb)
  have hxa : log (log a) ≤ log (log x) :=
    log_le_log (log_pos ha) (log_le_log (by linarith only [ha]) hax)
  have hbx : log (log x) ≤ log (log b) :=
    log_le_log (log_pos (ha.trans_le hax))
      (log_le_log (by linarith only [ha,hax]) hxb)
  unfold relativePrefix
  constructor <;> linarith only [hpax,hpxb,hxa,hbx,hlower,hupper,hla,hub,hlr,hur]

theorem relative_cell_paid {a b x r lower upper la ub lr ur : ℝ}
    (ha : 1 < a) (hax : a ≤ x) (hxb : x ≤ b)
    (hlower : lower ≤ primeReciprocalSum ⌊a⌋₊-primeReciprocalSum ⌊r⌋₊)
    (hupper : primeReciprocalSum ⌊b⌋₊-primeReciprocalSum ⌊r⌋₊ ≤ upper)
    (hla : la ≤ log (log a)) (hub : log (log b) ≤ ub)
    (hlr : lr ≤ log (log r)) (hur : log (log r) ≤ ur)
    (hlo : -finiteAllowance ≤ lower-ub+lr)
    (hhi : upper-la+ur ≤ finiteAllowance) :
    |relativePrefix x r| ≤ finiteAllowance := by
  have h := relative_cell ha hax hxb hlower hupper hla hub hlr hur
  exact abs_le.mpr ⟨hlo.trans h.1,h.2.trans hhi⟩

#print axioms relative_cell_paid
end ChenEffective.PlattWindow
