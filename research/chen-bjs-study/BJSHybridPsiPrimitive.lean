import BJSHybridZeroSplit

noncomputable section
namespace ChenEffective.HybridProduct
open Real Finset Set Filter MeasureTheory
open scoped Topology ArithmeticFunction.vonMangoldt
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem psi1_continuousAt {x : ℝ} (hx : 0 < x) : ContinuousAt Dusart.psi1 x := by
  let N : ℕ := ⌊x⌋₊+2
  have hxN : x < (N:ℝ) := by
    have hh := Nat.lt_floor_add_one x
    dsimp [N]
    push_cast
    linarith only [hh]
  have he : Dusart.psi1 =ᶠ[𝓝 x] (fun y : ℝ => ∑ n ∈ Iic N,max (y-n) 0*Λ n) := by
    filter_upwards [Ioo_mem_nhds hx hxN] with y hy
    have hfloor : ⌊y⌋₊ ≤ N := by
      have hh := Nat.floor_mono hy.2.le
      simpa only [Nat.floor_natCast] using hh
    exact (Dusart.psi1_ext hy.1.le hfloor).symm
  have hc : ContinuousAt (fun y : ℝ => ∑ n ∈ Iic N,max (y-n) 0*Λ n) x := by fun_prop
  exact hc.congr_of_eventuallyEq he

theorem psi1_right_derivative {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt Dusart.psi1 (Chebyshev.psi x) (Ioi x) x := by
  have he : Dusart.psi1 =ᶠ[𝓝[Ioi x] x]
      (fun y : ℝ => ∑ n ∈ Iic ⌊x⌋₊,(y-n)*Λ n) := by
    have hb : ∀ᶠ y in 𝓝[Ioi x] x,y < (⌊x⌋₊:ℝ)+1 :=
      (eventually_lt_nhds (Nat.lt_floor_add_one x)).filter_mono inf_le_left
    filter_upwards [hb,self_mem_nhdsWithin] with y hy hxy
    have hy0 : 0 ≤ y := hx.trans hxy.le
    have hfloor : ⌊y⌋₊=⌊x⌋₊ := (Nat.floor_eq_iff hy0).mpr
      ⟨(Nat.floor_le hx).trans hxy.le,hy⟩
    simp only [Dusart.psi1,hfloor]
  have hd : HasDerivAt (fun y : ℝ => ∑ n ∈ Iic ⌊x⌋₊,(y-n)*Λ n) (Dusart.psiF x) x := by
    have hh := HasDerivAt.fun_sum (u:=Iic ⌊x⌋₊) (fun n _ =>
      ((hasDerivAt_id x).sub_const (n:ℝ)).mul_const (Λ n))
    simpa only [one_mul,Dusart.psiF,id_eq] using hh
  rw [Dusart.psiF_eq_chebyshev] at hd
  exact hd.hasDerivWithinAt.congr_of_eventuallyEq he rfl

def psi1Error (x : ℝ) : ℝ := Dusart.psi1 x-x^2/2

theorem psi1_error_right_derivative {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt psi1Error (Chebyshev.psi x-x) (Ioi x) x := by
  have hp : HasDerivAt (fun y : ℝ => y^2/2) x x := by
    convert! ((hasDerivAt_id x).pow 2).div_const 2 using 1
    simp
  exact (psi1_right_derivative hx).sub hp.hasDerivWithinAt

theorem psi_error_primitive {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b,Chebyshev.psi t-t=psi1Error b-psi1Error a := by
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
  · intro x hx
    exact ((psi1_continuousAt (ha.trans_le hx.1)).sub (by fun_prop)).continuousWithinAt
  · intro x hx
    exact psi1_error_right_derivative (ha.trans_le hx.1.le).le
  · exact (show IntervalIntegrable Chebyshev.psi volume a b from Chebyshev.psi_mono.intervalIntegrable).sub (continuous_id.intervalIntegrable a b)

#print axioms psi_error_primitive
end ChenEffective.HybridProduct



