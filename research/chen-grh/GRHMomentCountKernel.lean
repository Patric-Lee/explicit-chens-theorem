import PlattReciprocalKernel

/-! Arithmetic certificate support; all evaluation uses the Lean kernel. -/
namespace ChenEffective.GRHSub12
noncomputable def sumFields (w Y : Nat) : Nat → Nat :=
  Nat.rec 0 (fun k acc => Nat.add acc (PlattWindow.packedField (2^w) Y k))
end ChenEffective.GRHSub12
