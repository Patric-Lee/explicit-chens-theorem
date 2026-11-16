import PlattIncrementKernel

namespace ChenEffective.PlattWindow
/-- An opaque value of this structure can hide the packed numeral from later
elaboration, while retaining both original kernel-checked proof fields. -/
structure SegmentPacket (lo w B lower upper : Nat) where
  packed : Nat
  counts : Nat.beq (segmentCounts lo w B) packed = true
  arithmetic : (Nat.beq (segmentFixed (2^48) lo w packed B).1 lower &&
    Nat.beq (segmentFixed (2^48) lo w packed B).2 upper) = true
end ChenEffective.PlattWindow
