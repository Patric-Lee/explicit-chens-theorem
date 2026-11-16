import PlattReciprocalKernel
namespace ChenEffective.PlattWindow.Manual.Count131072.C076264
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def packed : Nat := 41
theorem count_checked : Nat.beq (segmentCounts 9999998977 9 1) packed = true := by
  decide +kernel
theorem arithmetic_checked :
    (Nat.beq (segmentFixed (2^48) 9999998977 9 packed 1).1 1154047 &&
     Nat.beq (segmentFixed (2^48) 9999998977 9 packed 1).2 1154048) = true := by
  decide +kernel
end ChenEffective.PlattWindow.Manual.Count131072.C076264
