import PlattPointSubsetKernel
import PlattPointPackets.S1B000501
import PlattPointPackets.S1B000502
import PlattPointPackets.S1B000503
import PlattPointPackets.S1B000504
import PlattPointPackets.S1B000505
import PlattGlobalGrid.S6B000066
namespace ChenEffective.PlattWindow.PointCovers.S6B000066
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000501.points ++ ChenEffective.PlattWindow.PointPackets.S1B000502.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000503.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000504.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000505.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000066.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000066.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000066
