import PlattPointSubsetKernel
import PlattPointPackets.S1B000525
import PlattPointPackets.S1B000526
import PlattPointPackets.S1B000527
import PlattPointPackets.S1B000528
import PlattPointPackets.S1B000529
import PlattGlobalGrid.S6B000072
namespace ChenEffective.PlattWindow.PointCovers.S6B000072
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000525.points ++ ChenEffective.PlattWindow.PointPackets.S1B000526.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000527.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000528.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000529.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000072.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000072.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000072
