import PlattPointSubsetKernel
import PlattPointPackets.S1B000332
import PlattPointPackets.S1B000333
import PlattPointPackets.S1B000334
import PlattGlobalGrid.S6B000012
namespace ChenEffective.PlattWindow.PointCovers.S6B000012
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000332.points ++ ChenEffective.PlattWindow.PointPackets.S1B000333.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000334.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000012.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000012.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000012
