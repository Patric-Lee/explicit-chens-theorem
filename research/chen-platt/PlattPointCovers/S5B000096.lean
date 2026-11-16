import PlattPointSubsetKernel
import PlattPointPackets.S1B000259
import PlattPointPackets.S1B000260
import PlattPointPackets.S1B000261
import PlattGlobalGrid.S5B000096
namespace ChenEffective.PlattWindow.PointCovers.S5B000096
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000259.points ++ ChenEffective.PlattWindow.PointPackets.S1B000260.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000261.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000096.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000096.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000096
