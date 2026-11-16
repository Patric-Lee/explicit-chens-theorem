import PlattPointSubsetKernel
import PlattPointPackets.S1B000029
import PlattPointPackets.S1B000030
import PlattGlobalGrid.S2B000059
namespace ChenEffective.PlattWindow.PointCovers.S2B000059
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000029.points ++ ChenEffective.PlattWindow.PointPackets.S1B000030.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S2B000059.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S2B000059.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S2B000059
