import PlattPointSubsetKernel
import PlattPointPackets.S1B000078
import PlattPointPackets.S1B000079
import PlattGlobalGrid.S4B000038
namespace ChenEffective.PlattWindow.PointCovers.S4B000038
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000078.points ++ ChenEffective.PlattWindow.PointPackets.S1B000079.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S4B000038.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S4B000038.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S4B000038
