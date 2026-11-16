import PlattPointSubsetKernel
import PlattPointPackets.S1B000226
import PlattPointPackets.S1B000227
import PlattPointPackets.S1B000228
import PlattGlobalGrid.S5B000078
namespace ChenEffective.PlattWindow.PointCovers.S5B000078
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000226.points ++ ChenEffective.PlattWindow.PointPackets.S1B000227.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000228.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000078.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000078.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000078
