import PlattPointSubsetKernel
import PlattPointPackets.S1B000188
import PlattPointPackets.S1B000189
import PlattPointPackets.S1B000190
import PlattGlobalGrid.S5B000053
namespace ChenEffective.PlattWindow.PointCovers.S5B000053
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000188.points ++ ChenEffective.PlattWindow.PointPackets.S1B000189.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000190.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000053.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000053.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000053
