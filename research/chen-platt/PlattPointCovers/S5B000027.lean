import PlattPointSubsetKernel
import PlattPointPackets.S1B000156
import PlattPointPackets.S1B000157
import PlattPointPackets.S1B000158
import PlattGlobalGrid.S5B000027
namespace ChenEffective.PlattWindow.PointCovers.S5B000027
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000156.points ++ ChenEffective.PlattWindow.PointPackets.S1B000157.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000158.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000027.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000027.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000027
