import PlattPointSubsetKernel
import PlattPointPackets.S1B000233
import PlattPointPackets.S1B000234
import PlattPointPackets.S1B000235
import PlattGlobalGrid.S5B000082
namespace ChenEffective.PlattWindow.PointCovers.S5B000082
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000233.points ++ ChenEffective.PlattWindow.PointPackets.S1B000234.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000235.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000082.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000082.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000082
