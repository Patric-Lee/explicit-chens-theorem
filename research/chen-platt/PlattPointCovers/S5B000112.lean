import PlattPointSubsetKernel
import PlattPointPackets.S1B000291
import PlattPointPackets.S1B000292
import PlattPointPackets.S1B000293
import PlattPointPackets.S1B000294
import PlattGlobalGrid.S5B000112
namespace ChenEffective.PlattWindow.PointCovers.S5B000112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000291.points ++ ChenEffective.PlattWindow.PointPackets.S1B000292.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000293.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000294.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000112.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000112.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000112
