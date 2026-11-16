import PlattPointSubsetKernel
import PlattPointPackets.S1B000414
import PlattPointPackets.S1B000415
import PlattPointPackets.S1B000416
import PlattPointPackets.S1B000417
import PlattGlobalGrid.S6B000041
namespace ChenEffective.PlattWindow.PointCovers.S6B000041
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000414.points ++ ChenEffective.PlattWindow.PointPackets.S1B000415.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000416.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000417.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000041.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000041.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000041
