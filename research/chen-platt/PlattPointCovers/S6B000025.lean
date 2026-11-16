import PlattPointSubsetKernel
import PlattPointPackets.S1B000366
import PlattPointPackets.S1B000367
import PlattPointPackets.S1B000368
import PlattPointPackets.S1B000369
import PlattGlobalGrid.S6B000025
namespace ChenEffective.PlattWindow.PointCovers.S6B000025
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000366.points ++ ChenEffective.PlattWindow.PointPackets.S1B000367.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000368.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000369.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000025.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000025.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000025
