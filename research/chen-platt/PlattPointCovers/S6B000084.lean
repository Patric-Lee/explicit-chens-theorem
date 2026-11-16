import PlattPointSubsetKernel
import PlattPointPackets.S1B000577
import PlattPointPackets.S1B000578
import PlattPointPackets.S1B000579
import PlattPointPackets.S1B000580
import PlattPointPackets.S1B000581
import PlattGlobalGrid.S6B000084
namespace ChenEffective.PlattWindow.PointCovers.S6B000084
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000577.points ++ ChenEffective.PlattWindow.PointPackets.S1B000578.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000579.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000580.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000581.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000084.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000084.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000084
