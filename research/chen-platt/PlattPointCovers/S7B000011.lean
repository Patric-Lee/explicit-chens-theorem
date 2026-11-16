import PlattPointSubsetKernel
import PlattPointPackets.S2B000083
import PlattPointPackets.S2B000084
import PlattPointPackets.S2B000085
import PlattPointPackets.S2B000086
import PlattGlobalGrid.S7B000011
namespace ChenEffective.PlattWindow.PointCovers.S7B000011
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000083.points ++ ChenEffective.PlattWindow.PointPackets.S2B000084.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000085.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000086.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000011.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000011.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000011
