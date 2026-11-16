import PlattPointSubsetKernel
import PlattPointPackets.S1B000389
import PlattPointPackets.S1B000390
import PlattPointPackets.S1B000391
import PlattPointPackets.S1B000392
import PlattGlobalGrid.S6B000033
namespace ChenEffective.PlattWindow.PointCovers.S6B000033
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000389.points ++ ChenEffective.PlattWindow.PointPackets.S1B000390.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000391.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000392.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000033.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000033.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000033
