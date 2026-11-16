import PlattPointSubsetKernel
import PlattPointPackets.S1B000568
import PlattPointPackets.S1B000569
import PlattPointPackets.S1B000570
import PlattPointPackets.S1B000571
import PlattPointPackets.S1B000572
import PlattGlobalGrid.S6B000082
namespace ChenEffective.PlattWindow.PointCovers.S6B000082
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000568.points ++ ChenEffective.PlattWindow.PointPackets.S1B000569.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000570.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000571.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000572.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000082.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000082.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000082
