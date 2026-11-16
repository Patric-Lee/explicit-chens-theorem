import PlattPointSubsetKernel
import PlattPointPackets.S1B000427
import PlattPointPackets.S1B000428
import PlattPointPackets.S1B000429
import PlattPointPackets.S1B000430
import PlattGlobalGrid.S6B000045
namespace ChenEffective.PlattWindow.PointCovers.S6B000045
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000427.points ++ ChenEffective.PlattWindow.PointPackets.S1B000428.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000429.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000430.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000045.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000045.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000045
