import PlattPointSubsetKernel
import PlattPointPackets.S1B000454
import PlattPointPackets.S1B000455
import PlattPointPackets.S1B000456
import PlattPointPackets.S1B000457
import PlattGlobalGrid.S6B000053
namespace ChenEffective.PlattWindow.PointCovers.S6B000053
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000454.points ++ ChenEffective.PlattWindow.PointPackets.S1B000455.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000456.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000457.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000053.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000053.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000053
