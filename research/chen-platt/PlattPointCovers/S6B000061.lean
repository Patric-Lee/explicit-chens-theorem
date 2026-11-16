import PlattPointSubsetKernel
import PlattPointPackets.S1B000482
import PlattPointPackets.S1B000483
import PlattPointPackets.S1B000484
import PlattPointPackets.S1B000485
import PlattPointPackets.S1B000486
import PlattGlobalGrid.S6B000061
namespace ChenEffective.PlattWindow.PointCovers.S6B000061
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000482.points ++ ChenEffective.PlattWindow.PointPackets.S1B000483.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000484.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000485.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000486.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000061.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000061.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000061
