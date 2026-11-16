import PlattPointSubsetKernel
import PlattPointPackets.S1B000450
import PlattPointPackets.S1B000451
import PlattPointPackets.S1B000452
import PlattPointPackets.S1B000453
import PlattPointPackets.S1B000454
import PlattGlobalGrid.S6B000052
namespace ChenEffective.PlattWindow.PointCovers.S6B000052
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000450.points ++ ChenEffective.PlattWindow.PointPackets.S1B000451.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000452.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000453.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000454.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000052.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000052.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000052
