import PlattPointSubsetKernel
import PlattPointPackets.S1B000468
import PlattPointPackets.S1B000469
import PlattPointPackets.S1B000470
import PlattPointPackets.S1B000471
import PlattGlobalGrid.S6B000057
namespace ChenEffective.PlattWindow.PointCovers.S6B000057
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000468.points ++ ChenEffective.PlattWindow.PointPackets.S1B000469.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000470.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000471.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000057.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000057.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000057
