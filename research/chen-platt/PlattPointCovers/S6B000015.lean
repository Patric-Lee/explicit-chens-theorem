import PlattPointSubsetKernel
import PlattPointPackets.S1B000339
import PlattPointPackets.S1B000340
import PlattPointPackets.S1B000341
import PlattPointPackets.S1B000342
import PlattGlobalGrid.S6B000015
namespace ChenEffective.PlattWindow.PointCovers.S6B000015
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000339.points ++ ChenEffective.PlattWindow.PointPackets.S1B000340.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000341.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000342.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000015.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000015.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000015
