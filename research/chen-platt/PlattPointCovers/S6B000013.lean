import PlattPointSubsetKernel
import PlattPointPackets.S1B000334
import PlattPointPackets.S1B000335
import PlattPointPackets.S1B000336
import PlattPointPackets.S1B000337
import PlattGlobalGrid.S6B000013
namespace ChenEffective.PlattWindow.PointCovers.S6B000013
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000334.points ++ ChenEffective.PlattWindow.PointPackets.S1B000335.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000336.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000337.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000013.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000013.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000013
