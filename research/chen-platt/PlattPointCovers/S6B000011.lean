import PlattPointSubsetKernel
import PlattPointPackets.S1B000329
import PlattPointPackets.S1B000330
import PlattPointPackets.S1B000331
import PlattPointPackets.S1B000332
import PlattGlobalGrid.S6B000011
namespace ChenEffective.PlattWindow.PointCovers.S6B000011
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000329.points ++ ChenEffective.PlattWindow.PointPackets.S1B000330.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000331.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000332.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000011.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000011.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000011
