import PlattPointSubsetKernel
import PlattPointPackets.S1B000345
import PlattPointPackets.S1B000346
import PlattPointPackets.S1B000347
import PlattGlobalGrid.S6B000017
namespace ChenEffective.PlattWindow.PointCovers.S6B000017
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000345.points ++ ChenEffective.PlattWindow.PointPackets.S1B000346.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000347.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000017.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000017.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000017
