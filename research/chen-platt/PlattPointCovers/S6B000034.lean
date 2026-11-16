import PlattPointSubsetKernel
import PlattPointPackets.S1B000392
import PlattPointPackets.S1B000393
import PlattPointPackets.S1B000394
import PlattPointPackets.S1B000395
import PlattGlobalGrid.S6B000034
namespace ChenEffective.PlattWindow.PointCovers.S6B000034
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000392.points ++ ChenEffective.PlattWindow.PointPackets.S1B000393.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000394.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000395.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000034.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000034.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000034
