import PlattPointSubsetKernel
import PlattPointPackets.S1B000430
import PlattPointPackets.S1B000431
import PlattPointPackets.S1B000432
import PlattPointPackets.S1B000433
import PlattGlobalGrid.S6B000046
namespace ChenEffective.PlattWindow.PointCovers.S6B000046
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000430.points ++ ChenEffective.PlattWindow.PointPackets.S1B000431.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000432.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000433.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000046.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000046.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000046
