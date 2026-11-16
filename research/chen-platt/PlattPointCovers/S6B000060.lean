import PlattPointSubsetKernel
import PlattPointPackets.S1B000479
import PlattPointPackets.S1B000480
import PlattPointPackets.S1B000481
import PlattPointPackets.S1B000482
import PlattGlobalGrid.S6B000060
namespace ChenEffective.PlattWindow.PointCovers.S6B000060
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000479.points ++ ChenEffective.PlattWindow.PointPackets.S1B000480.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000481.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000482.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000060.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000060.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000060
