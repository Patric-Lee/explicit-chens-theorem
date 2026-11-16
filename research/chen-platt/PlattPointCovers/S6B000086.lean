import PlattPointSubsetKernel
import PlattPointPackets.S1B000586
import PlattPointPackets.S1B000587
import PlattPointPackets.S1B000588
import PlattPointPackets.S1B000589
import PlattPointPackets.S1B000590
import PlattGlobalGrid.S6B000086
namespace ChenEffective.PlattWindow.PointCovers.S6B000086
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000586.points ++ ChenEffective.PlattWindow.PointPackets.S1B000587.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000588.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000589.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000590.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000086.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000086.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000086
