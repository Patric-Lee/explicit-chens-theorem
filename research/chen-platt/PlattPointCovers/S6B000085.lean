import PlattPointSubsetKernel
import PlattPointPackets.S1B000581
import PlattPointPackets.S1B000582
import PlattPointPackets.S1B000583
import PlattPointPackets.S1B000584
import PlattPointPackets.S1B000585
import PlattPointPackets.S1B000586
import PlattGlobalGrid.S6B000085
namespace ChenEffective.PlattWindow.PointCovers.S6B000085
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S1B000581.points ++ ChenEffective.PlattWindow.PointPackets.S1B000582.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000583.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000584.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000585.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000586.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000085.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000085.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000085
