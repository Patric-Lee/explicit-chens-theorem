import PlattPointSubsetKernel
import PlattPointPackets.S1B000638
import PlattPointPackets.S1B000639
import PlattPointPackets.S1B000640
import PlattPointPackets.S1B000641
import PlattPointPackets.S1B000642
import PlattPointPackets.S1B000643
import PlattGlobalGrid.S6B000097
namespace ChenEffective.PlattWindow.PointCovers.S6B000097
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S1B000638.points ++ ChenEffective.PlattWindow.PointPackets.S1B000639.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000640.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000641.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000642.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000643.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000097.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000097.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000097
