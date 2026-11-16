import PlattPointSubsetKernel
import PlattPointPackets.S1B000572
import PlattPointPackets.S1B000573
import PlattPointPackets.S1B000574
import PlattPointPackets.S1B000575
import PlattPointPackets.S1B000576
import PlattPointPackets.S1B000577
import PlattGlobalGrid.S6B000083
namespace ChenEffective.PlattWindow.PointCovers.S6B000083
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S1B000572.points ++ ChenEffective.PlattWindow.PointPackets.S1B000573.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000574.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000575.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000576.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000577.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000083.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000083.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000083
