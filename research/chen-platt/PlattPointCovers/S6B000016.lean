import PlattPointSubsetKernel
import PlattPointPackets.S1B000342
import PlattPointPackets.S1B000343
import PlattPointPackets.S1B000344
import PlattPointPackets.S1B000345
import PlattGlobalGrid.S6B000016
namespace ChenEffective.PlattWindow.PointCovers.S6B000016
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000342.points ++ ChenEffective.PlattWindow.PointPackets.S1B000343.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000344.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000345.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000016.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000016.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000016
