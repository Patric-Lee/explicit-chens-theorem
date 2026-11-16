import PlattPointSubsetKernel
import PlattPointPackets.S1B000355
import PlattPointPackets.S1B000356
import PlattPointPackets.S1B000357
import PlattPointPackets.S1B000358
import PlattGlobalGrid.S6B000021
namespace ChenEffective.PlattWindow.PointCovers.S6B000021
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000355.points ++ ChenEffective.PlattWindow.PointPackets.S1B000356.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000357.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000358.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000021.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000021.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000021
