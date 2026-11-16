import PlattPointSubsetKernel
import PlattPointPackets.S2B000058
import PlattPointPackets.S2B000059
import PlattPointPackets.S2B000060
import PlattPointPackets.S2B000061
import PlattGlobalGrid.S7B000003
namespace ChenEffective.PlattWindow.PointCovers.S7B000003
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000058.points ++ ChenEffective.PlattWindow.PointPackets.S2B000059.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000060.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000061.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000003.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000003.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000003
