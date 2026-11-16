import PlattPointSubsetKernel
import PlattPointPackets.S2B000026
import PlattPointPackets.S2B000027
import PlattPointPackets.S2B000028
import PlattPointPackets.S2B000029
import PlattGlobalGrid.S6B000109
namespace ChenEffective.PlattWindow.PointCovers.S6B000109
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000026.points ++ ChenEffective.PlattWindow.PointPackets.S2B000027.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000028.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000029.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000109.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000109.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000109
