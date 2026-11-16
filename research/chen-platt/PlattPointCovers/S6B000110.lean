import PlattPointSubsetKernel
import PlattPointPackets.S2B000029
import PlattPointPackets.S2B000030
import PlattPointPackets.S2B000031
import PlattGlobalGrid.S6B000110
namespace ChenEffective.PlattWindow.PointCovers.S6B000110
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S2B000029.points ++ ChenEffective.PlattWindow.PointPackets.S2B000030.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000031.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000110.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000110.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000110
