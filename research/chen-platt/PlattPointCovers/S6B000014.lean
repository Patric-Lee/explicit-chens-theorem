import PlattPointSubsetKernel
import PlattPointPackets.S1B000337
import PlattPointPackets.S1B000338
import PlattPointPackets.S1B000339
import PlattGlobalGrid.S6B000014
namespace ChenEffective.PlattWindow.PointCovers.S6B000014
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000337.points ++ ChenEffective.PlattWindow.PointPackets.S1B000338.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000339.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000014.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000014.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000014
