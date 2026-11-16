import PlattPointSubsetKernel
import PlattPointPackets.S1B000457
import PlattPointPackets.S1B000458
import PlattPointPackets.S1B000459
import PlattPointPackets.S1B000460
import PlattPointPackets.S1B000461
import PlattGlobalGrid.S6B000054
namespace ChenEffective.PlattWindow.PointCovers.S6B000054
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000457.points ++ ChenEffective.PlattWindow.PointPackets.S1B000458.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000459.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000460.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000461.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000054.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000054.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000054
