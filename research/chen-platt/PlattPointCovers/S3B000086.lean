import PlattPointSubsetKernel
import PlattPointPackets.S1B000053
import PlattPointPackets.S1B000054
import PlattGlobalGrid.S3B000086
namespace ChenEffective.PlattWindow.PointCovers.S3B000086
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000053.points ++ ChenEffective.PlattWindow.PointPackets.S1B000054.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S3B000086.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S3B000086.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S3B000086
