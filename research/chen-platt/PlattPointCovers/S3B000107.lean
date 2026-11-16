import PlattPointSubsetKernel
import PlattPointPackets.S1B000059
import PlattPointPackets.S1B000060
import PlattGlobalGrid.S3B000107
namespace ChenEffective.PlattWindow.PointCovers.S3B000107
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000059.points ++ ChenEffective.PlattWindow.PointPackets.S1B000060.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S3B000107.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S3B000107.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S3B000107
