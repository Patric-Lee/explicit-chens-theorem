import PlattPointSubsetKernel
import PlattPointPackets.S3B000100
import PlattPointPackets.S3B000101
import PlattPointPackets.S3B000102
import PlattPointPackets.S3B000103
import PlattPointPackets.S3B000104
import PlattPointPackets.S3B000105
import PlattPointPackets.S3B000106
import PlattGlobalGrid.S7B000086
namespace ChenEffective.PlattWindow.PointCovers.S7B000086
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000100.points ++ ChenEffective.PlattWindow.PointPackets.S3B000101.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000102.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000103.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000104.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000105.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000106.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000086.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000086.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000086
